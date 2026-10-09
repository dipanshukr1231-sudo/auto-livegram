"""
Central Owner Bot + Multi-Clone Bot Management System.

Single-file application:
  * Owner Bot (BOT_TOKEN) - private management interface for the platform owner,
    delegated managers and clone administrators.
  * Up to MAX_CLONES clone bots, each running its own python-telegram-bot
    Application on the same event loop under a supervisor.
  * SQLite (aiosqlite) or PostgreSQL (asyncpg) persistence, selected by DATABASE_URL.
  * Fernet-encrypted clone tokens (ENCRYPTION_KEY).
  * Cross-bot message relay (user -> admins via Owner Bot, admin -> user via clone),
    persisted broadcast engine with live progress, backup/restore, diagnostics and
    a Render-compatible HTTP health server.
"""

import asyncio
import csv
import html
import io
import json
import logging
import os
import re
import secrets
import shutil
import signal
import sqlite3
import sys
import threading
import time
import traceback
import uuid
import zipfile
from contextlib import asynccontextmanager
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any, Callable, Optional
from urllib.parse import urlparse

import aiosqlite
from cryptography.fernet import Fernet, InvalidToken
from telegram import (
    Bot,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    InputFile,
    Message,
    MessageEntity,
    Update,
    User,
)
from telegram.constants import MessageLimit, ParseMode
from telegram.error import (
    BadRequest,
    Conflict,
    Forbidden,
    InvalidToken as TelegramInvalidToken,
    NetworkError,
    RetryAfter,
    TelegramError,
    TimedOut,
)
from telegram.ext import (
    AIORateLimiter,
    Application,
    ApplicationBuilder,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    filters,
)
from telegram.request import HTTPXRequest

try:  # PostgreSQL support is optional at import time; required only when DATABASE_URL is set.
    import asyncpg  # type: ignore
except Exception:  # pragma: no cover - asyncpg missing
    asyncpg = None

# --------------------------------------------------------------------------------------
# Configuration
# --------------------------------------------------------------------------------------

APP_VERSION = "2.0.0"
SCHEMA_VERSION = 2
MAX_CLONES = 50
MAX_BROADCAST_BUTTONS = 6
MAX_MEDIA_BYTES = 20 * 1024 * 1024  # Bot API download limit for bots
STATE_TIMEOUT_SECONDS = 30 * 60
PROGRESS_EDIT_INTERVAL = 3.0
PAGE_SIZE = 8


def _env_int(name: str, default: int, lo: int, hi: int) -> int:
    try:
        return max(lo, min(hi, int(os.environ.get(name, str(default)))))
    except ValueError:
        return default


def _env_ids(name: str) -> set:
    return {
        int(value.strip())
        for value in os.environ.get(name, "").split(",")
        if value.strip().lstrip("-").isdigit()
    }


TOKEN = os.environ.get("BOT_TOKEN", "").strip()
DATABASE_URL = os.environ.get("DATABASE_URL", "").strip()
DATABASE_PATH = Path(os.environ.get("DATABASE_PATH", "data/bot.db")).expanduser().resolve()
BACKUP_DIR = Path(os.environ.get("BACKUP_DIR", "data/backups")).expanduser().resolve()
MEDIA_TMP_DIR = Path(os.environ.get("MEDIA_TMP_DIR", "data/tmp")).expanduser().resolve()
ENCRYPTION_KEY = os.environ.get("ENCRYPTION_KEY", "").strip()
ALLOW_EPHEMERAL_SQLITE = os.environ.get("ALLOW_EPHEMERAL_SQLITE", "0").strip() == "1"
ACTIVE_DAYS = _env_int("ACTIVE_DAYS", 30, 1, 365)
BROADCAST_WORKERS = _env_int("BROADCAST_WORKERS", 8, 1, 20)
BROADCAST_PER_CLONE_CONCURRENCY = _env_int("BROADCAST_PER_CLONE_CONCURRENCY", 4, 1, 10)
BROADCAST_MAX_RETRIES = _env_int("BROADCAST_MAX_RETRIES", 3, 0, 10)
CLONE_RESTART_LIMIT = _env_int("CLONE_RESTART_LIMIT", 5, 0, 50)
AUTO_START_CLONES = os.environ.get("AUTO_START_CLONES", "1").strip() != "0"
LOG_LEVEL = os.environ.get("LOG_LEVEL", "INFO").upper()
INITIAL_OWNER_IDS = _env_ids("OWNER_IDS")
INITIAL_ADMIN_IDS = _env_ids("ADMIN_IDS")  # backward compatible: become delegated managers
if not INITIAL_OWNER_IDS:
    INITIAL_OWNER_IDS = set(INITIAL_ADMIN_IDS)
DEFAULT_START = os.environ.get("DEFAULT_START_MESSAGE", "Hello, Welcome to our bot!")
DEFAULT_MAINTENANCE = os.environ.get(
    "DEFAULT_MAINTENANCE_MESSAGE", "The bot is temporarily under maintenance. Please try again later."
)
WEB_HOST = os.environ.get("WEB_HOST", "0.0.0.0")
WEB_PORT = int(os.environ.get("PORT", os.environ.get("WEB_PORT", "10000")))

# --------------------------------------------------------------------------------------
# Logging with secret redaction
# --------------------------------------------------------------------------------------

TOKEN_RE = re.compile(r"\b\d{6,12}:[A-Za-z0-9_-]{30,}\b")


def redact(text: object) -> str:
    value = str(text)
    value = TOKEN_RE.sub("<redacted-token>", value)
    if TOKEN:
        value = value.replace(TOKEN, "<redacted-token>")
    if ENCRYPTION_KEY:
        value = value.replace(ENCRYPTION_KEY, "<redacted-key>")
    return value


class RedactingFormatter(logging.Formatter):
    def format(self, record: logging.LogRecord) -> str:
        return redact(super().format(record))


_handler = logging.StreamHandler(sys.stdout)
_handler.setFormatter(RedactingFormatter("%(asctime)s | %(levelname)s | %(name)s | %(message)s"))
logging.basicConfig(level=getattr(logging, LOG_LEVEL, logging.INFO), handlers=[_handler])
logging.getLogger("httpx").setLevel(logging.WARNING)
logging.getLogger("telegram").setLevel(logging.WARNING)
logger = logging.getLogger("owner_platform")

# --------------------------------------------------------------------------------------
# Small utilities
# --------------------------------------------------------------------------------------


def utcnow() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def now_dt() -> datetime:
    return datetime.now(timezone.utc)


def today() -> str:
    return now_dt().date().isoformat()


def days_ago_iso(days: int) -> str:
    return (now_dt() - timedelta(days=days)).isoformat(timespec="seconds")


def esc(value: object) -> str:
    return html.escape(str(value if value is not None else ""))


def fmt_int(value: object) -> str:
    try:
        return f"{int(value or 0):,}"
    except (TypeError, ValueError):
        return "0"


def human_duration(seconds: float) -> str:
    seconds = max(0, int(seconds))
    days, seconds = divmod(seconds, 86400)
    hours, seconds = divmod(seconds, 3600)
    minutes, seconds = divmod(seconds, 60)
    parts = []
    if days:
        parts.append(f"{days}d")
    if hours or days:
        parts.append(f"{hours}h")
    if minutes or hours or days:
        parts.append(f"{minutes}m")
    parts.append(f"{seconds}s")
    return " ".join(parts)


def short_time(iso: Optional[str]) -> str:
    if not iso:
        return "-"
    return iso.replace("T", " ").replace("+00:00", " UTC")


def utf16_len(text: str) -> int:
    return len(text.encode("utf-16-le")) // 2


def mask_token(token: str) -> str:
    bot_id = token.split(":", 1)[0] if ":" in token else "?"
    return f"{bot_id}:••••••••"


def parse_int(text: str) -> Optional[int]:
    text = (text or "").strip()
    if text.lstrip("-").isdigit():
        try:
            return int(text)
        except ValueError:
            return None
    return None


def user_label(first_name: Optional[str], last_name: Optional[str], username: Optional[str], user_id: int) -> str:
    name = " ".join(p for p in [first_name or "", last_name or ""] if p).strip() or "Unknown"
    if username:
        return f"{name} (@{username})"
    return f"{name} [{user_id}]"


def validate_button_url(url: str) -> tuple[bool, str]:
    """Return (ok, reason). Only http(s), tg:// and t.me style destinations are accepted."""
    url = (url or "").strip()
    if not url or len(url) > 1024:
        return False, "The URL is empty or too long."
    if any(ch.isspace() for ch in url):
        return False, "The URL must not contain spaces."
    try:
        parsed = urlparse(url)
    except ValueError:
        return False, "The URL could not be parsed."
    scheme = (parsed.scheme or "").lower()
    if scheme in {"http", "https"}:
        if not parsed.netloc or "." not in parsed.netloc:
            return False, "The URL must contain a valid host name."
        return True, ""
    if scheme == "tg":
        if parsed.netloc in {"resolve", "user", "join", "addstickers", "login"}:
            return True, ""
        return False, "Only tg://resolve, tg://user, tg://join and tg://addstickers links are allowed."
    return False, "Only http://, https:// and tg:// links are allowed."


def validate_token_format(token: str) -> bool:
    return bool(re.fullmatch(r"\d{6,12}:[A-Za-z0-9_-]{30,}", token or ""))


# --------------------------------------------------------------------------------------
# Token encryption
# --------------------------------------------------------------------------------------


class TokenVault:
    def __init__(self, key: str):
        try:
            self._fernet = Fernet(key.encode())
        except Exception as exc:  # invalid key material
            raise RuntimeError(
                "ENCRYPTION_KEY is invalid. Generate one with: "
                "python -c \"from cryptography.fernet import Fernet; print(Fernet.generate_key().decode())\""
            ) from exc

    def encrypt(self, token: str) -> str:
        return self._fernet.encrypt(token.encode()).decode()

    def decrypt(self, blob: str) -> str:
        try:
            return self._fernet.decrypt(blob.encode()).decode()
        except InvalidToken as exc:
            raise RuntimeError("Stored clone token cannot be decrypted with the configured ENCRYPTION_KEY.") from exc

    @staticmethod
    def fingerprint(token: str) -> str:
        import hashlib

        return hashlib.sha256(token.encode()).hexdigest()

# --------------------------------------------------------------------------------------
# Database layer (SQLite via aiosqlite, PostgreSQL via asyncpg)
# --------------------------------------------------------------------------------------

SCHEMA_TABLES = [
    """CREATE TABLE IF NOT EXISTS schema_version (
        version INTEGER NOT NULL,
        applied_at TEXT NOT NULL
    )""",
    """CREATE TABLE IF NOT EXISTS owners (
        user_id BIGINT PRIMARY KEY,
        added_at TEXT NOT NULL
    )""",
    """CREATE TABLE IF NOT EXISTS managers (
        user_id BIGINT PRIMARY KEY,
        permissions TEXT NOT NULL,
        added_at TEXT NOT NULL,
        added_by BIGINT
    )""",
    """CREATE TABLE IF NOT EXISTS settings (
        key TEXT PRIMARY KEY,
        value TEXT NOT NULL,
        updated_at TEXT NOT NULL
    )""",
    """CREATE TABLE IF NOT EXISTS clones (
        id {PK},
        bot_id BIGINT NOT NULL UNIQUE,
        username TEXT NOT NULL,
        display_name TEXT NOT NULL,
        token_enc TEXT NOT NULL,
        token_fingerprint TEXT NOT NULL UNIQUE,
        admin_id BIGINT NOT NULL,
        status TEXT NOT NULL,
        desired_running INTEGER NOT NULL DEFAULT 1,
        last_error TEXT,
        restart_count INTEGER NOT NULL DEFAULT 0,
        created_by BIGINT,
        created_at TEXT NOT NULL,
        updated_at TEXT NOT NULL,
        started_at TEXT,
        last_activity TEXT,
        deleted_at TEXT
    )""",
    """CREATE TABLE IF NOT EXISTS clone_operators (
        clone_id BIGINT NOT NULL REFERENCES clones(id) ON DELETE CASCADE,
        user_id BIGINT NOT NULL,
        added_at TEXT NOT NULL,
        added_by BIGINT,
        PRIMARY KEY(clone_id, user_id)
    )""",
    """CREATE TABLE IF NOT EXISTS clone_settings (
        clone_id BIGINT NOT NULL REFERENCES clones(id) ON DELETE CASCADE,
        key TEXT NOT NULL,
        value TEXT NOT NULL,
        updated_at TEXT NOT NULL,
        PRIMARY KEY(clone_id, key)
    )""",
    """CREATE TABLE IF NOT EXISTS platform_users (
        user_id BIGINT PRIMARY KEY,
        username TEXT,
        first_name TEXT,
        last_name TEXT,
        language_code TEXT,
        first_seen TEXT NOT NULL,
        last_seen TEXT NOT NULL
    )""",
    """CREATE TABLE IF NOT EXISTS clone_users (
        clone_id BIGINT NOT NULL REFERENCES clones(id) ON DELETE CASCADE,
        user_id BIGINT NOT NULL,
        username TEXT,
        first_name TEXT,
        last_name TEXT,
        language_code TEXT,
        is_banned INTEGER NOT NULL DEFAULT 0,
        is_active INTEGER NOT NULL DEFAULT 1,
        unread INTEGER NOT NULL DEFAULT 0,
        created_at TEXT NOT NULL,
        last_seen TEXT NOT NULL,
        last_message_at TEXT,
        last_answered_at TEXT,
        PRIMARY KEY(clone_id, user_id)
    )""",
    """CREATE TABLE IF NOT EXISTS message_log (
        id {PK},
        clone_id BIGINT NOT NULL,
        direction TEXT NOT NULL,
        user_id BIGINT,
        admin_id BIGINT,
        message_type TEXT NOT NULL,
        telegram_chat_id BIGINT,
        telegram_message_id BIGINT,
        related_message_id BIGINT,
        preview TEXT,
        created_at TEXT NOT NULL,
        UNIQUE(clone_id, direction, telegram_chat_id, telegram_message_id)
    )""",
    """CREATE TABLE IF NOT EXISTS forward_map (
        admin_chat_id BIGINT NOT NULL,
        admin_message_id BIGINT NOT NULL,
        clone_id BIGINT NOT NULL,
        user_id BIGINT NOT NULL,
        user_message_id BIGINT,
        created_at TEXT NOT NULL,
        PRIMARY KEY(admin_chat_id, admin_message_id)
    )""",
    """CREATE TABLE IF NOT EXISTS processed_updates (
        clone_id BIGINT NOT NULL,
        update_id BIGINT NOT NULL,
        processed_at TEXT NOT NULL,
        PRIMARY KEY(clone_id, update_id)
    )""",
    """CREATE TABLE IF NOT EXISTS broadcasts (
        id {PK},
        created_by BIGINT NOT NULL,
        origin TEXT NOT NULL,
        payload TEXT NOT NULL,
        buttons TEXT NOT NULL,
        status TEXT NOT NULL,
        total INTEGER NOT NULL DEFAULT 0,
        success INTEGER NOT NULL DEFAULT 0,
        failed INTEGER NOT NULL DEFAULT 0,
        progress_chat_id BIGINT,
        progress_message_id BIGINT,
        created_at TEXT NOT NULL,
        started_at TEXT,
        finished_at TEXT,
        error TEXT
    )""",
    """CREATE TABLE IF NOT EXISTS broadcast_targets (
        broadcast_id BIGINT NOT NULL REFERENCES broadcasts(id) ON DELETE CASCADE,
        clone_id BIGINT NOT NULL,
        status TEXT NOT NULL,
        total INTEGER NOT NULL DEFAULT 0,
        success INTEGER NOT NULL DEFAULT 0,
        failed INTEGER NOT NULL DEFAULT 0,
        error TEXT,
        PRIMARY KEY(broadcast_id, clone_id)
    )""",
    """CREATE TABLE IF NOT EXISTS broadcast_deliveries (
        broadcast_id BIGINT NOT NULL REFERENCES broadcasts(id) ON DELETE CASCADE,
        clone_id BIGINT NOT NULL,
        user_id BIGINT NOT NULL,
        status TEXT NOT NULL,
        attempts INTEGER NOT NULL DEFAULT 0,
        error TEXT,
        delivered_at TEXT,
        PRIMARY KEY(broadcast_id, clone_id, user_id)
    )""",
    """CREATE TABLE IF NOT EXISTS daily_stats (
        clone_id BIGINT NOT NULL,
        day TEXT NOT NULL,
        new_users INTEGER NOT NULL DEFAULT 0,
        incoming INTEGER NOT NULL DEFAULT 0,
        outgoing INTEGER NOT NULL DEFAULT 0,
        admin_replies INTEGER NOT NULL DEFAULT 0,
        broadcast_success INTEGER NOT NULL DEFAULT 0,
        broadcast_failed INTEGER NOT NULL DEFAULT 0,
        PRIMARY KEY(clone_id, day)
    )""",
    """CREATE TABLE IF NOT EXISTS errors (
        id {PK},
        clone_id BIGINT,
        context TEXT NOT NULL,
        error TEXT NOT NULL,
        traceback TEXT,
        created_at TEXT NOT NULL
    )""",
    """CREATE TABLE IF NOT EXISTS audit_log (
        id {PK},
        actor_id BIGINT,
        clone_id BIGINT,
        action TEXT NOT NULL,
        detail TEXT,
        result TEXT NOT NULL,
        created_at TEXT NOT NULL
    )""",
    """CREATE TABLE IF NOT EXISTS backups (
        id {PK},
        filename TEXT NOT NULL,
        size_bytes BIGINT NOT NULL,
        kind TEXT NOT NULL,
        created_by BIGINT,
        created_at TEXT NOT NULL
    )""",
]

SCHEMA_INDEXES = [
    "CREATE INDEX IF NOT EXISTS idx_clone_users_seen ON clone_users(clone_id, last_seen)",
    "CREATE INDEX IF NOT EXISTS idx_clone_users_user ON clone_users(user_id)",
    "CREATE INDEX IF NOT EXISTS idx_clone_users_unread ON clone_users(clone_id, unread)",
    "CREATE INDEX IF NOT EXISTS idx_message_log_user ON message_log(clone_id, user_id, created_at)",
    "CREATE INDEX IF NOT EXISTS idx_message_log_date ON message_log(created_at)",
    "CREATE INDEX IF NOT EXISTS idx_forward_map_user ON forward_map(clone_id, user_id)",
    "CREATE INDEX IF NOT EXISTS idx_deliveries_status ON broadcast_deliveries(broadcast_id, status)",
    "CREATE INDEX IF NOT EXISTS idx_errors_date ON errors(created_at)",
    "CREATE INDEX IF NOT EXISTS idx_audit_date ON audit_log(created_at)",
    "CREATE INDEX IF NOT EXISTS idx_processed_time ON processed_updates(processed_at)",
]

BACKUP_TABLES = [
    "owners", "managers", "settings", "clones", "clone_operators", "clone_settings",
    "platform_users", "clone_users", "message_log", "forward_map", "broadcasts",
    "broadcast_targets", "broadcast_deliveries", "daily_stats", "errors", "audit_log", "backups",
]

INTEGRITY_ERRORS: tuple = (sqlite3.IntegrityError,)
if asyncpg is not None:
    INTEGRITY_ERRORS = (sqlite3.IntegrityError, asyncpg.UniqueViolationError, asyncpg.IntegrityConstraintViolationError)


def _pg_sql(sql: str) -> str:
    """Convert '?' placeholders to $1..$n (ignores '?' inside quotes)."""
    out = []
    n = 0
    in_quote = False
    for ch in sql:
        if ch == "'":
            in_quote = not in_quote
        if ch == "?" and not in_quote:
            n += 1
            out.append(f"${n}")
        else:
            out.append(ch)
    return "".join(out)


class _SqliteTx:
    def __init__(self, conn):
        self.conn = conn

    async def execute(self, sql: str, params=()):
        cur = await self.conn.execute(sql, params)
        return cur.rowcount

    async def fetchone(self, sql: str, params=()):
        async with self.conn.execute(sql, params) as cur:
            row = await cur.fetchone()
            return dict(row) if row is not None else None

    async def fetchall(self, sql: str, params=()):
        async with self.conn.execute(sql, params) as cur:
            return [dict(r) for r in await cur.fetchall()]

    async def fetchval(self, sql: str, params=()):
        row = await self.fetchone(sql, params)
        if row is None:
            return None
        return next(iter(row.values()))


class _PgTx:
    def __init__(self, conn):
        self.conn = conn

    async def execute(self, sql: str, params=()):
        status = await self.conn.execute(_pg_sql(sql), *params)
        try:
            return int(status.split()[-1])
        except (ValueError, IndexError):
            return 0

    async def fetchone(self, sql: str, params=()):
        row = await self.conn.fetchrow(_pg_sql(sql), *params)
        return dict(row) if row is not None else None

    async def fetchall(self, sql: str, params=()):
        return [dict(r) for r in await self.conn.fetch(_pg_sql(sql), *params)]

    async def fetchval(self, sql: str, params=()):
        return await self.conn.fetchval(_pg_sql(sql), *params)


class Database:
    """Thin async DB abstraction with identical semantics for SQLite and PostgreSQL."""

    def __init__(self):
        self.is_postgres = bool(DATABASE_URL)
        self.pool = None
        self.write_lock = asyncio.Lock()
        self.ready = False
        self.last_error: Optional[str] = None

    # ---- connection management ---------------------------------------------------
    async def open(self):
        if self.is_postgres:
            if asyncpg is None:
                raise RuntimeError("DATABASE_URL is set but asyncpg is not installed.")
            self.pool = await asyncpg.create_pool(DATABASE_URL, min_size=1, max_size=10, command_timeout=60)
        else:
            DATABASE_PATH.parent.mkdir(parents=True, exist_ok=True)
            async with self._sqlite() as conn:
                await conn.execute("PRAGMA journal_mode=WAL")
        await self._migrate()
        self.ready = True

    async def close(self):
        if self.pool is not None:
            await self.pool.close()
            self.pool = None
        self.ready = False

    @asynccontextmanager
    async def _sqlite(self):
        conn = await aiosqlite.connect(DATABASE_PATH, timeout=30)
        conn.row_factory = aiosqlite.Row
        try:
            await conn.execute("PRAGMA foreign_keys=ON")
            await conn.execute("PRAGMA busy_timeout=10000")
            yield conn
        finally:
            await conn.close()

    @asynccontextmanager
    async def transaction(self):
        """Serialized write transaction. Yields an object with execute/fetchone/fetchall/fetchval."""
        if self.is_postgres:
            async with self.pool.acquire() as conn:
                async with conn.transaction():
                    yield _PgTx(conn)
        else:
            async with self.write_lock:
                async with self._sqlite() as conn:
                    try:
                        await conn.execute("BEGIN IMMEDIATE")
                        yield _SqliteTx(conn)
                        await conn.commit()
                    except BaseException:
                        await conn.rollback()
                        raise

    async def execute(self, sql: str, params=()) -> int:
        async with self.transaction() as tx:
            return await tx.execute(sql, params)

    async def insert(self, sql: str, params=()) -> int:
        """Execute an INSERT ... RETURNING id and return the id."""
        async with self.transaction() as tx:
            return await tx.fetchval(sql, params)

    async def fetchone(self, sql: str, params=()):
        if self.is_postgres:
            async with self.pool.acquire() as conn:
                return await _PgTx(conn).fetchone(sql, params)
        async with self._sqlite() as conn:
            return await _SqliteTx(conn).fetchone(sql, params)

    async def fetchall(self, sql: str, params=()):
        if self.is_postgres:
            async with self.pool.acquire() as conn:
                return await _PgTx(conn).fetchall(sql, params)
        async with self._sqlite() as conn:
            return await _SqliteTx(conn).fetchall(sql, params)

    async def fetchval(self, sql: str, params=()):
        row = await self.fetchone(sql, params)
        if row is None:
            return None
        return next(iter(row.values()))

    async def ping(self) -> bool:
        try:
            await self.fetchval("SELECT 1")
            self.last_error = None
            return True
        except Exception as exc:
            self.last_error = redact(exc)
            return False

    async def size_bytes(self) -> Optional[int]:
        try:
            if self.is_postgres:
                return int(await self.fetchval("SELECT pg_database_size(current_database())"))
            return DATABASE_PATH.stat().st_size if DATABASE_PATH.exists() else 0
        except Exception:
            return None

    # ---- schema ----------------------------------------------------------------------
    async def _migrate(self):
        pk = "BIGSERIAL PRIMARY KEY" if self.is_postgres else "INTEGER PRIMARY KEY AUTOINCREMENT"
        async with self.transaction() as tx:
            for stmt in SCHEMA_TABLES:
                await tx.execute(stmt.replace("{PK}", pk))
            for stmt in SCHEMA_INDEXES:
                await tx.execute(stmt)
            row = await tx.fetchone("SELECT MAX(version) AS v FROM schema_version")
            current = int(row["v"]) if row and row["v"] is not None else 0
            if current < 1:
                await self._migrate_legacy(tx)
                await tx.execute("INSERT INTO schema_version(version, applied_at) VALUES(?,?)", (1, utcnow()))
            if current < 2:
                await tx.execute("INSERT INTO schema_version(version, applied_at) VALUES(?,?)", (2, utcnow()))
            now = utcnow()
            for key, value in {
                "default_start_message": DEFAULT_START,
                "default_maintenance_message": DEFAULT_MAINTENANCE,
                "notify_owners_on_user_message": "0",
                "forward_header": "1",
            }.items():
                await tx.execute(
                    "INSERT INTO settings(key,value,updated_at) VALUES(?,?,?) ON CONFLICT(key) DO NOTHING",
                    (key, value, now),
                )
            for owner_id in INITIAL_OWNER_IDS:
                await tx.execute(
                    "INSERT INTO owners(user_id,added_at) VALUES(?,?) ON CONFLICT(user_id) DO NOTHING",
                    (owner_id, now),
                )
            first_owner = next(iter(sorted(INITIAL_OWNER_IDS)), None)
            for admin_id in INITIAL_ADMIN_IDS - INITIAL_OWNER_IDS:
                await tx.execute(
                    "INSERT INTO managers(user_id,permissions,added_at,added_by) VALUES(?,?,?,?) ON CONFLICT(user_id) DO NOTHING",
                    (admin_id, json.dumps(sorted(DEFAULT_MANAGER_PERMS)), now, first_owner),
                )

    async def _migrate_legacy(self, tx):
        """Import data from the single-bot schema (legacy 'users' and 'admins' tables) if present."""
        if self.is_postgres:
            return
        tables = {r["name"] for r in await tx.fetchall("SELECT name FROM sqlite_master WHERE type='table'")}
        if "admins" in tables:
            rows = await tx.fetchall("SELECT user_id, added_at, added_by FROM admins")
            for r in rows:
                await tx.execute(
                    "INSERT INTO managers(user_id,permissions,added_at,added_by) VALUES(?,?,?,?) ON CONFLICT(user_id) DO NOTHING",
                    (r["user_id"], json.dumps(sorted(DEFAULT_MANAGER_PERMS)), r["added_at"], r["added_by"]),
                )
        if "users" in tables:
            rows = await tx.fetchall("SELECT * FROM users")
            for r in rows:
                await tx.execute(
                    """INSERT INTO platform_users(user_id,username,first_name,last_name,language_code,first_seen,last_seen)
                    VALUES(?,?,?,?,?,?,?) ON CONFLICT(user_id) DO NOTHING""",
                    (r["user_id"], r["username"], r["first_name"], r["last_name"], r["language_code"], r["created_at"], r["last_seen"]),
                )
        legacy_msg = await tx.fetchone("SELECT value FROM settings WHERE key='start_message'")
        if legacy_msg:
            await tx.execute(
                "INSERT INTO settings(key,value,updated_at) VALUES(?,?,?) ON CONFLICT(key) DO UPDATE SET value=excluded.value",
                ("default_start_message", legacy_msg["value"], utcnow()),
            )
        legacy_m = await tx.fetchone("SELECT value FROM settings WHERE key='maintenance_message'")
        if legacy_m:
            await tx.execute(
                "INSERT INTO settings(key,value,updated_at) VALUES(?,?,?) ON CONFLICT(key) DO UPDATE SET value=excluded.value",
                ("default_maintenance_message", legacy_m["value"], utcnow()),
            )

    # ---- settings ----------------------------------------------------------------------
    async def setting(self, key: str, default: str = "") -> str:
        row = await self.fetchone("SELECT value FROM settings WHERE key=?", (key,))
        return row["value"] if row else default

    async def set_setting(self, key: str, value: str):
        await self.execute(
            "INSERT INTO settings(key,value,updated_at) VALUES(?,?,?) ON CONFLICT(key) DO UPDATE SET value=excluded.value, updated_at=excluded.updated_at",
            (key, value, utcnow()),
        )

    async def clone_setting(self, clone_id: int, key: str, default: str = "") -> str:
        row = await self.fetchone("SELECT value FROM clone_settings WHERE clone_id=? AND key=?", (clone_id, key))
        return row["value"] if row else default

    async def set_clone_setting(self, clone_id: int, key: str, value: str):
        await self.execute(
            """INSERT INTO clone_settings(clone_id,key,value,updated_at) VALUES(?,?,?,?)
            ON CONFLICT(clone_id,key) DO UPDATE SET value=excluded.value, updated_at=excluded.updated_at""",
            (clone_id, key, value, utcnow()),
        )

    # ---- roles -----------------------------------------------------------------------------
    async def is_owner(self, user_id: int) -> bool:
        return bool(await self.fetchone("SELECT 1 FROM owners WHERE user_id=?", (user_id,)))

    async def owner_ids(self) -> list:
        return [r["user_id"] for r in await self.fetchall("SELECT user_id FROM owners ORDER BY added_at")]

    async def manager_perms(self, user_id: int) -> Optional[set]:
        row = await self.fetchone("SELECT permissions FROM managers WHERE user_id=?", (user_id,))
        if not row:
            return None
        try:
            return set(json.loads(row["permissions"]))
        except Exception:
            return set()

    async def clone_ids_for_admin(self, user_id: int) -> list:
        rows = await self.fetchall(
            """SELECT id FROM clones WHERE deleted_at IS NULL AND (admin_id=? OR id IN
            (SELECT clone_id FROM clone_operators WHERE user_id=?)) ORDER BY id""",
            (user_id, user_id),
        )
        return [r["id"] for r in rows]

    async def role_of(self, user_id: int) -> Optional[str]:
        if await self.is_owner(user_id):
            return "owner"
        if await self.manager_perms(user_id) is not None:
            return "manager"
        if await self.clone_ids_for_admin(user_id):
            return "clone_admin"
        return None

    # ---- clones -------------------------------------------------------------------------------
    async def clone(self, clone_id: int) -> Optional[dict]:
        return await self.fetchone("SELECT * FROM clones WHERE id=? AND deleted_at IS NULL", (clone_id,))

    async def clones(self, status: Optional[str] = None) -> list:
        if status:
            return await self.fetchall("SELECT * FROM clones WHERE deleted_at IS NULL AND status=? ORDER BY id", (status,))
        return await self.fetchall("SELECT * FROM clones WHERE deleted_at IS NULL ORDER BY id")

    async def clone_count(self) -> int:
        return int(await self.fetchval("SELECT COUNT(*) AS n FROM clones WHERE deleted_at IS NULL") or 0)

    async def set_clone_status(self, clone_id: int, status: str, error: Optional[str] = None, **extra):
        sets = ["status=?", "updated_at=?", "last_error=?"]
        params: list = [status, utcnow(), redact(error)[:1000] if error else None]
        if status == "LIVE":
            sets.append("started_at=?")
            params.append(utcnow())
        for key, value in extra.items():
            if key in {"desired_running", "restart_count"}:
                sets.append(f"{key}=?")
                params.append(value)
        params.append(clone_id)
        await self.execute(f"UPDATE clones SET {', '.join(sets)} WHERE id=?", tuple(params))

    # ---- users / messages --------------------------------------------------------------------
    async def upsert_clone_user(self, clone_id: int, user: User) -> bool:
        now = utcnow()
        async with self.transaction() as tx:
            await tx.execute(
                """INSERT INTO platform_users(user_id,username,first_name,last_name,language_code,first_seen,last_seen)
                VALUES(?,?,?,?,?,?,?) ON CONFLICT(user_id) DO UPDATE SET username=excluded.username,
                first_name=excluded.first_name, last_name=excluded.last_name, language_code=excluded.language_code,
                last_seen=excluded.last_seen""",
                (user.id, user.username, user.first_name, user.last_name, user.language_code, now, now),
            )
            existing = await tx.fetchone("SELECT 1 AS x FROM clone_users WHERE clone_id=? AND user_id=?", (clone_id, user.id))
            is_new = existing is None
            await tx.execute(
                """INSERT INTO clone_users(clone_id,user_id,username,first_name,last_name,language_code,created_at,last_seen)
                VALUES(?,?,?,?,?,?,?,?) ON CONFLICT(clone_id,user_id) DO UPDATE SET username=excluded.username,
                first_name=excluded.first_name, last_name=excluded.last_name, language_code=excluded.language_code,
                last_seen=excluded.last_seen, is_active=1""",
                (clone_id, user.id, user.username, user.first_name, user.last_name, user.language_code, now, now),
            )
            if is_new:
                await self._daily_inc(tx, clone_id, "new_users")
            await tx.execute("UPDATE clones SET last_activity=? WHERE id=?", (now, clone_id))
            return is_new

    async def _daily_inc(self, tx, clone_id: int, column: str, amount: int = 1):
        allowed = {"new_users", "incoming", "outgoing", "admin_replies", "broadcast_success", "broadcast_failed"}
        if column not in allowed:
            raise ValueError("Invalid counter")
        await tx.execute(
            "INSERT INTO daily_stats(clone_id, day) VALUES(?,?) ON CONFLICT(clone_id, day) DO NOTHING",
            (clone_id, today()),
        )
        await tx.execute(
            f"UPDATE daily_stats SET {column}={column}+? WHERE clone_id=? AND day=?", (amount, clone_id, today())
        )

    async def log_message(self, clone_id: int, direction: str, user_id: Optional[int], admin_id: Optional[int],
                          message_type: str, chat_id: Optional[int], message_id: Optional[int],
                          related_message_id: Optional[int] = None, preview: Optional[str] = None) -> bool:
        async with self.transaction() as tx:
            changed = await tx.execute(
                """INSERT INTO message_log(clone_id,direction,user_id,admin_id,message_type,telegram_chat_id,
                telegram_message_id,related_message_id,preview,created_at) VALUES(?,?,?,?,?,?,?,?,?,?)
                ON CONFLICT(clone_id,direction,telegram_chat_id,telegram_message_id) DO NOTHING""",
                (clone_id, direction, user_id, admin_id, message_type, chat_id, message_id, related_message_id,
                 (preview or "")[:200], utcnow()),
            )
            if changed == 0:
                return False
            counter = {"incoming": "incoming", "outgoing": "outgoing", "admin_reply": "admin_replies"}.get(direction)
            if counter:
                await self._daily_inc(tx, clone_id, counter)
            if direction == "admin_reply":
                await self._daily_inc(tx, clone_id, "outgoing")
            now = utcnow()
            if direction == "incoming" and user_id is not None:
                await tx.execute(
                    "UPDATE clone_users SET unread=unread+1, last_message_at=? WHERE clone_id=? AND user_id=?",
                    (now, clone_id, user_id),
                )
            elif direction == "admin_reply" and user_id is not None:
                await tx.execute(
                    "UPDATE clone_users SET unread=0, last_answered_at=? WHERE clone_id=? AND user_id=?",
                    (now, clone_id, user_id),
                )
            await tx.execute("UPDATE clones SET last_activity=? WHERE id=?", (now, clone_id))
            return True

    async def claim_update(self, clone_id: int, update_id: Optional[int]) -> bool:
        if update_id is None:
            return True
        try:
            changed = await self.execute(
                "INSERT INTO processed_updates(clone_id,update_id,processed_at) VALUES(?,?,?) ON CONFLICT(clone_id,update_id) DO NOTHING",
                (clone_id, update_id, utcnow()),
            )
            return changed == 1
        except Exception:
            logger.exception("Could not claim update")
            return True

    async def record_error(self, context: str, error: BaseException, clone_id: Optional[int] = None):
        text = redact(f"{type(error).__name__}: {error}")[:4000]
        tb = redact("".join(traceback.format_exception(type(error), error, error.__traceback__)))[-12000:]
        try:
            await self.execute(
                "INSERT INTO errors(clone_id,context,error,traceback,created_at) VALUES(?,?,?,?,?)",
                (clone_id, context[:250], text, tb, utcnow()),
            )
        except Exception:
            logger.exception("Could not persist error")

    async def audit(self, actor_id: Optional[int], action: str, result: str = "ok",
                    clone_id: Optional[int] = None, detail: Optional[str] = None):
        try:
            await self.execute(
                "INSERT INTO audit_log(actor_id,clone_id,action,detail,result,created_at) VALUES(?,?,?,?,?,?)",
                (actor_id, clone_id, action[:100], redact(detail)[:1000] if detail else None, result[:100], utcnow()),
            )
        except Exception:
            logger.exception("Could not write audit log")

    async def cleanup(self):
        cutoff = days_ago_iso(3)
        try:
            await self.execute("DELETE FROM processed_updates WHERE processed_at<?", (cutoff,))
        except Exception:
            logger.exception("Cleanup failed")

# --------------------------------------------------------------------------------------
# Message payloads: serialization + cross-bot delivery
# --------------------------------------------------------------------------------------

RELAY_TYPES = {
    "text", "photo", "video", "document", "voice", "audio", "sticker", "animation",
    "video_note", "contact", "location", "venue", "dice",
}


def message_kind(message: Message) -> str:
    for name in (
        "text", "photo", "video", "document", "voice", "audio", "sticker",
        "animation", "video_note", "contact", "location", "venue", "poll", "dice",
    ):
        if getattr(message, name, None):
            return name
    return "other"


def entities_to_json(entities) -> list:
    return [e.to_dict() for e in (entities or [])]


def entities_from_json(data: list) -> Optional[list]:
    if not data:
        return None
    result = []
    for item in data:
        ent = MessageEntity.de_json(dict(item), None)
        if ent is not None:
            result.append(ent)
    return result or None


def strip_custom_emoji(entities: list) -> list:
    return [e for e in (entities or []) if e.get("type") != "custom_emoji"]


def shift_entities(entities: list, offset: int) -> list:
    shifted = []
    for e in entities or []:
        item = dict(e)
        item["offset"] = int(item.get("offset", 0)) + offset
        shifted.append(item)
    return shifted


def serialize_message(message: Message) -> dict:
    """Turn a Telegram message into a JSON-serializable payload that can be re-sent by another bot."""
    kind = message_kind(message)
    payload: dict[str, Any] = {
        "kind": kind,
        "text": message.text or "",
        "entities": entities_to_json(message.entities),
        "caption": message.caption or "",
        "caption_entities": entities_to_json(message.caption_entities),
        "file_id": None,
        "file_unique_id": None,
        "file_size": None,
        "file_name": None,
        "mime_type": None,
        "extra": {},
        "source_bot_id": message.get_bot().id if message.get_bot() else None,
        "source_chat_id": message.chat_id,
        "source_message_id": message.message_id,
        "has_spoiler": bool(getattr(message, "has_media_spoiler", False)),
    }
    media = None
    if kind == "photo":
        media = message.photo[-1]
    elif kind in {"video", "document", "voice", "audio", "sticker", "animation", "video_note"}:
        media = getattr(message, kind)
    if media is not None:
        payload["file_id"] = media.file_id
        payload["file_unique_id"] = media.file_unique_id
        payload["file_size"] = getattr(media, "file_size", None)
        payload["file_name"] = getattr(media, "file_name", None)
        payload["mime_type"] = getattr(media, "mime_type", None)
        if kind == "sticker":
            payload["extra"] = {"is_animated": media.is_animated, "is_video": media.is_video, "emoji": media.emoji}
        if kind == "audio":
            payload["extra"] = {"title": media.title, "performer": media.performer, "duration": media.duration}
        if kind in {"video", "animation", "video_note", "voice"}:
            payload["extra"] = {"duration": getattr(media, "duration", None)}
    if kind == "contact":
        c = message.contact
        payload["extra"] = {"phone_number": c.phone_number, "first_name": c.first_name, "last_name": c.last_name, "vcard": c.vcard}
    elif kind == "location":
        loc = message.location
        payload["extra"] = {"latitude": loc.latitude, "longitude": loc.longitude}
    elif kind == "venue":
        v = message.venue
        payload["extra"] = {"latitude": v.location.latitude, "longitude": v.location.longitude, "title": v.title, "address": v.address}
    elif kind == "dice":
        payload["extra"] = {"emoji": message.dice.emoji}
    elif kind == "poll":
        payload["extra"] = {"question": message.poll.question}
    return payload


def payload_preview(payload: dict) -> str:
    kind = payload.get("kind", "other")
    text = payload.get("text") or payload.get("caption") or ""
    if text:
        text = text.replace("\n", " ")
        return (text[:80] + "…") if len(text) > 80 else text
    labels = {
        "photo": "📷 Photo", "video": "🎬 Video", "document": "📎 Document", "voice": "🎤 Voice message",
        "audio": "🎵 Audio", "sticker": "🩵 Sticker", "animation": "🎞 GIF", "video_note": "📹 Video note",
        "contact": "👤 Contact", "location": "📍 Location", "venue": "📍 Venue", "dice": "🎲 Dice", "poll": "📊 Poll",
    }
    return labels.get(kind, "Unsupported message")


def payload_supported(payload: dict) -> tuple[bool, str]:
    kind = payload.get("kind")
    if kind not in RELAY_TYPES:
        return False, f"Message type '{kind}' cannot be relayed by another bot."
    size = payload.get("file_size") or 0
    if size and size > MAX_MEDIA_BYTES:
        return False, "The media file exceeds the 20 MB limit bots are allowed to download."
    return True, ""


def build_url_keyboard(buttons: list, extra_rows: Optional[list] = None) -> Optional[InlineKeyboardMarkup]:
    rows = []
    for b in buttons or []:
        rows.append([InlineKeyboardButton(b["label"], url=b["url"])])
    for row in extra_rows or []:
        rows.append(row)
    return InlineKeyboardMarkup(rows) if rows else None


def prepend_header(payload: dict, header: str) -> dict:
    """Prepend a plain-text header to text/caption while keeping entity offsets valid."""
    out = json.loads(json.dumps(payload))
    kind = out.get("kind")
    head = header + "\n\n"
    shift = utf16_len(head)
    if kind == "text":
        if utf16_len(out["text"]) + shift <= MessageLimit.MAX_TEXT_LENGTH:
            out["text"] = head + out["text"]
            out["entities"] = shift_entities(out.get("entities"), shift)
            out["header_entities"] = [{"type": "bold", "offset": 0, "length": utf16_len(header)}]
    elif kind in {"photo", "video", "document", "voice", "audio", "animation"}:
        caption = out.get("caption") or ""
        if utf16_len(caption) + shift <= MessageLimit.CAPTION_LENGTH:
            out["caption"] = head + caption if caption else header
            out["caption_entities"] = shift_entities(out.get("caption_entities"), shift if caption else 0)
            out["header_entities"] = [{"type": "bold", "offset": 0, "length": utf16_len(header)}]
    return out


class MediaCache:
    """Per-bot cache of re-uploaded file ids so a broadcast uploads each file at most once per bot."""

    def __init__(self):
        self._ids: dict[tuple, str] = {}
        self._paths: dict[str, Path] = {}

    def file_id(self, bot_id: int, unique_id: str) -> Optional[str]:
        return self._ids.get((bot_id, unique_id))

    def store(self, bot_id: int, unique_id: str, file_id: str):
        self._ids[(bot_id, unique_id)] = file_id

    def path(self, unique_id: str) -> Optional[Path]:
        p = self._paths.get(unique_id)
        return p if p and p.exists() else None

    def set_path(self, unique_id: str, path: Path):
        self._paths[unique_id] = path

    def cleanup(self):
        for p in self._paths.values():
            try:
                p.unlink(missing_ok=True)
            except Exception:
                pass
        self._paths.clear()


async def download_media(source_bot: Bot, payload: dict, cache: Optional[MediaCache]) -> Path:
    unique = payload["file_unique_id"]
    if cache is not None:
        cached = cache.path(unique)
        if cached:
            return cached
    MEDIA_TMP_DIR.mkdir(parents=True, exist_ok=True)
    suffix = Path(payload.get("file_name") or "").suffix or {
        "photo": ".jpg", "video": ".mp4", "voice": ".ogg", "audio": ".mp3", "sticker": ".webp",
        "animation": ".mp4", "video_note": ".mp4",
    }.get(payload["kind"], ".bin")
    target = MEDIA_TMP_DIR / f"{uuid.uuid4().hex}{suffix}"
    tg_file = await source_bot.get_file(payload["file_id"])
    if tg_file.file_size and tg_file.file_size > MAX_MEDIA_BYTES:
        raise ValueError("Media exceeds the 20 MB download limit.")
    await tg_file.download_to_drive(custom_path=str(target))
    if cache is not None:
        cache.set_path(unique, target)
    return target


def _extract_file_id(message: Message, kind: str) -> Optional[str]:
    if kind == "photo" and message.photo:
        return message.photo[-1].file_id
    media = getattr(message, kind, None)
    return getattr(media, "file_id", None) if media is not None else None


async def send_payload(bot: Bot, chat_id: int, payload: dict, source_bot: Optional[Bot] = None,
                       reply_markup=None, cache: Optional[MediaCache] = None, reply_to_message_id: Optional[int] = None) -> Message:
    """Deliver a serialized payload with `bot`. When the payload originated from a different bot,
    media is downloaded with `source_bot` and re-uploaded, since file ids are bot-specific."""
    kind = payload["kind"]
    ok, reason = payload_supported(payload)
    if not ok:
        raise ValueError(reason)
    text_entities = (payload.get("header_entities") or []) + list(payload.get("entities") or [])
    caption_entities = (payload.get("header_entities") or []) + list(payload.get("caption_entities") or [])
    common = {"chat_id": chat_id, "reply_markup": reply_markup}
    if reply_to_message_id:
        common["reply_to_message_id"] = reply_to_message_id

    async def _send(ents_text: list, ents_caption: list) -> Message:
        if kind == "text":
            return await bot.send_message(text=payload["text"], entities=entities_from_json(ents_text), **common)
        if kind == "contact":
            e = payload["extra"]
            return await bot.send_contact(phone_number=e["phone_number"], first_name=e["first_name"],
                                          last_name=e.get("last_name"), vcard=e.get("vcard"), **common)
        if kind == "location":
            e = payload["extra"]
            return await bot.send_location(latitude=e["latitude"], longitude=e["longitude"], **common)
        if kind == "venue":
            e = payload["extra"]
            return await bot.send_venue(latitude=e["latitude"], longitude=e["longitude"], title=e["title"],
                                        address=e["address"], **common)
        if kind == "dice":
            return await bot.send_dice(emoji=payload["extra"].get("emoji"), **common)
        # media kinds
        same_bot = source_bot is None or source_bot.id == bot.id
        media_ref: Any = None
        cached_id = cache.file_id(bot.id, payload["file_unique_id"]) if cache else None
        handle = None
        if same_bot:
            media_ref = payload["file_id"]
        elif cached_id:
            media_ref = cached_id
        else:
            path = await download_media(source_bot, payload, cache)
            handle = path.open("rb")
            media_ref = InputFile(handle, filename=payload.get("file_name") or path.name)
        try:
            cap = {"caption": payload.get("caption") or None, "caption_entities": entities_from_json(ents_caption)}
            if kind == "photo":
                msg = await bot.send_photo(photo=media_ref, has_spoiler=payload.get("has_spoiler") or None, **cap, **common)
            elif kind == "video":
                msg = await bot.send_video(video=media_ref, has_spoiler=payload.get("has_spoiler") or None, **cap, **common)
            elif kind == "document":
                msg = await bot.send_document(document=media_ref, **cap, **common)
            elif kind == "voice":
                msg = await bot.send_voice(voice=media_ref, **cap, **common)
            elif kind == "audio":
                e = payload.get("extra") or {}
                msg = await bot.send_audio(audio=media_ref, title=e.get("title"), performer=e.get("performer"), **cap, **common)
            elif kind == "animation":
                msg = await bot.send_animation(animation=media_ref, has_spoiler=payload.get("has_spoiler") or None, **cap, **common)
            elif kind == "video_note":
                msg = await bot.send_video_note(video_note=media_ref, **common)
            elif kind == "sticker":
                msg = await bot.send_sticker(sticker=media_ref, **common)
            else:
                raise ValueError(f"Unsupported kind {kind}")
        finally:
            if handle is not None:
                handle.close()
                if cache is None:
                    try:
                        Path(handle.name).unlink(missing_ok=True)
                    except Exception:
                        pass
        if cache is not None and not same_bot:
            new_id = _extract_file_id(msg, kind)
            if new_id:
                cache.store(bot.id, payload["file_unique_id"], new_id)
        return msg

    try:
        return await _send(text_entities, caption_entities)
    except BadRequest as exc:
        msg = str(exc).lower()
        if "custom emoji" in msg or "custom_emoji" in msg or "entity" in msg:
            # Bots may only use custom emoji they are entitled to; fall back to standard Unicode fallback text.
            return await _send(strip_custom_emoji(text_entities), strip_custom_emoji(caption_entities))
        raise

# --------------------------------------------------------------------------------------
# Roles, permissions, conversation state
# --------------------------------------------------------------------------------------

PERM_CLONES = "clones"
PERM_BROADCAST = "broadcast"
PERM_CONVERSATIONS = "conversations"
PERM_STATS = "stats"
PERM_SETTINGS = "settings"
PERM_BACKUP = "backup"
PERM_LOGS = "logs"
PERM_ADMINS = "admins"   # owner only
PERM_TOKENS = "tokens"   # owner only (create / rotate / delete clones)

ALL_PERMS = [PERM_CLONES, PERM_BROADCAST, PERM_CONVERSATIONS, PERM_STATS, PERM_SETTINGS, PERM_BACKUP, PERM_LOGS]
OWNER_ONLY_PERMS = {PERM_ADMINS, PERM_TOKENS}
DEFAULT_MANAGER_PERMS = {PERM_CLONES, PERM_CONVERSATIONS, PERM_STATS, PERM_BROADCAST}
PERM_LABELS = {
    PERM_CLONES: "🤖 Clone control (start/stop/settings)",
    PERM_BROADCAST: "📣 Broadcasts",
    PERM_CONVERSATIONS: "💬 Conversations",
    PERM_STATS: "📈 Statistics",
    PERM_SETTINGS: "⚙️ Global settings",
    PERM_BACKUP: "💾 Backup & restore",
    PERM_LOGS: "📜 Logs & diagnostics",
}


@dataclass
class Actor:
    user_id: int
    role: str                        # owner | manager | clone_admin
    perms: set = field(default_factory=set)
    clone_ids: list = field(default_factory=list)

    @property
    def is_owner(self) -> bool:
        return self.role == "owner"

    def has(self, perm: str) -> bool:
        if self.role == "owner":
            return True
        if self.role == "manager":
            return perm in self.perms and perm not in OWNER_ONLY_PERMS
        return False

    def can_clone(self, clone_id: int, perm: str = PERM_CONVERSATIONS) -> bool:
        if self.role == "owner":
            return True
        if self.role == "manager":
            return self.has(perm)
        return clone_id in self.clone_ids and perm in {PERM_CONVERSATIONS, PERM_STATS, PERM_BROADCAST, PERM_CLONES}


async def resolve_actor(user_id: int) -> Optional[Actor]:
    if await db.is_owner(user_id):
        return Actor(user_id, "owner", set(ALL_PERMS) | OWNER_ONLY_PERMS, [])
    perms = await db.manager_perms(user_id)
    clone_ids = await db.clone_ids_for_admin(user_id)
    if perms is not None:
        return Actor(user_id, "manager", perms, clone_ids)
    if clone_ids:
        return Actor(user_id, "clone_admin", set(), clone_ids)
    return None


class StateStore:
    """Per-user wizard state with expiry. Keyed by (scope, user_id); scope is 'owner' or a clone id."""

    def __init__(self):
        self._states: dict[tuple, dict] = {}

    def get(self, scope: Any, user_id: int) -> Optional[dict]:
        st = self._states.get((scope, user_id))
        if not st:
            return None
        if time.monotonic() - st["updated"] > STATE_TIMEOUT_SECONDS:
            self.clear(scope, user_id)
            return None
        st["updated"] = time.monotonic()
        return st

    def set(self, scope: Any, user_id: int, flow: str, step: str, data: Optional[dict] = None,
            panel: Optional[tuple] = None) -> dict:
        prev = self._states.get((scope, user_id)) or {}
        st = {
            "flow": flow,
            "step": step,
            "data": data if data is not None else prev.get("data", {}),
            "panel": panel or prev.get("panel"),
            "updated": time.monotonic(),
        }
        self._states[(scope, user_id)] = st
        return st

    def clear(self, scope: Any, user_id: int) -> Optional[dict]:
        st = self._states.pop((scope, user_id), None)
        if st:
            _cleanup_state_files(st)
        return st

    def clear_user_everywhere(self, user_id: int):
        for key in [k for k in self._states if k[1] == user_id]:
            st = self._states.pop(key, None)
            if st:
                _cleanup_state_files(st)

    def sweep(self):
        for key in list(self._states):
            st = self._states[key]
            if time.monotonic() - st["updated"] > STATE_TIMEOUT_SECONDS:
                self._states.pop(key, None)
                _cleanup_state_files(st)


def _cleanup_state_files(st: dict):
    path = (st.get("data") or {}).get("restore_path")
    if path:
        try:
            Path(path).unlink(missing_ok=True)
        except Exception:
            pass


# --------------------------------------------------------------------------------------
# Globals
# --------------------------------------------------------------------------------------

db = Database()
STATES = StateStore()
START_MONOTONIC = time.monotonic()
LAST_HEALTH_OK: dict[str, Optional[str]] = {"at": None}
NOTIFY_WARNED: dict[int, float] = {}
VAULT: Optional[TokenVault] = None
OWNER_BOT_USERNAME: dict[str, str] = {"value": ""}


# --------------------------------------------------------------------------------------
# UI helpers
# --------------------------------------------------------------------------------------


def kb(rows: list) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[InlineKeyboardButton(t, callback_data=d) if not d.startswith("url:") else
                                  InlineKeyboardButton(t, url=d[4:]) for t, d in row] for row in rows])


def back_cancel(back: str, cancel: str = "o:cancel") -> InlineKeyboardMarkup:
    return kb([[("⬅️ Back", back), ("❌ Cancel", cancel)]])


def back_only(back: str) -> InlineKeyboardMarkup:
    return kb([[("⬅️ Back", back)]])


def status_icon(status: str) -> str:
    return {
        "LIVE": "🟢", "STARTING": "🟡", "VALIDATING": "🟡", "PENDING": "⚪️", "STOPPING": "🟠",
        "STOPPED": "⚪️", "ERROR": "🔴", "RESTARTING": "🟡", "DELETED": "⚫️",
    }.get(status, "⚪️")


async def safe_edit(query, text: str, keyboard=None, parse_mode=ParseMode.HTML):
    try:
        await query.edit_message_text(text, reply_markup=keyboard, parse_mode=parse_mode)
    except BadRequest as exc:
        low = str(exc).lower()
        if "message is not modified" in low:
            return
        if "no text in the message" in low or "message can't be edited" in low or "message to edit not found" in low:
            await query.message.reply_text(text, reply_markup=keyboard, parse_mode=parse_mode)
            return
        raise


async def edit_or_send(bot: Bot, chat_id: int, message_id: Optional[int], text: str, keyboard=None) -> Optional[int]:
    """Edit the panel message if possible; otherwise send a new one. Returns the message id in use."""
    if message_id:
        try:
            await bot.edit_message_text(text, chat_id=chat_id, message_id=message_id, reply_markup=keyboard,
                                        parse_mode=ParseMode.HTML)
            return message_id
        except BadRequest as exc:
            if "message is not modified" in str(exc).lower():
                return message_id
        except TelegramError:
            pass
    try:
        sent = await bot.send_message(chat_id, text, reply_markup=keyboard, parse_mode=ParseMode.HTML)
        return sent.message_id
    except TelegramError as exc:
        logger.warning("Could not send panel message: %s", redact(exc))
        return None


async def try_delete(bot: Bot, chat_id: int, message_id: Optional[int]):
    if not message_id:
        return
    try:
        await bot.delete_message(chat_id, message_id)
    except TelegramError:
        pass


def paginate(items: list, page: int, size: int = PAGE_SIZE) -> tuple[list, int, int]:
    total_pages = max(1, (len(items) + size - 1) // size)
    page = max(0, min(page, total_pages - 1))
    return items[page * size:(page + 1) * size], page, total_pages


def nav_row(prefix: str, page: int, total_pages: int) -> list:
    row = []
    if page > 0:
        row.append(("◀️", f"{prefix}:{page - 1}"))
    row.append((f"{page + 1}/{total_pages}", "o:noop"))
    if page < total_pages - 1:
        row.append(("▶️", f"{prefix}:{page + 1}"))
    return row


def clone_title(c: dict) -> str:
    return f"{esc(c['display_name'])} (@{esc(c['username'])})"


async def notify_owners(text: str):
    """Best-effort owner notification through the Owner Bot."""
    app = MANAGER.owner_app if MANAGER else None
    if not app:
        return
    for oid in await db.owner_ids():
        try:
            await app.bot.send_message(oid, text, parse_mode=ParseMode.HTML)
        except TelegramError:
            pass

# --------------------------------------------------------------------------------------
# Clone bot handlers: user-facing behaviour and user -> admin relay
# --------------------------------------------------------------------------------------


def clone_id_of(context: ContextTypes.DEFAULT_TYPE) -> int:
    return int(context.application.bot_data["clone_id"])


async def clone_admin_targets(clone: dict) -> list:
    """Admin chat ids that should receive user messages for a clone, via the Owner Bot."""
    targets = [clone["admin_id"]]
    for r in await db.fetchall("SELECT user_id FROM clone_operators WHERE clone_id=?", (clone["id"],)):
        if r["user_id"] not in targets:
            targets.append(r["user_id"])
    if await db.setting("notify_owners_on_user_message", "0") == "1":
        for oid in await db.owner_ids():
            if oid not in targets:
                targets.append(oid)
    return targets


async def relay_user_message_to_admins(clone: dict, message: Message, user: User):
    """Single-message relay: content + header + profile button through the Owner Bot."""
    owner_app = MANAGER.owner_app
    if owner_app is None:
        return
    payload = serialize_message(message)
    ok, reason = payload_supported(payload)
    header = f"👤 {user_label(user.first_name, user.last_name, user.username, user.id)} · via @{clone['username']}"
    if not ok:
        payload = {"kind": "text", "text": f"{header}\n\n[{payload_preview(payload)}] – this message type cannot be relayed.",
                   "entities": [], "caption": "", "caption_entities": [], "file_id": None, "file_unique_id": None,
                   "file_size": None, "file_name": None, "mime_type": None, "extra": {}}
        await db.record_error("relay.unsupported", ValueError(reason), clone["id"])
    elif await db.setting("forward_header", "1") == "1":
        payload = prepend_header(payload, header)
    markup = InlineKeyboardMarkup([[
        InlineKeyboardButton("👤 View Profile", url=f"tg://user?id={user.id}"),
        InlineKeyboardButton("💬 Open", callback_data=f"o:conv:{clone['id']}:{user.id}"),
    ]])
    clone_bot = MANAGER.bot_for(clone["id"])
    for admin_chat_id in await clone_admin_targets(clone):
        try:
            sent = await send_payload(owner_app.bot, admin_chat_id, payload, source_bot=clone_bot, reply_markup=markup)
        except Forbidden:
            await _warn_admin_not_started(clone, admin_chat_id)
            continue
        except ValueError as exc:
            await db.record_error("relay.payload", exc, clone["id"])
            continue
        except TelegramError as exc:
            await db.record_error("relay.send", exc, clone["id"])
            continue
        await db.execute(
            """INSERT INTO forward_map(admin_chat_id,admin_message_id,clone_id,user_id,user_message_id,created_at)
            VALUES(?,?,?,?,?,?) ON CONFLICT(admin_chat_id,admin_message_id) DO NOTHING""",
            (admin_chat_id, sent.message_id, clone["id"], user.id, message.message_id, utcnow()),
        )


async def _warn_admin_not_started(clone: dict, admin_id: int):
    """The Owner Bot cannot message an admin who never started it. Tell them via the clone bot (rate limited)."""
    last = NOTIFY_WARNED.get(admin_id, 0)
    if time.monotonic() - last < 3600:
        return
    NOTIFY_WARNED[admin_id] = time.monotonic()
    await db.record_error("relay.admin_unreachable", RuntimeError(f"admin {admin_id} has not started the management bot"), clone["id"])
    clone_bot = MANAGER.bot_for(clone["id"])
    if clone_bot is None:
        return
    uname = OWNER_BOT_USERNAME["value"]
    hint = f"@{uname}" if uname else "the management bot"
    try:
        await clone_bot.send_message(
            admin_id,
            f"⚠️ You are assigned as administrator of this bot, but {hint} cannot reach you yet.\n"
            f"Please open {hint} and press /start to receive user messages.",
        )
    except TelegramError:
        pass


async def clone_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.effective_user or not update.effective_message or update.effective_chat.type != "private":
        return
    clone_id = clone_id_of(context)
    if not await db.claim_update(clone_id, update.update_id):
        return
    clone = await db.clone(clone_id)
    if not clone:
        return
    user = update.effective_user
    await db.upsert_clone_user(clone_id, user)
    actor = await resolve_actor(user.id)
    if actor and actor.can_clone(clone_id, PERM_CLONES):
        await update.effective_message.reply_text(
            await clone_panel_text(clone), reply_markup=clone_panel_keyboard(clone_id), parse_mode=ParseMode.HTML
        )
        return
    row = await db.fetchone("SELECT is_banned FROM clone_users WHERE clone_id=? AND user_id=?", (clone_id, user.id))
    if row and row["is_banned"]:
        return
    if await db.clone_setting(clone_id, "maintenance_mode", "0") == "1":
        text = await db.clone_setting(clone_id, "maintenance_message", await db.setting("default_maintenance_message", DEFAULT_MAINTENANCE))
    else:
        text = await db.clone_setting(clone_id, "start_message", await db.setting("default_start_message", DEFAULT_START))
    sent = await update.effective_message.reply_text(text)
    await db.log_message(clone_id, "outgoing", user.id, None, "start", sent.chat_id, sent.message_id)


async def clone_user_message(update: Update, context: ContextTypes.DEFAULT_TYPE):
    message = update.effective_message
    user = update.effective_user
    if not message or not user or update.effective_chat.type != "private":
        return
    clone_id = clone_id_of(context)
    if not await db.claim_update(clone_id, update.update_id):
        return
    clone = await db.clone(clone_id)
    if not clone:
        return
    actor = await resolve_actor(user.id)
    if actor and actor.can_clone(clone_id, PERM_CLONES):
        if await clone_admin_text_input(update, context, clone, actor):
            return
        if message.reply_to_message:
            await message.reply_text("Replies are handled from the management bot: reply to the relayed message there.")
        else:
            await message.reply_text("Use /start to open the clone panel.", reply_markup=clone_panel_keyboard(clone_id))
        return
    await db.upsert_clone_user(clone_id, user)
    row = await db.fetchone("SELECT is_banned FROM clone_users WHERE clone_id=? AND user_id=?", (clone_id, user.id))
    if row and row["is_banned"]:
        return
    if await db.clone_setting(clone_id, "maintenance_mode", "0") == "1":
        text = await db.clone_setting(clone_id, "maintenance_message", await db.setting("default_maintenance_message", DEFAULT_MAINTENANCE))
        sent = await message.reply_text(text)
        await db.log_message(clone_id, "outgoing", user.id, None, "maintenance", sent.chat_id, sent.message_id)
        return
    payload = serialize_message(message)
    logged = await db.log_message(clone_id, "incoming", user.id, None, payload["kind"], message.chat_id,
                                  message.message_id, preview=payload_preview(payload))
    if not logged:
        return  # duplicate update
    await relay_user_message_to_admins(clone, message, user)


async def clone_error_handler(update: object, context: ContextTypes.DEFAULT_TYPE):
    err = context.error
    clone_id = context.application.bot_data.get("clone_id")
    if isinstance(err, Conflict):
        logger.error("Clone %s: polling conflict (token used elsewhere)", clone_id)
        if MANAGER:
            await MANAGER.report_conflict(int(clone_id), err)
        return
    if isinstance(err, (NetworkError, TimedOut)):
        logger.warning("Clone %s network issue: %s", clone_id, redact(err))
        return
    logger.error("Clone %s handler error: %s", clone_id, redact(err))
    await db.record_error("clone.handler", err, int(clone_id) if clone_id is not None else None)


# ---- Clone admin panel (inside the clone bot itself) ---------------------------------------


def clone_panel_keyboard(clone_id: int) -> InlineKeyboardMarkup:
    c = clone_id
    return kb([
        [("📊 Statistics", f"c:stats:{c}"), ("👥 Users", f"c:users:{c}")],
        [("📣 Broadcast", f"c:bc:{c}"), ("💬 Inbox", f"c:inbox:{c}:0")],
        [("👋 Welcome Message", f"c:edit:{c}:start_message"), ("🛠 Maintenance", f"c:maint:{c}")],
        [("🩺 Diagnostics", f"c:diag:{c}")],
    ])


async def clone_panel_text(clone: dict) -> str:
    stats = await clone_stats_row(clone["id"])
    rt = MANAGER.runtime(clone["id"]) if MANAGER else None
    state = rt.status if rt else clone["status"]
    return (
        f"<b>🤖 {clone_title(clone)}</b>\n\n"
        f"State: {status_icon(state)} <b>{esc(state)}</b>\n"
        f"Users: <b>{fmt_int(stats['users'])}</b> | Active ({ACTIVE_DAYS}d): <b>{fmt_int(stats['active'])}</b>\n"
        f"Unread conversations: <b>{fmt_int(stats['unread'])}</b>\n\n"
        "Choose a section:"
    )


async def clone_stats_row(clone_id: int) -> dict:
    users = await db.fetchone(
        """SELECT COUNT(*) AS users, SUM(CASE WHEN is_banned=1 THEN 1 ELSE 0 END) AS banned,
        SUM(CASE WHEN last_seen>=? THEN 1 ELSE 0 END) AS active,
        SUM(CASE WHEN unread>0 THEN 1 ELSE 0 END) AS unread FROM clone_users WHERE clone_id=?""",
        (days_ago_iso(ACTIVE_DAYS), clone_id),
    )
    msgs = await db.fetchone(
        """SELECT SUM(CASE WHEN direction='incoming' THEN 1 ELSE 0 END) AS incoming,
        SUM(CASE WHEN direction IN ('outgoing','admin_reply') THEN 1 ELSE 0 END) AS outgoing,
        SUM(CASE WHEN direction='admin_reply' THEN 1 ELSE 0 END) AS replies FROM message_log WHERE clone_id=?""",
        (clone_id,),
    )
    bc = await db.fetchone(
        "SELECT COUNT(*) AS total, COALESCE(SUM(success),0) AS success, COALESCE(SUM(failed),0) AS failed FROM broadcast_targets WHERE clone_id=?",
        (clone_id,),
    )
    return {
        "users": users["users"] or 0, "banned": users["banned"] or 0, "active": users["active"] or 0,
        "unread": users["unread"] or 0, "incoming": msgs["incoming"] or 0, "outgoing": msgs["outgoing"] or 0,
        "replies": msgs["replies"] or 0, "broadcasts": bc["total"] or 0, "bc_success": bc["success"] or 0,
        "bc_failed": bc["failed"] or 0,
    }


async def clone_stats_text(clone: dict) -> str:
    s = await clone_stats_row(clone["id"])
    lines = [f"<b>📊 Statistics – {clone_title(clone)}</b>", "",
             f"👥 Users: <b>{fmt_int(s['users'])}</b>", f"🟢 Active ({ACTIVE_DAYS}d): <b>{fmt_int(s['active'])}</b>",
             f"🚫 Banned: <b>{fmt_int(s['banned'])}</b>", f"📥 Received: <b>{fmt_int(s['incoming'])}</b>",
             f"📤 Sent: <b>{fmt_int(s['outgoing'])}</b>", f"💬 Admin replies: <b>{fmt_int(s['replies'])}</b>",
             f"📣 Broadcasts: <b>{fmt_int(s['broadcasts'])}</b> (✅ {fmt_int(s['bc_success'])} / ❌ {fmt_int(s['bc_failed'])})",
             "", "<b>Period breakdown</b>"]
    for label, days in (("Today", 0), ("7 days", 6), ("30 days", 29)):
        r = await db.fetchone(
            """SELECT COALESCE(SUM(new_users),0) AS nu, COALESCE(SUM(incoming),0) AS inc, COALESCE(SUM(outgoing),0) AS out,
            COALESCE(SUM(broadcast_success),0) AS bs FROM daily_stats WHERE clone_id=? AND day>=?""",
            (clone["id"], (now_dt() - timedelta(days=days)).date().isoformat()),
        )
        lines.append(f"{label}: +{r['nu']} users | ↓{r['inc']} | ↑{r['out']} | 📣{r['bs']}")
    return "\n".join(lines)


async def clone_users_text(clone: dict) -> str:
    s = await clone_stats_row(clone["id"])
    recent = await db.fetchall(
        "SELECT user_id,username,first_name,last_seen,is_banned FROM clone_users WHERE clone_id=? ORDER BY last_seen DESC LIMIT 8",
        (clone["id"],),
    )
    lines = [f"<b>👥 Users – {clone_title(clone)}</b>", "",
             f"Total: <b>{fmt_int(s['users'])}</b> | Banned: <b>{fmt_int(s['banned'])}</b>", "", "<b>Recently active</b>"]
    for r in recent:
        label = f"@{r['username']}" if r["username"] else (r["first_name"] or "Unknown")
        lines.append(f"{'🚫' if r['is_banned'] else '👤'} <code>{r['user_id']}</code> – {esc(label)}")
    if not recent:
        lines.append("No users yet.")
    return "\n".join(lines)


async def user_detail_text(clone_id: int, user_id: int) -> Optional[str]:
    u = await db.fetchone("SELECT * FROM clone_users WHERE clone_id=? AND user_id=?", (clone_id, user_id))
    if not u:
        return None
    m = await db.fetchone(
        """SELECT COUNT(*) AS total, SUM(CASE WHEN direction='incoming' THEN 1 ELSE 0 END) AS incoming,
        SUM(CASE WHEN direction IN ('outgoing','admin_reply') THEN 1 ELSE 0 END) AS outgoing
        FROM message_log WHERE clone_id=? AND user_id=?""",
        (clone_id, user_id),
    )
    return (
        "<b>👤 User Details</b>\n\n"
        f"ID: <code>{u['user_id']}</code>\n"
        f"Name: {esc(((u['first_name'] or '') + ' ' + (u['last_name'] or '')).strip())}\n"
        f"Username: {('@' + esc(u['username'])) if u['username'] else '-'}\n"
        f"Language: {esc(u['language_code'] or '-')}\n"
        f"Status: <b>{'Banned' if u['is_banned'] else 'Active'}</b>\n"
        f"Unread: <b>{u['unread']}</b>\n"
        f"Joined: {short_time(u['created_at'])}\n"
        f"Last seen: {short_time(u['last_seen'])}\n"
        f"Messages: {m['total']} ({m['incoming'] or 0} in / {m['outgoing'] or 0} out)"
    )


def user_detail_keyboard(clone_id: int, user_id: int, banned: bool, back: str, prefix: str = "o") -> InlineKeyboardMarkup:
    return kb([
        [("✅ Unban" if banned else "🚫 Ban", f"{prefix}:ban:{clone_id}:{user_id}"), ("💬 Conversation", f"{prefix}:conv:{clone_id}:{user_id}")],
        [("👤 View Profile", f"url:tg://user?id={user_id}")],
        [("⬅️ Back", back)],
    ])


async def clone_diag_text(clone: dict) -> str:
    rt = MANAGER.runtime(clone["id"]) if MANAGER else None
    errors = await db.fetchall("SELECT context,error,created_at FROM errors WHERE clone_id=? ORDER BY id DESC LIMIT 5", (clone["id"],))
    jobs = await db.fetchall(
        """SELECT b.id, b.status FROM broadcasts b JOIN broadcast_targets t ON t.broadcast_id=b.id
        WHERE t.clone_id=? AND b.status IN ('queued','running','cancelling','interrupted') ORDER BY b.id DESC LIMIT 5""",
        (clone["id"],),
    )
    state = rt.status if rt else clone["status"]
    lines = [f"<b>🩺 Diagnostics – {clone_title(clone)}</b>", "",
             f"State: {status_icon(state)} <b>{esc(state)}</b>",
             f"Polling: <b>{'running' if rt and rt.polling_running() else 'not running'}</b>",
             f"Desired: <b>{'running' if clone['desired_running'] else 'stopped'}</b>",
             f"Restart attempts: <b>{clone['restart_count']}</b>",
             f"Started: {short_time(clone['started_at'])}",
             f"Last activity: {short_time(clone['last_activity'])}",
             f"Last error: {esc(clone['last_error'] or '-')}", "",
             f"<b>Open jobs</b>: {', '.join(f'#{j['id']} {j['status']}' for j in jobs) or 'none'}", "",
             "<b>Recent errors</b>"]
    lines += [f"{short_time(r['created_at'])} – {esc(r['context'])}: {esc(r['error'][:120])}" for r in errors] or ["No recorded errors."]
    return "\n".join(lines)


async def clone_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Callback router for the admin panel inside a clone bot."""
    q = update.callback_query
    if not q or not q.data:
        return
    clone_id = clone_id_of(context)
    actor = await resolve_actor(q.from_user.id)
    if not actor or not actor.can_clone(clone_id, PERM_CLONES):
        await q.answer()  # silent for unauthorized users
        return
    clone = await db.clone(clone_id)
    if not clone:
        await q.answer("This bot is no longer registered.", show_alert=True)
        return
    parts = q.data.split(":")
    if parts[0] != "c" or len(parts) < 3 or parse_int(parts[2]) != clone_id:
        await q.answer()
        return
    action = parts[1]
    args = parts[3:]
    scope = clone_id
    uid = q.from_user.id
    await q.answer()
    home = f"c:home:{clone_id}"
    if action == "home" or action == "cancel":
        STATES.clear(scope, uid)
        await safe_edit(q, await clone_panel_text(clone), clone_panel_keyboard(clone_id))
    elif action == "stats":
        await safe_edit(q, await clone_stats_text(clone), kb([[("🔄 Refresh", q.data)], [("⬅️ Back", home)]]))
    elif action == "users":
        STATES.clear(scope, uid)
        await safe_edit(q, await clone_users_text(clone), kb([
            [("🔎 Search", f"c:usearch:{clone_id}"), ("📤 Export CSV", f"c:export:{clone_id}")],
            [("⬅️ Back", home)],
        ]))
    elif action == "usearch":
        STATES.set(scope, uid, "user_search", "query", {}, panel=(q.message.chat_id, q.message.message_id))
        await safe_edit(q, "<b>🔎 Search Users</b>\n\nSend a Telegram ID or exact @username.", back_cancel(f"c:users:{clone_id}", f"c:cancel:{clone_id}"))
    elif action == "export":
        await export_users_csv(context.bot, q.from_user.id, clone)
    elif action == "ban" and len(args) >= 1:
        target = parse_int(args[0])
        banned = await toggle_ban(clone_id, target, actor.user_id)
        if banned is None:
            await q.answer("User not found.", show_alert=True)
            return
        await safe_edit(q, await user_detail_text(clone_id, target), user_detail_keyboard(clone_id, target, banned, f"c:users:{clone_id}", "c"))
    elif action == "conv" and len(args) >= 1:
        target = parse_int(args[0])
        text, markup = await conversation_view(clone, target, back=f"c:inbox:{clone_id}:0", prefix="c")
        await safe_edit(q, text, markup)
    elif action == "inbox":
        page = parse_int(args[0]) if args else 0
        text, markup = await inbox_view([clone], page or 0, back=home, prefix="c", filter_label="this clone")
        await safe_edit(q, text, markup)
    elif action == "reply" and len(args) >= 1:
        target = parse_int(args[0])
        STATES.set(scope, uid, "reply", "content", {"clone_id": clone_id, "user_id": target}, panel=(q.message.chat_id, q.message.message_id))
        await safe_edit(q, f"<b>💬 Reply to <code>{target}</code></b>\n\nSend the message to deliver via @{esc(clone['username'])}.",
                        back_cancel(f"c:conv:{clone_id}:{target}", f"c:cancel:{clone_id}"))
    elif action == "edit" and len(args) >= 1 and args[0] in {"start_message", "maintenance_message"}:
        key = args[0]
        current = await db.clone_setting(clone_id, key, await db.setting("default_" + key, ""))
        STATES.set(scope, uid, "edit_setting", key, {"key": key}, panel=(q.message.chat_id, q.message.message_id))
        await safe_edit(q, f"<b>✏️ Edit {'Welcome Message' if key == 'start_message' else 'Maintenance Notice'}</b>\n\nCurrent:\n<blockquote>{esc(current)}</blockquote>\n\nSend the new text.",
                        back_cancel(home, f"c:cancel:{clone_id}"))
    elif action == "maint":
        enabled = await db.clone_setting(clone_id, "maintenance_mode", "0") == "1"
        await safe_edit(q, f"<b>🛠 Maintenance Mode</b>\n\nStatus: <b>{'ON' if enabled else 'OFF'}</b>", kb([
            [("🔴 Disable" if enabled else "🟢 Enable", f"c:maintconfirm:{clone_id}")],
            [("✏️ Edit Notice", f"c:edit:{clone_id}:maintenance_message")],
            [("⬅️ Back", home)],
        ]))
    elif action == "maintconfirm":
        enabled = await db.clone_setting(clone_id, "maintenance_mode", "0") == "1"
        await safe_edit(q, f"Turn maintenance mode <b>{'OFF' if enabled else 'ON'}</b>?", kb([
            [("✅ Confirm", f"c:mainttoggle:{clone_id}:{0 if enabled else 1}"), ("❌ Cancel", f"c:maint:{clone_id}")]
        ]))
    elif action == "mainttoggle" and len(args) >= 1:
        new = "1" if args[0] == "1" else "0"
        await db.set_clone_setting(clone_id, "maintenance_mode", new)
        await db.audit(uid, "clone.maintenance", clone_id=clone_id, detail=f"mode={new}")
        await safe_edit(q, f"✅ Maintenance mode is now <b>{'ON' if new == '1' else 'OFF'}</b>.", back_only(home))
    elif action == "diag":
        await safe_edit(q, await clone_diag_text(clone), kb([[("🔄 Refresh", q.data)], [("⬅️ Back", home)]]))
    elif action == "bc":
        await bc_start(UICtx(context.bot, uid, q.message.chat_id, q.message.message_id, scope, home, f"c:cancel:{clone_id}"), actor, fixed_clone=clone_id)
    elif action.startswith("bc"):
        await bc_callback(UICtx(context.bot, uid, q.message.chat_id, q.message.message_id, scope, home, f"c:cancel:{clone_id}"), actor, action, args, q)
    else:
        await q.answer("This button is no longer valid.", show_alert=True)


async def clone_admin_text_input(update: Update, context: ContextTypes.DEFAULT_TYPE, clone: dict, actor: Actor) -> bool:
    """Handle wizard text input from a clone admin inside the clone bot."""
    uid = update.effective_user.id
    st = STATES.get(clone["id"], uid)
    if not st:
        return False
    ui = UICtx(context.bot, uid, update.effective_chat.id, (st.get("panel") or (None, None))[1], clone["id"],
               f"c:home:{clone['id']}", f"c:cancel:{clone['id']}")
    return await handle_state_input(ui, actor, st, update.effective_message)


async def toggle_ban(clone_id: int, user_id: Optional[int], actor_id: int) -> Optional[bool]:
    if user_id is None:
        return None
    row = await db.fetchone("SELECT is_banned FROM clone_users WHERE clone_id=? AND user_id=?", (clone_id, user_id))
    if not row:
        return None
    new = 0 if row["is_banned"] else 1
    await db.execute("UPDATE clone_users SET is_banned=? WHERE clone_id=? AND user_id=?", (new, clone_id, user_id))
    await db.audit(actor_id, "user.ban" if new else "user.unban", clone_id=clone_id, detail=f"user={user_id}")
    return bool(new)


async def export_users_csv(bot: Bot, chat_id: int, clone: dict):
    rows = await db.fetchall(
        "SELECT user_id,username,first_name,last_name,language_code,is_banned,is_active,created_at,last_seen FROM clone_users WHERE clone_id=? ORDER BY created_at",
        (clone["id"],),
    )
    buf = io.StringIO()
    writer = csv.writer(buf)
    writer.writerow(["user_id", "username", "first_name", "last_name", "language_code", "is_banned", "is_active", "created_at", "last_seen"])
    for r in rows:
        writer.writerow([r["user_id"], r["username"], r["first_name"], r["last_name"], r["language_code"], r["is_banned"], r["is_active"], r["created_at"], r["last_seen"]])
    data = buf.getvalue().encode("utf-8")
    try:
        await bot.send_document(chat_id, document=InputFile(io.BytesIO(data), filename=f"users_{clone['username']}_{now_dt().strftime('%Y%m%d_%H%M%S')}.csv"),
                                caption=f"Exported {len(rows)} users of @{clone['username']}.")
    except TelegramError as exc:
        await bot.send_message(chat_id, f"❌ Export failed: {esc(redact(exc))}", parse_mode=ParseMode.HTML)

# --------------------------------------------------------------------------------------
# Bot manager: lifecycle of the Owner Bot and all clones on a single event loop
# --------------------------------------------------------------------------------------


@dataclass
class CloneRuntime:
    clone_id: int
    app: Optional[Application] = None
    status: str = "STOPPED"
    last_error: Optional[str] = None
    restart_count: int = 0
    started_at: Optional[float] = None
    lock: asyncio.Lock = field(default_factory=asyncio.Lock)
    supervisor: Optional[asyncio.Task] = None
    conflict: bool = False

    def polling_running(self) -> bool:
        try:
            return bool(self.app and self.app.updater and self.app.updater.running)
        except Exception:
            return False


def build_request() -> HTTPXRequest:
    return HTTPXRequest(connection_pool_size=16, connect_timeout=20, read_timeout=30, write_timeout=30, pool_timeout=10)


async def validate_bot_token(token: str) -> tuple[Optional[User], Optional[str]]:
    """Call getMe with the candidate token. Returns (bot_user, error_message)."""
    bot = Bot(token=token, request=build_request())
    try:
        await bot.initialize()
        me = await bot.get_me()
        return me, None
    except TelegramInvalidToken:
        return None, "Telegram rejected this token as invalid or revoked."
    except Forbidden:
        return None, "Telegram refused access with this token (unauthorized)."
    except (TimedOut, NetworkError):
        return None, "Telegram could not be reached (timeout or network failure). Please try again."
    except TelegramError as exc:
        return None, f"Telegram error: {redact(exc)}"
    finally:
        try:
            await bot.shutdown()
        except Exception:
            pass


class BotManager:
    def __init__(self):
        self.owner_app: Optional[Application] = None
        self.runtimes: dict[int, CloneRuntime] = {}
        self.stop_event = asyncio.Event()
        self.ready = False

    # ---- helpers ----------------------------------------------------------------------------
    def runtime(self, clone_id: int) -> Optional[CloneRuntime]:
        return self.runtimes.get(clone_id)

    def bot_for(self, clone_id: int) -> Optional[Bot]:
        rt = self.runtimes.get(clone_id)
        return rt.app.bot if rt and rt.app else None

    def live_count(self) -> int:
        return sum(1 for rt in self.runtimes.values() if rt.status == "LIVE")

    def status_counts(self) -> dict:
        counts: dict[str, int] = {}
        for rt in self.runtimes.values():
            counts[rt.status] = counts.get(rt.status, 0) + 1
        return counts

    async def _set_status(self, rt: CloneRuntime, status: str, error: Optional[str] = None, **extra):
        rt.status = status
        rt.last_error = redact(error) if error else None
        try:
            await db.set_clone_status(rt.clone_id, status, error, **extra)
        except Exception:
            logger.exception("Could not persist clone status")

    # ---- build applications ------------------------------------------------------------------
    def build_clone_app(self, clone_id: int, token: str) -> Application:
        app = (
            ApplicationBuilder()
            .token(token)
            .request(build_request())
            .get_updates_request(build_request())
            .rate_limiter(AIORateLimiter(max_retries=2))
            .concurrent_updates(8)
            .build()
        )
        app.bot_data["clone_id"] = clone_id
        app.add_handler(CommandHandler("start", clone_start))
        app.add_handler(CallbackQueryHandler(clone_callback))
        app.add_handler(MessageHandler(filters.ChatType.PRIVATE & ~filters.COMMAND, clone_user_message))
        app.add_error_handler(clone_error_handler)
        return app

    # ---- clone lifecycle ---------------------------------------------------------------------
    async def start_clone(self, clone_id: int, actor_id: Optional[int] = None, manual: bool = True) -> tuple[bool, str]:
        rt = self.runtimes.setdefault(clone_id, CloneRuntime(clone_id))
        async with rt.lock:
            if rt.app is not None and rt.polling_running():
                return True, "Clone is already running."
            clone = await db.clone(clone_id)
            if not clone:
                return False, "Clone not found."
            if manual:
                await db.execute("UPDATE clones SET desired_running=1, restart_count=0 WHERE id=?", (clone_id,))
                rt.restart_count = 0
            rt.conflict = False
            await self._set_status(rt, "STARTING")
            try:
                token = VAULT.decrypt(clone["token_enc"])
            except RuntimeError as exc:
                await self._set_status(rt, "ERROR", str(exc))
                return False, str(exc)
            app = self.build_clone_app(clone_id, token)
            try:
                await app.initialize()
                me = await app.bot.get_me()
                if me.id != clone["bot_id"]:
                    raise RuntimeError("The token now belongs to a different bot than the one registered.")
                await app.start()
                await app.updater.start_polling(allowed_updates=["message", "callback_query", "edited_message"],
                                                drop_pending_updates=False, error_callback=self._polling_error_callback(clone_id))
                # startup validation: give polling a moment to surface an immediate conflict/auth failure
                await asyncio.sleep(1.5)
                if rt.conflict:
                    raise Conflict("Another process is polling with this bot token.")
                if not app.updater.running:
                    raise RuntimeError("Polling did not start.")
            except Exception as exc:
                await self._teardown_app(app)
                rt.app = None
                reason = self._describe_start_error(exc)
                await self._set_status(rt, "ERROR", reason)
                await db.record_error("clone.start", exc, clone_id)
                await db.audit(actor_id, "clone.start", "failed", clone_id, reason)
                return False, reason
            rt.app = app
            rt.started_at = time.monotonic()
            if me.username and (me.username != clone["username"] or me.first_name != clone["display_name"]):
                await db.execute("UPDATE clones SET username=?, display_name=? WHERE id=?", (me.username, me.first_name or me.username, clone_id))
            await self._set_status(rt, "LIVE")
            if rt.supervisor is None or rt.supervisor.done():
                rt.supervisor = asyncio.create_task(self._supervise(clone_id), name=f"supervise-{clone_id}")
            await db.audit(actor_id, "clone.start", "ok", clone_id)
            return True, "Clone is live."

    @staticmethod
    def _describe_start_error(exc: BaseException) -> str:
        if isinstance(exc, Conflict):
            return "Polling conflict: this token is already being used by another running process."
        if isinstance(exc, TelegramInvalidToken):
            return "Telegram rejected the stored token (invalid or revoked). Rotate the token."
        if isinstance(exc, (TimedOut, NetworkError)):
            return f"Network problem while connecting to Telegram: {redact(exc)}"
        return redact(f"{type(exc).__name__}: {exc}")[:300]

    def _polling_error_callback(self, clone_id: int) -> Callable:
        def _cb(exc: TelegramError):
            rt = self.runtimes.get(clone_id)
            if isinstance(exc, Conflict) and rt:
                rt.conflict = True
                rt.last_error = "Polling conflict: token used by another process."
            logger.warning("Clone %s polling error: %s", clone_id, redact(exc))
        return _cb

    async def report_conflict(self, clone_id: int, exc: BaseException):
        rt = self.runtimes.get(clone_id)
        if rt:
            rt.conflict = True
            rt.last_error = "Polling conflict: token used by another process."

    async def _teardown_app(self, app: Application):
        for step in (
            lambda: app.updater.stop() if app.updater and app.updater.running else asyncio.sleep(0),
            lambda: app.stop() if app.running else asyncio.sleep(0),
            lambda: app.shutdown(),
        ):
            try:
                await asyncio.wait_for(step(), timeout=20)
            except Exception as exc:
                logger.debug("Teardown step failed: %s", redact(exc))

    async def stop_clone(self, clone_id: int, actor_id: Optional[int] = None, manual: bool = True, final_status: str = "STOPPED") -> tuple[bool, str]:
        rt = self.runtimes.get(clone_id)
        if rt is None:
            if manual:
                await db.execute("UPDATE clones SET desired_running=0, status='STOPPED', updated_at=? WHERE id=? AND deleted_at IS NULL", (utcnow(), clone_id))
            return True, "Clone was not running."
        async with rt.lock:
            if manual:
                await db.execute("UPDATE clones SET desired_running=0 WHERE id=?", (clone_id,))
            if rt.supervisor and not rt.supervisor.done() and asyncio.current_task() is not rt.supervisor:
                rt.supervisor.cancel()
            rt.supervisor = None
            if rt.app is not None:
                await self._set_status(rt, "STOPPING")
                await self._teardown_app(rt.app)
                rt.app = None
            await self._set_status(rt, final_status)
            if manual:
                await db.audit(actor_id, "clone.stop", "ok", clone_id)
            return True, "Clone stopped."

    async def restart_clone(self, clone_id: int, actor_id: Optional[int] = None) -> tuple[bool, str]:
        rt = self.runtimes.setdefault(clone_id, CloneRuntime(clone_id))
        await self._set_status(rt, "RESTARTING")
        await self.stop_clone(clone_id, actor_id, manual=False, final_status="RESTARTING")
        return await self.start_clone(clone_id, actor_id, manual=True)

    async def remove_clone(self, clone_id: int):
        await self.stop_clone(clone_id, manual=False, final_status="DELETED")
        self.runtimes.pop(clone_id, None)

    async def _supervise(self, clone_id: int):
        """Watch a clone; on polling death or conflict, back off and restart (bounded)."""
        try:
            while not self.stop_event.is_set():
                await asyncio.sleep(10)
                rt = self.runtimes.get(clone_id)
                if rt is None or rt.app is None:
                    return
                clone = await db.clone(clone_id)
                if not clone or not clone["desired_running"]:
                    return
                if rt.conflict:
                    await self.stop_clone(clone_id, manual=False, final_status="ERROR")
                    await self._set_status(rt, "ERROR", "Polling conflict: another process uses this token. Stop it and start the clone again.")
                    await notify_owners(f"🔴 Clone <b>{esc(clone['display_name'])}</b> stopped: polling conflict (token used elsewhere).")
                    return
                if rt.polling_running():
                    continue
                # polling died unexpectedly
                rt.restart_count += 1
                await db.execute("UPDATE clones SET restart_count=? WHERE id=?", (rt.restart_count, clone_id))
                if rt.restart_count > CLONE_RESTART_LIMIT:
                    await self.stop_clone(clone_id, manual=False, final_status="ERROR")
                    await self._set_status(rt, "ERROR", f"Polling stopped and {CLONE_RESTART_LIMIT} automatic restarts failed.")
                    await notify_owners(f"🔴 Clone <b>{esc(clone['display_name'])}</b> entered ERROR after repeated restart failures.")
                    return
                delay = min(300, 5 * (2 ** (rt.restart_count - 1)))
                await self._set_status(rt, "RESTARTING", f"Polling stopped; automatic restart {rt.restart_count} in {delay}s.")
                await asyncio.sleep(delay)
                await self.stop_clone(clone_id, manual=False, final_status="RESTARTING")
                ok, _ = await self.start_clone(clone_id, manual=False)
                if ok:
                    return  # start_clone created a new supervisor task
        except asyncio.CancelledError:
            return
        except Exception as exc:
            logger.exception("Supervisor for clone %s crashed", clone_id)
            await db.record_error("clone.supervisor", exc, clone_id)

    # ---- boot / shutdown -------------------------------------------------------------------------
    async def start_all_clones(self):
        clones = await db.clones()
        results = []
        for c in clones:
            self.runtimes.setdefault(c["id"], CloneRuntime(c["id"]))
            if c["desired_running"] and AUTO_START_CLONES:
                ok, msg = await self.start_clone(c["id"], manual=False)
                results.append((c["display_name"], ok, msg))
            else:
                await db.set_clone_status(c["id"], "STOPPED")
                self.runtimes[c["id"]].status = "STOPPED"
        return results

    async def shutdown(self):
        self.stop_event.set()
        for clone_id in list(self.runtimes):
            try:
                await self.stop_clone(clone_id, manual=False, final_status="STOPPED")
            except Exception:
                logger.exception("Error stopping clone %s", clone_id)


MANAGER: Optional[BotManager] = None

# --------------------------------------------------------------------------------------
# Broadcast engine
# --------------------------------------------------------------------------------------


@dataclass
class UICtx:
    """Where a wizard renders: the bot whose chat we edit, the user, the panel message, and callback prefixes."""
    bot: Bot
    user_id: int
    chat_id: int
    message_id: Optional[int]
    scope: Any            # "owner" or clone id
    home_cb: str
    cancel_cb: str

    @property
    def prefix(self) -> str:
        return "o" if self.scope == "owner" else "c"

    def cb(self, action: str, *args) -> str:
        if self.scope == "owner":
            return ":".join(["o", action, *map(str, args)])
        return ":".join(["c", action, str(self.scope), *map(str, args)])

    async def render(self, text: str, keyboard=None):
        self.message_id = await edit_or_send(self.bot, self.chat_id, self.message_id, text, keyboard)
        st = STATES.get(self.scope, self.user_id)
        if st is not None:
            st["panel"] = (self.chat_id, self.message_id)


BROADCAST_TASKS: dict[int, asyncio.Task] = {}
BROADCAST_CANCEL: set = set()


def is_permanent_error(exc: BaseException) -> bool:
    if isinstance(exc, Forbidden):
        return True
    if isinstance(exc, BadRequest):
        low = str(exc).lower()
        return any(k in low for k in ("chat not found", "user is deactivated", "bot was blocked", "not enough rights",
                                       "wrong file identifier", "message is too long", "caption is too long", "peer_id_invalid"))
    return False


async def create_broadcast(actor_id: int, origin: str, payload: dict, buttons: list, clone_ids: list,
                           progress: Optional[tuple] = None) -> int:
    now = utcnow()
    async with db.transaction() as tx:
        bid = await tx.fetchval(
            """INSERT INTO broadcasts(created_by,origin,payload,buttons,status,created_at,progress_chat_id,progress_message_id)
            VALUES(?,?,?,?,?,?,?,?) RETURNING id""",
            (actor_id, origin, json.dumps(payload), json.dumps(buttons), "queued", now,
             progress[0] if progress else None, progress[1] if progress else None),
        )
        total = 0
        for cid in clone_ids:
            users = await tx.fetchall(
                "SELECT user_id FROM clone_users WHERE clone_id=? AND is_banned=0 AND is_active=1", (cid,)
            )
            for u in users:
                await tx.execute(
                    """INSERT INTO broadcast_deliveries(broadcast_id,clone_id,user_id,status,attempts)
                    VALUES(?,?,?,'pending',0) ON CONFLICT(broadcast_id,clone_id,user_id) DO NOTHING""",
                    (bid, cid, u["user_id"]),
                )
            await tx.execute(
                "INSERT INTO broadcast_targets(broadcast_id,clone_id,status,total) VALUES(?,?,?,?)",
                (bid, cid, "queued", len(users)),
            )
            total += len(users)
        await tx.execute("UPDATE broadcasts SET total=? WHERE id=?", (total, bid))
    return int(bid)


def launch_broadcast(bid: int):
    if bid in BROADCAST_TASKS and not BROADCAST_TASKS[bid].done():
        return
    BROADCAST_TASKS[bid] = asyncio.create_task(run_broadcast(bid), name=f"broadcast-{bid}")


async def _mark_delivery(bid: int, cid: int, uid: int, success: bool, error: Optional[str], attempts: int):
    status = "success" if success else "failed"
    async with db.transaction() as tx:
        current = await tx.fetchone(
            "SELECT status FROM broadcast_deliveries WHERE broadcast_id=? AND clone_id=? AND user_id=?", (bid, cid, uid)
        )
        if not current or current["status"] in ("success", "failed"):
            return  # idempotent: never count a recipient twice
        await tx.execute(
            "UPDATE broadcast_deliveries SET status=?, error=?, delivered_at=?, attempts=? WHERE broadcast_id=? AND clone_id=? AND user_id=?",
            (status, redact(error)[:300] if error else None, utcnow(), attempts, bid, cid, uid),
        )
        col = "success" if success else "failed"
        await tx.execute(f"UPDATE broadcast_targets SET {col}={col}+1 WHERE broadcast_id=? AND clone_id=?", (bid, cid))
        await tx.execute(f"UPDATE broadcasts SET {col}={col}+1 WHERE id=?", (bid,))
        await db._daily_inc(tx, cid, "broadcast_success" if success else "broadcast_failed")
        if success:
            await db._daily_inc(tx, cid, "outgoing")
        if isinstance(error, str) and ("blocked" in error.lower() or "deactivated" in error.lower()):
            await tx.execute("UPDATE clone_users SET is_active=0 WHERE clone_id=? AND user_id=?", (cid, uid))


async def _deliver_one(bot: Bot, source_bot: Optional[Bot], payload: dict, markup, cache: MediaCache,
                       bid: int, cid: int, uid: int, sem: asyncio.Semaphore):
    attempts = 0
    async with sem:
        while True:
            if bid in BROADCAST_CANCEL:
                return
            attempts += 1
            try:
                await send_payload(bot, uid, payload, source_bot=source_bot, reply_markup=markup, cache=cache)
                await _mark_delivery(bid, cid, uid, True, None, attempts)
                return
            except RetryAfter as exc:
                await asyncio.sleep(float(exc.retry_after) + 0.5)
                attempts -= 1  # rate limiting is not a recipient failure
                continue
            except (TimedOut, NetworkError) as exc:
                if attempts > BROADCAST_MAX_RETRIES:
                    await _mark_delivery(bid, cid, uid, False, f"network: {exc}", attempts)
                    return
                await asyncio.sleep(min(30, 2 ** attempts))
            except TelegramError as exc:
                if is_permanent_error(exc) or attempts > BROADCAST_MAX_RETRIES:
                    await _mark_delivery(bid, cid, uid, False, f"{type(exc).__name__}: {exc}", attempts)
                    return
                await asyncio.sleep(min(30, 2 ** attempts))
            except Exception as exc:
                await _mark_delivery(bid, cid, uid, False, f"{type(exc).__name__}: {exc}", attempts)
                return


async def run_broadcast(bid: int):
    cache = MediaCache()
    try:
        b = await db.fetchone("SELECT * FROM broadcasts WHERE id=?", (bid,))
        if not b or b["status"] in ("completed", "cancelled", "failed"):
            return
        payload = json.loads(b["payload"])
        buttons = json.loads(b["buttons"])
        markup = build_url_keyboard(buttons)
        await db.execute("UPDATE broadcasts SET status='running', started_at=COALESCE(started_at,?) WHERE id=?", (utcnow(), bid))
        owner_bot = MANAGER.owner_app.bot if MANAGER and MANAGER.owner_app else None
        source_bot = owner_bot if payload.get("source_bot_id") in (None, owner_bot.id if owner_bot else None) else None
        if source_bot is None and payload.get("source_bot_id"):
            for rt in MANAGER.runtimes.values():
                if rt.app and rt.app.bot.id == payload["source_bot_id"]:
                    source_bot = rt.app.bot
        progress_task = asyncio.create_task(_progress_loop(bid))
        global_sem = asyncio.Semaphore(BROADCAST_WORKERS)
        targets = await db.fetchall("SELECT * FROM broadcast_targets WHERE broadcast_id=? ORDER BY clone_id", (bid,))
        for t in targets:
            cid = t["clone_id"]
            if bid in BROADCAST_CANCEL:
                break
            bot = MANAGER.bot_for(cid)
            if bot is None:
                await db.execute("UPDATE broadcast_targets SET status='skipped', error='clone not running' WHERE broadcast_id=? AND clone_id=?", (bid, cid))
                pend = await db.fetchall("SELECT user_id FROM broadcast_deliveries WHERE broadcast_id=? AND clone_id=? AND status='pending'", (bid, cid))
                for p in pend:
                    await _mark_delivery(bid, cid, p["user_id"], False, "clone not running", 0)
                continue
            await db.execute("UPDATE broadcast_targets SET status='running' WHERE broadcast_id=? AND clone_id=?", (bid, cid))
            pending = await db.fetchall("SELECT user_id FROM broadcast_deliveries WHERE broadcast_id=? AND clone_id=? AND status='pending'", (bid, cid))
            per_clone_sem = asyncio.Semaphore(BROADCAST_PER_CLONE_CONCURRENCY)

            async def _one(uid: int, _bot=bot, _cid=cid, _sem=per_clone_sem):
                async with global_sem:
                    await _deliver_one(_bot, source_bot if source_bot and source_bot.id != _bot.id else None,
                                       payload, markup, cache, bid, _cid, uid, _sem)

            chunk = 200
            for i in range(0, len(pending), chunk):
                if bid in BROADCAST_CANCEL:
                    break
                await asyncio.gather(*(_one(p["user_id"]) for p in pending[i:i + chunk]))
            t_status = "cancelled" if bid in BROADCAST_CANCEL else "completed"
            await db.execute("UPDATE broadcast_targets SET status=? WHERE broadcast_id=? AND clone_id=?", (t_status, bid, cid))
        progress_task.cancel()
        final = "cancelled" if bid in BROADCAST_CANCEL else "completed"
        await db.execute("UPDATE broadcasts SET status=?, finished_at=? WHERE id=?", (final, utcnow(), bid))
        await _render_progress(bid, final=True)
    except asyncio.CancelledError:
        await db.execute("UPDATE broadcasts SET status='interrupted' WHERE id=? AND status IN ('running','queued','cancelling')", (bid,))
        raise
    except Exception as exc:
        logger.exception("Broadcast %s failed", bid)
        await db.record_error("broadcast.run", exc)
        await db.execute("UPDATE broadcasts SET status='failed', finished_at=?, error=? WHERE id=?", (utcnow(), redact(exc)[:500], bid))
        await _render_progress(bid, final=True)
    finally:
        cache.cleanup()
        BROADCAST_CANCEL.discard(bid)
        BROADCAST_TASKS.pop(bid, None)


async def _progress_loop(bid: int):
    try:
        while True:
            await asyncio.sleep(PROGRESS_EDIT_INTERVAL)
            await _render_progress(bid)
    except asyncio.CancelledError:
        return


async def broadcast_progress_text(b: dict, targets: list) -> str:
    total, success, failed = b["total"], b["success"], b["failed"]
    remaining = max(0, total - success - failed)
    pct = (success + failed) / total * 100 if total else 100.0
    started = b["started_at"] or b["created_at"]
    try:
        elapsed = (now_dt() - datetime.fromisoformat(started)).total_seconds()
    except Exception:
        elapsed = 0
    status = b["status"].upper()
    icon = {"RUNNING": "📣", "COMPLETED": "✅", "CANCELLED": "🛑", "CANCELLING": "🛑", "FAILED": "❌", "INTERRUPTED": "⚠️", "QUEUED": "⏳"}.get(status, "📣")
    lines = [f"<b>{icon} Broadcast #{b['id']}</b>", "",
             f"Status: <b>{esc(status)}</b>", f"Target clones: <b>{len(targets)}</b>",
             f"Total recipients: <b>{fmt_int(total)}</b>", f"✅ Successfully delivered: <b>{fmt_int(success)}</b>",
             f"❌ Failed: <b>{fmt_int(failed)}</b>", f"⏳ Remaining: <b>{fmt_int(remaining)}</b>",
             f"📊 Progress: <b>{pct:.1f}%</b>", f"⏱ Started: {short_time(started)} · Elapsed: {human_duration(elapsed)}"]
    if len(targets) > 1 or True:
        lines += ["", "<b>Per clone</b>"]
        for t in targets:
            c = await db.fetchone("SELECT display_name, username FROM clones WHERE id=?", (t["clone_id"],))
            name = f"@{c['username']}" if c else f"clone {t['clone_id']}"
            lines.append(f"• {esc(name)}: {t['status']} ✅{fmt_int(t['success'])} ❌{fmt_int(t['failed'])} / {fmt_int(t['total'])}")
    if b["error"]:
        lines += ["", f"Error: {esc(b['error'])}"]
    return "\n".join(lines)


def broadcast_progress_keyboard(b: dict) -> InlineKeyboardMarkup:
    rows = []
    if b["status"] in ("running", "queued"):
        rows.append([("🛑 Cancel Broadcast", f"o:bccancel:{b['id']}")])
    if b["status"] == "interrupted":
        rows.append([("▶️ Resume", f"o:bcresume:{b['id']}")])
    rows.append([("🔄 Refresh", f"o:bcview:{b['id']}"), ("❗ Failures", f"o:bcfail:{b['id']}")])
    rows.append([("⬅️ Panel", "o:home")])
    return kb(rows)


async def _render_progress(bid: int, final: bool = False):
    b = await db.fetchone("SELECT * FROM broadcasts WHERE id=?", (bid,))
    if not b or not b["progress_chat_id"] or not b["progress_message_id"]:
        return
    targets = await db.fetchall("SELECT * FROM broadcast_targets WHERE broadcast_id=?", (bid,))
    text = await broadcast_progress_text(b, targets)
    bot = None
    if b["origin"] == "owner" and MANAGER.owner_app:
        bot = MANAGER.owner_app.bot
    elif b["origin"].startswith("clone:"):
        bot = MANAGER.bot_for(int(b["origin"].split(":")[1]))
    if bot is None:
        return
    markup = broadcast_progress_keyboard(b) if b["origin"] == "owner" else None
    try:
        await bot.edit_message_text(text, chat_id=b["progress_chat_id"], message_id=b["progress_message_id"],
                                    reply_markup=markup, parse_mode=ParseMode.HTML)
    except BadRequest as exc:
        if "not modified" not in str(exc).lower():
            logger.debug("Progress edit failed: %s", redact(exc))
    except TelegramError as exc:
        logger.debug("Progress edit failed: %s", redact(exc))


async def request_broadcast_cancel(bid: int, actor_id: int) -> bool:
    b = await db.fetchone("SELECT status FROM broadcasts WHERE id=?", (bid,))
    if not b or b["status"] not in ("queued", "running"):
        return False
    BROADCAST_CANCEL.add(bid)
    await db.execute("UPDATE broadcasts SET status='cancelling' WHERE id=?", (bid,))
    await db.audit(actor_id, "broadcast.cancel", clone_id=None, detail=f"broadcast={bid}")
    if bid not in BROADCAST_TASKS:
        await db.execute("UPDATE broadcasts SET status='cancelled', finished_at=? WHERE id=?", (utcnow(), bid))
        await _render_progress(bid, final=True)
    return True


async def recover_broadcasts_on_startup():
    rows = await db.fetchall("SELECT id FROM broadcasts WHERE status IN ('running','queued','cancelling')")
    for r in rows:
        await db.execute("UPDATE broadcasts SET status='interrupted' WHERE id=?", (r["id"],))
        await _render_progress(r["id"], final=True)
    if rows:
        logger.warning("%d broadcast(s) marked interrupted; resume them from the Owner Panel.", len(rows))


async def resume_broadcast(bid: int, actor_id: int) -> tuple[bool, str]:
    b = await db.fetchone("SELECT status FROM broadcasts WHERE id=?", (bid,))
    if not b:
        return False, "Broadcast not found."
    if b["status"] != "interrupted":
        return False, f"Broadcast is {b['status']}, not interrupted."
    await db.execute("UPDATE broadcasts SET status='queued' WHERE id=?", (bid,))
    await db.execute("UPDATE broadcast_targets SET status='queued' WHERE broadcast_id=? AND status IN ('running','queued')", (bid,))
    await db.audit(actor_id, "broadcast.resume", detail=f"broadcast={bid}")
    launch_broadcast(bid)
    return True, "Broadcast resumed. Already delivered recipients are skipped."


# ---- Broadcast creation wizard (shared by Owner Bot and clone panels) ------------------------


async def bc_start(ui: UICtx, actor: Actor, fixed_clone: Optional[int] = None):
    if not (actor.has(PERM_BROADCAST) or (fixed_clone is not None and actor.can_clone(fixed_clone, PERM_BROADCAST))):
        await ui.render("⛔️ You do not have broadcast permission.", back_only(ui.home_cb))
        return
    data = {"clone_ids": [fixed_clone] if fixed_clone else [], "fixed": fixed_clone is not None, "buttons": []}
    STATES.set(ui.scope, ui.user_id, "broadcast", "targets" if fixed_clone is None else "content", data, panel=(ui.chat_id, ui.message_id))
    if fixed_clone is None:
        await bc_render_targets(ui, actor)
    else:
        await ui.render("<b>📣 New Broadcast</b>\n\nSend the message or media to broadcast. Formatting and supported media are preserved.",
                        back_cancel(ui.home_cb, ui.cancel_cb))


async def bc_render_targets(ui: UICtx, actor: Actor):
    st = STATES.get(ui.scope, ui.user_id)
    if not st:
        return
    selected = set(st["data"]["clone_ids"])
    clones = await db.clones()
    if actor.role == "clone_admin":
        clones = [c for c in clones if c["id"] in actor.clone_ids]
    rows = []
    for c in clones:
        rt = MANAGER.runtime(c["id"])
        live = rt and rt.status == "LIVE"
        mark = "☑️" if c["id"] in selected else ("▫️" if live else "⚠️")
        rows.append([(f"{mark} @{c['username']}", ui.cb("bctoggle", c["id"]))])
    rows.append([("✅ All live clones", ui.cb("bcall")), ("➡️ Continue", ui.cb("bcnext"))])
    rows.append([("❌ Cancel", ui.cancel_cb)])
    await ui.render(f"<b>📣 New Broadcast – Step 1</b>\n\nSelect the clone(s) that should deliver this broadcast.\nSelected: <b>{len(selected)}</b> (⚠️ = not live, will be skipped)", kb(rows))


async def bc_render_preview(ui: UICtx):
    st = STATES.get(ui.scope, ui.user_id)
    if not st:
        return
    d = st["data"]
    payload = d["payload"]
    names = []
    recipients = 0
    for cid in d["clone_ids"]:
        c = await db.clone(cid)
        if c:
            names.append(f"@{esc(c['username'])}")
            recipients += int(await db.fetchval("SELECT COUNT(*) AS n FROM clone_users WHERE clone_id=? AND is_banned=0 AND is_active=1", (cid,)) or 0)
    btns = "\n".join(f"• {esc(b['label'])} → {esc(b['url'])}" for b in d["buttons"]) or "none"
    ok, reason = payload_supported(payload)
    warn = "" if ok else f"\n\n⚠️ {esc(reason)}"
    has_custom = any(e.get("type") == "custom_emoji" for e in (payload.get("entities") or []) + (payload.get("caption_entities") or []))
    if has_custom:
        warn += "\n\nℹ️ Custom emoji entities are sent when the delivering bot is entitled to use them; otherwise Telegram's fallback emoji is shown."
    text = (f"<b>📣 Broadcast Preview</b>\n\nContent: {esc(payload_preview(payload))}\nType: <b>{esc(payload['kind'])}</b>\n"
            f"Destination clones: {', '.join(names) or '-'}\nEstimated recipients: <b>{fmt_int(recipients)}</b>\nButtons:\n{btns}{warn}\n\nStart this broadcast?")
    rows = []
    if ok:
        rows.append([("✅ Confirm & Send", ui.cb("bcconfirm"))])
    rows.append([("⬅️ Back", ui.cb("bcbtnask")), ("❌ Cancel", ui.cancel_cb)])
    st["step"] = "preview"
    await ui.render(text, kb(rows))


async def bc_ask_buttons(ui: UICtx):
    st = STATES.get(ui.scope, ui.user_id)
    if not st:
        return
    st["step"] = "ask_button"
    n = len(st["data"]["buttons"])
    if n == 0:
        text = "Do you want to add an inline button to this broadcast?"
        rows = [[("✅ Yes", ui.cb("bcbtnyes")), ("❌ No", ui.cb("bcpreview"))]]
    else:
        text = f"<b>Buttons ({n}/{MAX_BROADCAST_BUTTONS})</b>\n" + "\n".join(f"• {esc(b['label'])}" for b in st["data"]["buttons"])
        rows = []
        if n < MAX_BROADCAST_BUTTONS:
            rows.append([("➕ Add Another Button", ui.cb("bcbtnyes"))])
        rows.append([("🗑 Remove Last", ui.cb("bcbtnpop")), ("✅ Done", ui.cb("bcpreview"))])
    rows.append([("❌ Cancel", ui.cancel_cb)])
    await ui.render(text, kb(rows))


async def bc_callback(ui: UICtx, actor: Actor, action: str, args: list, q):
    st = STATES.get(ui.scope, ui.user_id)
    if action in ("bcview", "bccancel", "bcfail", "bcresume", "bchist"):
        return  # handled by the owner router
    if not st or st["flow"] != "broadcast":
        await q.answer("This broadcast draft has expired.", show_alert=True)
        return
    d = st["data"]
    if action == "bctoggle" and args:
        cid = parse_int(args[0])
        if cid is not None and (actor.has(PERM_BROADCAST) or actor.can_clone(cid, PERM_BROADCAST)):
            if cid in d["clone_ids"]:
                d["clone_ids"].remove(cid)
            else:
                d["clone_ids"].append(cid)
        await bc_render_targets(ui, actor)
    elif action == "bcall":
        d["clone_ids"] = [c["id"] for c in await db.clones() if MANAGER.runtime(c["id"]) and MANAGER.runtime(c["id"]).status == "LIVE"
                          and (actor.has(PERM_BROADCAST) or actor.can_clone(c["id"], PERM_BROADCAST))]
        await bc_render_targets(ui, actor)
    elif action == "bcnext":
        if not d["clone_ids"]:
            await q.answer("Select at least one clone.", show_alert=True)
            return
        st["step"] = "content"
        await ui.render("<b>📣 New Broadcast – Step 2</b>\n\nSend the message or media to broadcast. Formatting, captions and supported media are preserved.",
                        back_cancel(ui.cb("bctargets"), ui.cancel_cb))
    elif action == "bctargets":
        if d.get("fixed"):
            await q.answer()
            return
        st["step"] = "targets"
        await bc_render_targets(ui, actor)
    elif action == "bcbtnask":
        await bc_ask_buttons(ui)
    elif action == "bcbtnyes":
        if len(d["buttons"]) >= MAX_BROADCAST_BUTTONS:
            await q.answer(f"Maximum {MAX_BROADCAST_BUTTONS} buttons.", show_alert=True)
            return
        st["step"] = "button_url"
        await ui.render("<b>🔗 Button URL</b>\n\nSend the destination URL (http://, https:// or tg://).", back_cancel(ui.cb("bcbtnask"), ui.cancel_cb))
    elif action == "bcbtnpop":
        if d["buttons"]:
            d["buttons"].pop()
        await bc_ask_buttons(ui)
    elif action == "bcpreview":
        if "payload" not in d:
            await q.answer("Send the broadcast content first.", show_alert=True)
            return
        await bc_render_preview(ui)
    elif action == "bcconfirm":
        if st.get("step") != "preview" or "payload" not in d:
            await q.answer("Nothing to confirm.", show_alert=True)
            return
        st["step"] = "launching"  # guard against duplicate taps
        origin = "owner" if ui.scope == "owner" else f"clone:{ui.scope}"
        await ui.render("⏳ Preparing broadcast…", None)
        bid = await create_broadcast(actor.user_id, origin, d["payload"], d["buttons"], d["clone_ids"], progress=(ui.chat_id, ui.message_id))
        STATES.clear(ui.scope, ui.user_id)
        await db.audit(actor.user_id, "broadcast.create", detail=f"broadcast={bid} clones={d['clone_ids']}")
        launch_broadcast(bid)
        await asyncio.sleep(0.5)
        await _render_progress(bid)
    else:
        await q.answer("This button is no longer valid.", show_alert=True)


async def bc_text_input(ui: UICtx, actor: Actor, st: dict, message: Message) -> bool:
    d = st["data"]
    step = st.get("step")
    if step == "content":
        payload = serialize_message(message)
        ok, reason = payload_supported(payload)
        if not ok:
            await ui.bot.send_message(ui.chat_id, f"⚠️ {esc(reason)}\nSend a different message.", parse_mode=ParseMode.HTML)
            return True
        d["payload"] = payload
        await bc_ask_buttons(ui)
        return True
    if step == "button_url":
        url = (message.text or "").strip()
        ok, reason = validate_button_url(url)
        if not ok:
            await ui.bot.send_message(ui.chat_id, f"⚠️ {esc(reason)}\nSend a valid URL.", parse_mode=ParseMode.HTML)
            return True
        d["pending_url"] = url
        st["step"] = "button_label"
        await ui.render("<b>🏷 Button Name</b>\n\nWhat name should appear on the button? (max 64 characters, standard emoji allowed)",
                        back_cancel(ui.cb("bcbtnyes"), ui.cancel_cb))
        return True
    if step == "button_label":
        label = (message.text or "").strip()
        if not label or len(label) > 64:
            await ui.bot.send_message(ui.chat_id, "⚠️ The label must be 1–64 characters.")
            return True
        d["buttons"].append({"label": label, "url": d.pop("pending_url", "")})
        await bc_ask_buttons(ui)
        return True
    if step in ("preview", "ask_button", "targets"):
        await ui.bot.send_message(ui.chat_id, "Use the buttons on the broadcast panel to continue.")
        return True
    return False

# --------------------------------------------------------------------------------------
# Conversations & inbox views (shared)
# --------------------------------------------------------------------------------------


async def inbox_view(clones: list, page: int, back: str, prefix: str = "o", filter_label: str = "all clones",
                     unanswered_only: bool = False) -> tuple[str, InlineKeyboardMarkup]:
    ids = [c["id"] for c in clones]
    if not ids:
        return "<b>💬 Inbox</b>\n\nNo clones available.", back_only(back)
    marks = ",".join("?" for _ in ids)
    where = f"cu.clone_id IN ({marks}) AND cu.last_message_at IS NOT NULL"
    if unanswered_only:
        where += " AND cu.unread>0"
    rows = await db.fetchall(
        f"""SELECT cu.clone_id, cu.user_id, cu.username, cu.first_name, cu.last_name, cu.unread, cu.last_message_at,
        c.username AS clone_username FROM clone_users cu JOIN clones c ON c.id=cu.clone_id
        WHERE {where} ORDER BY cu.last_message_at DESC LIMIT 200""",
        tuple(ids),
    )
    items, page, total_pages = paginate(rows, page)
    lines = [f"<b>💬 Inbox – {esc(filter_label)}</b>", f"Showing {'unanswered' if unanswered_only else 'recent'} conversations ({len(rows)})", ""]
    buttons = []
    for r in items:
        label = user_label(r["first_name"], r["last_name"], r["username"], r["user_id"])
        unread = f" 🔴{r['unread']}" if r["unread"] else ""
        lines.append(f"{'🔴' if r['unread'] else '▫️'} {esc(label)} · @{esc(r['clone_username'])} · {short_time(r['last_message_at'])}")
        conv_cb = f"o:conv:{r['clone_id']}:{r['user_id']}" if prefix == "o" else f"c:conv:{r['clone_id']}:{r['user_id']}"
        buttons.append([(f"{esc(label)[:28]}{unread}", conv_cb)])
    if not items:
        lines.append("No conversations yet.")
    nav_prefix = f"o:inbox:{'all' if len(ids) > 1 else ids[0]}:{1 if unanswered_only else 0}" if prefix == "o" else f"c:inbox:{ids[0]}"
    buttons.append(nav_row(nav_prefix, page, total_pages))
    if prefix == "o":
        buttons.append([("🔴 Unanswered only" if not unanswered_only else "📋 All recent",
                         f"o:inbox:{'all' if len(ids) > 1 else ids[0]}:{0 if unanswered_only else 1}:0")])
    buttons.append([("⬅️ Back", back)])
    return "\n".join(lines), kb(buttons)


async def conversation_view(clone: dict, user_id: Optional[int], back: str, prefix: str = "o") -> tuple[str, Optional[InlineKeyboardMarkup]]:
    if user_id is None:
        return "User not found.", back_only(back)
    u = await db.fetchone("SELECT * FROM clone_users WHERE clone_id=? AND user_id=?", (clone["id"], user_id))
    if not u:
        return "This user has no record for this clone.", back_only(back)
    history = await db.fetchall(
        "SELECT direction, message_type, preview, created_at, admin_id FROM message_log WHERE clone_id=? AND user_id=? ORDER BY id DESC LIMIT 12",
        (clone["id"], user_id),
    )
    lines = [f"<b>💬 Conversation</b> · @{esc(clone['username'])}", "",
             f"👤 {esc(user_label(u['first_name'], u['last_name'], u['username'], user_id))} · <code>{user_id}</code>",
             f"Status: <b>{'Banned' if u['is_banned'] else 'Active'}</b> · Unread: <b>{u['unread']}</b>",
             f"Last message: {short_time(u['last_message_at'])} · Last answered: {short_time(u['last_answered_at'])}", "",
             "<b>Recent history</b> (newest first)"]
    for h in history:
        arrow = {"incoming": "⬇️", "admin_reply": "⬆️", "outgoing": "🤖"}.get(h["direction"], "•")
        text = h["preview"] or f"[{h['message_type']}]"
        lines.append(f"{arrow} {short_time(h['created_at'])} {esc(text)}")
    if not history:
        lines.append("No messages recorded.")
    lines += ["", "Reply with the button below, or reply directly to any relayed message of this user."]
    rows = [
        [("✍️ Reply", f"{prefix}:reply:{clone['id']}:{user_id}"), ("👤 View Profile", f"url:tg://user?id={user_id}")],
        [("✅ Unban" if u["is_banned"] else "🚫 Ban", f"{prefix}:ban:{clone['id']}:{user_id}"), ("👁 Mark read", f"{prefix}:read:{clone['id']}:{user_id}")],
        [("⬅️ Back", back)],
    ]
    return "\n".join(lines), kb(rows)


async def deliver_admin_reply(clone: dict, admin_id: int, source_bot: Bot, message: Message, user_id: int,
                              reply_to_user_message_id: Optional[int] = None) -> tuple[bool, str]:
    """Send an admin's message to the customer through the clone bot that owns the conversation."""
    bot = MANAGER.bot_for(clone["id"])
    rt = MANAGER.runtime(clone["id"])
    if bot is None or not rt or rt.status != "LIVE":
        return False, f"Clone @{clone['username']} is not running; start it before replying."
    payload = serialize_message(message)
    ok, reason = payload_supported(payload)
    if not ok:
        return False, reason
    try:
        sent = await send_payload(bot, user_id, payload, source_bot=source_bot, reply_to_message_id=reply_to_user_message_id)
    except BadRequest as exc:
        if reply_to_user_message_id and "replied" in str(exc).lower():
            try:
                sent = await send_payload(bot, user_id, payload, source_bot=source_bot)
            except TelegramError as exc2:
                return False, redact(exc2)
        else:
            return False, redact(exc)
    except Forbidden:
        await db.execute("UPDATE clone_users SET is_active=0 WHERE clone_id=? AND user_id=?", (clone["id"], user_id))
        return False, "The user has blocked this clone bot."
    except (TelegramError, ValueError) as exc:
        return False, redact(exc)
    await db.log_message(clone["id"], "admin_reply", user_id, admin_id, payload["kind"], sent.chat_id, sent.message_id,
                         related_message_id=message.message_id, preview=payload_preview(payload))
    return True, f"Delivered via @{clone['username']}"


# --------------------------------------------------------------------------------------
# Owner Bot: texts and keyboards
# --------------------------------------------------------------------------------------


def owner_home_keyboard(actor: Actor) -> InlineKeyboardMarkup:
    rows = []
    if actor.is_owner:
        rows.append([("🤖 Create Clone Bot", "o:create")])
    if actor.has(PERM_CLONES) or actor.role == "clone_admin":
        rows.append([("📋 Manage Clone Bots", "o:clones:0"), ("📊 Clone Status", "o:status")])
    if actor.has(PERM_BROADCAST) or actor.role == "clone_admin":
        rows.append([("📣 Global Broadcast" if actor.role != "clone_admin" else "📣 Broadcast", "o:bcstart"), ("📜 Broadcast History", "o:bchist:0")])
    if actor.has(PERM_CONVERSATIONS) or actor.role == "clone_admin":
        rows.append([("💬 Conversation Management", "o:convs")])
    if actor.has(PERM_STATS) or actor.role == "clone_admin":
        rows.append([("📈 Global Statistics" if actor.role != "clone_admin" else "📈 Statistics", "o:stats")])
    if actor.is_owner:
        rows.append([("👥 Admin Management", "o:admins")])
    if actor.has(PERM_SETTINGS):
        rows.append([("⚙️ Global Settings", "o:settings")])
    if actor.has(PERM_LOGS):
        rows.append([("🩺 System Diagnostics", "o:diag")])
    if actor.has(PERM_BACKUP):
        rows.append([("💾 Backup and Restore", "o:backup")])
    if actor.has(PERM_LOGS):
        rows.append([("📜 Activity and Error Logs", "o:logs:audit:0")])
    return kb(rows)


async def owner_home_text(actor: Actor) -> str:
    total = await db.clone_count()
    counts = MANAGER.status_counts()
    users = await db.fetchval("SELECT COUNT(*) AS n FROM platform_users")
    active_bc = await db.fetchval("SELECT COUNT(*) AS n FROM broadcasts WHERE status IN ('queued','running','cancelling')")
    role = {"owner": "👑 Platform Owner", "manager": "🛡 Delegated Manager", "clone_admin": "🧑‍💼 Clone Administrator"}[actor.role]
    return (
        "<b>👑 Owner Panel</b>\n\n"
        f"Role: <b>{role}</b>\n"
        f"Clones: <b>{total}/{MAX_CLONES}</b> · 🟢 {counts.get('LIVE', 0)} live · 🔴 {counts.get('ERROR', 0)} error\n"
        f"Platform users: <b>{fmt_int(users)}</b> · Active broadcasts: <b>{fmt_int(active_bc)}</b>\n"
        f"Uptime: <b>{human_duration(time.monotonic() - START_MONOTONIC)}</b>\n\n"
        "Choose a section:"
    )


async def visible_clones(actor: Actor) -> list:
    clones = await db.clones()
    if actor.role == "clone_admin":
        return [c for c in clones if c["id"] in actor.clone_ids]
    return clones


def clone_line(c: dict, users: int) -> str:
    rt = MANAGER.runtime(c["id"])
    state = rt.status if rt else c["status"]
    return (f"{status_icon(state)} <b>{esc(c['display_name'])}</b> @{esc(c['username'])} · {esc(state)}\n"
            f"   🛡 {c['admin_id']} · 👥 {fmt_int(users)} · 🕒 {short_time(c['last_activity'])}"
            + (f"\n   ⚠️ {esc((c['last_error'] or '')[:90])}" if c["last_error"] and state in ("ERROR", "RESTARTING") else ""))


async def clones_list_view(actor: Actor, page: int, filter_status: Optional[str] = None) -> tuple[str, InlineKeyboardMarkup]:
    clones = await visible_clones(actor)
    if filter_status:
        clones = [c for c in clones if (MANAGER.runtime(c["id"]).status if MANAGER.runtime(c["id"]) else c["status"]) in filter_status.split(",")]
    items, page, total_pages = paginate(clones, page, 5)
    lines = [f"<b>📋 Manage Clone Bots</b> · {len(clones)} registered" + (f" ({esc(filter_status.lower())})" if filter_status else ""), ""]
    buttons = []
    for c in items:
        users = await db.fetchval("SELECT COUNT(*) AS n FROM clone_users WHERE clone_id=?", (c["id"],))
        lines.append(clone_line(c, users or 0))
        buttons.append([(f"{status_icon((MANAGER.runtime(c['id']).status if MANAGER.runtime(c['id']) else c['status']))} @{c['username']}", f"o:clone:{c['id']}")])
    if not items:
        lines.append("No clone bots registered yet.")
    buttons.append(nav_row(f"o:clones", page, total_pages) if not filter_status else [("⬅️ Status", "o:status")])
    buttons.append([("⬅️ Back", "o:home")])
    return "\n".join(lines), kb(buttons)


async def clone_detail_view(actor: Actor, clone: dict) -> tuple[str, InlineKeyboardMarkup]:
    rt = MANAGER.runtime(clone["id"])
    state = rt.status if rt else clone["status"]
    s = await clone_stats_row(clone["id"])
    ops = [r["user_id"] for r in await db.fetchall("SELECT user_id FROM clone_operators WHERE clone_id=?", (clone["id"],))]
    text = (
        f"<b>🤖 {clone_title(clone)}</b>\n\n"
        f"State: {status_icon(state)} <b>{esc(state)}</b> · Polling: <b>{'yes' if rt and rt.polling_running() else 'no'}</b>\n"
        f"Bot ID: <code>{clone['bot_id']}</code> · Registration #{clone['id']}\n"
        f"🛡 Admin: <code>{clone['admin_id']}</code>" + (f" · Operators: {', '.join(f'<code>{o}</code>' for o in ops)}" if ops else "") + "\n"
        f"👥 Users: <b>{fmt_int(s['users'])}</b> · Unread: <b>{fmt_int(s['unread'])}</b>\n"
        f"📥 {fmt_int(s['incoming'])} in · 📤 {fmt_int(s['outgoing'])} out · 📣 {fmt_int(s['broadcasts'])} broadcasts\n"
        f"🛠 Maintenance: <b>{'ON' if await db.clone_setting(clone['id'], 'maintenance_mode', '0') == '1' else 'OFF'}</b>\n"
        f"Created: {short_time(clone['created_at'])} · Restarts: {clone['restart_count']}\n"
        f"Last activity: {short_time(clone['last_activity'])}\n"
        + (f"⚠️ Last error: {esc(clone['last_error'])}\n" if clone["last_error"] else "")
    )
    c = clone["id"]
    rows = [[("📊 Statistics", f"o:cstats:{c}"), ("💬 Inbox", f"o:inbox:{c}:0:0")]]
    if actor.can_clone(c, PERM_CLONES):
        if state == "LIVE":
            rows.append([("🔄 Restart", f"o:crestart:{c}"), ("⏹ Stop", f"o:cstopask:{c}")])
        else:
            rows.append([("▶️ Start", f"o:cstart:{c}")])
        rows.append([("👋 Welcome", f"o:cedit:{c}:start_message"), ("🛠 Maintenance", f"o:cmaint:{c}")])
        rows.append([("👥 Users", f"o:cusers:{c}"), ("📣 Broadcast", f"o:bcstart:{c}")])
        rows.append([("📜 Delivery History", f"o:bchist:0:{c}"), ("🩺 Diagnostics", f"o:cdiag:{c}")])
    if actor.is_owner:
        rows.append([("🛡 Change Admin", f"o:cadmin:{c}"), ("➕ Operators", f"o:cops:{c}")])
        rows.append([("🔑 Rotate Token", f"o:crotate:{c}"), ("🗑 Delete", f"o:cdelask:{c}")])
    rows.append([("⬅️ Back", "o:clones:0")])
    return text, kb(rows)


async def status_dashboard_text() -> str:
    total = await db.clone_count()
    counts = MANAGER.status_counts()
    active_bc = await db.fetchval("SELECT COUNT(*) AS n FROM broadcasts WHERE status IN ('queued','running','cancelling')")
    users = await db.fetchval("SELECT COUNT(*) AS n FROM clone_users")
    msgs = await db.fetchone(
        "SELECT SUM(CASE WHEN direction='incoming' THEN 1 ELSE 0 END) AS inc, SUM(CASE WHEN direction IN ('outgoing','admin_reply') THEN 1 ELSE 0 END) AS out FROM message_log"
    )
    errors = await db.fetchall("SELECT clone_id, context, error, created_at FROM errors ORDER BY id DESC LIMIT 3")
    lines = ["<b>📊 Clone Status Dashboard</b>", "",
             f"Registered: <b>{total}/{MAX_CLONES}</b>",
             f"🟢 Live: <b>{counts.get('LIVE', 0)}</b> · 🟡 Starting: <b>{counts.get('STARTING', 0) + counts.get('VALIDATING', 0)}</b> · 🔁 Restarting: <b>{counts.get('RESTARTING', 0)}</b>",
             f"⚪️ Stopped: <b>{counts.get('STOPPED', 0) + counts.get('STOPPING', 0)}</b> · 🔴 Error: <b>{counts.get('ERROR', 0)}</b>",
             f"📣 Active broadcast jobs: <b>{fmt_int(active_bc)}</b>",
             f"👥 Total clone users: <b>{fmt_int(users)}</b>",
             f"📥 Incoming messages: <b>{fmt_int(msgs['inc'])}</b> · 📤 Outgoing: <b>{fmt_int(msgs['out'])}</b>",
             f"🩺 Last successful health check: {short_time(LAST_HEALTH_OK['at'])}", "", "<b>Recent system errors</b>"]
    lines += [f"{short_time(e['created_at'])} · clone {e['clone_id'] or '-'} · {esc(e['context'])}: {esc(e['error'][:80])}" for e in errors] or ["None recorded."]
    return "\n".join(lines)


def status_dashboard_keyboard() -> InlineKeyboardMarkup:
    return kb([
        [("🔄 Refresh", "o:status")],
        [("🟢 Live", "o:clonesf:LIVE"), ("⚪️ Stopped", "o:clonesf:STOPPED,STOPPING"), ("🔴 Failed", "o:clonesf:ERROR,RESTARTING")],
        [("⬅️ Back", "o:home")],
    ])


async def global_stats_text(actor: Actor) -> str:
    clones = await visible_clones(actor)
    ids = [c["id"] for c in clones]
    if not ids:
        return "<b>📈 Global Statistics</b>\n\nNo clones registered."
    marks = ",".join("?" for _ in ids)
    counts = MANAGER.status_counts()
    unique_users = await db.fetchval(f"SELECT COUNT(DISTINCT user_id) AS n FROM clone_users WHERE clone_id IN ({marks})", tuple(ids))
    memberships = await db.fetchval(f"SELECT COUNT(*) AS n FROM clone_users WHERE clone_id IN ({marks})", tuple(ids))
    msgs = await db.fetchone(
        f"""SELECT SUM(CASE WHEN direction='incoming' THEN 1 ELSE 0 END) AS inc,
        SUM(CASE WHEN direction IN ('outgoing','admin_reply') THEN 1 ELSE 0 END) AS out,
        SUM(CASE WHEN direction='admin_reply' THEN 1 ELSE 0 END) AS rep FROM message_log WHERE clone_id IN ({marks})""", tuple(ids))
    bc = await db.fetchone(
        f"SELECT COUNT(DISTINCT broadcast_id) AS n, COALESCE(SUM(success),0) AS s, COALESCE(SUM(failed),0) AS f FROM broadcast_targets WHERE clone_id IN ({marks})", tuple(ids))
    restarts = await db.fetchval(f"SELECT COALESCE(SUM(restart_count),0) AS n FROM clones WHERE id IN ({marks})", tuple(ids))
    errors = await db.fetchval("SELECT COUNT(*) AS n FROM errors WHERE created_at>=?", (days_ago_iso(7),))
    lines = ["<b>📈 Global Statistics</b>", "",
             f"🤖 Clones: <b>{len(ids)}</b> · 🟢 {counts.get('LIVE', 0)} · ⚪️ {counts.get('STOPPED', 0)} · 🟡 {counts.get('STARTING', 0) + counts.get('RESTARTING', 0)} · 🔴 {counts.get('ERROR', 0)}",
             f"👤 Unique platform users: <b>{fmt_int(unique_users)}</b>",
             f"👥 Clone-user memberships: <b>{fmt_int(memberships)}</b>",
             f"📥 Incoming: <b>{fmt_int(msgs['inc'])}</b> · 📤 Outgoing: <b>{fmt_int(msgs['out'])}</b> · 💬 Admin replies: <b>{fmt_int(msgs['rep'])}</b>",
             f"📣 Broadcasts: <b>{fmt_int(bc['n'])}</b> · ✅ {fmt_int(bc['s'])} · ❌ {fmt_int(bc['f'])}",
             f"🔁 Clone restarts: <b>{fmt_int(restarts)}</b> · ⚠️ Errors (7d): <b>{fmt_int(errors)}</b>", "", "<b>Period breakdown</b>"]
    for label, days in (("Today", 0), ("7 days", 6), ("30 days", 29)):
        r = await db.fetchone(
            f"""SELECT COALESCE(SUM(new_users),0) AS nu, COALESCE(SUM(incoming),0) AS inc, COALESCE(SUM(outgoing),0) AS out,
            COALESCE(SUM(admin_replies),0) AS rep, COALESCE(SUM(broadcast_success),0) AS bs FROM daily_stats
            WHERE clone_id IN ({marks}) AND day>=?""",
            tuple(ids) + ((now_dt() - timedelta(days=days)).date().isoformat(),))
        lines.append(f"{label}: +{r['nu']} users | ↓{r['inc']} | ↑{r['out']} | 💬{r['rep']} | 📣{r['bs']}")
    top = await db.fetchall(
        f"""SELECT c.username, COUNT(m.id) AS n FROM clones c LEFT JOIN message_log m ON m.clone_id=c.id AND m.created_at>=?
        WHERE c.id IN ({marks}) GROUP BY c.id, c.username ORDER BY n DESC LIMIT 5""",
        (days_ago_iso(7),) + tuple(ids))
    lines += ["", "<b>Most active clones (7d)</b>"] + [f"• @{esc(t['username'])}: {fmt_int(t['n'])} messages" for t in top]
    return "\n".join(lines)


async def admins_view() -> tuple[str, InlineKeyboardMarkup]:
    owners = await db.owner_ids()
    managers = await db.fetchall("SELECT user_id, permissions FROM managers ORDER BY added_at")
    clones = await db.clones()
    lines = ["<b>👥 Admin Management</b>", "", "<b>Platform owners</b>"] + [f"👑 <code>{o}</code>" for o in owners]
    lines += ["", "<b>Delegated managers</b>"]
    for m in managers:
        try:
            perms = json.loads(m["permissions"])
        except Exception:
            perms = []
        lines.append(f"🛡 <code>{m['user_id']}</code> – {', '.join(perms) or 'no permissions'}")
    if not managers:
        lines.append("None.")
    lines += ["", "<b>Clone administrators</b>"]
    by_admin: dict[int, list] = {}
    for c in clones:
        by_admin.setdefault(c["admin_id"], []).append(f"@{c['username']}")
    lines += [f"🧑‍💼 <code>{a}</code> – {esc(', '.join(v))}" for a, v in by_admin.items()] or ["None."]
    buttons = [[("➕ Add Manager", "o:madd"), ("➖ Remove Manager", "o:mremove")]]
    buttons += [[(f"🛡 Permissions {m['user_id']}", f"o:mperm:{m['user_id']}")] for m in managers[:10]]
    buttons.append([("📜 Recent admin actions", "o:logs:audit:0")])
    buttons.append([("⬅️ Back", "o:home")])
    return "\n".join(lines), kb(buttons)


async def manager_perm_view(user_id: int) -> tuple[str, InlineKeyboardMarkup]:
    perms = await db.manager_perms(user_id)
    if perms is None:
        return "Manager not found.", back_only("o:admins")
    rows = [[(f"{'☑️' if p in perms else '▫️'} {PERM_LABELS[p]}", f"o:mtoggle:{user_id}:{p}")] for p in ALL_PERMS]
    rows.append([("⬅️ Back", "o:admins")])
    return f"<b>🛡 Permissions for <code>{user_id}</code></b>\n\nToggle what this manager may do:", kb(rows)


async def settings_view() -> tuple[str, InlineKeyboardMarkup]:
    start = await db.setting("default_start_message")
    maint = await db.setting("default_maintenance_message")
    notify = await db.setting("notify_owners_on_user_message", "0") == "1"
    header = await db.setting("forward_header", "1") == "1"
    text = ("<b>⚙️ Global Settings</b>\n\n"
            f"Default welcome message:\n<blockquote>{esc(start)}</blockquote>\n"
            f"Default maintenance notice:\n<blockquote>{esc(maint)}</blockquote>\n"
            f"Owners also receive all user messages: <b>{'ON' if notify else 'OFF'}</b>\n"
            f"Sender header on relayed messages: <b>{'ON' if header else 'OFF'}</b>\n\n"
            f"Clone capacity: {MAX_CLONES} · Broadcast workers: {BROADCAST_WORKERS} · DB: {'PostgreSQL' if db.is_postgres else 'SQLite'}")
    rows = [[("👋 Default Welcome", "o:sedit:default_start_message"), ("🛠 Default Maintenance", "o:sedit:default_maintenance_message")],
            [(f"{'🔕 Disable' if notify else '🔔 Enable'} owner copies", "o:stoggle:notify_owners_on_user_message"),
             (f"{'Hide' if header else 'Show'} sender header", "o:stoggle:forward_header")],
            [("⬅️ Back", "o:home")]]
    return text, kb(rows)


async def diagnostics_text() -> str:
    db_ok = await db.ping()
    size = await db.size_bytes()
    total = await db.clone_count()
    jobs = await db.fetchall("SELECT id, status FROM broadcasts WHERE status IN ('queued','running','cancelling','interrupted') ORDER BY id DESC LIMIT 10")
    errors = await db.fetchall("SELECT clone_id, context, error, created_at FROM errors ORDER BY id DESC LIMIT 5")
    actions = await db.fetchall("SELECT actor_id, action, result, created_at FROM audit_log ORDER BY id DESC LIMIT 5")
    restarts = await db.fetchval("SELECT COALESCE(SUM(restart_count),0) AS n FROM clones WHERE deleted_at IS NULL")
    lines = ["<b>🩺 System Diagnostics</b>", "",
             f"Version: <b>{APP_VERSION}</b> · Schema: <b>{SCHEMA_VERSION}</b>",
             f"Uptime: <b>{human_duration(time.monotonic() - START_MONOTONIC)}</b>",
             f"Database: <b>{'PostgreSQL' if db.is_postgres else 'SQLite'}</b> · Connectivity: <b>{'OK' if db_ok else 'FAILED'}</b>"
             + (f" · Size: <b>{size / 1024 / 1024:.2f} MB</b>" if size is not None else ""),
             f"Registered clones: <b>{total}/{MAX_CLONES}</b> · Running tasks: <b>{len([t for t in asyncio.all_tasks() if not t.done()])}</b>",
             f"Restart attempts (total): <b>{fmt_int(restarts)}</b>",
             f"Last successful health check: {short_time(LAST_HEALTH_OK['at'])}", "", "<b>Per-clone polling</b>"]
    for c in await db.clones():
        rt = MANAGER.runtime(c["id"])
        lines.append(f"{status_icon(rt.status if rt else c['status'])} @{esc(c['username'])}: {rt.status if rt else c['status']}"
                     f"{' · polling' if rt and rt.polling_running() else ''}{(' · ' + esc((rt.last_error or '')[:60])) if rt and rt.last_error else ''}")
    lines += ["", "<b>Open / interrupted jobs</b>"] + ([f"#{j['id']} {j['status']}" for j in jobs] or ["None."])
    lines += ["", "<b>Recent errors</b>"] + ([f"{short_time(e['created_at'])} · {esc(e['context'])}: {esc(e['error'][:80])}" for e in errors] or ["None."])
    lines += ["", "<b>Recent admin actions</b>"] + ([f"{short_time(a['created_at'])} · {a['actor_id']} · {esc(a['action'])} ({esc(a['result'])})" for a in actions] or ["None."])
    return "\n".join(lines)


async def logs_view(kind: str, page: int) -> tuple[str, InlineKeyboardMarkup]:
    if kind == "errors":
        rows = await db.fetchall("SELECT clone_id, context, error, created_at FROM errors ORDER BY id DESC LIMIT 100")
        items, page, total_pages = paginate(rows, page)
        lines = ["<b>📜 Error Log</b>", ""] + [f"{short_time(r['created_at'])} · clone {r['clone_id'] or '-'} · <b>{esc(r['context'])}</b>\n{esc(r['error'][:160])}" for r in items]
    else:
        rows = await db.fetchall("SELECT actor_id, clone_id, action, detail, result, created_at FROM audit_log ORDER BY id DESC LIMIT 100")
        items, page, total_pages = paginate(rows, page)
        lines = ["<b>📜 Activity Log</b>", ""] + [f"{short_time(r['created_at'])} · <code>{r['actor_id']}</code> · <b>{esc(r['action'])}</b> {esc(r['result'])}"
                                                 + (f" · clone {r['clone_id']}" if r["clone_id"] else "") + (f"\n{esc(r['detail'][:120])}" if r["detail"] else "") for r in items]
    if not items:
        lines.append("Nothing recorded.")
    buttons = [nav_row(f"o:logs:{kind}", page, total_pages),
               [("⚠️ Errors" if kind != "errors" else "📜 Activity", f"o:logs:{'errors' if kind != 'errors' else 'audit'}:0")],
               [("⬅️ Back", "o:home")]]
    return "\n".join(lines), kb(buttons)


async def broadcast_history_view(actor: Actor, page: int, clone_id: Optional[int] = None) -> tuple[str, InlineKeyboardMarkup]:
    if clone_id is not None:
        rows = await db.fetchall(
            """SELECT b.* FROM broadcasts b JOIN broadcast_targets t ON t.broadcast_id=b.id WHERE t.clone_id=? ORDER BY b.id DESC LIMIT 100""", (clone_id,))
    elif actor.role == "clone_admin":
        marks = ",".join("?" for _ in actor.clone_ids) or "NULL"
        rows = await db.fetchall(
            f"SELECT DISTINCT b.* FROM broadcasts b JOIN broadcast_targets t ON t.broadcast_id=b.id WHERE t.clone_id IN ({marks}) ORDER BY b.id DESC LIMIT 100",
            tuple(actor.clone_ids))
    else:
        rows = await db.fetchall("SELECT * FROM broadcasts ORDER BY id DESC LIMIT 100")
    items, page, total_pages = paginate(rows, page)
    lines = ["<b>📜 Broadcast History</b>", ""]
    buttons = []
    for b in items:
        lines.append(f"#{b['id']} · <b>{esc(b['status'])}</b> · ✅{fmt_int(b['success'])} ❌{fmt_int(b['failed'])} / {fmt_int(b['total'])} · {short_time(b['created_at'])}")
        buttons.append([(f"#{b['id']} {b['status']}", f"o:bcview:{b['id']}")])
    if not items:
        lines.append("No broadcasts yet.")
    buttons.append(nav_row(f"o:bchist" if clone_id is None else f"o:bchistc:{clone_id}", page, total_pages))
    buttons.append([("⬅️ Back", "o:home" if clone_id is None else f"o:clone:{clone_id}")])
    return "\n".join(lines), kb(buttons)

# --------------------------------------------------------------------------------------
# Owner Bot handlers
# --------------------------------------------------------------------------------------


def owner_ui(update: Update, context: ContextTypes.DEFAULT_TYPE, message_id: Optional[int] = None) -> UICtx:
    return UICtx(context.bot, update.effective_user.id, update.effective_chat.id, message_id, "owner", "o:home", "o:cancel")


async def owner_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.effective_user or not update.effective_message or update.effective_chat.type != "private":
        return
    actor = await resolve_actor(update.effective_user.id)
    if actor is None:
        return  # silent for unauthorized users
    STATES.clear("owner", actor.user_id)
    await update.effective_message.reply_text(await owner_home_text(actor), reply_markup=owner_home_keyboard(actor), parse_mode=ParseMode.HTML)


async def owner_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    if not q or not q.data:
        return
    actor = await resolve_actor(q.from_user.id)
    if actor is None:
        await q.answer()
        return
    parts = q.data.split(":")
    if parts[0] != "o" or len(parts) < 2:
        await q.answer()
        return
    action, args = parts[1], parts[2:]
    uid = actor.user_id
    ui = UICtx(context.bot, uid, q.message.chat_id, q.message.message_id, "owner", "o:home", "o:cancel")
    try:
        await q.answer()
    except TelegramError:
        pass

    def arg_int(i: int) -> Optional[int]:
        return parse_int(args[i]) if len(args) > i else None

    async def need(perm: str, clone_id: Optional[int] = None) -> bool:
        ok = actor.can_clone(clone_id, perm) if clone_id is not None else actor.has(perm)
        if not ok:
            await q.answer("⛔️ You are not authorized for this action.", show_alert=True)
        return ok

    async def clone_or_none(i: int = 0) -> Optional[dict]:
        cid = arg_int(i)
        c = await db.clone(cid) if cid is not None else None
        if not c:
            await safe_edit(q, "This clone no longer exists.", back_only("o:clones:0"))
        return c

    # ---------------- navigation ----------------
    if action == "noop":
        return
    if action in ("home", "cancel"):
        if action == "cancel":
            STATES.clear("owner", uid)
        await safe_edit(q, await owner_home_text(actor), owner_home_keyboard(actor))
        return

    # ---------------- clone creation wizard (owner only) ----------------
    if action == "create":
        if not actor.is_owner:
            return await q.answer("⛔️ Owner only.", show_alert=True)
        count = await db.clone_count()
        if count >= MAX_CLONES:
            return await safe_edit(q, f"🚫 The platform limit of {MAX_CLONES} registered clones is reached ({count}/{MAX_CLONES}). Delete a clone to free a slot.", back_only("o:home"))
        STATES.set("owner", uid, "create", "token", {}, panel=(q.message.chat_id, q.message.message_id))
        return await safe_edit(q, "<b>🤖 Create Your Clone Bot</b>\n\nPlease send me the BotFather token of the Telegram bot you want to connect.\n\nYour token will be validated securely before the bot is registered.",
                               kb([[("❌ Cancel", "o:cancel")]]))
    if action == "createback":
        st = STATES.get("owner", uid)
        if not st or st["flow"] != "create" or not actor.is_owner:
            return await safe_edit(q, "The creation workflow has expired.", back_only("o:home"))
        step = args[0] if args else "token"
        if step == "token":
            st["step"] = "token"
            st["data"].pop("token", None)
            return await safe_edit(q, "<b>🤖 Create Your Clone Bot</b>\n\nSend the BotFather token.", kb([[("❌ Cancel", "o:cancel")]]))
        st["step"] = "admin"
        return await safe_edit(q, "<b>🛡 Clone Administrator</b>\n\nSend the Telegram numeric user ID of the administrator who will manage this clone.", back_cancel("o:createback:token"))
    if action == "createconfirm":
        st = STATES.get("owner", uid)
        if not st or st["flow"] != "create" or st.get("step") != "confirm" or not actor.is_owner:
            return await safe_edit(q, "The creation workflow has expired or was already confirmed.", back_only("o:home"))
        st["step"] = "committing"
        return await finalize_clone_creation(ui, actor, st)

    # ---------------- clone list / detail ----------------
    if action == "clones":
        text, markup = await clones_list_view(actor, arg_int(0) or 0)
        return await safe_edit(q, text, markup)
    if action == "clonesf":
        text, markup = await clones_list_view(actor, 0, args[0] if args else None)
        return await safe_edit(q, text, markup)
    if action == "status":
        return await safe_edit(q, await status_dashboard_text(), status_dashboard_keyboard())
    if action == "clone":
        c = await clone_or_none()
        if not c or not actor.can_clone(c["id"], PERM_STATS):
            return
        STATES.clear("owner", uid)
        text, markup = await clone_detail_view(actor, c)
        return await safe_edit(q, text, markup)
    if action == "cstats":
        c = await clone_or_none()
        if c and actor.can_clone(c["id"], PERM_STATS):
            return await safe_edit(q, await clone_stats_text(c), kb([[("🔄 Refresh", q.data)], [("⬅️ Back", f"o:clone:{c['id']}")]]))
        return
    if action == "cdiag":
        c = await clone_or_none()
        if c and actor.can_clone(c["id"], PERM_CLONES):
            return await safe_edit(q, await clone_diag_text(c), kb([[("🔄 Refresh", q.data)], [("⬅️ Back", f"o:clone:{c['id']}")]]))
        return
    if action in ("cstart", "crestart"):
        c = await clone_or_none()
        if not c or not await need(PERM_CLONES, c["id"]):
            return
        await safe_edit(q, f"⏳ {'Restarting' if action == 'crestart' else 'Starting'} @{esc(c['username'])}…", None)
        ok, msg = await (MANAGER.restart_clone if action == "crestart" else MANAGER.start_clone)(c["id"], uid)
        c = await db.clone(c["id"])
        text, markup = await clone_detail_view(actor, c)
        return await safe_edit(q, f"{'✅' if ok else '❌'} {esc(msg)}\n\n{text}", markup)
    if action == "cstopask":
        c = await clone_or_none()
        if c and await need(PERM_CLONES, c["id"]):
            return await safe_edit(q, f"Stop @{esc(c['username'])}? Users will not receive responses until it is started again. Running broadcasts through this clone will fail for remaining recipients.",
                                   kb([[("✅ Stop", f"o:cstop:{c['id']}"), ("❌ Cancel", f"o:clone:{c['id']}")]]))
        return
    if action == "cstop":
        c = await clone_or_none()
        if not c or not await need(PERM_CLONES, c["id"]):
            return
        await safe_edit(q, f"⏳ Stopping @{esc(c['username'])}…", None)
        ok, msg = await MANAGER.stop_clone(c["id"], uid)
        c = await db.clone(c["id"])
        text, markup = await clone_detail_view(actor, c)
        return await safe_edit(q, f"{'✅' if ok else '❌'} {esc(msg)}\n\n{text}", markup)
    if action == "cusers":
        c = await clone_or_none()
        if c and actor.can_clone(c["id"], PERM_CONVERSATIONS):
            STATES.clear("owner", uid)
            return await safe_edit(q, await clone_users_text(c), kb([
                [("🔎 Search", f"o:usearch:{c['id']}"), ("📤 Export CSV", f"o:uexport:{c['id']}")],
                [("⬅️ Back", f"o:clone:{c['id']}")]]))
        return
    if action == "usearch":
        c = await clone_or_none()
        if c and actor.can_clone(c["id"], PERM_CONVERSATIONS):
            STATES.set("owner", uid, "user_search", "query", {"clone_id": c["id"]}, panel=(q.message.chat_id, q.message.message_id))
            return await safe_edit(q, "<b>🔎 Search Users</b>\n\nSend a Telegram ID or exact @username.", back_cancel(f"o:cusers:{c['id']}"))
        return
    if action == "uexport":
        c = await clone_or_none()
        if c and actor.can_clone(c["id"], PERM_CONVERSATIONS):
            return await export_users_csv(context.bot, uid, c)
        return
    if action == "ban":
        c = await clone_or_none()
        if not c or not actor.can_clone(c["id"], PERM_CONVERSATIONS):
            return
        target = arg_int(1)
        banned = await toggle_ban(c["id"], target, uid)
        if banned is None:
            return await q.answer("User not found.", show_alert=True)
        return await safe_edit(q, await user_detail_text(c["id"], target), user_detail_keyboard(c["id"], target, banned, f"o:cusers:{c['id']}"))
    if action == "read":
        c = await clone_or_none()
        if c and actor.can_clone(c["id"], PERM_CONVERSATIONS):
            await db.execute("UPDATE clone_users SET unread=0 WHERE clone_id=? AND user_id=?", (c["id"], arg_int(1)))
            text, markup = await conversation_view(c, arg_int(1), back=f"o:inbox:{c['id']}:0:0")
            return await safe_edit(q, text, markup)
        return
    if action == "cedit":
        c = await clone_or_none()
        key = args[1] if len(args) > 1 else ""
        if c and await need(PERM_CLONES, c["id"]) and key in {"start_message", "maintenance_message"}:
            current = await db.clone_setting(c["id"], key, await db.setting("default_" + key, ""))
            STATES.set("owner", uid, "edit_setting", key, {"key": key, "clone_id": c["id"]}, panel=(q.message.chat_id, q.message.message_id))
            return await safe_edit(q, f"<b>✏️ {'Welcome Message' if key == 'start_message' else 'Maintenance Notice'} – @{esc(c['username'])}</b>\n\nCurrent:\n<blockquote>{esc(current)}</blockquote>\n\nSend the new text.",
                                   back_cancel(f"o:clone:{c['id']}"))
        return
    if action == "cmaint":
        c = await clone_or_none()
        if c and await need(PERM_CLONES, c["id"]):
            enabled = await db.clone_setting(c["id"], "maintenance_mode", "0") == "1"
            return await safe_edit(q, f"<b>🛠 Maintenance – @{esc(c['username'])}</b>\n\nStatus: <b>{'ON' if enabled else 'OFF'}</b>", kb([
                [("🔴 Disable" if enabled else "🟢 Enable", f"o:cmaintset:{c['id']}:{0 if enabled else 1}")],
                [("✏️ Edit Notice", f"o:cedit:{c['id']}:maintenance_message")], [("⬅️ Back", f"o:clone:{c['id']}")]]))
        return
    if action == "cmaintset":
        c = await clone_or_none()
        if c and await need(PERM_CLONES, c["id"]):
            new = "1" if args[1:2] == ["1"] else "0"
            await db.set_clone_setting(c["id"], "maintenance_mode", new)
            await db.audit(uid, "clone.maintenance", clone_id=c["id"], detail=f"mode={new}")
            return await safe_edit(q, f"✅ Maintenance mode for @{esc(c['username'])} is now <b>{'ON' if new == '1' else 'OFF'}</b>.", back_only(f"o:clone:{c['id']}"))
        return

    # ---------------- owner-only clone administration ----------------
    if action in ("cadmin", "cops", "crotate", "cdelask", "cdel", "copsdel"):
        if not actor.is_owner:
            return await q.answer("⛔️ Owner only.", show_alert=True)
        c = await clone_or_none()
        if not c:
            return
        if action == "cadmin":
            STATES.set("owner", uid, "change_admin", "id", {"clone_id": c["id"]}, panel=(q.message.chat_id, q.message.message_id))
            return await safe_edit(q, f"<b>🛡 Change Administrator – @{esc(c['username'])}</b>\n\nCurrent admin: <code>{c['admin_id']}</code>\n\nSend the numeric Telegram ID of the new administrator.", back_cancel(f"o:clone:{c['id']}"))
        if action == "cops":
            ops = await db.fetchall("SELECT user_id FROM clone_operators WHERE clone_id=?", (c["id"],))
            STATES.set("owner", uid, "add_operator", "id", {"clone_id": c["id"]}, panel=(q.message.chat_id, q.message.message_id))
            rows = [[(f"➖ Remove {o['user_id']}", f"o:copsdel:{c['id']}:{o['user_id']}")] for o in ops]
            rows.append([("⬅️ Back", f"o:clone:{c['id']}")])
            return await safe_edit(q, f"<b>➕ Operators – @{esc(c['username'])}</b>\n\nOperators share the clone admin's conversation access.\nSend a numeric Telegram ID to add an operator, or remove one below.", kb(rows))
        if action == "copsdel":
            target = arg_int(1)
            await db.execute("DELETE FROM clone_operators WHERE clone_id=? AND user_id=?", (c["id"], target))
            STATES.clear_user_everywhere(target)
            await db.audit(uid, "clone.operator_remove", clone_id=c["id"], detail=f"user={target}")
            return await safe_edit(q, f"✅ Operator <code>{target}</code> removed.", back_only(f"o:cops:{c['id']}"))
        if action == "crotate":
            STATES.set("owner", uid, "rotate_token", "token", {"clone_id": c["id"]}, panel=(q.message.chat_id, q.message.message_id))
            return await safe_edit(q, f"<b>🔑 Rotate Token – @{esc(c['username'])}</b>\n\nSend the new BotFather token for the <u>same</u> bot (ID <code>{c['bot_id']}</code>). The clone will be restarted with the new token after validation.", back_cancel(f"o:clone:{c['id']}"))
        if action == "cdelask":
            return await safe_edit(q, f"<b>🗑 Delete @{esc(c['username'])}?</b>\n\nThe clone will be stopped and unregistered, freeing one of {MAX_CLONES} slots.\n\n"
                                      "• Deleted: encrypted token, polling worker, admin assignment, settings.\n"
                                      "• Retained (archived): users, conversation history, broadcast records, statistics, logs.\n"
                                      "• Outstanding broadcast recipients of this clone will be marked failed.\n\nThis cannot be undone.",
                                   kb([[("✅ Yes, delete", f"o:cdel:{c['id']}"), ("❌ Cancel", f"o:clone:{c['id']}")]]))
        if action == "cdel":
            await safe_edit(q, "⏳ Deleting clone…", None)
            await MANAGER.remove_clone(c["id"])
            for bid in [r["broadcast_id"] for r in await db.fetchall("SELECT DISTINCT broadcast_id FROM broadcast_deliveries WHERE clone_id=? AND status='pending'", (c["id"],))]:
                for p in await db.fetchall("SELECT user_id FROM broadcast_deliveries WHERE broadcast_id=? AND clone_id=? AND status='pending'", (bid, c["id"])):
                    await _mark_delivery(bid, c["id"], p["user_id"], False, "clone deleted", 0)
            await db.execute("UPDATE clones SET status='DELETED', deleted_at=?, desired_running=0, token_enc='', token_fingerprint=?, updated_at=? WHERE id=?",
                             (utcnow(), f"deleted-{c['id']}-{secrets.token_hex(4)}", utcnow(), c["id"]))
            await db.execute("DELETE FROM clone_operators WHERE clone_id=?", (c["id"],))
            STATES.clear_user_everywhere(c["admin_id"])
            await db.audit(uid, "clone.delete", clone_id=c["id"], detail=f"@{c['username']}")
            return await safe_edit(q, f"✅ Clone @{esc(c['username'])} deleted. Registered clones: {await db.clone_count()}/{MAX_CLONES}.", back_only("o:clones:0"))

    # ---------------- conversations ----------------
    if action == "convs":
        if not (actor.has(PERM_CONVERSATIONS) or actor.role == "clone_admin"):
            return await q.answer("⛔️ Not authorized.", show_alert=True)
        clones = await visible_clones(actor)
        rows = [[("📋 All clones", "o:inbox:all:0:0"), ("🔴 Unanswered", "o:inbox:all:1:0")]]
        rows += [[(f"@{c['username']}", f"o:inbox:{c['id']}:0:0")] for c in clones[:20]]
        rows.append([("🔎 Find user", "o:findconv")])
        rows.append([("⬅️ Back", "o:home")])
        unread = await db.fetchval("SELECT COUNT(*) AS n FROM clone_users WHERE unread>0" + (f" AND clone_id IN ({','.join('?' for _ in actor.clone_ids)})" if actor.role == 'clone_admin' else ""),
                                   tuple(actor.clone_ids) if actor.role == "clone_admin" else ())
        return await safe_edit(q, f"<b>💬 Conversation Management</b>\n\nUnanswered conversations: <b>{fmt_int(unread)}</b>\n\nChoose a filter:", kb(rows))
    if action == "inbox":
        sel = args[0] if args else "all"
        unanswered = (arg_int(1) or 0) == 1
        page = arg_int(2) or 0
        clones = await visible_clones(actor)
        if sel != "all":
            clones = [c for c in clones if c["id"] == parse_int(sel)]
            if not clones:
                return await safe_edit(q, "Clone not found or not accessible.", back_only("o:convs"))
            if not actor.can_clone(clones[0]["id"], PERM_CONVERSATIONS):
                return await q.answer("⛔️ Not authorized.", show_alert=True)
        elif not (actor.has(PERM_CONVERSATIONS) or actor.role == "clone_admin"):
            return await q.answer("⛔️ Not authorized.", show_alert=True)
        text, markup = await inbox_view(clones, page, back="o:convs", filter_label="all clones" if sel == "all" else f"@{clones[0]['username']}", unanswered_only=unanswered)
        return await safe_edit(q, text, markup)
    if action == "findconv":
        if not (actor.has(PERM_CONVERSATIONS) or actor.role == "clone_admin"):
            return
        STATES.set("owner", uid, "find_conv", "query", {}, panel=(q.message.chat_id, q.message.message_id))
        return await safe_edit(q, "<b>🔎 Find Conversation</b>\n\nSend a Telegram user ID or @username. All accessible clones are searched.", back_cancel("o:convs"))
    if action == "conv":
        c = await clone_or_none()
        if not c or not actor.can_clone(c["id"], PERM_CONVERSATIONS):
            return
        text, markup = await conversation_view(c, arg_int(1), back=f"o:inbox:{c['id']}:0:0")
        return await safe_edit(q, text, markup)
    if action == "reply":
        c = await clone_or_none()
        if not c or not actor.can_clone(c["id"], PERM_CONVERSATIONS):
            return
        target = arg_int(1)
        STATES.set("owner", uid, "reply", "content", {"clone_id": c["id"], "user_id": target}, panel=(q.message.chat_id, q.message.message_id))
        return await safe_edit(q, f"<b>✍️ Reply to <code>{target}</code> via @{esc(c['username'])}</b>\n\nSend the message (text or media) to deliver.", back_cancel(f"o:conv:{c['id']}:{target}"))

    # ---------------- broadcasts ----------------
    if action == "bcstart":
        fixed = arg_int(0)
        if fixed is not None and not actor.can_clone(fixed, PERM_BROADCAST):
            return await q.answer("⛔️ Not authorized.", show_alert=True)
        if fixed is None and not (actor.has(PERM_BROADCAST) or actor.role == "clone_admin"):
            return await q.answer("⛔️ Not authorized.", show_alert=True)
        return await bc_start(ui, actor, fixed_clone=fixed)
    if action == "bchist":
        text, markup = await broadcast_history_view(actor, arg_int(0) or 0, arg_int(1))
        return await safe_edit(q, text, markup)
    if action == "bchistc":
        text, markup = await broadcast_history_view(actor, arg_int(1) or 0, arg_int(0))
        return await safe_edit(q, text, markup)
    if action in ("bcview", "bccancel", "bcfail", "bcresume"):
        bid = arg_int(0)
        b = await db.fetchone("SELECT * FROM broadcasts WHERE id=?", (bid,))
        if not b:
            return await safe_edit(q, "Broadcast not found.", back_only("o:bchist:0"))
        targets = await db.fetchall("SELECT * FROM broadcast_targets WHERE broadcast_id=?", (bid,))
        allowed = actor.has(PERM_BROADCAST) or b["created_by"] == uid or all(actor.can_clone(t["clone_id"], PERM_BROADCAST) for t in targets)
        if not allowed:
            return await q.answer("⛔️ Not authorized.", show_alert=True)
        if action == "bccancel":
            ok = await request_broadcast_cancel(bid, uid)
            await q.answer("Cancellation requested." if ok else "This broadcast is not running.", show_alert=True)
        elif action == "bcresume":
            ok, msg = await resume_broadcast(bid, uid)
            await q.answer(msg, show_alert=True)
            if ok:
                await db.execute("UPDATE broadcasts SET progress_chat_id=?, progress_message_id=? WHERE id=?", (q.message.chat_id, q.message.message_id, bid))
        elif action == "bcfail":
            fails = await db.fetchall("SELECT clone_id, user_id, error FROM broadcast_deliveries WHERE broadcast_id=? AND status='failed' ORDER BY delivered_at DESC LIMIT 15", (bid,))
            lines = [f"<b>❗ Failed deliveries – Broadcast #{bid}</b>", ""] + [f"clone {f['clone_id']} · <code>{f['user_id']}</code> · {esc((f['error'] or '')[:70])}" for f in fails] or ["No failures."]
            return await safe_edit(q, "\n".join(lines), kb([[("⬅️ Back", f"o:bcview:{bid}")]]))
        b = await db.fetchone("SELECT * FROM broadcasts WHERE id=?", (bid,))
        targets = await db.fetchall("SELECT * FROM broadcast_targets WHERE broadcast_id=?", (bid,))
        return await safe_edit(q, await broadcast_progress_text(b, targets), broadcast_progress_keyboard(b))
    if action.startswith("bc"):
        return await bc_callback(ui, actor, action, args, q)

    # ---------------- statistics ----------------
    if action == "stats":
        if not (actor.has(PERM_STATS) or actor.role == "clone_admin"):
            return await q.answer("⛔️ Not authorized.", show_alert=True)
        return await safe_edit(q, await global_stats_text(actor), kb([[("🔄 Refresh", "o:stats")], [("⬅️ Back", "o:home")]]))

    # ---------------- admin management (owner only) ----------------
    if action in ("admins", "madd", "mremove", "mperm", "mtoggle"):
        if not actor.is_owner:
            return await q.answer("⛔️ Owner only.", show_alert=True)
        if action == "admins":
            STATES.clear("owner", uid)
            text, markup = await admins_view()
            return await safe_edit(q, text, markup)
        if action in ("madd", "mremove"):
            STATES.set("owner", uid, action, "id", {}, panel=(q.message.chat_id, q.message.message_id))
            return await safe_edit(q, f"<b>{'➕ Add' if action == 'madd' else '➖ Remove'} Delegated Manager</b>\n\nSend the numeric Telegram user ID.", back_cancel("o:admins"))
        if action == "mperm":
            text, markup = await manager_perm_view(arg_int(0))
            return await safe_edit(q, text, markup)
        if action == "mtoggle":
            target, perm = arg_int(0), (args[1] if len(args) > 1 else "")
            perms = await db.manager_perms(target)
            if perms is None or perm not in ALL_PERMS:
                return await q.answer("Invalid.", show_alert=True)
            perms ^= {perm}
            await db.execute("UPDATE managers SET permissions=? WHERE user_id=?", (json.dumps(sorted(perms)), target))
            STATES.clear_user_everywhere(target)
            await db.audit(uid, "manager.permissions", detail=f"user={target} perms={sorted(perms)}")
            text, markup = await manager_perm_view(target)
            return await safe_edit(q, text, markup)

    # ---------------- settings ----------------
    if action in ("settings", "sedit", "stoggle"):
        if not await need(PERM_SETTINGS):
            return
        if action == "settings":
            STATES.clear("owner", uid)
            text, markup = await settings_view()
            return await safe_edit(q, text, markup)
        if action == "sedit":
            key = args[0] if args else ""
            if key not in {"default_start_message", "default_maintenance_message"}:
                return
            STATES.set("owner", uid, "edit_global", key, {"key": key}, panel=(q.message.chat_id, q.message.message_id))
            return await safe_edit(q, f"<b>✏️ Edit {esc(key.replace('_', ' '))}</b>\n\nCurrent:\n<blockquote>{esc(await db.setting(key))}</blockquote>\n\nSend the new text.", back_cancel("o:settings"))
        if action == "stoggle":
            key = args[0] if args else ""
            if key not in {"notify_owners_on_user_message", "forward_header"}:
                return
            new = "0" if await db.setting(key, "0") == "1" else "1"
            await db.set_setting(key, new)
            await db.audit(uid, "settings.toggle", detail=f"{key}={new}")
            text, markup = await settings_view()
            return await safe_edit(q, text, markup)

    # ---------------- diagnostics / logs ----------------
    if action == "diag":
        if await need(PERM_LOGS):
            return await safe_edit(q, await diagnostics_text(), kb([[("🔄 Refresh", "o:diag")], [("⬅️ Back", "o:home")]]))
        return
    if action == "logs":
        if await need(PERM_LOGS):
            text, markup = await logs_view(args[0] if args else "audit", arg_int(1) or 0)
            return await safe_edit(q, text, markup)
        return

    # ---------------- backup / restore ----------------
    if action in ("backup", "bkcreate", "bkrestore", "bkconfirm"):
        if not await need(PERM_BACKUP):
            return
        if action == "backup":
            STATES.clear("owner", uid)
            recent = await db.fetchall("SELECT filename, size_bytes, kind, created_at FROM backups ORDER BY id DESC LIMIT 5")
            lines = ["<b>💾 Backup and Restore</b>", "", f"Database: <b>{'PostgreSQL' if db.is_postgres else 'SQLite'}</b>", "", "<b>Recent backups</b>"]
            lines += [f"{short_time(r['created_at'])} · {esc(r['filename'])} · {r['size_bytes'] / 1024:.0f} KB ({esc(r['kind'])})" for r in recent] or ["None yet."]
            return await safe_edit(q, "\n".join(lines), kb([[("💾 Create Backup", "o:bkcreate")], [("♻️ Restore Backup", "o:bkrestore")], [("⬅️ Back", "o:home")]]))
        if action == "bkcreate":
            await safe_edit(q, "⏳ Creating a consistent backup…", None)
            try:
                path = await backup_database(uid, "manual")
                with path.open("rb") as f:
                    await context.bot.send_document(uid, document=f, caption="✅ Platform backup (tokens stay encrypted inside).")
                await db.audit(uid, "backup.create", detail=path.name)
                return await safe_edit(q, f"✅ Backup created and sent: <code>{esc(path.name)}</code>", back_only("o:backup"))
            except Exception as exc:
                await db.record_error("backup.create", exc)
                return await safe_edit(q, f"❌ Backup failed: {esc(redact(exc))}", back_only("o:backup"))
        if action == "bkrestore":
            if not actor.is_owner:
                return await q.answer("⛔️ Owner only.", show_alert=True)
            STATES.set("owner", uid, "restore_upload", "file", {}, panel=(q.message.chat_id, q.message.message_id))
            return await safe_edit(q, "<b>♻️ Restore Backup</b>\n\nUpload a backup ZIP created by this platform. It is validated first and a safety backup is taken before anything is replaced. All clones are stopped during the restore.", back_cancel("o:backup"))
        if action == "bkconfirm":
            st = STATES.get("owner", uid)
            path = (st or {}).get("data", {}).get("restore_path")
            if not actor.is_owner or not st or st.get("step") != "confirm" or not path or not Path(path).exists():
                return await safe_edit(q, "The uploaded backup is no longer available.", back_only("o:backup"))
            st["step"] = "restoring"
            await safe_edit(q, "⏳ Validating and restoring… clones are being stopped.", None)
            try:
                safety = await restore_database(Path(path), uid)
                STATES.clear("owner", uid)
                await db.audit(uid, "backup.restore", detail=f"safety={safety.name}")
                results = await MANAGER.start_all_clones()
                summary = "\n".join(f"{'✅' if ok else '❌'} {esc(n)}: {esc(m)}" for n, ok, m in results) or "No clones to start."
                return await safe_edit(q, f"✅ Restore completed. Safety backup: <code>{esc(safety.name)}</code>\n\nClones restarted:\n{summary}", back_only("o:home"))
            except Exception as exc:
                await db.record_error("backup.restore", exc)
                STATES.clear("owner", uid)
                await MANAGER.start_all_clones()
                return await safe_edit(q, f"❌ Restore failed, current database kept: {esc(redact(exc))}", back_only("o:backup"))
    await q.answer("This button is no longer valid.", show_alert=True)


# ---- clone creation finalization ---------------------------------------------------------


async def render_create_confirm(ui: UICtx, st: dict):
    d = st["data"]
    count = await db.clone_count()
    st["step"] = "confirm"
    await ui.render(
        "<b>🚀 Confirm Clone Bot</b>\n\n"
        f"🤖 Name: {esc(d['bot_name'])}\n🔗 Username: @{esc(d['bot_username'])}\n🆔 Bot ID: <code>{d['bot_id']}</code>\n"
        f"🛡 Assigned Admin: <code>{d['admin_id']}</code>\n📊 Registration: {count + 1}/{MAX_CLONES}\nInitial status: PENDING → LIVE\n\n"
        "Do you want to register and start this bot?",
        kb([[("✅ Confirm & Start", "o:createconfirm")], [("⬅️ Back", "o:createback:admin"), ("❌ Cancel", "o:cancel")]]),
    )


async def finalize_clone_creation(ui: UICtx, actor: Actor, st: dict):
    d = st["data"]
    await ui.render("⏳ Registering clone…", None)
    try:
        async with db.transaction() as tx:
            count = await tx.fetchval("SELECT COUNT(*) AS n FROM clones WHERE deleted_at IS NULL")
            if int(count or 0) >= MAX_CLONES:
                raise ValueError(f"The platform limit of {MAX_CLONES} clones is reached.")
            dup = await tx.fetchone("SELECT id FROM clones WHERE (token_fingerprint=? OR bot_id=?) AND deleted_at IS NULL", (d["fingerprint"], d["bot_id"]))
            if dup:
                raise ValueError("This bot is already registered as a clone.")
            now = utcnow()
            clone_id = await tx.fetchval(
                """INSERT INTO clones(bot_id,username,display_name,token_enc,token_fingerprint,admin_id,status,desired_running,created_by,created_at,updated_at)
                VALUES(?,?,?,?,?,?,?,?,?,?,?) RETURNING id""",
                (d["bot_id"], d["bot_username"], d["bot_name"], d["token_enc"], d["fingerprint"], d["admin_id"], "PENDING", 1, actor.user_id, now, now),
            )
    except INTEGRITY_ERRORS:
        STATES.clear("owner", ui.user_id)
        return await ui.render("❌ This bot token or bot ID is already registered.", back_only("o:home"))
    except ValueError as exc:
        STATES.clear("owner", ui.user_id)
        return await ui.render(f"❌ {esc(exc)}", back_only("o:home"))
    STATES.clear("owner", ui.user_id)
    await db.audit(actor.user_id, "clone.create", clone_id=clone_id, detail=f"@{d['bot_username']} admin={d['admin_id']}")
    ok, msg = await MANAGER.start_clone(int(clone_id), actor.user_id)
    c = await db.clone(int(clone_id))
    text, markup = await clone_detail_view(actor, c)
    head = f"✅ Clone registered and started ({await db.clone_count()}/{MAX_CLONES})." if ok else f"⚠️ Clone registered but failed to start: {esc(msg)}"
    await ui.render(f"{head}\n\n{text}", markup)


# ---- text / media input while a wizard is active ------------------------------------------------


async def handle_state_input(ui: UICtx, actor: Actor, st: dict, message: Message) -> bool:
    flow = st["flow"]
    text = (message.text or "").strip()
    d = st["data"]
    if flow == "broadcast":
        return await bc_text_input(ui, actor, st, message)
    if flow == "create":
        if not actor.is_owner:
            STATES.clear(ui.scope, ui.user_id)
            return True
        if st["step"] == "token":
            await try_delete(ui.bot, ui.chat_id, message.message_id)  # never leave the token visible in chat
            if not validate_token_format(text):
                await ui.render("⚠️ That does not look like a valid BotFather token. Please send the token again.", kb([[("❌ Cancel", "o:cancel")]]))
                return True
            if text == TOKEN:
                await ui.render("⚠️ That is the Owner Bot's own token. Send the token of a different bot.", kb([[("❌ Cancel", "o:cancel")]]))
                return True
            fp = TokenVault.fingerprint(text)
            if await db.fetchone("SELECT id FROM clones WHERE token_fingerprint=? AND deleted_at IS NULL", (fp,)):
                await ui.render("⚠️ This token is already registered to another clone.", kb([[("❌ Cancel", "o:cancel")]]))
                return True
            if await db.clone_count() >= MAX_CLONES:
                STATES.clear(ui.scope, ui.user_id)
                await ui.render(f"🚫 The platform limit of {MAX_CLONES} clones is reached.", back_only("o:home"))
                return True
            st["step"] = "validating"
            await ui.render("⏳ Validating token with Telegram…", None)
            me, err = await validate_bot_token(text)
            if err or me is None or not me.is_bot:
                st["step"] = "token"
                await ui.render(f"❌ {esc(err or 'The token does not belong to a bot.')}\n\nSend another token.", kb([[("❌ Cancel", "o:cancel")]]))
                return True
            if await db.fetchone("SELECT id FROM clones WHERE bot_id=? AND deleted_at IS NULL", (me.id,)):
                st["step"] = "token"
                await ui.render("⚠️ This bot is already registered as a clone (same bot ID).", kb([[("❌ Cancel", "o:cancel")]]))
                return True
            d.update({"token_enc": VAULT.encrypt(text), "fingerprint": fp, "bot_id": me.id, "bot_username": me.username or str(me.id), "bot_name": me.first_name or me.username or "Bot"})
            st["step"] = "admin"
            await ui.render("<b>✅ Bot Token Received</b>\n\nYour bot has been authenticated successfully.\n\nNow please send the Telegram numeric user ID of the administrator who will manage this clone.",
                            back_cancel("o:createback:token"))
            return True
        if st["step"] == "admin":
            admin_id = parse_int(text)
            if admin_id is None or admin_id <= 0:
                await ui.render("⚠️ Send a numeric Telegram user ID (not a username). You can find it with @userinfobot.", back_cancel("o:createback:token"))
                return True
            note = ""
            if await db.is_owner(admin_id):
                note = "ℹ️ This ID is a platform owner; owners already control every clone.\n"
            elif await db.manager_perms(admin_id) is not None:
                note = "ℹ️ This ID is a delegated manager; it will additionally become this clone's administrator.\n"
            d["admin_id"] = admin_id
            if note:
                d["note"] = note
            await render_create_confirm(ui, st)
            return True
        await ui.bot.send_message(ui.chat_id, "Use the buttons to continue the clone creation.")
        return True
    if flow == "rotate_token":
        if not actor.is_owner:
            STATES.clear(ui.scope, ui.user_id)
            return True
        await try_delete(ui.bot, ui.chat_id, message.message_id)
        c = await db.clone(d["clone_id"])
        if not c:
            STATES.clear(ui.scope, ui.user_id)
            return True
        if not validate_token_format(text) or text == TOKEN:
            await ui.render("⚠️ Invalid token. Send the new token for this bot.", back_cancel(f"o:clone:{c['id']}"))
            return True
        await ui.render("⏳ Validating new token…", None)
        me, err = await validate_bot_token(text)
        if err or me is None:
            await ui.render(f"❌ {esc(err or 'Validation failed.')}", back_cancel(f"o:clone:{c['id']}"))
            return True
        if me.id != c["bot_id"]:
            await ui.render(f"❌ This token belongs to @{esc(me.username)} (ID {me.id}), not to the registered bot (ID {c['bot_id']}).", back_cancel(f"o:clone:{c['id']}"))
            return True
        await db.execute("UPDATE clones SET token_enc=?, token_fingerprint=?, updated_at=? WHERE id=?", (VAULT.encrypt(text), TokenVault.fingerprint(text), utcnow(), c["id"]))
        STATES.clear(ui.scope, ui.user_id)
        await db.audit(actor.user_id, "clone.rotate_token", clone_id=c["id"])
        ok, msg = await MANAGER.restart_clone(c["id"], actor.user_id)
        await ui.render(f"{'✅' if ok else '⚠️'} Token rotated. {esc(msg)}", back_only(f"o:clone:{c['id']}"))
        return True
    if flow == "change_admin":
        if not actor.is_owner:
            STATES.clear(ui.scope, ui.user_id)
            return True
        c = await db.clone(d["clone_id"])
        new_admin = parse_int(text)
        if not c:
            STATES.clear(ui.scope, ui.user_id)
            return True
        if new_admin is None or new_admin <= 0:
            await ui.render("⚠️ Send a numeric Telegram user ID.", back_cancel(f"o:clone:{c['id']}"))
            return True
        old = c["admin_id"]
        async with db.transaction() as tx:
            await tx.execute("UPDATE clones SET admin_id=?, updated_at=? WHERE id=?", (new_admin, utcnow(), c["id"]))
            await tx.execute("DELETE FROM clone_operators WHERE clone_id=? AND user_id=?", (c["id"], new_admin))
        STATES.clear_user_everywhere(old)
        STATES.clear(ui.scope, ui.user_id)
        await db.audit(actor.user_id, "clone.change_admin", clone_id=c["id"], detail=f"{old} -> {new_admin}")
        await ui.render(f"✅ Administrator of @{esc(c['username'])} changed from <code>{old}</code> to <code>{new_admin}</code>.", back_only(f"o:clone:{c['id']}"))
        return True
    if flow == "add_operator":
        if not actor.is_owner:
            STATES.clear(ui.scope, ui.user_id)
            return True
        target = parse_int(text)
        c = await db.clone(d["clone_id"])
        if c and target and target > 0:
            await db.execute("INSERT INTO clone_operators(clone_id,user_id,added_at,added_by) VALUES(?,?,?,?) ON CONFLICT(clone_id,user_id) DO NOTHING", (c["id"], target, utcnow(), actor.user_id))
            await db.audit(actor.user_id, "clone.operator_add", clone_id=c["id"], detail=f"user={target}")
            await ui.render(f"✅ Operator <code>{target}</code> added to @{esc(c['username'])}.", back_only(f"o:cops:{c['id']}"))
        else:
            await ui.bot.send_message(ui.chat_id, "⚠️ Send a numeric Telegram user ID.")
        return True
    if flow in ("madd", "mremove"):
        if not actor.is_owner:
            STATES.clear(ui.scope, ui.user_id)
            return True
        target = parse_int(text)
        if target is None:
            await ui.bot.send_message(ui.chat_id, "⚠️ Send a numeric Telegram user ID.")
            return True
        if await db.is_owner(target):
            await ui.render("⚠️ That ID is a platform owner. Owners cannot be added or removed here.", back_only("o:admins"))
            STATES.clear(ui.scope, ui.user_id)
            return True
        if flow == "madd":
            await db.execute("INSERT INTO managers(user_id,permissions,added_at,added_by) VALUES(?,?,?,?) ON CONFLICT(user_id) DO NOTHING",
                             (target, json.dumps(sorted(DEFAULT_MANAGER_PERMS)), utcnow(), actor.user_id))
            await db.audit(actor.user_id, "manager.add", detail=f"user={target}")
            STATES.clear(ui.scope, ui.user_id)
            text_out, markup = await manager_perm_view(target)
            await ui.render(f"✅ Manager <code>{target}</code> added.\n\n{text_out}", markup)
        else:
            st["step"] = "confirm"
            d["target"] = target
            await ui.render(f"Remove manager <code>{target}</code>?", kb([[("✅ Remove", f"o:mremovedo:{target}"), ("❌ Cancel", "o:admins")]]))
        return True
    if flow == "edit_setting":
        if not text:
            await ui.bot.send_message(ui.chat_id, "Send a text message.")
            return True
        c = await db.clone(d["clone_id"])
        if not c or not actor.can_clone(c["id"], PERM_CLONES):
            STATES.clear(ui.scope, ui.user_id)
            return True
        await db.set_clone_setting(c["id"], d["key"], text[:4000])
        await db.audit(actor.user_id, "clone.setting", clone_id=c["id"], detail=d["key"])
        STATES.clear(ui.scope, ui.user_id)
        back = f"o:clone:{c['id']}" if ui.scope == "owner" else f"c:home:{c['id']}"
        await ui.render("✅ Message updated.", back_only(back))
        return True
    if flow == "edit_global":
        if not actor.has(PERM_SETTINGS):
            STATES.clear(ui.scope, ui.user_id)
            return True
        if not text:
            await ui.bot.send_message(ui.chat_id, "Send a text message.")
            return True
        await db.set_setting(d["key"], text[:4000])
        await db.audit(actor.user_id, "settings.edit", detail=d["key"])
        STATES.clear(ui.scope, ui.user_id)
        await ui.render("✅ Setting updated.", back_only("o:settings"))
        return True
    if flow == "user_search":
        clone_id = d.get("clone_id", ui.scope if ui.scope != "owner" else None)
        c = await db.clone(clone_id) if clone_id is not None else None
        if not c or not actor.can_clone(c["id"], PERM_CONVERSATIONS):
            STATES.clear(ui.scope, ui.user_id)
            return True
        uid = await _lookup_user(c["id"], text)
        if uid is None:
            await ui.bot.send_message(ui.chat_id, "User not found. Send an exact ID or @username.")
            return True
        STATES.clear(ui.scope, ui.user_id)
        u = await db.fetchone("SELECT is_banned FROM clone_users WHERE clone_id=? AND user_id=?", (c["id"], uid))
        back = f"o:cusers:{c['id']}" if ui.scope == "owner" else f"c:users:{c['id']}"
        await ui.render(await user_detail_text(c["id"], uid), user_detail_keyboard(c["id"], uid, bool(u["is_banned"]), back, ui.prefix))
        return True
    if flow == "find_conv":
        clones = await visible_clones(actor)
        hits = []
        for c in clones:
            uid = await _lookup_user(c["id"], text)
            if uid is not None:
                hits.append((c, uid))
        if not hits:
            await ui.bot.send_message(ui.chat_id, "No conversation found for that user.")
            return True
        STATES.clear(ui.scope, ui.user_id)
        rows = [[(f"@{c['username']} · {uid}", f"o:conv:{c['id']}:{uid}")] for c, uid in hits[:20]]
        rows.append([("⬅️ Back", "o:convs")])
        await ui.render(f"<b>🔎 Results</b>\n\nFound in {len(hits)} clone(s):", kb(rows))
        return True
    if flow == "reply":
        c = await db.clone(d["clone_id"])
        if not c or not actor.can_clone(c["id"], PERM_CONVERSATIONS):
            STATES.clear(ui.scope, ui.user_id)
            return True
        ok, msg = await deliver_admin_reply(c, actor.user_id, ui.bot, message, d["user_id"])
        STATES.clear(ui.scope, ui.user_id)
        await message.reply_text(f"{'✅' if ok else '❌'} {msg}")
        back = f"o:conv:{c['id']}:{d['user_id']}" if ui.scope == "owner" else f"c:conv:{c['id']}:{d['user_id']}"
        text_out, markup = await conversation_view(c, d["user_id"], back=back if ui.scope == "owner" else f"c:inbox:{c['id']}:0", prefix=ui.prefix)
        await ui.render(text_out, markup)
        return True
    if flow == "restore_upload":
        if not actor.is_owner:
            STATES.clear(ui.scope, ui.user_id)
            return True
        doc = message.document
        if not doc or not (doc.file_name or "").lower().endswith(".zip"):
            await ui.bot.send_message(ui.chat_id, "Upload the backup ZIP file.")
            return True
        if doc.file_size and doc.file_size > MAX_MEDIA_BYTES:
            await ui.bot.send_message(ui.chat_id, "The archive is larger than 20 MB and cannot be downloaded through the Bot API.")
            return True
        BACKUP_DIR.mkdir(parents=True, exist_ok=True)
        target = BACKUP_DIR / f"upload_{uuid.uuid4().hex}.zip"
        tg_file = await ui.bot.get_file(doc.file_id)
        await tg_file.download_to_drive(custom_path=str(target))
        try:
            info = validate_backup_archive(target)
        except Exception as exc:
            target.unlink(missing_ok=True)
            await ui.render(f"❌ Invalid backup: {esc(redact(exc))}", back_only("o:backup"))
            STATES.clear(ui.scope, ui.user_id)
            return True
        d["restore_path"] = str(target)
        st["step"] = "confirm"
        await ui.render(f"<b>♻️ Confirm Restore</b>\n\nBackup created: {short_time(info['created_at'])}\nSchema: {info['schema']} · Tables: {info['tables']} · Rows: {fmt_int(info['rows'])}\n\n"
                        "All clones will be stopped, a safety backup will be created, and the current data replaced. Continue?",
                        kb([[("✅ Restore", "o:bkconfirm"), ("❌ Cancel", "o:cancel")]]))
        return True
    return False


async def _lookup_user(clone_id: int, text: str) -> Optional[int]:
    text = (text or "").strip()
    if text.startswith("@"):
        row = await db.fetchone("SELECT user_id FROM clone_users WHERE clone_id=? AND lower(username)=lower(?)", (clone_id, text[1:]))
        return row["user_id"] if row else None
    uid = parse_int(text)
    if uid is None:
        return None
    row = await db.fetchone("SELECT user_id FROM clone_users WHERE clone_id=? AND user_id=?", (clone_id, uid))
    return row["user_id"] if row else None


async def owner_message(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Owner Bot: wizard input, or an admin reply to a relayed user message."""
    message = update.effective_message
    user = update.effective_user
    if not message or not user or update.effective_chat.type != "private":
        return
    actor = await resolve_actor(user.id)
    if actor is None:
        return  # silent
    st = STATES.get("owner", user.id)
    if st:
        ui = owner_ui(update, context, (st.get("panel") or (None, None))[1])
        if await handle_state_input(ui, actor, st, message):
            return
    if message.reply_to_message:
        mapping = await db.fetchone("SELECT * FROM forward_map WHERE admin_chat_id=? AND admin_message_id=?",
                                    (message.chat_id, message.reply_to_message.message_id))
        if not mapping:
            await message.reply_text("ℹ️ That message is not linked to a user conversation. Reply directly to a relayed user message, or open the conversation from the panel.")
            return
        clone = await db.clone(mapping["clone_id"])
        if not clone:
            await message.reply_text("⚠️ The clone that received this message no longer exists.")
            return
        if not actor.can_clone(clone["id"], PERM_CONVERSATIONS):
            await message.reply_text("⛔️ You are not authorized for this clone.")
            return
        ok, msg = await deliver_admin_reply(clone, user.id, context.bot, message, mapping["user_id"], mapping["user_message_id"])
        await message.reply_text(f"{'✅' if ok else '❌'} {msg}")
        return
    await message.reply_text("Use /start to open the panel.", reply_markup=owner_home_keyboard(actor))


async def owner_mremovedo(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    actor = await resolve_actor(q.from_user.id)
    if not actor or not actor.is_owner:
        await q.answer()
        return
    await q.answer()
    target = parse_int(q.data.split(":")[2])
    changed = await db.execute("DELETE FROM managers WHERE user_id=?", (target,))
    STATES.clear_user_everywhere(target)
    STATES.clear("owner", actor.user_id)
    await db.audit(actor.user_id, "manager.remove", "ok" if changed else "not_found", detail=f"user={target}")
    await safe_edit(q, f"{'✅ Manager removed.' if changed else 'ℹ️ That ID was not a manager.'}", back_only("o:admins"))


async def owner_error_handler(update: object, context: ContextTypes.DEFAULT_TYPE):
    err = context.error
    if isinstance(err, Conflict):
        logger.critical("Owner Bot polling conflict: another process is using BOT_TOKEN.")
        return
    if isinstance(err, (NetworkError, TimedOut)):
        logger.warning("Owner Bot network issue: %s", redact(err))
        return
    logger.error("Owner Bot handler error: %s", redact(err))
    await db.record_error("owner.handler", err)
    if isinstance(update, Update) and update.callback_query:
        try:
            await update.callback_query.answer("⚠️ Something went wrong. The error has been logged.", show_alert=True)
        except TelegramError:
            pass

# --------------------------------------------------------------------------------------
# Backup, restore, health server, startup
# --------------------------------------------------------------------------------------


def _serialize_value(value: Any) -> Any:
    if isinstance(value, datetime):
        return value.isoformat()
    return value


async def backup_database(actor_id: Optional[int] = None, kind: str = "manual") -> Path:
    """Create a portable JSON backup archive of every platform table (works for SQLite and PostgreSQL)."""
    BACKUP_DIR.mkdir(parents=True, exist_ok=True)
    stamp = now_dt().strftime("%Y%m%d_%H%M%S")
    archive = BACKUP_DIR / f"platform_backup_{stamp}.zip"
    data: dict[str, Any] = {"manifest": {
        "created_at": utcnow(), "schema": SCHEMA_VERSION, "version": APP_VERSION,
        "database": "postgresql" if db.is_postgres else "sqlite", "tables": BACKUP_TABLES,
    }}
    total_rows = 0
    for table in BACKUP_TABLES:
        try:
            rows = await db.fetchall(f"SELECT * FROM {table}")
        except Exception as exc:
            logger.warning("Backup: could not read %s: %s", table, redact(exc))
            rows = []
        data[table] = [{k: _serialize_value(v) for k, v in row.items()} for row in rows]
        total_rows += len(rows)
    data["manifest"]["rows"] = total_rows
    payload = json.dumps(data, ensure_ascii=False).encode("utf-8")
    manifest = json.dumps(data["manifest"], indent=2).encode("utf-8")
    with zipfile.ZipFile(archive, "w", compression=zipfile.ZIP_DEFLATED) as zf:
        zf.writestr("manifest.json", manifest)
        zf.writestr("data.json", payload)
    try:
        await db.execute(
            "INSERT INTO backups(filename,size_bytes,kind,created_by,created_at) VALUES(?,?,?,?,?)",
            (archive.name, archive.stat().st_size, kind, actor_id, utcnow()),
        )
    except Exception:
        logger.exception("Could not record backup metadata")
    if not db.is_postgres:
        # keep a raw SQLite copy alongside the JSON for fast, exact recovery
        try:
            shutil.copy2(DATABASE_PATH, BACKUP_DIR / f"sqlite_{stamp}.db")
        except Exception as exc:
            logger.warning("Could not copy SQLite file: %s", redact(exc))
    logger.info("Backup created: %s (%s rows)", archive.name, total_rows)
    return archive


def validate_backup_archive(path: Path) -> dict:
    """Validate structure without touching the live database. Raises ValueError when unsafe."""
    if not zipfile.is_zipfile(path):
        raise ValueError("The uploaded file is not a ZIP archive.")
    with zipfile.ZipFile(path) as zf:
        names = zf.namelist()
        for name in names:
            if Path(name).name != name or name.startswith("/") or ".." in name:
                raise ValueError("The archive contains unsafe paths.")
        if "manifest.json" not in names:
            raise ValueError("manifest.json is missing from the archive.")
        manifest = json.loads(zf.read("manifest.json"))
        if not isinstance(manifest, dict):
            raise ValueError("The manifest is malformed.")
        if "data.json" in names:
            data = json.loads(zf.read("data.json"))
            tables = {k for k in data if k != "manifest"}
            rows = sum(len(v) for k, v in data.items() if k != "manifest" and isinstance(v, list))
            missing = {"clones", "clone_users", "owners"} - tables
            if missing:
                raise ValueError(f"The backup is incomplete (missing tables: {', '.join(sorted(missing))}).")
        else:  # legacy single-bot archive
            db_name = manifest.get("database")
            if not db_name or db_name not in names or "manifest.json" not in names:
                raise ValueError("Legacy archive manifest is invalid.")
            temp = BACKUP_DIR / f"check_{uuid.uuid4().hex}.db"
            try:
                with zipfile.ZipFile(path) as zf2:
                    zf2.extract(db_name, BACKUP_DIR)
                extracted = BACKUP_DIR / db_name
                shutil.move(str(extracted), str(temp))
                conn = sqlite3.connect(temp)
                try:
                    integrity = conn.execute("PRAGMA integrity_check").fetchone()[0]
                    if integrity != "ok":
                        raise ValueError("The SQLite database inside the archive is corrupt.")
                    tables = {r[0] for r in conn.execute("SELECT name FROM sqlite_master WHERE type='table'")}
                    rows = conn.execute("SELECT COUNT(*) FROM users").fetchone()[0] if "users" in tables else 0
                finally:
                    conn.close()
            finally:
                temp.unlink(missing_ok=True)
            manifest["tables"] = sorted(tables) if isinstance(tables, set) else tables
            manifest["legacy"] = True
        return {
            "created_at": manifest.get("created_at", "unknown"),
            "schema": manifest.get("schema", "?"),
            "tables": len(manifest.get("tables") or []),
            "rows": manifest.get("rows", rows),
            "legacy": bool(manifest.get("legacy")),
        }


async def restore_database(archive_path: Path, actor_id: Optional[int] = None) -> Path:
    """Validate, take a safety backup, then replace the data. Raises before touching anything on failure."""
    info = validate_backup_archive(archive_path)
    if info.get("legacy"):
        raise ValueError(
            "This archive is from the single-bot design and cannot be restored into the multi-clone schema. "
            "Import it manually if needed; the current database was left untouched."
        )
    with zipfile.ZipFile(archive_path) as zf:
        data = json.loads(zf.read("data.json"))
    safety = await backup_database(actor_id, "pre-restore")
    await MANAGER.shutdown()
    try:
        for table in BACKUP_TABLES:
            await db.execute(f"DELETE FROM {table}")
        async with db.transaction() as tx:
            for table in BACKUP_TABLES:
                rows = data.get(table) or []
                for row in rows:
                    if not isinstance(row, dict) or not row:
                        continue
                    cols = list(row.keys())
                    placeholders = ",".join("?" for _ in cols)
                    await tx.execute(f"INSERT INTO {table}({','.join(cols)}) VALUES({placeholders})", tuple(row[c] for c in cols))
        await db.execute("UPDATE clones SET status='STOPPED', desired_running=1, updated_at=?", (utcnow(),))
    except Exception:
        logger.exception("Restore failed mid-way; restoring the safety backup")
        with zipfile.ZipFile(safety) as zf:
            original = json.loads(zf.read("data.json"))
        for table in BACKUP_TABLES:
            await db.execute(f"DELETE FROM {table}")
            async with db.transaction() as tx:
                for row in original.get(table) or []:
                    cols = list(row.keys())
                    await tx.execute(f"INSERT INTO {table}({','.join(cols)}) VALUES({','.join('?' for _ in cols)})", tuple(row[c] for c in cols))
        raise ValueError("The restore failed; the database was rolled back to the safety backup.")
    logger.info("Restore completed from %s", archive_path.name)
    return safety


# --------------------------------------------------------------------------------------
# Render-compatible HTTP health server
# --------------------------------------------------------------------------------------


def health_payload(full: bool = False) -> tuple[int, dict]:
    counts = MANAGER.status_counts() if MANAGER else {}
    ready = bool(MANAGER and MANAGER.ready and db.ready)
    body = {
        "status": "ok" if ready else "starting",
        "service": "owner-bot-platform",
        "version": APP_VERSION,
        "uptime_seconds": round(time.monotonic() - START_MONOTONIC, 1),
        "ready": ready,
        "clones": {"registered": sum(counts.values()), "max": MAX_CLONES, "live": counts.get("LIVE", 0)},
    }
    if full:
        body["clones"]["by_status"] = counts
        body["database"] = {"backend": "postgresql" if db.is_postgres else "sqlite", "connected": db.ready}
        body["owner_bot"] = {"polling": bool(MANAGER and MANAGER.owner_app and MANAGER.owner_app.updater and MANAGER.owner_app.updater.running)}
    return (200 if ready else 503), body


class HealthHandler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"

    def _respond(self, status: int, payload: dict):
        data = json.dumps(payload).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(data)

    def do_GET(self):
        path = urlparse(self.path).path.rstrip("/") or "/"
        LAST_HEALTH_OK["at"] = utcnow()
        if path in ("/healthz", "/health", "/readyz", "/ready"):
            status, body = health_payload(full=True)
            return self._respond(status, body)
        if path == "/":
            status, body = health_payload(full=False)
            return self._respond(status, body)
        return self._respond(404, {"status": "not_found"})

    def do_HEAD(self):
        self.do_GET()

    def log_message(self, fmt, *args):
        logger.debug("health: " + fmt, *args)


def start_health_server() -> ThreadingHTTPServer:
    server = ThreadingHTTPServer((WEB_HOST, WEB_PORT), HealthHandler)
    server.daemon_threads = True
    threading.Thread(target=server.serve_forever, name="health-server", daemon=True).start()
    logger.info("Health server listening on %s:%s", WEB_HOST, WEB_PORT)
    return server


# --------------------------------------------------------------------------------------
# Application assembly
# --------------------------------------------------------------------------------------


def build_owner_app() -> Application:
    app = (
        ApplicationBuilder()
        .token(TOKEN)
        .request(build_request())
        .get_updates_request(build_request())
        .rate_limiter(AIORateLimiter(max_retries=2))
        .concurrent_updates(16)
        .build()
    )
    app.add_handler(CommandHandler(["start"], owner_start))
    app.add_handler(CallbackQueryHandler(owner_mremovedo, pattern=r"^o:mremovedo:"))
    app.add_handler(CallbackQueryHandler(owner_callback, pattern=r"^o:"))
    app.add_handler(MessageHandler(filters.ChatType.PRIVATE, owner_message))
    app.add_error_handler(owner_error_handler)
    return app


def fail_fast_checks() -> list:
    problems = []
    if not TOKEN:
        problems.append("BOT_TOKEN is not set: the Owner Bot cannot start.")
    if not ENCRYPTION_KEY:
        problems.append(
            "ENCRYPTION_KEY is not set: clone tokens cannot be encrypted at rest.\n"
            "    Generate one with: python -c \"from cryptography.fernet import Fernet; print(Fernet.generate_key().decode())\""
        )
    if not INITIAL_OWNER_IDS:
        problems.append("OWNER_IDS is not set: nobody would be able to reach the Owner Panel.")
    if not db.is_postgres:
        container = Path("/.dockerenv").exists() or bool(os.environ.get("RENDER"))
        on_disk = str(DATABASE_PATH).startswith("/var/")
        if container and not on_disk and not ALLOW_EPHEMERAL_SQLITE:
            problems.append(
                f"SQLite is configured at {DATABASE_PATH}, which is likely an ephemeral container filesystem.\n"
                "    Set DATABASE_URL (PostgreSQL) or point DATABASE_PATH at a mounted persistent disk.\n"
                "    Set ALLOW_EPHEMERAL_SQLITE=1 to accept data loss on redeploy."
            )
    if db.is_postgres and asyncpg is None:
        problems.append("DATABASE_URL is set but asyncpg is not installed.")
    return problems


async def async_main(stop_event: asyncio.Event):
    global MANAGER, OWNER_BOT_USERNAME
    await db.open()
    logger.info("Database ready (%s)", "PostgreSQL" if db.is_postgres else f"SQLite at {DATABASE_PATH}")
    await recover_broadcasts_on_startup()
    MANAGER = BotManager()
    MANAGER.owner_app = build_owner_app()
    await MANAGER.owner_app.initialize()
    try:
        me = await MANAGER.owner_app.bot.get_me()
        OWNER_BOT_USERNAME["value"] = me.username or ""
        logger.info("Owner Bot online: @%s", me.username)
    except TelegramError as exc:
        logger.warning("Could not resolve the Owner Bot identity: %s", redact(exc))
    await MANAGER.owner_app.start()
    await MANAGER.owner_app.updater.start_polling(allowed_updates=["message", "callback_query", "edited_message"],
                                                  drop_pending_updates=False)
    MANAGER.ready = True
    results = await MANAGER.start_all_clones()
    for name, ok, msg in results:
        logger.info("Clone %s: %s (%s)", name, "started" if ok else "FAILED", msg)
    await notify_owners(
        f"✅ <b>Platform online</b>\nVersion {APP_VERSION} · {await db.clone_count()}/{MAX_CLONES} clones registered\n"
        f"Serving {len(results)} clone start attempt(s) from the last boot."
    )
    sweeper = asyncio.create_task(_housekeeping(), name="housekeeping")
    await stop_event.wait()
    sweeper.cancel()
    logger.info("Shutdown requested; stopping clones and services")
    await MANAGER.shutdown()
    for bid, task in list(BROADCAST_TASKS.items()):
        try:
            await db.execute("UPDATE broadcasts SET status='interrupted' WHERE id=? AND status IN ('running','queued','cancelling')", (bid,))
            await _render_progress(bid, final=True)
        except Exception:
            logger.exception("Could not mark broadcast %s interrupted", bid)
    try:
        await MANAGER.owner_app.updater.stop()
        await MANAGER.owner_app.stop()
        await MANAGER.owner_app.shutdown()
    except Exception as exc:
        logger.warning("Owner Bot shutdown issue: %s", redact(exc))
    await db.close()


async def _housekeeping():
    while True:
        try:
            await asyncio.sleep(300)
            STATES.sweep()
            await db.cleanup()
            for bid, task in list(BROADCAST_TASKS.items()):
                if task.done():
                    BROADCAST_TASKS.pop(bid, None)
        except asyncio.CancelledError:
            return
        except Exception:
            logger.exception("Housekeeping error")


def main():
    problems = fail_fast_checks()
    if problems:
        for p in problems:
            logger.error("CONFIGURATION ERROR: %s", p)
        raise SystemExit("Configuration is invalid; nothing was started. Fix the errors above and redeploy.")
    global VAULT
    try:
        VAULT = TokenVault(ENCRYPTION_KEY)
    except RuntimeError as exc:
        raise SystemExit(str(exc))
    health_server = start_health_server()
    loop = asyncio.new_event_loop()
    asyncio.set_event_loop(loop)
    stop_event = asyncio.Event()
    if threading.current_thread() is threading.main_thread():
        for sig in (signal.SIGINT, signal.SIGTERM):
            try:
                loop.add_signal_handler(sig, stop_event.set)
            except (NotImplementedError, RuntimeError):
                signal.signal(sig, lambda *_: loop.call_soon_threadsafe(stop_event.set))
    try:
        loop.run_until_complete(async_main(stop_event))
    except KeyboardInterrupt:
        stop_event.set()
        loop.run_until_complete(asyncio.sleep(1))
    finally:
        try:
            pending = [t for t in asyncio.all_tasks(loop) if not t.done()]
            for t in pending:
                t.cancel()
            if pending:
                loop.run_until_complete(asyncio.gather(*pending, return_exceptions=True))
        finally:
            loop.close()
            health_server.shutdown()
            health_server.server_close()
    logger.info("Shutdown complete")


if __name__ == "__main__":
    main()

