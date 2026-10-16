"""
app.py — Clinical Data De-identification Console (Single-File Edition)

EASA College of Engineering and Technology (ECET)
Centre of Excellence — AIMAA
Department of Artificial Intelligence and Data Science

Sri Manakula Vinayagar Medical College and Hospital (SMVMCH)
Department of General Medicine

Features:
  • JWT authentication (login, logout, register, refresh)
  • User profile page (/profile) — view/update own account
  • Admin CRUD (/admin/users) — full user management
  • Re-identification console (/admin/reidentify) with search
  • Role-Based Access Control: admin / auditor / user
  • 25 interactive Plotly charts
  • Icon-enhanced navbar
  • Complete transaction logging (SQLite + rotating file)
  • Admin audit viewer at /audit
  • Upload status tracking (per-user session view + admin-wide view)
  • REAL PROGRESS BARS — driven by actual server-side pipeline stages
  • SIMILARITY CHECK: raw vs de-identified comparison + report
  • PROCESSING REPORT: end-to-end pipeline timeline on results page
  • Admin similarity reports at /admin/reports
  • Dark / Light theme switch (persisted via localStorage + cookie)
  • Fully responsive: phone / tablet / laptop / desktop / large desktop
  • GLOBAL IP NUMBERING (Convention B): every distinct (MR, IP) pair gets
      a globally-unique dummy IP — no two patients' admissions ever share
      the same dummy value, but the pair remains bound to its MR
  • STABLE CROSS-UPLOAD NUMBERING: dummy MR / IP counters continue from
      the highest value in MRIPRegistry; returning patients keep their
      original dummy ID, only new patients consume new counter slots.
  • ACCUMULATING CROSSWALKS: SECURE_mr_crosswalk.csv and
      SECURE_ip_crosswalk.csv grow with every upload — never regenerated,
      never overwritten. The full history of every patient ever processed
      is preserved on disk.
  • WHOLE-FILE DUPLICATE DETECTION: identical workbook contents are detected
      by content-hash and skipped, redirecting to the earlier successful run
  • CROSS-UPLOAD MR/IP REGISTRY: per-pair signatures across every upload.
      Same (MR, IP) with identical data → skipped.
      Same (MR, IP) with different data → flagged as conflict.
      Admin viewer at /admin/mrip-registry.
  • Inline templates + inline CSS
  • Self-healing schema migration
  • Robust column-name detection (many real-world aliases)
  • Descriptive error messages (no truncated AssertionErrors)

Run:    python app.py
Visit:  http://127.0.0.1:5000
Login:  admin / admin123
"""

# ============================================================
# IMPORTS
# ============================================================
import os
import re
import uuid
import json
import hashlib
import logging
import threading
import traceback
from logging.handlers import RotatingFileHandler
from pathlib import Path
from datetime import datetime, timedelta, timezone
from functools import wraps

import jwt
import pandas as pd
from flask import (
    Flask, request, jsonify, redirect, url_for,
    send_from_directory, flash, g, make_response,
    render_template_string, session
)
from flask_sqlalchemy import SQLAlchemy
from werkzeug.security import generate_password_hash, check_password_hash
from werkzeug.utils import secure_filename
from jinja2 import DictLoader, ChoiceLoader

# ---- Visualization ----
try:
    import plotly.graph_objects as go
    import plotly.express as px
    from plotly.io import to_html
    PLOTLY_OK = True
except ImportError:
    PLOTLY_OK = False


# ============================================================
# CONFIG
# ============================================================
BASE_DIR    = Path(__file__).resolve().parent
UPLOAD_DIR  = BASE_DIR / "uploads"
PUBLIC_DIR  = BASE_DIR / "public"
SECURE_DIR  = BASE_DIR / "SECURE"
DATASET_DIR = BASE_DIR / "DATASET"
LOG_DIR     = BASE_DIR / "logs"

for d in (UPLOAD_DIR, PUBLIC_DIR, SECURE_DIR, DATASET_DIR, LOG_DIR):
    d.mkdir(exist_ok=True)

ALLOWED_EXT = {".xlsx", ".xls"}

JWT_SECRET           = os.environ.get("JWT_SECRET", "change-me-in-production-please")
JWT_ALGORITHM        = "HS256"
ACCESS_TOKEN_EXPIRY  = timedelta(hours=8)
REFRESH_TOKEN_EXPIRY = timedelta(days=7)
COOKIE_NAME          = "access_token"
REFRESH_COOKIE_NAME  = "refresh_token"
THEME_COOKIE_NAME    = "theme"

COPYRIGHT_YEAR = "2026"

ROLE_LEVELS = {"admin": 100, "auditor": 50, "user": 10}
VALID_ROLES = set(ROLE_LEVELS.keys())

TOTAL_CHARTS = 25


# ============================================================
# REAL-TIME PROGRESS STORE (in-memory, per-job)
# ============================================================
PROGRESS_STORE = {}
PROGRESS_LOCK  = threading.Lock()

STAGE_WEIGHTS = {
    "received":    2,
    "parsing":     8,
    "validating":  5,
    "mapping_mr":  8,
    "mapping_ip":  8,
    "crosswalks":  5,
    "saving":      6,
    "similarity": 10,
    "charts":     48,
    "finalizing":  0,
}


def progress_init(job_id: str):
    with PROGRESS_LOCK:
        PROGRESS_STORE[job_id] = {
            "pct": 0.0,
            "stage": "Queued",
            "status": "running",
            "result_url": "",
            "error": "",
            "detail": "",
        }


def progress_set(job_id: str, stage: str, pct: float, detail: str = ""):
    with PROGRESS_LOCK:
        row = PROGRESS_STORE.get(job_id)
        if not row:
            return
        row["stage"] = stage
        row["pct"] = round(min(100.0, max(0.0, pct)), 1)
        row["detail"] = detail


def progress_advance(job_id: str, stage: str, detail: str = ""):
    with PROGRESS_LOCK:
        row = PROGRESS_STORE.get(job_id)
        if not row:
            return
        weight = STAGE_WEIGHTS.get(stage, 0)
        row["pct"] = round(min(100.0, row["pct"] + weight), 1)
        row["stage"] = stage
        row["detail"] = detail


def progress_done(job_id: str, result_url: str):
    with PROGRESS_LOCK:
        row = PROGRESS_STORE.get(job_id)
        if not row:
            return
        row["pct"] = 100.0
        row["stage"] = "Complete"
        row["status"] = "done"
        row["result_url"] = result_url


def progress_fail(job_id: str, error: str):
    with PROGRESS_LOCK:
        row = PROGRESS_STORE.get(job_id)
        if not row:
            return
        row["stage"] = "Failed"
        row["status"] = "failed"
        row["error"] = error


def progress_get(job_id: str):
    with PROGRESS_LOCK:
        return dict(PROGRESS_STORE.get(job_id, {}))


# ============================================================
# AUDIT LOGGER
# ============================================================
def _build_logger():
    logger = logging.getLogger("audit")
    logger.setLevel(logging.INFO)
    logger.propagate = False
    if logger.handlers:
        return logger
    fmt = logging.Formatter("%(asctime)s | %(levelname)-7s | %(message)s",
                            datefmt="%Y-%m-%d %H:%M:%S")
    fh = RotatingFileHandler(LOG_DIR / "audit.log",
                             maxBytes=5 * 1024 * 1024,
                             backupCount=5, encoding="utf-8")
    fh.setFormatter(fmt)
    logger.addHandler(fh)
    ch = logging.StreamHandler()
    ch.setFormatter(fmt)
    logger.addHandler(ch)
    return logger


audit_logger = _build_logger()


# ============================================================
# FLASK APP
# ============================================================
app = Flask(__name__)
app.secret_key = "change-me-session-secret"
app.config["MAX_CONTENT_LENGTH"] = 50 * 1024 * 1024
app.config["SQLALCHEMY_DATABASE_URI"] = f"sqlite:///{BASE_DIR / 'users.db'}"
app.config["SQLALCHEMY_TRACK_MODIFICATIONS"] = False
app.config["SESSION_COOKIE_SECURE"] = False

db = SQLAlchemy(app)


# ============================================================
# MODELS
# ============================================================
class User(db.Model):
    __tablename__ = "users"

    id            = db.Column(db.Integer, primary_key=True)
    username      = db.Column(db.String(64), unique=True, nullable=False, index=True)
    email         = db.Column(db.String(120), unique=True, nullable=True)
    full_name     = db.Column(db.String(120), nullable=True)
    department    = db.Column(db.String(120), nullable=True)
    phone         = db.Column(db.String(32), nullable=True)
    password_hash = db.Column(db.String(255), nullable=False)
    role          = db.Column(db.String(20), default="user", nullable=False)
    is_active_    = db.Column(db.Boolean, default=True)
    created_at    = db.Column(db.DateTime, default=datetime.utcnow)
    updated_at    = db.Column(db.DateTime, default=datetime.utcnow, onupdate=datetime.utcnow)
    last_login    = db.Column(db.DateTime, nullable=True)

    def set_password(self, raw: str) -> None:
        self.password_hash = generate_password_hash(raw)

    def check_password(self, raw: str) -> bool:
        return check_password_hash(self.password_hash, raw)

    @property
    def is_active(self):
        return self.is_active_

    @property
    def role_level(self):
        return ROLE_LEVELS.get(self.role, 0)

    def to_dict(self):
        return {
            "id": self.id, "username": self.username, "email": self.email,
            "full_name": self.full_name, "department": self.department,
            "phone": self.phone, "role": self.role, "is_active": self.is_active_,
            "created_at": self.created_at.strftime("%Y-%m-%d %H:%M") if self.created_at else None,
            "last_login": self.last_login.strftime("%Y-%m-%d %H:%M") if self.last_login else None,
        }


class AuditLog(db.Model):
    __tablename__ = "audit_log"

    id         = db.Column(db.Integer, primary_key=True)
    timestamp  = db.Column(db.DateTime, default=datetime.utcnow, index=True)
    user_id    = db.Column(db.Integer, nullable=True)
    username   = db.Column(db.String(64), nullable=True, index=True)
    role       = db.Column(db.String(20), nullable=True)
    action     = db.Column(db.String(64), nullable=False, index=True)
    status     = db.Column(db.String(16), nullable=False, default="success")
    entity     = db.Column(db.String(64), nullable=True)
    entity_id  = db.Column(db.String(64), nullable=True)
    ip_address = db.Column(db.String(64), nullable=True)
    user_agent = db.Column(db.String(255), nullable=True)
    method     = db.Column(db.String(8), nullable=True)
    path       = db.Column(db.String(255), nullable=True)
    message    = db.Column(db.Text, nullable=True)
    details    = db.Column(db.Text, nullable=True)


class ReidentificationRequest(db.Model):
    __tablename__ = "reid_requests"

    id              = db.Column(db.Integer, primary_key=True)
    timestamp       = db.Column(db.DateTime, default=datetime.utcnow, index=True)
    admin_id        = db.Column(db.Integer, nullable=True)
    admin_username  = db.Column(db.String(64), nullable=True, index=True)
    search_query    = db.Column(db.String(255), nullable=True)
    mode            = db.Column(db.String(16), nullable=False, default="single")
    matched_mr      = db.Column(db.Text, nullable=True)
    matched_ip      = db.Column(db.Text, nullable=True)
    match_count     = db.Column(db.Integer, default=0)
    reason          = db.Column(db.String(255), nullable=True)
    download_file   = db.Column(db.String(255), nullable=True)
    notes           = db.Column(db.Text, nullable=True)


class UploadRecord(db.Model):
    __tablename__ = "upload_records"

    id              = db.Column(db.Integer, primary_key=True)
    job_id          = db.Column(db.String(16), nullable=True, index=True)
    timestamp       = db.Column(db.DateTime, default=datetime.utcnow, index=True)
    user_id         = db.Column(db.Integer, nullable=True, index=True)
    username        = db.Column(db.String(64), nullable=True, index=True)
    role            = db.Column(db.String(20), nullable=True)

    # Whole-file fingerprint (SHA-256 hex) of the raw workbook contents.
    content_hash    = db.Column(db.String(64), nullable=True, index=True)

    original_name   = db.Column(db.String(255), nullable=True)
    saved_name      = db.Column(db.String(255), nullable=True)
    size_bytes      = db.Column(db.Integer, nullable=True)

    sheet1          = db.Column(db.String(64), nullable=True)
    sheet2          = db.Column(db.String(64), nullable=True)
    mr_prefix       = db.Column(db.String(16), nullable=True)
    ip_prefix       = db.Column(db.String(16), nullable=True)

    status          = db.Column(db.String(16), nullable=False, default="success", index=True)
    message         = db.Column(db.Text, nullable=True)

    unique_mr       = db.Column(db.Integer, nullable=True)
    unique_ip       = db.Column(db.Integer, nullable=True)
    sheet1_rows     = db.Column(db.Integer, nullable=True)
    sheet2_rows     = db.Column(db.Integer, nullable=True)
    relation        = db.Column(db.String(8), nullable=True)

    sh1_file        = db.Column(db.String(255), nullable=True)
    sh2_file        = db.Column(db.String(255), nullable=True)


class SimilarityReport(db.Model):
    __tablename__ = "similarity_reports"

    id                = db.Column(db.Integer, primary_key=True)
    job_id            = db.Column(db.String(16), nullable=True, index=True)
    timestamp         = db.Column(db.DateTime, default=datetime.utcnow, index=True)
    user_id           = db.Column(db.Integer, nullable=True, index=True)
    username          = db.Column(db.String(64), nullable=True, index=True)

    sh1_rows          = db.Column(db.Integer, nullable=True)
    sh2_rows          = db.Column(db.Integer, nullable=True)
    sh1_cols          = db.Column(db.Integer, nullable=True)
    sh2_cols          = db.Column(db.Integer, nullable=True)

    sh1_overall_pct   = db.Column(db.Float, nullable=True)
    sh2_overall_pct   = db.Column(db.Float, nullable=True)
    combined_pct      = db.Column(db.Float, nullable=True)

    rows_preserved    = db.Column(db.Boolean, default=True)
    columns_preserved = db.Column(db.Boolean, default=True)

    per_column_json   = db.Column(db.Text, nullable=True)
    notes             = db.Column(db.Text, nullable=True)


class MRIPRegistry(db.Model):
    """
    Cross-upload registry: one row per distinct (originalMR, originalIP).
    Stores the dummy mapping plus a per-pair content signature so we can
    detect identical vs conflicting data across different uploads.

    The dummy_mr / dummy_ip columns are the authoritative, stable,
    globally-unique identifiers across ALL uploads.
    """
    __tablename__ = "mrip_registry"

    id              = db.Column(db.Integer, primary_key=True)
    timestamp       = db.Column(db.DateTime, default=datetime.utcnow, index=True)

    original_mr     = db.Column(db.String(255), nullable=False, index=True)
    original_ip     = db.Column(db.String(255), nullable=False, index=True)
    dummy_mr        = db.Column(db.String(64),  nullable=True)
    dummy_ip        = db.Column(db.String(64),  nullable=True)

    data_signature  = db.Column(db.String(64),  nullable=True, index=True)

    job_id          = db.Column(db.String(16),  nullable=True, index=True)
    username        = db.Column(db.String(64),  nullable=True, index=True)
    user_id         = db.Column(db.Integer,     nullable=True)

    seen_count      = db.Column(db.Integer, default=1)
    row_count       = db.Column(db.Integer, nullable=True)

    __table_args__ = (
        db.UniqueConstraint("original_mr", "original_ip", name="uq_mrip_pair"),
    )


# ============================================================
# AUDIT LOG HELPER
# ============================================================
def log_event(action, status="success", entity=None, entity_id=None,
              message=None, details=None, user=None):
    try:
        u = user
        if u is None:
            u = getattr(g, "current_user", None)

        user_id  = getattr(u, "id", None)
        username = getattr(u, "username", None)
        role     = getattr(u, "role", None)

        ip = ua = method = path = None
        try:
            ip = request.headers.get("X-Forwarded-For", request.remote_addr)
            ua = (request.headers.get("User-Agent") or "")[:255]
            method = request.method
            path = request.path
        except Exception:
            pass

        details_json = None
        if details is not None:
            try:
                details_json = json.dumps(details, default=str)
            except Exception:
                details_json = str(details)

        row = AuditLog(
            user_id=user_id, username=username, role=role,
            action=action, status=status, entity=entity, entity_id=entity_id,
            ip_address=ip, user_agent=ua, method=method, path=path,
            message=message, details=details_json,
        )
        db.session.add(row)
        db.session.commit()

        audit_logger.info(
            f"user={username or '-'} role={role or '-'} "
            f"action={action} status={status} "
            f"entity={entity or '-'} id={entity_id or '-'} "
            f"ip={ip or '-'} path={path or '-'} msg={message or '-'}"
        )
    except Exception:
        try:
            audit_logger.exception("Failed to write audit log")
        except Exception:
            pass


# ============================================================
# WORKBOOK FINGERPRINT (whole-file identical re-upload detection)
# ============================================================
def compute_workbook_fingerprint(file_path, sheet1: str, sheet2: str) -> str:
    """
    Return a stable SHA-256 hex digest of the *contents* of sh1 and sh2.

    Insensitive to cosmetic re-saves but fully sensitive to any data change.
    """
    try:
        h = hashlib.sha256()
        h.update(f"sh1={sheet1}\n".encode("utf-8"))
        h.update(f"sh2={sheet2}\n".encode("utf-8"))

        xls = pd.ExcelFile(file_path, engine="openpyxl")
        for sheet_name in (sheet1, sheet2):
            if sheet_name not in xls.sheet_names:
                h.update(f"[missing:{sheet_name}]\n".encode("utf-8"))
                continue
            df = pd.read_excel(xls, sheet_name=sheet_name, dtype=str).fillna("")
            h.update(f"[{sheet_name}]cols={list(df.columns)}\n".encode("utf-8"))
            h.update(f"[{sheet_name}]rows={len(df)}\n".encode("utf-8"))
            for row_tuple in df.itertuples(index=False, name=None):
                h.update("|".join(str(c) for c in row_tuple).encode("utf-8"))
                h.update(b"\n")
        return h.hexdigest()
    except Exception:
        audit_logger.exception("Fingerprint computation failed")
        return ""


def find_previous_identical_upload(content_hash: str):
    """Return most recent *successful* UploadRecord with matching hash, else None."""
    if not content_hash:
        return None
    return (UploadRecord.query
            .filter(UploadRecord.content_hash == content_hash,
                    UploadRecord.status == "success")
            .order_by(UploadRecord.timestamp.desc())
            .first())


# ============================================================
# GLOBAL COUNTERS + REGISTRY LOOKUPS
# ============================================================
def _max_numeric_suffix(values, prefix: str) -> int:
    """
    Given an iterable of dummy strings and a prefix, return the largest
    integer N such that a value looks like f"{prefix}{N:0X}". Returns 0
    when nothing matches.
    """
    try:
        pat = re.compile(rf"^{re.escape(prefix)}(\d+)$")
        max_n = 0
        for v in values:
            if not v:
                continue
            m = pat.match(str(v))
            if m:
                n = int(m.group(1))
                if n > max_n:
                    max_n = n
        return max_n
    except Exception:
        audit_logger.exception("_max_numeric_suffix failed")
        return 0


def next_mr_counter(mr_prefix: str) -> int:
    """
    Return the next integer to use when assigning a fresh dummy MR,
    continuing from the highest value ever seen in MRIPRegistry.
    """
    try:
        values = [r[0] for r in
                  db.session.query(MRIPRegistry.dummy_mr).distinct().all()]
        return _max_numeric_suffix(values, mr_prefix) + 1
    except Exception:
        audit_logger.exception("next_mr_counter failed")
        return 1


def next_ip_counter(ip_prefix: str) -> int:
    """
    Return the next integer to use when assigning a fresh dummy IP,
    continuing from the highest value ever seen in MRIPRegistry.
    """
    try:
        values = [r[0] for r in
                  db.session.query(MRIPRegistry.dummy_ip).distinct().all()]
        return _max_numeric_suffix(values, ip_prefix) + 1
    except Exception:
        audit_logger.exception("next_ip_counter failed")
        return 1


def load_existing_mr_map() -> dict:
    """Return {original_mr: dummy_mr} for every already-registered MR."""
    try:
        rows = (db.session.query(MRIPRegistry.original_mr, MRIPRegistry.dummy_mr)
                .filter(MRIPRegistry.dummy_mr.isnot(None))
                .all())
        return {str(orig): dummy for orig, dummy in rows if orig and dummy}
    except Exception:
        audit_logger.exception("load_existing_mr_map failed")
        return {}


def load_existing_ip_map() -> dict:
    """
    Return {(original_mr, original_ip): dummy_ip} for every already-
    registered (MR, IP) pair.
    """
    try:
        rows = (db.session.query(
                    MRIPRegistry.original_mr,
                    MRIPRegistry.original_ip,
                    MRIPRegistry.dummy_ip)
                .filter(MRIPRegistry.dummy_ip.isnot(None))
                .all())
        out = {}
        for orig_mr, orig_ip, dummy_ip in rows:
            if orig_mr and orig_ip and dummy_ip:
                out[(str(orig_mr), str(orig_ip))] = dummy_ip
        return out
    except Exception:
        audit_logger.exception("load_existing_ip_map failed")
        return {}


# ============================================================
# ACCUMULATING CROSSWALK WRITERS
# ============================================================
def _read_crosswalk_if_exists(path: Path, required_cols) -> pd.DataFrame:
    """Return existing crosswalk or an empty frame with the required columns."""
    try:
        if path.exists():
            df = pd.read_csv(path, dtype=str, keep_default_na=False)
            for c in required_cols:
                if c not in df.columns:
                    df[c] = ""
            return df[required_cols]
    except Exception:
        audit_logger.exception(f"Failed to read crosswalk {path}")
    return pd.DataFrame(columns=required_cols)


def append_mr_crosswalk(path: Path, new_pairs: dict) -> dict:
    """
    Append new MR mappings to the on-disk crosswalk without regenerating
    existing rows. Returns counters {"added": N, "skipped": N, "total": N}.
    """
    REQUIRED = ["originalMR", "dummyMR"]
    existing = _read_crosswalk_if_exists(path, REQUIRED)

    seen_originals = set(existing["originalMR"].astype(str))
    seen_dummies   = set(existing["dummyMR"].astype(str))

    new_rows = []
    added = 0
    skipped = 0

    for original_mr, dummy_mr in new_pairs.items():
        orig_s = str(original_mr)
        dummy_s = str(dummy_mr)

        # Pair already known → skip (do not overwrite)
        if orig_s in seen_originals:
            existing_dummy = existing.loc[
                existing["originalMR"].astype(str) == orig_s, "dummyMR"
            ].iloc[0]
            if str(existing_dummy) == dummy_s:
                skipped += 1
                continue
            # Same original MR but a different dummy would be a bug
            # (shouldn't happen with the stable-counter fix).
            audit_logger.warning(
                f"MR crosswalk conflict for {orig_s}: existing={existing_dummy}, "
                f"new={dummy_s} — keeping existing"
            )
            skipped += 1
            continue

        # Dummy already used by a different original → defensive skip
        if dummy_s in seen_dummies:
            audit_logger.warning(
                f"Dummy MR {dummy_s} already assigned — skipping {orig_s}"
            )
            skipped += 1
            continue

        new_rows.append({"originalMR": orig_s, "dummyMR": dummy_s})
        seen_originals.add(orig_s)
        seen_dummies.add(dummy_s)
        added += 1

    if new_rows:
        combined = pd.concat(
            [existing, pd.DataFrame(new_rows, columns=REQUIRED)],
            ignore_index=True,
        )
    else:
        combined = existing

    try:
        combined.to_csv(path, index=False)
    except Exception:
        audit_logger.exception(f"Failed to write crosswalk {path}")

    return {
        "added": added,
        "skipped": skipped,
        "total": int(len(combined)),
    }


def append_ip_crosswalk(path: Path, new_rows_list: list) -> dict:
    """
    Append new IP mappings to the on-disk crosswalk without regenerating
    existing rows. `new_rows_list` is a list of dicts with keys
    originalMR, originalIP, dummyMR, dummyIP.

    Returns counters {"added": N, "skipped": N, "total": N}.
    """
    REQUIRED = ["originalMR", "originalIP", "dummyMR", "dummyIP"]
    existing = _read_crosswalk_if_exists(path, REQUIRED)

    # Key = (originalMR, originalIP) — the stable identity of an admission
    seen_pairs = set(
        zip(existing["originalMR"].astype(str),
            existing["originalIP"].astype(str))
    )
    seen_dummies = set(existing["dummyIP"].astype(str))

    to_append = []
    added = 0
    skipped = 0

    for row in new_rows_list:
        orig_mr = str(row.get("originalMR", ""))
        orig_ip = str(row.get("originalIP", ""))
        dummy_mr = str(row.get("dummyMR", ""))
        dummy_ip = str(row.get("dummyIP", ""))

        if not orig_mr or not orig_ip or not dummy_ip:
            skipped += 1
            continue

        key = (orig_mr, orig_ip)

        if key in seen_pairs:
            # Already known — never overwrite
            skipped += 1
            continue

        if dummy_ip in seen_dummies:
            # Dummy already used by a different admission — defensive
            audit_logger.warning(
                f"Dummy IP {dummy_ip} already assigned — skipping "
                f"({orig_mr}, {orig_ip})"
            )
            skipped += 1
            continue

        to_append.append({
            "originalMR": orig_mr,
            "originalIP": orig_ip,
            "dummyMR":    dummy_mr,
            "dummyIP":    dummy_ip,
        })
        seen_pairs.add(key)
        seen_dummies.add(dummy_ip)
        added += 1

    if to_append:
        combined = pd.concat(
            [existing, pd.DataFrame(to_append, columns=REQUIRED)],
            ignore_index=True,
        )
    else:
        combined = existing

    try:
        combined.to_csv(path, index=False)
    except Exception:
        audit_logger.exception(f"Failed to write crosswalk {path}")

    return {
        "added": added,
        "skipped": skipped,
        "total": int(len(combined)),
    }


# ============================================================
# PER-(MR, IP) SIGNATURES + REGISTRY
# ============================================================
def compute_mrip_signatures(raw_sh1: pd.DataFrame,
                            raw_sh2: pd.DataFrame) -> dict:
    """
    For each distinct (originalMR, originalIP) pair in raw_sh1, compute a
    SHA-256 signature over the corresponding rows in raw_sh2.

    Row order inside a pair does not affect the signature (rows are sorted).
    Column order does (it is included in the hash).

    Returns: {(raw_mr, raw_ip): {"signature": hex, "row_count": int}}
    """
    out = {}
    try:
        needed = {"duplicateMR", "duplicateIP"}
        if not needed.issubset(raw_sh1.columns) or not needed.issubset(raw_sh2.columns):
            return out

        pairs = (raw_sh1[["duplicateMR", "duplicateIP"]]
                 .dropna()
                 .astype(str)
                 .drop_duplicates()
                 .reset_index(drop=True))

        sh2 = raw_sh2.copy()
        sh2["duplicateMR"] = sh2["duplicateMR"].astype(str)
        sh2["duplicateIP"] = sh2["duplicateIP"].astype(str)

        str_cols = list(sh2.columns)
        for c in str_cols:
            sh2[c] = sh2[c].fillna("").astype(str)

        for raw_mr, raw_ip in pairs.itertuples(index=False):
            mask = (sh2["duplicateMR"] == raw_mr) & (sh2["duplicateIP"] == raw_ip)
            block = sh2.loc[mask, str_cols].copy()
            if len(block) == 0:
                h = hashlib.sha256()
                h.update(b"EMPTY")
                out[(raw_mr, raw_ip)] = {"signature": h.hexdigest(), "row_count": 0}
                continue

            block = block.sort_values(by=str_cols).reset_index(drop=True)
            h = hashlib.sha256()
            h.update(("|".join(str_cols) + "\n").encode("utf-8"))
            for row_tuple in block.itertuples(index=False, name=None):
                h.update("|".join(str(c) for c in row_tuple).encode("utf-8"))
                h.update(b"\n")

            out[(raw_mr, raw_ip)] = {
                "signature": h.hexdigest(),
                "row_count": int(len(block)),
            }
    except Exception:
        audit_logger.exception("compute_mrip_signatures failed")
    return out


def classify_mrip_pairs(signatures: dict) -> dict:
    """
    Compare each (MR, IP) pair against the MRIPRegistry.

    Returns {"new": [...], "identical": [...], "conflict": [...]}.
    """
    result = {"new": [], "identical": [], "conflict": []}
    if not signatures:
        return result

    pairs = list(signatures.keys())
    existing = {}
    try:
        CHUNK = 400
        for i in range(0, len(pairs), CHUNK):
            chunk = pairs[i:i+CHUNK]
            rows = (MRIPRegistry.query
                    .filter(MRIPRegistry.original_mr.in_([p[0] for p in chunk]),
                            MRIPRegistry.original_ip.in_([p[1] for p in chunk]))
                    .all())
            for r in rows:
                existing[(r.original_mr, r.original_ip)] = r
    except Exception:
        audit_logger.exception("classify_mrip_pairs: DB lookup failed")

    for pair, info in signatures.items():
        rec = existing.get(pair)
        entry = {
            "raw_mr": pair[0],
            "raw_ip": pair[1],
            "signature": info["signature"],
            "row_count": info["row_count"],
        }
        if rec is None:
            result["new"].append(entry)
        elif rec.data_signature == info["signature"]:
            entry.update({
                "existing_job": rec.job_id,
                "existing_username": rec.username,
                "existing_at": rec.timestamp.strftime("%Y-%m-%d %H:%M:%S") if rec.timestamp else "",
            })
            result["identical"].append(entry)
        else:
            entry.update({
                "existing_signature": rec.data_signature,
                "existing_job": rec.job_id,
                "existing_username": rec.username,
                "existing_at": rec.timestamp.strftime("%Y-%m-%d %H:%M:%S") if rec.timestamp else "",
            })
            result["conflict"].append(entry)
    return result


def upsert_mrip_registry(signatures: dict,
                         mr_map: dict,
                         ip_pair_map: dict,
                         job_id: str,
                         username: str,
                         user_id: int) -> int:
    """
    Insert or update every (MR, IP) pair in the registry.

    Crucially, dummy_mr / dummy_ip are **never overwritten** with a
    different value when a row already exists — the previously assigned
    global ID is authoritative. Only data_signature / job_id / username
    are updated when the underlying data has changed.
    """
    if not signatures:
        return 0

    touched = 0
    try:
        pairs = list(signatures.keys())
        existing = {}
        CHUNK = 400
        for i in range(0, len(pairs), CHUNK):
            chunk = pairs[i:i+CHUNK]
            rows = (MRIPRegistry.query
                    .filter(MRIPRegistry.original_mr.in_([p[0] for p in chunk]),
                            MRIPRegistry.original_ip.in_([p[1] for p in chunk]))
                    .all())
            for r in rows:
                existing[(r.original_mr, r.original_ip)] = r

        for pair, info in signatures.items():
            rec = existing.get(pair)
            dummy_mr = mr_map.get(pair[0])
            dummy_ip = ip_pair_map.get(pair)

            if rec is None:
                rec = MRIPRegistry(
                    original_mr=pair[0],
                    original_ip=pair[1],
                    dummy_mr=dummy_mr,
                    dummy_ip=dummy_ip,
                    data_signature=info["signature"],
                    job_id=job_id,
                    username=username,
                    user_id=user_id,
                    seen_count=1,
                    row_count=info["row_count"],
                )
                db.session.add(rec)
            else:
                rec.seen_count = (rec.seen_count or 1) + 1
                if rec.data_signature != info["signature"]:
                    rec.data_signature = info["signature"]
                    rec.job_id = job_id
                    rec.username = username
                    rec.user_id = user_id
                rec.row_count = info["row_count"]
                # Never overwrite existing dummy IDs — they are the
                # authoritative, stable, cross-upload identifiers.
                if not rec.dummy_mr and dummy_mr:
                    rec.dummy_mr = dummy_mr
                if not rec.dummy_ip and dummy_ip:
                    rec.dummy_ip = dummy_ip
            touched += 1

        db.session.commit()
    except Exception:
        try:
            db.session.rollback()
        except Exception:
            pass
        audit_logger.exception("upsert_mrip_registry failed")
    return touched


# ============================================================
# UPLOAD RECORD HELPERS
# ============================================================
def record_upload(*, job_id, original_name, saved_name=None, size_bytes=None,
                  sheet1=None, sheet2=None, mr_prefix=None, ip_prefix=None,
                  status="success", message=None,
                  unique_mr=None, unique_ip=None,
                  sheet1_rows=None, sheet2_rows=None, relation=None,
                  sh1_file=None, sh2_file=None,
                  content_hash=None,
                  user=None):
    try:
        u = user or getattr(g, "current_user", None)
        row = UploadRecord(
            job_id=job_id,
            user_id=getattr(u, "id", None),
            username=getattr(u, "username", None),
            role=getattr(u, "role", None),
            content_hash=content_hash,
            original_name=(original_name or "")[:255] or None,
            saved_name=(saved_name or "")[:255] or None,
            size_bytes=size_bytes,
            sheet1=sheet1, sheet2=sheet2,
            mr_prefix=mr_prefix, ip_prefix=ip_prefix,
            status=status, message=message,
            unique_mr=unique_mr, unique_ip=unique_ip,
            sheet1_rows=sheet1_rows, sheet2_rows=sheet2_rows,
            relation=relation,
            sh1_file=sh1_file, sh2_file=sh2_file,
        )
        db.session.add(row)
        db.session.commit()
        return row.id
    except Exception:
        try:
            db.session.rollback()
        except Exception:
            pass
        audit_logger.exception("Failed to record upload")
        return None


def _remember_upload_in_session(job_id: str):
    try:
        if not job_id:
            return
        recent = session.get("recent_uploads", [])
        recent = [job_id] + [j for j in recent if j != job_id]
        session["recent_uploads"] = recent[:10]
    except Exception:
        pass


# ============================================================
# PROGRESS HELPERS
# ============================================================
def pct(part, total):
    try:
        part = float(part or 0)
        total = float(total or 0)
        if total <= 0:
            return 0.0
        return round(min(100.0, max(0.0, part / total * 100.0)), 1)
    except Exception:
        return 0.0


def ratio_parts(*values):
    vals = [max(0, int(v or 0)) for v in values]
    total = sum(vals) or 1
    return [round(v / total * 100.0, 2) for v in vals], total


# ============================================================
# SIMILARITY CHECK HELPERS
# ============================================================
def _column_match_score(before: pd.Series, after: pd.Series) -> float:
    try:
        n = min(len(before), len(after))
        if n == 0:
            return 0.0
        b = before.iloc[:n].astype(str).fillna("").reset_index(drop=True)
        a = after.iloc[:n].astype(str).fillna("").reset_index(drop=True)
        same = (b == a).sum()
        return round(same / n * 100.0, 2)
    except Exception:
        return 0.0


def _classify_column(col: str) -> str:
    c = str(col).strip().lower()
    ident = {"duplicatemr", "duplicateip", "mr", "ip",
             "dupmr", "dupip", "patientid", "patient_id"}
    if c in ident:
        return "identifier"
    return "preserved"


def compute_similarity_report(before_sh1: pd.DataFrame,
                              before_sh2: pd.DataFrame,
                              after_sh1: pd.DataFrame,
                              after_sh2: pd.DataFrame) -> dict:
    def _analyze(before, after, sheet_name):
        report = {
            "sheet": sheet_name,
            "rows_before": int(len(before)),
            "rows_after": int(len(after)),
            "cols_before": int(before.shape[1]),
            "cols_after": int(after.shape[1]),
            "rows_preserved": int(len(before)) == int(len(after)),
            "columns": [],
            "overall_pct": 0.0,
            "notes": [],
        }

        common_cols = [c for c in before.columns if c in after.columns]
        if not common_cols:
            report["notes"].append("No common columns between raw and de-identified data.")
            return report

        total_weight = 0.0
        weighted_sum = 0.0

        for col in common_cols:
            try:
                score = _column_match_score(before[col], after[col])
            except Exception:
                score = 0.0
            kind = _classify_column(col)
            weight = 0.5 if kind == "identifier" else 1.0
            weighted_sum += score * weight
            total_weight += weight

            report["columns"].append({
                "name": col,
                "kind": kind,
                "match_pct": score,
                "changed": score < 99.99,
            })

        report["overall_pct"] = round(weighted_sum / total_weight, 2) if total_weight else 0.0

        if not report["rows_preserved"]:
            report["notes"].append(
                f"⚠ Row count changed: {report['rows_before']} → {report['rows_after']}"
            )

        new_cols = [c for c in after.columns if c not in before.columns]
        if new_cols:
            report["notes"].append(f"New columns added: {', '.join(new_cols)}")

        return report

    sh1_report = _analyze(before_sh1, after_sh1, "sh1")
    sh2_report = _analyze(before_sh2, after_sh2, "sh2")

    combined = round((sh1_report["overall_pct"] + sh2_report["overall_pct"]) / 2.0, 2)

    return {
        "sh1": sh1_report,
        "sh2": sh2_report,
        "combined_pct": combined,
        "rows_preserved": sh1_report["rows_preserved"] and sh2_report["rows_preserved"],
        "columns_preserved": True,
        "timestamp": datetime.utcnow().strftime("%Y-%m-%d %H:%M:%S"),
    }


def record_similarity_report(job_id: str, report: dict, user=None) -> int:
    try:
        u = user or getattr(g, "current_user", None)
        row = SimilarityReport(
            job_id=job_id,
            user_id=getattr(u, "id", None),
            username=getattr(u, "username", None),
            sh1_rows=report["sh1"]["rows_after"],
            sh2_rows=report["sh2"]["rows_after"],
            sh1_cols=report["sh1"]["cols_after"],
            sh2_cols=report["sh2"]["cols_after"],
            sh1_overall_pct=report["sh1"]["overall_pct"],
            sh2_overall_pct=report["sh2"]["overall_pct"],
            combined_pct=report["combined_pct"],
            rows_preserved=report["rows_preserved"],
            columns_preserved=report["columns_preserved"],
            per_column_json=json.dumps({
                "sh1": report["sh1"]["columns"],
                "sh2": report["sh2"]["columns"],
                "notes_sh1": report["sh1"]["notes"],
                "notes_sh2": report["sh2"]["notes"],
            }, default=str),
        )
        db.session.add(row)
        db.session.commit()
        return row.id
    except Exception:
        try:
            db.session.rollback()
        except Exception:
            pass
        audit_logger.exception("Failed to record similarity report")
        return None


def build_processing_report(result: dict, similarity, charts_built: int, charts_total: int) -> dict:
    stages = [
        {"label": "File validated",                 "pct": 100, "ok": True},
        {"label": "Sheets loaded (sh1 + sh2)",      "pct": 100, "ok": True},
        {"label": "MR → dummy MR mapping",          "pct": 100, "ok": True},
        {"label": "IP → dummy IP mapping (global)", "pct": 100, "ok": True},
        {"label": "Crosswalks appended (SECURE)",   "pct": 100, "ok": True},
        {"label": "De-identified workbooks saved",  "pct": 100, "ok": True},
        {"label": f"Charts built ({charts_built}/{charts_total})",
         "pct": pct(charts_built, charts_total),
         "ok": charts_built == charts_total},
        {"label": "Similarity check",
         "pct": (similarity or {}).get("combined_pct", 0),
         "ok": bool(similarity) and similarity.get("rows_preserved", False)},
    ]
    total = sum(s["pct"] for s in stages) / len(stages)
    return {"stages": stages, "overall_pct": round(total, 1)}


# ============================================================
# JWT HELPERS
# ============================================================
def create_access_token(user: User) -> str:
    now = datetime.now(timezone.utc)
    payload = {
        "sub": str(user.id), "username": user.username, "role": user.role,
        "iat": now, "exp": now + ACCESS_TOKEN_EXPIRY, "type": "access",
    }
    return jwt.encode(payload, JWT_SECRET, algorithm=JWT_ALGORITHM)


def create_refresh_token(user: User) -> str:
    now = datetime.now(timezone.utc)
    payload = {"sub": str(user.id), "iat": now, "exp": now + REFRESH_TOKEN_EXPIRY, "type": "refresh"}
    return jwt.encode(payload, JWT_SECRET, algorithm=JWT_ALGORITHM)


def decode_token(token: str):
    try:
        return jwt.decode(token, JWT_SECRET, algorithms=[JWT_ALGORITHM])
    except jwt.ExpiredSignatureError:
        return None
    except jwt.InvalidTokenError:
        return None


def get_token_from_request():
    auth = request.headers.get("Authorization", "")
    if auth.startswith("Bearer "):
        return auth[7:]
    return request.cookies.get(COOKIE_NAME)


def jwt_required(f):
    @wraps(f)
    def wrapper(*args, **kwargs):
        token = get_token_from_request()
        if not token:
            return _unauthorized("Missing token")
        payload = decode_token(token)
        if not payload or payload.get("type") != "access":
            return _unauthorized("Invalid or expired token")
        user = db.session.get(User, int(payload["sub"]))
        if not user or not user.is_active:
            return _unauthorized("User not found or inactive")
        g.current_user = user
        return f(*args, **kwargs)
    return wrapper


def admin_required(f):
    @wraps(f)
    @jwt_required
    def wrapper(*args, **kwargs):
        if g.current_user.role != "admin":
            log_event("admin_access_denied", status="denied",
                      message="Non-admin attempted admin-only route")
            flash("Admin access required.", "error")
            return redirect(url_for("index"))
        return f(*args, **kwargs)
    return wrapper


def _unauthorized(msg):
    if request.path.startswith("/api/"):
        return jsonify({"error": "unauthorized", "message": msg}), 401
    flash("Please log in to access this page.", "warning")
    return redirect(url_for("login_page"))


# ============================================================
# VALIDATION HELPERS
# ============================================================
USERNAME_RE = re.compile(r"^[A-Za-z0-9_.-]{3,32}$")
EMAIL_RE    = re.compile(r"^[^@\s]+@[^@\s]+\.[^@\s]+$")


def validate_user_input(username=None, email=None, password=None,
                        confirm=None, role=None, require_password=False):
    errors, cleaned = [], {}
    if username is not None:
        username = username.strip()
        if not USERNAME_RE.match(username):
            errors.append("Username must be 3–32 chars (A–Z, 0–9, . _ -).")
        cleaned["username"] = username
    if email is not None:
        email = email.strip() or None
        if email and not EMAIL_RE.match(email):
            errors.append("Email address is not valid.")
        cleaned["email"] = email
    if role is not None:
        role = role.strip() or "user"
        if role not in VALID_ROLES:
            errors.append(f"Role must be one of: {', '.join(sorted(VALID_ROLES))}.")
        cleaned["role"] = role
    if require_password or (password is not None and password != ""):
        if not password or len(password) < 6:
            errors.append("Password must be at least 6 characters.")
        if password != (confirm if confirm is not None else password):
            errors.append("Passwords do not match.")
        cleaned["password"] = password
    return errors, cleaned


# ============================================================
# RE-IDENTIFICATION HELPERS
# ============================================================
def _load_crosswalk(kind: str) -> pd.DataFrame:
    if kind == "mr":
        path = SECURE_DIR / "SECURE_mr_crosswalk.csv"
    elif kind == "ip":
        path = SECURE_DIR / "SECURE_ip_crosswalk.csv"
    else:
        raise ValueError("kind must be 'mr' or 'ip'")
    if not path.exists():
        return pd.DataFrame()
    return pd.read_csv(path, dtype=str, keep_default_na=False)


def _search_crosswalk(query: str, kind: str = "both") -> dict:
    query = (query or "").strip()
    results = {"mr": [], "ip": [], "query": query}
    if not query:
        return results
    q = query.upper()
    if kind in ("both", "mr"):
        df = _load_crosswalk("mr")
        if not df.empty:
            mask = (
                df["originalMR"].astype(str).str.upper().str.contains(q, na=False) |
                df["dummyMR"].astype(str).str.upper().str.contains(q, na=False)
            )
            results["mr"] = df[mask].to_dict(orient="records")
    if kind in ("both", "ip"):
        df = _load_crosswalk("ip")
        if not df.empty:
            mask = (
                df["originalMR"].astype(str).str.upper().str.contains(q, na=False) |
                df["originalIP"].astype(str).str.upper().str.contains(q, na=False) |
                df["dummyMR"].astype(str).str.upper().str.contains(q, na=False) |
                df["dummyIP"].astype(str).str.upper().str.contains(q, na=False)
            )
            results["ip"] = df[mask].to_dict(orient="records")
    return results


def _reverse_dataset(mr_list, ip_list):
    sh1_path = PUBLIC_DIR / "sh1_deidentified.xlsx"
    sh2_path = PUBLIC_DIR / "sh2_deidentified.xlsx"
    if not sh1_path.exists() or not sh2_path.exists():
        raise FileNotFoundError("De-identified dataset not found in public/")

    sh1 = pd.read_excel(sh1_path, engine="openpyxl")
    sh2 = pd.read_excel(sh2_path, engine="openpyxl")

    mr_df = _load_crosswalk("mr")
    ip_df = _load_crosswalk("ip")

    if mr_list:
        mr_df = mr_df[mr_df["dummyMR"].isin(mr_list)] if not mr_df.empty else mr_df
        ip_df = ip_df[ip_df["dummyMR"].isin(mr_list)] if not ip_df.empty else ip_df
    if ip_list:
        ip_df = ip_df[ip_df["dummyIP"].isin(ip_list)] if not ip_df.empty else ip_df
        if not mr_list and not ip_df.empty:
            mr_df = mr_df[mr_df["dummyMR"].isin(ip_df["dummyMR"].unique())]

    if not mr_df.empty:
        sh1_out = sh1.merge(
            mr_df[["dummyMR", "originalMR"]].rename(columns={"dummyMR": "MR"}),
            on="MR", how="left",
        )
    else:
        sh1_out = sh1.copy()

    if not ip_df.empty:
        ip_lookup = (ip_df[["dummyMR", "dummyIP", "originalMR", "originalIP"]]
                     .rename(columns={"dummyMR": "MR", "dummyIP": "IP"}))
        sh2_out = sh2.merge(ip_lookup, on=["MR", "IP"], how="left")
    else:
        sh2_out = sh2.copy()

    def _reorder(df, first_cols):
        cols = [c for c in first_cols if c in df.columns] + \
               [c for c in df.columns if c not in first_cols]
        return df[cols]

    sh1_out = _reorder(sh1_out, ["MR", "IP", "originalMR"])
    sh2_out = _reorder(sh2_out, ["MR", "IP", "originalMR", "originalIP"])
    return sh1_out, sh2_out


def _write_reid_outputs(sh1_out, sh2_out, admin_username: str) -> tuple:
    ts = datetime.utcnow().strftime("%Y%m%d_%H%M%S")
    f1 = f"sh1_reidentified_{admin_username}_{ts}.xlsx"
    f2 = f"sh2_reidentified_{admin_username}_{ts}.xlsx"
    sh1_out.to_excel(PUBLIC_DIR / f1, index=False)
    sh2_out.to_excel(PUBLIC_DIR / f2, index=False)
    return f1, f2


# ============================================================
# DE-IDENTIFICATION ENGINE
# ============================================================
_MR_TARGET = "duplicateMR"
_IP_TARGET = "duplicateIP"

_MR_ALIASES = {
    "duplicatemr", "dupmr", "mr", "mrn", "medicalrecord",
    "medicalrecordnumber", "medicalrecordno", "patientid",
    "patient", "hospitalid", "hospitalno", "uhid", "opid",
    "regno", "registrationno", "registrationnumber",
    "patientno", "patientnumber", "patid", "patno",
}
_IP_ALIASES = {
    "duplicateip", "dupip", "ip", "ipno", "ipnumber",
    "admissionno", "admissionnumber", "admissionid",
    "visitid", "visitno", "visitnumber",
    "encounterid", "encounterno", "encounternumber",
    "inpatientno", "inpatientnumber", "inpatientid",
    "admission", "visit", "encounter",
}


def _colkey(col) -> str:
    return str(col).strip().lower().replace(" ", "").replace("_", "").replace(".", "").replace("-", "")


def normalize_columns(df: pd.DataFrame) -> pd.DataFrame:
    rename_dict = {}
    has_mr = any(_colkey(c) == _MR_TARGET.lower() for c in df.columns)
    has_ip = any(_colkey(c) == _IP_TARGET.lower() for c in df.columns)

    for col in df.columns:
        k = _colkey(col)
        if k in _MR_ALIASES and not has_mr:
            rename_dict[col] = _MR_TARGET
            has_mr = True
        elif k in _IP_ALIASES and not has_ip:
            rename_dict[col] = _IP_TARGET
            has_ip = True

    df = df.rename(columns=rename_dict)

    if _MR_TARGET not in df.columns:
        for col in df.columns:
            k = _colkey(col)
            if "mrn" in k or ("mr" in k and "number" in k) or k.endswith("mr") or k.startswith("mr"):
                df = df.rename(columns={col: _MR_TARGET})
                break
    if _IP_TARGET not in df.columns:
        for col in df.columns:
            k = _colkey(col)
            if k in _IP_ALIASES or k.endswith("ip") or k.startswith("ip") \
               or "admission" in k or "visit" in k:
                if col != _MR_TARGET:
                    df = df.rename(columns={col: _IP_TARGET})
                    break

    return df


def detect_cardinality(sh1: pd.DataFrame) -> dict:
    pairs = sh1[["duplicateMR", "duplicateIP"]].drop_duplicates()
    mr_counts = pairs.groupby("duplicateMR")["duplicateIP"].nunique()
    ip_counts = pairs.groupby("duplicateIP")["duplicateMR"].nunique()
    max_ip_per_mr = int(mr_counts.max()) if len(mr_counts) else 0
    max_mr_per_ip = int(ip_counts.max()) if len(ip_counts) else 0
    if max_ip_per_mr == 1 and max_mr_per_ip == 1:
        relation = "1:1"
    elif max_ip_per_mr >= 1 and max_mr_per_ip == 1:
        relation = "1:M"
    elif max_ip_per_mr == 1 and max_mr_per_ip >= 1:
        relation = "M:1"
    else:
        relation = "M:M"
    return {
        "relation": relation,
        "n_mr": int(sh1["duplicateMR"].nunique()),
        "n_ip": int(sh1["duplicateIP"].nunique()),
        "max_ip_per_mr": max_ip_per_mr, "max_mr_per_ip": max_mr_per_ip,
        "avg_ip_per_mr": float(mr_counts.mean()) if len(mr_counts) else 0.0,
    }


def _missing_columns_msg(sheet_name: str, df: pd.DataFrame, missing: set) -> str:
    found = list(df.columns)
    preview = found[:25]
    more = "" if len(found) <= 25 else f" …(+{len(found)-25} more)"
    return (
        f"Sheet '{sheet_name}' is missing required column(s): {sorted(missing)}. "
        f"Found {len(found)} column(s): {preview}{more}. "
        f"Please ensure the sheet contains an MR/patient identifier column and "
        f"an IP/admission identifier column."
    )


def deidentify(file_path, output_dir, secure_dir,
               mr_prefix="P", ip_prefix="IP",
               mr_width=3, ip_width=3,
               sheet1="sh1", sheet2="sh2",
               job_id=None,
               mr_start: int = 1,
               ip_start: int = 1):
    """
    Full de-identification pipeline.

    MR mapping:
        One raw MR  →  one globally-unique dummy MR (stable across uploads).
        Returning MRs re-use their previously assigned dummy MR.

    IP mapping (Convention B — global counter, MR-bound pair key):
        Every distinct (raw_mr, raw_ip) pair gets a globally-unique dummy IP
        (stable across uploads). Returning pairs re-use their previously
        assigned dummy IP.

    Crosswalks (SECURE_mr_crosswalk.csv / SECURE_ip_crosswalk.csv):
        APPEND-ONLY. New mappings are added; existing rows are never
        rewritten or removed. The on-disk file grows monotonically with
        every upload and preserves the full history of every patient.

    `mr_start` and `ip_start` are the next free integers for brand-new
    identifiers. Only genuinely new identifiers consume fresh slots.
    """
    file_path = Path(file_path)
    output_dir = Path(output_dir)
    secure_dir = Path(secure_dir)
    output_dir.mkdir(exist_ok=True, parents=True)
    secure_dir.mkdir(exist_ok=True, parents=True)

    def _prog(stage, detail=""):
        if job_id:
            progress_advance(job_id, stage, detail)

    _prog("parsing", f"Opening {file_path.name}")
    try:
        xls = pd.ExcelFile(file_path, engine="openpyxl")
    except Exception as e:
        raise ValueError(f"Could not open workbook: {e}")

    available = list(xls.sheet_names)
    if sheet1 not in available:
        raise ValueError(f"Sheet '{sheet1}' not found. Available sheets: {available}")
    if sheet2 not in available:
        raise ValueError(f"Sheet '{sheet2}' not found. Available sheets: {available}")

    sh1 = pd.read_excel(xls, sheet_name=sheet1)
    sh2 = pd.read_excel(xls, sheet_name=sheet2)
    _prog("parsing", f"Loaded sh1={len(sh1)} rows, sh2={len(sh2)} rows")

    sh1 = normalize_columns(sh1)
    sh2 = normalize_columns(sh2)

    _prog("validating", "Checking identifier columns")
    required = {"duplicateMR", "duplicateIP"}
    missing_sh1 = required - set(sh1.columns)
    missing_sh2 = required - set(sh2.columns)

    if missing_sh1 or missing_sh2:
        parts = []
        if missing_sh1:
            parts.append(_missing_columns_msg(sheet1, sh1, missing_sh1))
        if missing_sh2:
            parts.append(_missing_columns_msg(sheet2, sh2, missing_sh2))
        msg = " | ".join(parts)
        audit_logger.error(f"Column validation failed: {msg}")
        raise ValueError(msg)

    if len(sh1) == 0:
        raise ValueError(f"Sheet '{sheet1}' contains no data rows.")
    if len(sh2) == 0:
        raise ValueError(f"Sheet '{sheet2}' contains no data rows.")

    card = detect_cardinality(sh1)

    # ---------------- MR MAPPING (stable across uploads) ----------------
    _prog("mapping_mr", "Generating dummy MR identifiers")

    existing_mr = load_existing_mr_map()
    unique_mrs = sorted(sh1["duplicateMR"].dropna().astype(str).unique())

    if not unique_mrs:
        raise ValueError(f"Sheet '{sheet1}' has no non-null MR values.")

    existing_mr_values = set(existing_mr.values())

    mr_map = {}
    used_dummies = set()
    cursor = int(mr_start)

    for old in unique_mrs:
        prior = existing_mr.get(old)
        if prior and prior not in used_dummies:
            mr_map[old] = prior
            used_dummies.add(prior)
        else:
            while True:
                candidate = f"{mr_prefix}{cursor:0{mr_width}d}"
                cursor += 1
                if candidate not in used_dummies and candidate not in existing_mr_values:
                    break
            mr_map[old] = candidate
            used_dummies.add(candidate)

    # ---------------- IP MAPPING (stable across uploads) ----------------
    _prog("mapping_ip", "Generating dummy IP identifiers (globally unique)")

    pairs_raw = (sh1[["duplicateMR", "duplicateIP"]]
                 .dropna()
                 .astype(str)
                 .drop_duplicates()
                 .sort_values(["duplicateMR", "duplicateIP"])
                 .reset_index(drop=True))

    if len(pairs_raw) == 0:
        raise ValueError(f"Sheet '{sheet1}' has no non-null IP values.")

    existing_ip = load_existing_ip_map()
    existing_ip_values = set(existing_ip.values())

    ip_pair_map = {}
    used_ips = set()
    ip_cursor = int(ip_start)

    for raw_mr, raw_ip in pairs_raw.itertuples(index=False):
        key = (raw_mr, raw_ip)
        prior = existing_ip.get(key)
        if prior and prior not in used_ips:
            ip_pair_map[key] = prior
            used_ips.add(prior)
        else:
            while True:
                candidate = f"{ip_prefix}{ip_cursor:0{ip_width}d}"
                ip_cursor += 1
                if candidate not in used_ips and candidate not in existing_ip_values:
                    break
            ip_pair_map[key] = candidate
            used_ips.add(candidate)

    # ---------------- CROSSWALKS (append-only) ----------------
    _prog("crosswalks", "Appending to SECURE crosswalks")

    mr_cw_path = secure_dir / "SECURE_mr_crosswalk.csv"
    ip_cw_path = secure_dir / "SECURE_ip_crosswalk.csv"

    mr_stats = append_mr_crosswalk(mr_cw_path, mr_map)

    ip_rows = []
    for (raw_mr, raw_ip), dummy_ip in ip_pair_map.items():
        ip_rows.append({
            "originalMR": raw_mr,
            "originalIP": raw_ip,
            "dummyMR":    mr_map.get(raw_mr),
            "dummyIP":    dummy_ip,
        })
    ip_stats = append_ip_crosswalk(ip_cw_path, ip_rows)

    audit_logger.info(
        f"Crosswalk append — MR: +{mr_stats['added']} new, "
        f"{mr_stats['skipped']} skipped, total={mr_stats['total']} | "
        f"IP: +{ip_stats['added']} new, {ip_stats['skipped']} skipped, "
        f"total={ip_stats['total']}"
    )

    # ---------------- APPLY MAPPINGS ----------------
    def _map_mr(series):
        return series.astype(str).map(mr_map)

    def _map_ip(df):
        return [
            ip_pair_map.get((str(mr), str(ip)))
            for mr, ip in zip(df["duplicateMR"], df["duplicateIP"])
        ]

    for df in (sh1, sh2):
        df["MR"] = _map_mr(df["duplicateMR"])
        df["IP"] = _map_ip(df)
        df.drop(columns=["duplicateMR", "duplicateIP"], inplace=True)

    if not sh1["MR"].notna().all():
        n = int(sh1["MR"].isna().sum())
        raise ValueError(f"sh1: {n} row(s) could not be mapped to a dummy MR.")
    if not sh1["IP"].notna().all():
        n = int(sh1["IP"].isna().sum())
        raise ValueError(f"sh1: {n} row(s) could not be mapped to a dummy IP.")
    if not sh2["MR"].notna().all():
        n = int(sh2["MR"].isna().sum())
        raise ValueError(f"sh2: {n} row(s) could not be mapped to a dummy MR.")
    if not sh2["IP"].notna().all():
        n = int(sh2["IP"].isna().sum())
        raise ValueError(f"sh2: {n} row(s) could not be mapped to a dummy IP.")

    if sh1["IP"].nunique() != sh1[["MR", "IP"]].drop_duplicates().shape[0]:
        raise ValueError("Internal error: dummy IP uniqueness violated in sh1.")

    ip_to_mr_dummy = sh1.groupby("IP")["MR"].nunique()
    if not (ip_to_mr_dummy == 1).all():
        bad = ip_to_mr_dummy[ip_to_mr_dummy != 1].to_dict()
        raise ValueError(
            f"Dummy IP maps to multiple MRs — cardinality violation. "
            f"Examples: {list(bad.items())[:5]}"
        )

    sh1_pairs = set(zip(sh1["MR"], sh1["IP"]))
    sh2_pairs = set(zip(sh2["MR"], sh2["IP"]))
    if not sh2_pairs.issubset(sh1_pairs):
        missing = list(sh2_pairs - sh1_pairs)[:5]
        raise ValueError(f"sh2 contains (MR, IP) pairs not present in sh1. Examples: {missing}")

    _prog("saving", "Writing de-identified workbooks")
    sh1_out = output_dir / "sh1_deidentified.xlsx"
    sh2_out = output_dir / "sh2_deidentified.xlsx"
    sh1.to_excel(sh1_out, index=False)
    sh2.to_excel(sh2_out, index=False)

    mr_ip_dist = (sh1.groupby("MR")["IP"].nunique()
                  .sort_values(ascending=False).to_dict())

    return {
        "success": True, "sheet1_rows": int(len(sh1)), "sheet2_rows": int(len(sh2)),
        "unique_mr": int(sh1["MR"].nunique()), "unique_ip": int(sh1["IP"].nunique()),
        "relation": card["relation"], "max_ip_per_mr": card["max_ip_per_mr"],
        "avg_ip_per_mr": round(card["avg_ip_per_mr"], 2),
        "sh1_file": str(sh1_out), "sh2_file": str(sh2_out),
        "crosswalk_mr": str(mr_cw_path),
        "crosswalk_ip": str(ip_cw_path),
        "crosswalk_mr_stats": mr_stats,
        "crosswalk_ip_stats": ip_stats,
        "mr_ip_distribution": mr_ip_dist,
        "mr_map": mr_map,
        "ip_pair_map": ip_pair_map,
        "preview_sh1": sh1.head(5).to_dict(orient="records"),
        "preview_sh2": sh2.head(5).to_dict(orient="records"),
    }


# ============================================================
# VISUALIZATION ENGINE (Plotly) — theme-aware, 25 charts
# ============================================================
PALETTE = {
    "teal": "#0d7377", "teal2": "#14b8a6",
    "navy": "#1a2b4a", "navy2": "#263d63",
    "ivory": "#f1f5f9", "ink": "#0f172a",
    "warning": "#d97706", "danger": "#dc2626", "success": "#059669",
}

PLOTLY_LAYOUT_LIGHT = dict(
    template="plotly_white",
    font=dict(family="Inter, sans-serif", size=12, color="#0f172a"),
    margin=dict(l=40, r=20, t=50, b=40),
    paper_bgcolor="white", plot_bgcolor="white",
    colorway=[PALETTE["teal"], PALETTE["navy"], PALETTE["teal2"], PALETTE["navy2"],
              PALETTE["warning"], PALETTE["danger"], PALETTE["success"],
              "#8b5cf6", "#ec4899", "#f97316"],
)

PLOTLY_LAYOUT_DARK = dict(
    template="plotly_dark",
    font=dict(family="Inter, sans-serif", size=12, color="#e6edf7"),
    margin=dict(l=40, r=20, t=50, b=40),
    paper_bgcolor="#111a2c", plot_bgcolor="#111a2c",
    colorway=["#14b8a6", "#60a5fa", "#22d3ee", "#818cf8",
              "#f59e0b", "#ef4444", "#10b981",
              "#a78bfa", "#f472b6", "#fb923c"],
)


def _current_theme() -> str:
    try:
        t = request.cookies.get(THEME_COOKIE_NAME, "light")
        return "dark" if t == "dark" else "light"
    except Exception:
        return "light"


def _fig_to_html(fig, height=400):
    theme = _current_theme()
    layout = PLOTLY_LAYOUT_DARK if theme == "dark" else PLOTLY_LAYOUT_LIGHT
    fig.update_layout(height=height, autosize=True, **layout)
    return to_html(
        fig, full_html=False, include_plotlyjs=False,
        config={
            "displayModeBar": True, "displaylogo": False, "responsive": True,
            "modeBarButtonsToRemove": ["lasso2d", "select2d"],
            "toImageButtonOptions": {"format": "png", "filename": "chart", "scale": 2},
        },
    )


def build_visualizations(sh1: pd.DataFrame, sh2: pd.DataFrame,
                         job_id: str = None) -> dict:
    charts = {}
    if not PLOTLY_OK:
        return {"error": "Plotly not installed. Run: pip install plotly"}

    CHART_STEP = STAGE_WEIGHTS["charts"] / 25.0
    _done = {"n": 0}

    def _tick(label: str):
        _done["n"] += 1
        if job_id:
            with PROGRESS_LOCK:
                row = PROGRESS_STORE.get(job_id)
                if row:
                    row["pct"] = round(min(100.0, row["pct"] + CHART_STEP), 1)
                    row["stage"] = "Building charts"
                    row["detail"] = f"{_done['n']}/25 — {label}"

    sh1w = sh1.copy()
    if "DOA" in sh1w.columns:
        sh1w["DOA"] = pd.to_datetime(sh1w["DOA"], errors="coerce")
    if "DOD" in sh1w.columns:
        sh1w["DOD"] = pd.to_datetime(sh1w["DOD"], errors="coerce")
    if "DOA" in sh1w.columns and "DOD" in sh1w.columns:
        sh1w["LOS"] = (sh1w["DOD"] - sh1w["DOA"]).dt.days

    diag = sh1["Diagnosis"].fillna("").str.upper() if "Diagnosis" in sh1.columns else pd.Series([""] * len(sh1))

    def numeric_lab(name_pattern):
        d = sh2[sh2["TestName"].str.contains(name_pattern, case=False, na=False)].copy()
        d["Result_num"] = pd.to_numeric(d["Result"], errors="coerce")
        return d.dropna(subset=["Result_num"])

    # 1
    try:
        fig = px.histogram(sh1, x="Age", color="SexName", nbins=10, barmode="stack",
                           title="Age Distribution by Sex",
                           labels={"Age": "Age (years)", "count": "Patients"},
                           color_discrete_map={"Female": PALETTE["teal"], "Male": PALETTE["navy"]})
        charts["age_sex"] = _fig_to_html(fig, height=380)
    except Exception as e:
        charts["age_sex"] = f"<p class='warn'>Chart 1 skipped: {e}</p>"
    _tick("Age × Sex")

    # 2
    try:
        los_df = sh1w.dropna(subset=["LOS"]).sort_values("LOS")
        fig = px.bar(los_df, x="LOS", y="MR", orientation="h",
                     color="LOS", color_continuous_scale="Teal",
                     title="Length of Stay per Patient",
                     labels={"LOS": "Days", "MR": "Patient"})
        fig.update_layout(coloraxis_showscale=False)
        charts["los"] = _fig_to_html(fig, height=max(360, 28 * len(los_df)))
    except Exception as e:
        charts["los"] = f"<p class='warn'>Chart 2 skipped: {e}</p>"
    _tick("Length of Stay")

    # 3
    try:
        flags = {
            "Diabetes": diag.str.contains("DIABET"),
            "HTN": diag.str.contains("HYPERTENSION"),
            "CAD / ACS": diag.str.contains("CAD|NSTEMI|CORONARY|ACS"),
            "Anemia": diag.str.contains("ANEMIA|ANAEMIA"),
            "Alcohol": diag.str.contains("ALCOHOL"),
            "Infection": diag.str.contains("DENGUE|UTI|FEVER|HEPATITIS|PID|BRONCH"),
            "Thyroid": diag.str.contains("THYROID"),
            "Epilepsy": diag.str.contains("EPILEPSY|SEIZURE"),
        }
        counts = {k: int(v.sum()) for k, v in flags.items()}
        fig = px.bar(x=list(counts.keys()), y=list(counts.values()),
                     title=f"Comorbidity Frequency (n={len(sh1)})",
                     labels={"x": "Condition", "y": "Patients"})
        fig.update_traces(marker_color=PALETTE["navy"])
        charts["comorbidities"] = _fig_to_html(fig, height=380)
    except Exception as e:
        charts["comorbidities"] = f"<p class='warn'>Chart 3 skipped: {e}</p>"
    _tick("Comorbidity Frequency")

    # 4
    try:
        top = sh2["TestName"].value_counts().head(15).sort_values()
        fig = px.bar(x=top.values, y=top.index, orientation="h",
                     title="Top 15 Lab Tests by Frequency",
                     labels={"x": "Measurements", "y": ""})
        fig.update_traces(marker_color=PALETTE["teal"])
        charts["top_tests"] = _fig_to_html(fig, height=500)
    except Exception as e:
        charts["top_tests"] = f"<p class='warn'>Chart 4 skipped: {e}</p>"
    _tick("Top Lab Tests")

    # 5
    try:
        dept = sh2["DeptName"].value_counts().head(10)
        fig = px.pie(names=dept.index, values=dept.values,
                     title="Lab Tests by Department", hole=0.45)
        fig.update_traces(textposition="inside", textinfo="percent+label")
        charts["dept_pie"] = _fig_to_html(fig, height=420)
    except Exception as e:
        charts["dept_pie"] = f"<p class='warn'>Chart 5 skipped: {e}</p>"
    _tick("Lab Tests by Department")

    # 6
    try:
        hba1c = numeric_lab("HbA1c")
        if len(hba1c):
            fig = px.histogram(hba1c, x="Result_num", nbins=10,
                               title=f"HbA1c Distribution (n={len(hba1c)})",
                               labels={"Result_num": "HbA1c (%)"})
            fig.update_traces(marker_color=PALETTE["danger"])
            fig.add_vline(x=7.0, line_dash="dash", annotation_text="Target < 7%")
            fig.add_vline(x=9.0, line_dash="dot", annotation_text="Poor > 9%")
            charts["hba1c"] = _fig_to_html(fig, height=380)
        else:
            charts["hba1c"] = "<p class='warn'>No HbA1c data.</p>"
    except Exception as e:
        charts["hba1c"] = f"<p class='warn'>Chart 6 skipped: {e}</p>"
    _tick("HbA1c Distribution")

    # 7
    try:
        hb = numeric_lab("HAEMOGLOBIN")
        if len(hb):
            hb["_seq"] = hb.groupby("MR").cumcount()
            fig = px.line(hb, x="_seq", y="Result_num", color="MR", markers=True,
                          title="Serial Hemoglobin Trends",
                          labels={"_seq": "Sequence", "Result_num": "Hb (g/dL)", "MR": "Patient"})
            fig.add_hline(y=12, line_dash="dash", annotation_text="Lower limit")
            charts["hb_trends"] = _fig_to_html(fig, height=420)
        else:
            charts["hb_trends"] = "<p class='warn'>No HB data.</p>"
    except Exception as e:
        charts["hb_trends"] = f"<p class='warn'>Chart 7 skipped: {e}</p>"
    _tick("Serial Hemoglobin Trends")

    # 8
    try:
        plt_df = sh2[sh2["TestName"].str.contains("PLATELET", case=False, na=False)].copy()
        plt_df["Result_num"] = (plt_df["Result"].astype(str)
                                .str.extract(r"(\d+)")[0].astype(float))
        plt_df = plt_df.dropna(subset=["Result_num"])
        if len(plt_df):
            plt_df["_seq"] = plt_df.groupby("MR").cumcount()
            fig = px.line(plt_df, x="_seq", y="Result_num", color="MR", markers=True,
                          title="Platelet Count Trajectories",
                          labels={"_seq": "Sequence", "Result_num": "Platelets (/mm³)", "MR": "Patient"})
            fig.add_hline(y=150000, line_dash="dash", annotation_text="Normal > 150k")
            charts["plt_trends"] = _fig_to_html(fig, height=420)
        else:
            charts["plt_trends"] = "<p class='warn'>No platelet data.</p>"
    except Exception as e:
        charts["plt_trends"] = f"<p class='warn'>Chart 8 skipped: {e}</p>"
    _tick("Platelet Count Trajectories")

    # 9
    try:
        k = numeric_lab("Potassium")
        if len(k):
            fig = px.box(k, x="MR", y="Result_num", color="MR",
                         title="Potassium Distribution per Patient",
                         labels={"Result_num": "K⁺ (mEq/L)", "MR": "Patient"})
            fig.add_hline(y=3.5, line_dash="dash", annotation_text="Low limit")
            fig.add_hline(y=5.1, line_dash="dash", annotation_text="High limit")
            fig.update_layout(showlegend=False, xaxis_tickangle=-45)
            charts["potassium"] = _fig_to_html(fig, height=420)
        else:
            charts["potassium"] = "<p class='warn'>No K⁺ data.</p>"
    except Exception as e:
        charts["potassium"] = f"<p class='warn'>Chart 9 skipped: {e}</p>"
    _tick("Potassium Distribution")

    # 10
    try:
        lft = sh2[sh2["TestCategory"] == "Liver Function Test"].copy()
        lft["Result_num"] = pd.to_numeric(lft["Result"], errors="coerce")
        pivot = lft.pivot_table(index="MR", columns="TestName",
                                values="Result_num", aggfunc="max")
        if "Bilirubin Total" in pivot.columns and \
           "Aspartate Transaminase (AST/SGOT)" in pivot.columns:
            size_col = ("Alanine Transaminase (ALT/SGPT)"
                        if "Alanine Transaminase (ALT/SGPT)" in pivot.columns else None)
            fig = px.scatter(pivot.dropna(subset=["Bilirubin Total"]),
                             x="Bilirubin Total",
                             y="Aspartate Transaminase (AST/SGOT)",
                             color=pivot.index, size=size_col,
                             title="LFT Profile — Bilirubin vs AST",
                             labels={"x": "Bilirubin Total (mg/dL)", "y": "AST (IU/L)"})
            charts["lft_scatter"] = _fig_to_html(fig, height=420)
        else:
            charts["lft_scatter"] = "<p class='warn'>Not enough LFT data.</p>"
    except Exception as e:
        charts["lft_scatter"] = f"<p class='warn'>Chart 10 skipped: {e}</p>"
    _tick("LFT Scatter")

    # 11
    try:
        sex_counts = sh1["SexName"].value_counts()
        fig = px.pie(names=sex_counts.index, values=sex_counts.values,
                     title="Sex Ratio", hole=0.5,
                     color=sex_counts.index,
                     color_discrete_map={"Female": PALETTE["teal"], "Male": PALETTE["navy"]})
        fig.update_traces(textposition="inside", textinfo="percent+label")
        charts["sex_ratio"] = _fig_to_html(fig, height=380)
    except Exception as e:
        charts["sex_ratio"] = f"<p class='warn'>Chart 11 skipped: {e}</p>"
    _tick("Sex Ratio")

    # 12
    try:
        fig = px.histogram(sh1, x="Age", nbins=12,
                           title="Age Histogram (all patients)",
                           labels={"Age": "Age (years)", "count": "Patients"})
        fig.update_traces(marker_color=PALETTE["teal2"])
        charts["age_hist"] = _fig_to_html(fig, height=380)
    except Exception as e:
        charts["age_hist"] = f"<p class='warn'>Chart 12 skipped: {e}</p>"
    _tick("Age Histogram")

    # 13
    try:
        fig = px.histogram(sh1w.dropna(subset=["DOA"]), x="DOA", nbins=15,
                           title="Admissions by Date (DOA)",
                           labels={"DOA": "Date of Admission", "count": "Patients"})
        fig.update_traces(marker_color=PALETTE["navy"])
        charts["doa_hist"] = _fig_to_html(fig, height=380)
    except Exception as e:
        charts["doa_hist"] = f"<p class='warn'>Chart 13 skipped: {e}</p>"
    _tick("Admissions by Date")

    # 14
    try:
        fig = px.histogram(sh1w.dropna(subset=["DOD"]), x="DOD", nbins=15,
                           title="Discharges by Date (DOD)",
                           labels={"DOD": "Date of Discharge", "count": "Patients"})
        fig.update_traces(marker_color=PALETTE["warning"])
        charts["dod_hist"] = _fig_to_html(fig, height=380)
    except Exception as e:
        charts["dod_hist"] = f"<p class='warn'>Chart 14 skipped: {e}</p>"
    _tick("Discharges by Date")

    # 15
    try:
        los_df = sh1w.dropna(subset=["LOS"])
        if len(los_df):
            fig = px.box(los_df, x="SexName", y="LOS", color="SexName",
                         title="Length of Stay by Sex",
                         labels={"LOS": "Days", "SexName": "Sex"},
                         color_discrete_map={"Female": PALETTE["teal"], "Male": PALETTE["navy"]})
            fig.update_layout(showlegend=False)
            charts["los_by_sex"] = _fig_to_html(fig, height=380)
        else:
            charts["los_by_sex"] = "<p class='warn'>No LOS data.</p>"
    except Exception as e:
        charts["los_by_sex"] = f"<p class='warn'>Chart 15 skipped: {e}</p>"
    _tick("LOS by Sex")

    # 16
    try:
        cat_df = sh2.copy()
        cat_df["DeptName"] = cat_df["DeptName"].fillna("Unknown")
        cat_df["TestCategory"] = cat_df["TestCategory"].fillna("General")
        fig = px.sunburst(cat_df, path=["DeptName", "TestCategory"],
                          title="Lab Hierarchy — Department → Test Category")
        charts["sunburst"] = _fig_to_html(fig, height=520)
    except Exception as e:
        charts["sunburst"] = f"<p class='warn'>Chart 16 skipped: {e}</p>"
    _tick("Lab Sunburst")

    # 17
    try:
        ug = sh2[sh2["TestName"].str.contains("URINE GLUCOSE", case=False, na=False)].copy()
        ug["Result_cat"] = ug["Result"].astype(str).str.strip()
        counts = ug["Result_cat"].value_counts().head(8)
        fig = px.bar(x=counts.index, y=counts.values,
                     title="Urine Glucose Categories",
                     labels={"x": "Result", "y": "Frequency"})
        fig.update_traces(marker_color=PALETTE["danger"])
        charts["urine_glucose"] = _fig_to_html(fig, height=380)
    except Exception as e:
        charts["urine_glucose"] = f"<p class='warn'>Chart 17 skipped: {e}</p>"
    _tick("Urine Glucose")

    # 18
    try:
        up = sh2[sh2["TestName"].str.contains("URINE PROTEIN", case=False, na=False)].copy()
        up["Result_cat"] = up["Result"].astype(str).str.strip()
        counts = up["Result_cat"].value_counts().head(8)
        fig = px.bar(x=counts.index, y=counts.values,
                     title="Urine Protein Categories",
                     labels={"x": "Result", "y": "Frequency"})
        fig.update_traces(marker_color=PALETTE["warning"])
        charts["urine_protein"] = _fig_to_html(fig, height=380)
    except Exception as e:
        charts["urine_protein"] = f"<p class='warn'>Chart 18 skipped: {e}</p>"
    _tick("Urine Protein")

    # 19
    try:
        cr = numeric_lab("Creatinine")
        if len(cr):
            fig = px.histogram(cr, x="Result_num", nbins=15,
                               title=f"Creatinine Distribution (n={len(cr)})",
                               labels={"Result_num": "Creatinine (mg/dL)"})
            fig.update_traces(marker_color=PALETTE["navy"])
            fig.add_vline(x=1.2, line_dash="dash", annotation_text="Upper limit")
            charts["creatinine"] = _fig_to_html(fig, height=380)
        else:
            charts["creatinine"] = "<p class='warn'>No creatinine data.</p>"
    except Exception as e:
        charts["creatinine"] = f"<p class='warn'>Chart 19 skipped: {e}</p>"
    _tick("Creatinine Distribution")

    # 20
    try:
        na = numeric_lab("Sodium")
        if len(na):
            fig = px.box(na, x="MR", y="Result_num", color="MR",
                         title="Sodium Distribution per Patient",
                         labels={"Result_num": "Na⁺ (mEq/L)", "MR": "Patient"})
            fig.add_hline(y=135, line_dash="dash", annotation_text="Low limit")
            fig.add_hline(y=145, line_dash="dash", annotation_text="High limit")
            fig.update_layout(showlegend=False, xaxis_tickangle=-45)
            charts["sodium"] = _fig_to_html(fig, height=420)
        else:
            charts["sodium"] = "<p class='warn'>No sodium data.</p>"
    except Exception as e:
        charts["sodium"] = f"<p class='warn'>Chart 20 skipped: {e}</p>"
    _tick("Sodium Distribution")

    # 21
    try:
        gf = numeric_lab("Glucose Fasting")
        if len(gf):
            gf["_seq"] = gf.groupby("MR").cumcount()
            fig = px.line(gf, x="_seq", y="Result_num", color="MR", markers=True,
                          title="Fasting Glucose Trends",
                          labels={"_seq": "Sequence", "Result_num": "Glucose (mg/dL)", "MR": "Patient"})
            fig.add_hline(y=126, line_dash="dash", annotation_text="Diabetes threshold")
            charts["glucose_trend"] = _fig_to_html(fig, height=420)
        else:
            charts["glucose_trend"] = "<p class='warn'>No glucose data.</p>"
    except Exception as e:
        charts["glucose_trend"] = f"<p class='warn'>Chart 21 skipped: {e}</p>"
    _tick("Fasting Glucose Trends")

    # 22
    try:
        req = sh2[["RequestNo"]].dropna().drop_duplicates().copy()
        req["ReqDate"] = req["RequestNo"].astype(str).str.slice(2, 8)
        req["ReqDate"] = pd.to_datetime(req["ReqDate"], format="%y%m%d", errors="coerce")
        req = req.dropna(subset=["ReqDate"])
        if len(req):
            daily = req.groupby(req["ReqDate"].dt.date).size().reset_index(name="count")
            daily.columns = ["ReqDate", "count"]
            fig = px.line(daily, x="ReqDate", y="count", markers=True,
                          title="Lab Request Volume Over Time",
                          labels={"ReqDate": "Date", "count": "Requests"})
            fig.update_traces(line_color=PALETTE["teal"])
            charts["req_time"] = _fig_to_html(fig, height=380)
        else:
            charts["req_time"] = "<p class='warn'>Could not parse request dates.</p>"
    except Exception as e:
        charts["req_time"] = f"<p class='warn'>Chart 22 skipped: {e}</p>"
    _tick("Lab Request Volume")

    # 23
    try:
        doc_counts = sh1["DoctorName"].value_counts()
        fig = px.bar(x=doc_counts.index, y=doc_counts.values,
                     title="Patients per Doctor",
                     labels={"x": "Doctor", "y": "Patients"})
        fig.update_traces(marker_color=PALETTE["navy2"])
        charts["doctor_load"] = _fig_to_html(fig, height=380)
    except Exception as e:
        charts["doctor_load"] = f"<p class='warn'>Chart 23 skipped: {e}</p>"
    _tick("Patients per Doctor")

    # 24
    try:
        sc = sh1w.dropna(subset=["LOS"])
        fig = px.scatter(sc, x="Age", y="LOS", color="SexName", size="LOS",
                         hover_data=["MR", "Diagnosis"],
                         title="Age vs Length of Stay",
                         labels={"Age": "Age (years)", "LOS": "Days in Hospital"},
                         color_discrete_map={"Female": PALETTE["teal"], "Male": PALETTE["navy"]})
        charts["age_los"] = _fig_to_html(fig, height=420)
    except Exception as e:
        charts["age_los"] = f"<p class='warn'>Chart 24 skipped: {e}</p>"
    _tick("Age vs LOS")

    # 25
    try:
        key_tests = ["HAEMOGLOBIN", "PLATELET COUNT", "Glucose Fasting",
                     "Creatinine", "Bilirubin Total", "Potassium(K)",
                     "Sodium(Na)", "HbA1c - Glycated Hemoglobin"]
        wide = (sh2[sh2["TestName"].isin(key_tests)]
                .assign(Result_num=lambda d: pd.to_numeric(d["Result"], errors="coerce"))
                .pivot_table(index="MR", columns="TestName",
                             values="Result_num", aggfunc="max"))
        if wide.shape[1] >= 2:
            corr = wide.corr().round(2)
            fig = px.imshow(corr, text_auto=True, aspect="auto",
                            color_continuous_scale="RdBu_r", zmin=-1, zmax=1,
                            title="Lab Value Correlation Matrix")
            charts["corr_matrix"] = _fig_to_html(fig, height=520)
        else:
            charts["corr_matrix"] = "<p class='warn'>Not enough lab values to correlate.</p>"
    except Exception as e:
        charts["corr_matrix"] = f"<p class='warn'>Chart 25 skipped: {e}</p>"
    _tick("Correlation Matrix")

    return charts


# ============================================================
# INLINE CSS (theme-aware + fully responsive)
# ============================================================
CSS = """
:root {
  --teal-900:#062c30; --teal-800:#0a4a50; --teal-700:#0d7377; --teal-600:#14b8a6;
  --teal-100:#ccfbf1;
  --navy-900:#0f1e38; --navy-800:#1a2b4a; --navy-700:#263d63;
  --ivory-50:#f8fafc; --ivory-100:#f1f5f9; --ivory-200:#e2e8f0; --ivory-300:#cbd5e1;
  --ivory-400:#94a3b8; --ivory-500:#64748b;
  --ink-900:#0f172a; --ink-700:#334155;
  --success:#059669; --warning:#d97706; --danger:#dc2626;
  --radius-sm:8px; --radius-md:12px; --radius-lg:18px;
  --shadow-sm:0 1px 2px rgba(15,23,42,0.06),0 1px 3px rgba(15,23,42,0.04);
  --shadow-md:0 4px 12px rgba(15,23,42,0.08),0 2px 4px rgba(15,23,42,0.04);
  --shadow-lg:0 12px 32px rgba(15,23,42,0.10),0 4px 8px rgba(15,23,42,0.05);
  --font-sans:"Inter",-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif;
  --font-serif:"Source Serif 4",Georgia,serif;

  --bg-app:var(--ivory-50);
  --bg-surface:#ffffff;
  --bg-subtle:var(--ivory-100);
  --bg-hover:var(--ivory-50);
  --text-primary:var(--ink-900);
  --text-secondary:var(--ink-700);
  --text-muted:var(--ivory-500);
  --border-subtle:var(--ivory-200);
  --border-strong:var(--ivory-300);
  --accent:var(--teal-700);
  --accent-hover:var(--teal-800);
  --header-bg:#ffffff;
  --footer-bg:var(--navy-900);
  color-scheme: light;
}
[data-theme="dark"] {
  --ivory-50:#0b1220; --ivory-100:#111a2c; --ivory-200:#1c2740;
  --ivory-300:#2a3654; --ivory-400:#7c8aa8; --ivory-500:#94a3b8;
  --ink-900:#e6edf7; --ink-700:#c2cbdd;

  --bg-app:#0b1220;
  --bg-surface:#111a2c;
  --bg-subtle:#172239;
  --bg-hover:#1a2742;
  --text-primary:#e6edf7;
  --text-secondary:#c2cbdd;
  --text-muted:#94a3b8;
  --border-subtle:#1f2c47;
  --border-strong:#2a3654;
  --accent:var(--teal-600);
  --accent-hover:#0d7377;
  --header-bg:#0e1626;
  --footer-bg:#060c17;

  --shadow-sm:0 1px 2px rgba(0,0,0,0.35);
  --shadow-md:0 4px 14px rgba(0,0,0,0.45);
  --shadow-lg:0 16px 40px rgba(0,0,0,0.55);
  color-scheme: dark;
}
*{box-sizing:border-box;margin:0;padding:0}
body{font-family:var(--font-sans);background:var(--bg-app);color:var(--text-primary);
  line-height:1.55;min-height:100vh;display:flex;flex-direction:column}
a{color:inherit;text-decoration:none}
img{max-width:100%;display:block}

body,.site-header,.card,.stat-card,.viz-block,.data-table,.data-table th,
input,select,.btn-ghost,.btn-sm,.subnav,.auth-card,.overlay-card,
.data-table td,.site-footer,.dropzone,.progress-track{
  transition:background-color .25s ease,color .25s ease,border-color .25s ease;
}

.site-header{background:var(--header-bg);border-bottom:1px solid var(--border-subtle);
  box-shadow:var(--shadow-sm);position:sticky;top:0;z-index:100}
.header-band{height:4px;background:linear-gradient(90deg,var(--teal-700) 0%,var(--teal-700) 35%,var(--navy-800) 65%,var(--navy-800) 100%)}
.header-inner{max-width:1280px;margin:0 auto;padding:16px 32px;display:flex;
  align-items:center;justify-content:space-between;gap:24px}
.brand-block{display:flex;align-items:center;gap:14px;flex-wrap:wrap}
.logo-circle{width:52px;height:52px;border-radius:50%;display:flex;align-items:center;
  justify-content:center;font-weight:700;font-size:11px;color:#fff;flex-shrink:0;
  letter-spacing:.5px;text-align:center;line-height:1.1;box-shadow:0 2px 6px rgba(15,23,42,.12)}
.logo-circle.ecet{background:linear-gradient(135deg,#1a2b4a,#263d63)}
.logo-circle.smvmch{background:linear-gradient(135deg,#0d7377,#14b8a6)}
.brand-text{line-height:1.25;max-width:320px}
.brand-title{font-family:var(--font-serif);font-size:.92rem;font-weight:700;color:var(--text-primary)}
.brand-sub{font-size:.7rem;color:var(--text-muted);font-weight:500;margin-top:2px}
.brand-divider{font-size:1.5rem;color:var(--border-strong);font-weight:300;margin:0 10px}
.user-actions{display:flex;align-items:center;gap:12px}
.user-chip{display:flex;align-items:center;gap:10px;padding:6px 14px 6px 6px;
  background:var(--bg-subtle);border:1px solid var(--border-subtle);border-radius:999px;
  cursor:pointer;transition:all .15s}
.user-chip:hover{background:var(--bg-hover);border-color:var(--accent)}
.user-avatar{width:32px;height:32px;border-radius:50%;background:var(--accent);
  color:#fff;display:flex;align-items:center;justify-content:center;
  font-weight:600;font-size:.9rem}
.user-meta{line-height:1.15}
.user-name{font-size:.85rem;font-weight:600;color:var(--text-primary)}
.user-role{font-size:.68rem;color:var(--text-muted);text-transform:uppercase;letter-spacing:.5px}
.btn-ghost{padding:8px 14px;border-radius:var(--radius-sm);border:1px solid var(--border-strong);
  background:var(--bg-surface);color:var(--text-secondary);font-size:.85rem;font-weight:600;cursor:pointer;
  transition:all .15s;display:inline-flex;align-items:center;gap:6px;font-family:inherit;
  min-height:38px}
.btn-ghost:hover{border-color:var(--accent);color:var(--accent);background:var(--bg-hover)}

.theme-toggle{
  width:38px;height:38px;border-radius:50%;
  display:inline-flex;align-items:center;justify-content:center;
  background:var(--bg-subtle);border:1px solid var(--border-subtle);
  color:var(--text-primary);cursor:pointer;
  transition:transform .2s,background .2s,border-color .2s,color .2s;
  flex-shrink:0;
}
.theme-toggle:hover{background:var(--bg-hover);border-color:var(--accent);
  color:var(--accent);transform:rotate(15deg)}
.theme-toggle svg{width:18px;height:18px;stroke:currentColor;fill:none;
  stroke-width:1.8;stroke-linecap:round;stroke-linejoin:round}
.theme-toggle .icon-sun{display:none}
.theme-toggle .icon-moon{display:block}
[data-theme="dark"] .theme-toggle .icon-sun{display:block}
[data-theme="dark"] .theme-toggle .icon-moon{display:none}

.subnav{background:var(--bg-subtle);border-top:1px solid var(--border-subtle)}
.subnav-inner{max-width:1280px;margin:0 auto;padding:8px 32px;display:flex;
  align-items:center;gap:8px;font-size:.8rem;color:var(--text-muted);flex-wrap:wrap}
.subnav-tag{font-weight:600;color:var(--text-primary);text-transform:uppercase;letter-spacing:.6px;font-size:.7rem}
.subnav-sep{color:var(--border-strong)}
.subnav-current{color:var(--text-secondary);font-weight:500}
.subnav-links{margin-left:auto;display:flex;gap:6px;flex-wrap:wrap}
.subnav-links a{color:var(--text-muted);font-weight:500;
  display:inline-flex;align-items:center;gap:6px;
  padding:6px 10px;border-radius:var(--radius-sm);
  transition:background .15s,color .15s}
.subnav-links a:hover{color:var(--accent);background:var(--bg-surface)}

.nav-icon{width:16px;height:16px;flex-shrink:0;stroke:currentColor;fill:none;
  stroke-width:1.8;stroke-linecap:round;stroke-linejoin:round}
.user-chip .nav-icon{width:18px;height:18px}
.btn-ghost .nav-icon{width:15px;height:15px}
.btn-primary .nav-icon,.btn-secondary .nav-icon,.btn-download .nav-icon,.btn-danger .nav-icon{width:16px;height:16px}

.site-main{flex:1;padding:32px 0 48px}
.container{max-width:1280px;margin:0 auto;padding:0 32px}

.flash-stack{display:flex;flex-direction:column;gap:10px;margin-bottom:24px}
.alert{padding:12px 18px;border-radius:var(--radius-md);font-size:.9rem;
  border-left:4px solid;background:var(--bg-surface);box-shadow:var(--shadow-sm)}
.alert-error{border-color:var(--danger);color:#7f1d1d;background:#fef2f2}
.alert-success{border-color:var(--success);color:#064e3b;background:#ecfdf5}
.alert-warning{border-color:var(--warning);color:#78350f;background:#fffbeb}
[data-theme="dark"] .alert-error{background:#3a1111;color:#fecaca}
[data-theme="dark"] .alert-success{background:#0d2f22;color:#a7f3d0}
[data-theme="dark"] .alert-warning{background:#3a2c0e;color:#fde68a}

.page-header{margin-bottom:28px}
.page-header h1{font-family:var(--font-serif);font-size:1.75rem;font-weight:700;
  color:var(--text-primary);margin-bottom:6px;letter-spacing:-.3px}
.page-header p{color:var(--text-muted);font-size:.95rem}

.card{background:var(--bg-surface);border:1px solid var(--border-subtle);
  border-radius:var(--radius-lg);padding:32px;margin-bottom:24px;box-shadow:var(--shadow-sm)}
.card h2{font-family:var(--font-serif);font-size:1.1rem;font-weight:700;
  color:var(--text-primary);margin:0 0 20px;padding-bottom:12px;
  border-bottom:1px solid var(--border-subtle);display:flex;align-items:center;gap:10px}

.dropzone{border:2px dashed var(--border-strong);border-radius:var(--radius-lg);
  padding:48px 32px;text-align:center;cursor:pointer;transition:all .2s;
  background:var(--bg-app);margin-bottom:24px}
.dropzone:hover,.dropzone.dragover{border-color:var(--accent);background:var(--bg-hover)}
.dropzone-label{display:block;cursor:pointer}
.dropzone-icon{font-size:2.6rem;display:block;margin-bottom:14px;opacity:.7}
#dropzone-text{color:var(--text-muted);font-size:.95rem;font-weight:500}

.grid-2,.grid-3,.grid-4{display:grid;gap:18px;margin-bottom:20px}
.grid-2{grid-template-columns:repeat(2,1fr)}
.grid-3{grid-template-columns:repeat(3,1fr)}
.grid-4{grid-template-columns:repeat(4,1fr)}
label{display:flex;flex-direction:column;gap:6px;font-size:.85rem;
  font-weight:500;color:var(--text-secondary)}
input[type="text"],input[type="number"],input[type="email"],input[type="password"],
input[type="tel"],select{
  padding:11px 14px;border-radius:var(--radius-sm);border:1px solid var(--border-strong);
  background:var(--bg-surface);color:var(--text-primary);font-size:.95rem;outline:none;
  transition:border-color .15s,box-shadow .15s;font-family:inherit;width:100%}
input:focus,select:focus{border-color:var(--accent);box-shadow:0 0 0 3px rgba(13,115,119,.18)}
[data-theme="dark"] input:focus,[data-theme="dark"] select:focus{
  box-shadow:0 0 0 3px rgba(20,184,166,.25);
}

.btn-primary,.btn-secondary,.btn-download,.btn-danger,.btn-sm{
  display:inline-flex;align-items:center;justify-content:center;gap:8px;
  padding:12px 24px;border-radius:var(--radius-sm);
  border:none;font-size:.95rem;font-weight:600;cursor:pointer;transition:all .15s;
  letter-spacing:.1px;text-decoration:none;font-family:inherit;min-height:44px}
.btn-primary{background:var(--accent);color:#fff;width:100%;padding:14px 24px;
  font-size:1rem;box-shadow:var(--shadow-sm)}
.btn-primary:hover{background:var(--accent-hover);box-shadow:var(--shadow-md);transform:translateY(-1px)}
.btn-primary:disabled{opacity:.6;cursor:not-allowed;transform:none}
.btn-secondary{background:var(--bg-subtle);color:var(--text-secondary);
  border:1px solid var(--border-strong);margin-top:16px}
.btn-secondary:hover{background:var(--bg-hover)}
.btn-download{background:var(--navy-800);color:#fff;box-shadow:var(--shadow-sm)}
.btn-download:hover{background:var(--navy-900);box-shadow:var(--shadow-md)}
.btn-danger{background:var(--danger);color:#fff;width:100%}
.btn-danger:hover{background:#b91c1c}
.btn-sm{padding:6px 12px;font-size:.78rem;border-radius:var(--radius-sm);
  background:var(--bg-subtle);color:var(--text-secondary);border:1px solid var(--border-strong);
  cursor:pointer;font-family:inherit;min-height:32px}
.btn-sm:hover{background:var(--bg-hover)}
.btn-sm.primary{background:var(--accent);color:#fff;border-color:var(--accent)}
.btn-sm.primary:hover{background:var(--accent-hover)}
.btn-sm.danger{background:var(--danger);color:#fff;border-color:var(--danger)}
.btn-sm.danger:hover{background:#b91c1c}

.download-row{display:flex;flex-wrap:wrap;gap:12px;margin-bottom:16px}

.stats-grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(160px,1fr));
  gap:16px;margin-bottom:28px}
.stat-card{background:var(--bg-surface);border:1px solid var(--border-subtle);
  border-radius:var(--radius-md);padding:22px 18px;text-align:center;
  box-shadow:var(--shadow-sm);transition:all .15s}
.stat-card:hover{box-shadow:var(--shadow-md);transform:translateY(-2px)}
.stat-value{font-family:var(--font-serif);font-size:2rem;font-weight:700;
  color:var(--accent);line-height:1;margin-bottom:8px}
.stat-label{font-size:.72rem;color:var(--text-muted);text-transform:uppercase;
  letter-spacing:.8px;font-weight:600}

.table-scroll{overflow:auto;max-height:520px;border-radius:var(--radius-md);
  border:1px solid var(--border-subtle);-webkit-overflow-scrolling:touch}
.data-table{width:100%;border-collapse:collapse;font-size:.85rem}
.data-table th,.data-table td{padding:10px 14px;text-align:left;
  border-bottom:1px solid var(--border-subtle)}
.data-table th{background:var(--bg-subtle);color:var(--text-primary);font-weight:600;
  font-size:.78rem;text-transform:uppercase;letter-spacing:.4px;position:sticky;top:0;
  backdrop-filter:blur(6px)}
.data-table tr:hover td{background:var(--bg-hover)}
.data-table tr:last-child td{border-bottom:none}

.preview-note{background:var(--bg-subtle);border-left:3px solid var(--accent);
  padding:12px 16px;border-radius:var(--radius-sm);font-size:.85rem;
  color:var(--text-secondary);margin-bottom:22px}
.warn{background:#fffbeb;border:1px solid #fcd34d;border-left:4px solid var(--warning);
  padding:12px 16px;border-radius:var(--radius-sm);font-size:.85rem;
  color:#78350f;margin-top:18px}
[data-theme="dark"] .warn{background:#3a2c0e;color:#fde68a;border-color:#7a5c10}
code{background:var(--bg-subtle);border:1px solid var(--border-subtle);padding:2px 6px;
  border-radius:4px;font-family:"JetBrains Mono","Courier New",monospace;
  font-size:.82rem;color:var(--text-primary)}

.auth-wrapper{display:flex;justify-content:center;align-items:center;
  min-height:calc(100vh - 320px);padding:24px 0}
.auth-card{background:var(--bg-surface);border:1px solid var(--border-subtle);
  border-radius:var(--radius-lg);padding:40px;width:100%;max-width:420px;
  box-shadow:var(--shadow-lg)}
.auth-card h1{font-family:var(--font-serif);font-size:1.6rem;color:var(--text-primary);
  text-align:center;margin-bottom:6px}
.auth-subtitle{text-align:center;color:var(--text-muted);font-size:.88rem;margin-bottom:28px}
.auth-form{display:flex;flex-direction:column;gap:18px}
.auth-form .btn-primary{margin-top:6px}
.auth-footer{text-align:center;margin-top:24px;font-size:.88rem;color:var(--text-muted)}
.auth-footer a{color:var(--accent);font-weight:600}
.auth-footer a:hover{text-decoration:underline}
.req{color:var(--danger)}
.checkbox-label{display:flex;flex-direction:row;align-items:center;gap:8px;
  font-size:.85rem;cursor:pointer}
.checkbox-label input{width:auto;margin:0}

.site-footer{background:var(--footer-bg);color:var(--text-secondary);margin-top:auto}
.footer-inner{max-width:1280px;margin:0 auto;padding:40px 32px 24px;display:grid;
  grid-template-columns:repeat(auto-fit,minmax(220px,1fr));gap:32px}
.footer-col{font-size:.82rem;line-height:1.6}
.footer-brand{font-family:var(--font-serif);font-size:1.1rem;font-weight:700;
  color:#fff;margin-bottom:8px;letter-spacing:.3px}
.footer-heading{font-size:.72rem;font-weight:700;color:var(--teal-600);
  text-transform:uppercase;letter-spacing:1px;margin-bottom:8px}
.footer-desc{color:#94a3b8;font-size:.8rem}
.footer-desc strong{color:#e2e8f0}
.footer-copyright{border-top:1px solid rgba(255,255,255,.08);background:var(--teal-900)}
.copyright-inner{max-width:1280px;margin:0 auto;padding:16px 32px;display:flex;
  flex-wrap:wrap;align-items:center;justify-content:center;gap:10px;
  font-size:.75rem;color:#94a3b8;text-align:center}
.copyright-inner strong{color:var(--teal-600);font-weight:700}
.copyright-sep{opacity:.4}

.viz-grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(460px,1fr));
  gap:24px;margin-top:12px}
.viz-block{background:var(--bg-surface);border:1px solid var(--border-subtle);
  border-radius:var(--radius-md);padding:16px 16px 8px;
  box-shadow:var(--shadow-sm);transition:box-shadow .15s, transform .15s;overflow:hidden}
.viz-block:hover{box-shadow:var(--shadow-md);transform:translateY(-1px)}
.viz-block.viz-full{grid-column:1 / -1}
.viz-title{font-family:var(--font-serif);font-size:.95rem;font-weight:700;
  color:var(--text-primary);margin:0 0 12px;padding-bottom:8px;
  border-bottom:1px solid var(--border-subtle);letter-spacing:.2px}
.viz-body{width:100%;overflow:hidden}
.viz-body .plotly-graph-div{width:100% !important}

.audit-badge{display:inline-block;padding:2px 8px;border-radius:4px;
  font-size:.7rem;font-weight:700;text-transform:uppercase;letter-spacing:.5px}
.badge-success{background:#dcfce7;color:#166534}
.badge-failed {background:#fee2e2;color:#991b1b}
.badge-denied {background:#fef3c7;color:#92400e}
.badge-info   {background:#dbeafe;color:#1e40af}
.badge-skipped{background:#e0e7ff;color:#3730a3}
[data-theme="dark"] .badge-success{background:#0d2f22;color:#86efac}
[data-theme="dark"] .badge-failed {background:#3a1111;color:#fca5a5}
[data-theme="dark"] .badge-denied {background:#3a2c0e;color:#fcd34d}
[data-theme="dark"] .badge-info   {background:#12223d;color:#93c5fd}
[data-theme="dark"] .badge-skipped{background:#1e1b4b;color:#a5b4fc}

.audit-filter{display:grid;grid-template-columns:repeat(auto-fit,minmax(160px,1fr));
  gap:12px;margin-bottom:20px}
.audit-filter label{font-size:.78rem}
.audit-details{font-family:"JetBrains Mono","Courier New",monospace;
  font-size:.72rem;color:var(--text-muted);word-break:break-all;max-width:380px}

.role-badge{display:inline-block;padding:2px 8px;border-radius:4px;
  font-size:.7rem;font-weight:700;text-transform:uppercase;letter-spacing:.5px}
.role-admin  {background:#dbeafe;color:#1e40af}
.role-auditor{background:#fef3c7;color:#92400e}
.role-user   {background:#f1f5f9;color:#334155}
[data-theme="dark"] .role-admin  {background:#12223d;color:#93c5fd}
[data-theme="dark"] .role-auditor{background:#3a2c0e;color:#fcd34d}
[data-theme="dark"] .role-user   {background:#1c2740;color:#cbd5e1}

.status-dot{display:inline-block;width:8px;height:8px;border-radius:50%;
  margin-right:6px;vertical-align:middle}
.dot-active  {background:var(--success)}
.dot-inactive{background:var(--danger)}
.row-actions{display:flex;gap:6px;flex-wrap:wrap}

.progress-wrap{margin:14px 0 6px}
.progress-label{display:flex;justify-content:space-between;align-items:center;
  font-size:.78rem;color:var(--text-muted);font-weight:600;margin-bottom:6px;
  letter-spacing:.3px;text-transform:uppercase}
.progress-label .pct{color:var(--accent);font-family:var(--font-serif);
  font-size:.95rem;font-weight:700;letter-spacing:0}
.progress-track{position:relative;width:100%;height:12px;border-radius:999px;
  background:var(--bg-subtle);overflow:hidden;box-shadow:inset 0 1px 2px rgba(15,23,42,.06)}
.progress-track.tall{height:16px}
.progress-track.thin{height:6px}
.progress-fill{position:absolute;top:0;left:0;bottom:0;
  background:linear-gradient(90deg,var(--teal-700),var(--teal-600));
  border-radius:999px;transition:width .35s ease;width:0%}
.progress-fill.navy{background:linear-gradient(90deg,var(--navy-800),var(--navy-700))}
.progress-fill.success{background:linear-gradient(90deg,#047857,#059669)}
.progress-fill.warning{background:linear-gradient(90deg,#b45309,#d97706)}
.progress-fill.danger{background:linear-gradient(90deg,#b91c1c,#dc2626)}
.progress-fill.striped{
  background-image:linear-gradient(45deg,rgba(255,255,255,.18) 25%,transparent 25%,
    transparent 50%,rgba(255,255,255,.18) 50%,rgba(255,255,255,.18) 75%,
    transparent 75%,transparent);
  background-size:22px 22px;
  animation:pstripes 1s linear infinite;
}
@keyframes pstripes{
  from{background-position:0 0}
  to{background-position:22px 0}
}
.progress-fill.indeterminate{
  width:35% !important;
  animation:pslide 1.4s ease-in-out infinite;
}
@keyframes pslide{
  0%{left:-35%}
  50%{left:35%}
  100%{left:100%}
}
.progress-mini{display:inline-block;width:70px;height:6px;border-radius:999px;
  background:var(--bg-subtle);vertical-align:middle;overflow:hidden;margin-left:6px}
.progress-mini .fill{display:block;height:100%;
  background:linear-gradient(90deg,var(--teal-700),var(--teal-600));border-radius:999px}
.progress-mini .fill.failed{background:linear-gradient(90deg,#b91c1c,#dc2626)}
.progress-mini .fill.rejected{background:linear-gradient(90deg,#b45309,#d97706)}
.progress-mini .fill.skipped{background:linear-gradient(90deg,#4338ca,#6366f1)}

.live-progress{margin-top:8px}
.live-stage{font-size:.9rem;color:var(--text-primary);font-weight:600;
  margin-bottom:4px;letter-spacing:.1px}
.live-detail{font-size:.78rem;color:var(--text-muted);margin-top:6px;
  min-height:1.1rem;font-family:"JetBrains Mono","Courier New",monospace}
.live-pct{font-family:var(--font-serif);font-size:1.4rem;font-weight:700;
  color:var(--accent);line-height:1}

.ratio-bar{display:flex;width:100%;height:14px;border-radius:999px;overflow:hidden;
  background:var(--bg-subtle);box-shadow:inset 0 1px 2px rgba(15,23,42,.06);
  margin:10px 0 6px}
.ratio-seg{height:100%;transition:width .3s}
.ratio-seg.s1{background:linear-gradient(90deg,#047857,#059669)}
.ratio-seg.s2{background:linear-gradient(90deg,#b91c1c,#dc2626)}
.ratio-seg.s3{background:linear-gradient(90deg,#b45309,#d97706)}
.ratio-seg.s4{background:linear-gradient(90deg,var(--navy-800),var(--navy-700))}
.ratio-legend{display:flex;flex-wrap:wrap;gap:14px;font-size:.78rem;
  color:var(--text-muted);margin-top:6px}
.ratio-legend .swatch{display:inline-block;width:10px;height:10px;border-radius:3px;
  margin-right:6px;vertical-align:middle}
.ratio-legend .swatch.s1{background:var(--success)}
.ratio-legend .swatch.s2{background:var(--danger)}
.ratio-legend .swatch.s3{background:var(--warning)}
.ratio-legend .swatch.s4{background:var(--navy-800)}

.overlay{position:fixed;inset:0;background:rgba(15,23,42,.65);z-index:9999;
  display:none;align-items:center;justify-content:center;padding:20px;
  backdrop-filter:blur(2px)}
.overlay.on{display:flex}
.overlay-card{background:var(--bg-surface);border-radius:var(--radius-lg);padding:28px 32px;
  width:100%;max-width:520px;box-shadow:var(--shadow-lg)}
.overlay-card h3{font-family:var(--font-serif);font-size:1.15rem;color:var(--text-primary);
  margin-bottom:10px}
.overlay-card p{font-size:.85rem;color:var(--text-muted);margin-bottom:16px}
.spinner{width:44px;height:44px;border-radius:50%;margin:0 auto 16px;
  border:4px solid var(--border-subtle);border-top-color:var(--accent);
  animation:pspin .9s linear infinite}
@keyframes pspin{to{transform:rotate(360deg)}}

*:focus-visible{
  outline:2px solid var(--accent);
  outline-offset:2px;
  border-radius:6px;
}
::-webkit-scrollbar{width:10px;height:10px}
::-webkit-scrollbar-track{background:var(--bg-subtle)}
::-webkit-scrollbar-thumb{
  background:var(--border-strong);border-radius:8px;
  border:2px solid var(--bg-subtle);
}
::-webkit-scrollbar-thumb:hover{background:var(--accent)}

@media (max-width:1024px){
  .header-inner{padding:14px 24px;gap:16px}
  .brand-text{max-width:240px}
  .brand-title{font-size:.86rem}
  .brand-sub{font-size:.66rem}
  .container{padding:0 24px}
  .viz-grid{grid-template-columns:1fr}
  .grid-3{grid-template-columns:repeat(2,1fr)}
  .grid-4{grid-template-columns:repeat(2,1fr)}
  .subnav-inner{padding:8px 24px}
}

@media (max-width:760px){
  .site-main{padding:20px 0 32px}
  .container{padding:0 16px}

  .header-inner{
    flex-direction:row;align-items:center;
    padding:12px 16px;gap:12px;flex-wrap:wrap;
  }
  .brand-block{flex:1 1 auto;min-width:0;gap:10px}
  .brand-text{max-width:none;min-width:0}
  .brand-title{font-size:.8rem;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
  .brand-sub{display:none}
  .brand-divider{display:none}
  .logo-circle{width:38px;height:38px;font-size:9px}
  .logo-circle.smvmch{display:none}

  .user-actions{gap:8px}
  .user-chip{padding:4px 10px 4px 4px}
  .user-avatar{width:28px;height:28px;font-size:.8rem}
  .user-name{font-size:.78rem}
  .user-role{display:none}
  .btn-ghost span{display:none}
  .btn-ghost{padding:8px 10px}
  .theme-toggle{width:34px;height:34px}
  .theme-toggle svg{width:16px;height:16px}

  .subnav-inner{padding:8px 16px;gap:6px}
  .subnav-tag,.subnav-sep{display:none}
  .subnav-links{
    margin-left:0;width:100%;
    overflow-x:auto;flex-wrap:nowrap;
    -webkit-overflow-scrolling:touch;
    scrollbar-width:none;padding-bottom:2px;
  }
  .subnav-links::-webkit-scrollbar{display:none}
  .subnav-links a{flex-shrink:0;font-size:.78rem;padding:6px 10px}

  .page-header h1{font-size:1.35rem}
  .page-header p{font-size:.85rem}
  .card{padding:20px 16px;border-radius:var(--radius-md)}
  .card h2{font-size:1rem}

  .grid-2,.grid-3,.grid-4{grid-template-columns:1fr;gap:12px}

  .stats-grid{grid-template-columns:repeat(2,1fr);gap:10px}
  .stat-card{padding:14px 10px}
  .stat-value{font-size:1.35rem}
  .stat-label{font-size:.62rem;letter-spacing:.4px}

  .dropzone{padding:28px 16px}
  .dropzone-icon{font-size:2rem;margin-bottom:8px}
  #dropzone-text{font-size:.85rem}

  .table-scroll{max-height:420px}
  .data-table{font-size:.78rem;min-width:640px}
  .data-table th,.data-table td{padding:8px 10px}

  .audit-filter{grid-template-columns:1fr}
  .audit-details{max-width:160px}

  .download-row{flex-direction:column}
  .download-row .btn-download{width:100%}

  .auth-wrapper{min-height:auto;padding:16px 0}
  .auth-card{padding:24px 18px}
  .auth-card h1{font-size:1.35rem}

  .viz-grid{grid-template-columns:1fr;gap:14px}
  .viz-block{padding:12px 10px 6px}

  .overlay-card{padding:22px 18px}
  .overlay-card h3{font-size:1rem}
  .live-pct{font-size:1.15rem}

  .footer-inner{padding:28px 16px 18px;gap:20px;grid-template-columns:1fr}
  .copyright-inner{padding:12px 16px;font-size:.7rem;gap:6px}
  .copyright-sep{display:none}

  .progress-mini{width:50px}
}

@media (max-width:420px){
  .stats-grid{grid-template-columns:1fr}
  .page-header h1{font-size:1.2rem}
  .brand-title{font-size:.74rem}
  .logo-circle{width:34px;height:34px;font-size:8px}
  .btn-ghost{padding:7px 8px}
  .subnav-links a span{display:none}
  .subnav-links a{padding:8px 10px}
}

@media (min-width:1400px){
  .container,.header-inner,.subnav-inner,.footer-inner,.copyright-inner{max-width:1440px}
}
"""


# ============================================================
# INLINE HTML TEMPLATES
# ============================================================
BASE_TEMPLATE = """
<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8" />
<meta name="viewport" content="width=device-width, initial-scale=1.0, viewport-fit=cover" />
<meta name="theme-color" content="#0d7377" media="(prefers-color-scheme: light)" />
<meta name="theme-color" content="#0b1220" media="(prefers-color-scheme: dark)" />
<title>{% block title %}Clinical De-ID Console · ECET × SMVMCH{% endblock %}</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600;700&family=Source+Serif+4:wght@600;700&display=swap" rel="stylesheet">
<script>
(function(){
  try {
    var t = localStorage.getItem('theme');
    if (!t) {
      var m = document.cookie.match(/(?:^|; )theme=([^;]+)/);
      t = m ? decodeURIComponent(m[1]) : null;
    }
    if (!t) {
      t = window.matchMedia('(prefers-color-scheme: dark)').matches ? 'dark' : 'light';
    }
    document.documentElement.setAttribute('data-theme', t);
  } catch(e) { document.documentElement.setAttribute('data-theme','light'); }
})();
</script>
<style>{{ css|safe }}</style>
</head>
<body>
<header class="site-header">
  <div class="header-band"></div>
  <div class="header-inner">
    <div class="brand-block">
      <div class="logo-circle ecet">ECET</div>
      <div class="brand-text">
        <div class="brand-title">EASA College of Engineering and Technology</div>
        <div class="brand-sub">Centre of Excellence — AIMAA · Dept. of AI &amp; Data Science</div>
      </div>
      <div class="brand-divider">×</div>
      <div class="logo-circle smvmch">SMVMCH</div>
      <div class="brand-text">
        <div class="brand-title">Sri Manakula Vinayagar Medical College and Hospital</div>
        <div class="brand-sub">Department of General Medicine</div>
      </div>
    </div>
    <div class="user-actions">
      <button type="button" class="theme-toggle" id="themeToggle"
              aria-label="Toggle dark mode" title="Toggle theme">
        <svg class="icon-moon" viewBox="0 0 24 24">
          <path d="M21 12.79A9 9 0 1 1 11.21 3 7 7 0 0 0 21 12.79z"/>
        </svg>
        <svg class="icon-sun" viewBox="0 0 24 24">
          <circle cx="12" cy="12" r="4"/>
          <path d="M12 2v2M12 20v2M4.93 4.93l1.41 1.41M17.66 17.66l1.41 1.41M2 12h2M20 12h2M6.34 17.66l-1.41 1.41M19.07 4.93l-1.41 1.41"/>
        </svg>
      </button>

      {% if user %}
        <a href="{{ url_for('profile_page') }}" class="user-chip" title="View profile">
          <span class="user-avatar">{{ user.username[0]|upper }}</span>
          <div class="user-meta">
            <div class="user-name">{{ user.username }}</div>
            <div class="user-role">{{ user.role }}</div>
          </div>
        </a>
        <a href="{{ url_for('logout_redirect') }}" class="btn-ghost">
          <svg class="nav-icon" viewBox="0 0 24 24"><path d="M9 21H5a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h4"/><polyline points="16 17 21 12 16 7"/><line x1="21" y1="12" x2="9" y2="12"/></svg>
          <span>Sign out</span>
        </a>
      {% else %}
        <a href="{{ url_for('login_page') }}" class="btn-ghost">
          <svg class="nav-icon" viewBox="0 0 24 24"><path d="M15 3h4a2 2 0 0 1 2 2v14a2 2 0 0 1-2 2h-4"/><polyline points="10 17 15 12 10 7"/><line x1="15" y1="12" x2="3" y2="12"/></svg>
          <span>Sign in</span>
        </a>
      {% endif %}
    </div>
  </div>
  <div class="subnav">
    <div class="subnav-inner">
      <span class="subnav-tag">Clinical Data Governance</span>
      <span class="subnav-sep">›</span>
      <span class="subnav-current">{% block breadcrumb %}De-identification Console{% endblock %}</span>
      <nav class="subnav-links">
        <a href="{{ url_for('index') }}">
          <svg class="nav-icon" viewBox="0 0 24 24"><rect x="3" y="3" width="7" height="7" rx="1"/><rect x="14" y="3" width="7" height="7" rx="1"/><rect x="3" y="14" width="7" height="7" rx="1"/><rect x="14" y="14" width="7" height="7" rx="1"/></svg>
          <span>Console</span>
        </a>
        <a href="{{ url_for('dashboard') }}">
          <svg class="nav-icon" viewBox="0 0 24 24"><line x1="18" y1="20" x2="18" y2="10"/><line x1="12" y1="20" x2="12" y2="4"/><line x1="6" y1="20" x2="6" y2="14"/></svg>
          <span>Dashboard</span>
        </a>
        {% if user %}
        <a href="{{ url_for('profile_page') }}">
          <svg class="nav-icon" viewBox="0 0 24 24"><path d="M20 21v-2a4 4 0 0 0-4-4H8a4 4 0 0 0-4 4v2"/><circle cx="12" cy="7" r="4"/></svg>
          <span>Profile</span>
        </a>
        {% endif %}
        {% if user and user.role == 'admin' %}
        <a href="{{ url_for('admin_users') }}">
          <svg class="nav-icon" viewBox="0 0 24 24"><path d="M17 21v-2a4 4 0 0 0-4-4H5a4 4 0 0 0-4 4v2"/><circle cx="9" cy="7" r="4"/><path d="M23 21v-2a4 4 0 0 0-3-3.87"/><path d="M16 3.13a4 4 0 0 1 0 7.75"/></svg>
          <span>Users</span>
        </a>
        <a href="{{ url_for('admin_uploads') }}">
          <svg class="nav-icon" viewBox="0 0 24 24"><path d="M21 15v4a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2v-4"/><polyline points="7 10 12 15 17 10"/><line x1="12" y1="15" x2="12" y2="3"/></svg>
          <span>Uploads</span>
        </a>
        <a href="{{ url_for('admin_reports') }}">
          <svg class="nav-icon" viewBox="0 0 24 24"><path d="M14 2H6a2 2 0 0 0-2 2v16a2 2 0 0 0 2 2h12a2 2 0 0 0 2-2V8z"/><polyline points="14 2 14 8 20 8"/><line x1="9" y1="13" x2="15" y2="13"/><line x1="9" y1="17" x2="15" y2="17"/></svg>
          <span>Reports</span>
        </a>
        <a href="{{ url_for('admin_reidentify') }}">
          <svg class="nav-icon" viewBox="0 0 24 24"><rect x="3" y="11" width="18" height="11" rx="2"/><path d="M7 11V7a5 5 0 0 0 10 0v4"/></svg>
          <span>Re-identify</span>
        </a>
        <a href="{{ url_for('admin_mrip_registry') }}">
          <svg class="nav-icon" viewBox="0 0 24 24"><path d="M12 2l9 4v6c0 5-3.5 9-9 10-5.5-1-9-5-9-10V6z"/></svg>
          <span>MR/IP</span>
        </a>
        <a href="{{ url_for('audit_page') }}">
          <svg class="nav-icon" viewBox="0 0 24 24"><path d="M14 2H6a2 2 0 0 0-2 2v16a2 2 0 0 0 2 2h12a2 2 0 0 0 2-2V8z"/><polyline points="14 2 14 8 20 8"/><line x1="9" y1="13" x2="15" y2="13"/><line x1="9" y1="17" x2="15" y2="17"/></svg>
          <span>Audit Log</span>
        </a>
        {% endif %}
      </nav>
    </div>
  </div>
</header>

<main class="site-main">
  <div class="container">
    {% with messages = get_flashed_messages(with_categories=true) %}
      {% if messages %}
        <div class="flash-stack">
          {% for category, msg in messages %}
            <div class="alert alert-{{ category }}">{{ msg }}</div>
          {% endfor %}
        </div>
      {% endif %}
    {% endwith %}
    {% block content %}{% endblock %}
  </div>
</main>

<footer class="site-footer">
  <div class="footer-inner">
    <div class="footer-col">
      <div class="footer-brand">ECET</div>
      <p class="footer-desc">
        <strong>EASA College of Engineering and Technology</strong><br>
        Centre of Excellence — AIMAA<br>
        Department of Artificial Intelligence and Data Science<br>
        Coimbatore, Tamil Nadu
      </p>
    </div>
    <div class="footer-col">
      <div class="footer-brand">SMVMCH</div>
      <p class="footer-desc">
        <strong>Sri Manakula Vinayagar Medical College and Hospital</strong><br>
        Department of General Medicine<br>
        Puducherry, India
      </p>
    </div>
    <div class="footer-col">
      <div class="footer-heading">Project</div>
      <p class="footer-desc">
        P1 — Clinical Data Sanitization<br>
        Version 2.5 · {{ copyright_year }}<br>
        Joint Research Initiative
      </p>
    </div>
    <div class="footer-col">
      <div class="footer-heading">Compliance</div>
      <p class="footer-desc">
        HIPAA-aligned de-identification<br>
        Globally-unique dummy IPs<br>
        Accumulating crosswalk history<br>
        Cross-upload MR/IP registry<br>
        Duplicate &amp; conflict detection<br>
        Role-based access control
      </p>
    </div>
  </div>
  <div class="footer-copyright">
    <div class="copyright-inner">
      <span>© {{ copyright_year }} <strong>EASA College of Engineering and Technology</strong>
        &amp; <strong>Sri Manakula Vinayagar Medical College and Hospital</strong>. All rights reserved.</span>
      <span class="copyright-sep">·</span>
      <span>Developed jointly by the Centre of Excellence — AIMAA (ECET) and General Medicine (SMVMCH).</span>
      <span class="copyright-sep">·</span>
      <span>For clinical &amp; research use only.</span>
    </div>
  </div>
</footer>

<script>
(function(){
  var btn = document.getElementById('themeToggle');
  if (!btn) return;
  btn.addEventListener('click', function(){
    var cur  = document.documentElement.getAttribute('data-theme') || 'light';
    var next = cur === 'dark' ? 'light' : 'dark';
    document.documentElement.setAttribute('data-theme', next);
    try { localStorage.setItem('theme', next); } catch(e){}
    document.cookie = "theme=" + next + "; path=/; max-age=31536000; SameSite=Lax";
    window.dispatchEvent(new Event('resize'));
  });
})();
</script>

{% block scripts %}{% endblock %}
</body>
</html>
"""


INDEX_TEMPLATE = """
{% extends "base" %}
{% block title %}Console · ECET × SMVMCH{% endblock %}
{% block breadcrumb %}De-identification Console{% endblock %}

{% block content %}
<div class="page-header">
  <h1>Clinical Data De-identification</h1>
  <p>Upload a discharge summary + lab data workbook to generate a de-identified copy with consistent dummy MR / IP identifiers.</p>
</div>

<form id="uploadForm" action="{{ url_for('upload') }}" method="post"
      enctype="multipart/form-data" class="card">
  <h2>Upload Workbook</h2>
  <div class="dropzone" id="dropzone">
    <input type="file" name="file" id="file" accept=".xlsx,.xls" required hidden />
    <label for="file" class="dropzone-label">
      <span class="dropzone-icon">📄</span>
      <span id="dropzone-text">Click or drag &amp; drop an .xlsx file here</span>
    </label>
  </div>

  <h2>Sheet Configuration</h2>
  <div class="grid-2">
    <label>Discharge summary sheet <input type="text" name="sheet1" value="sh1" required /></label>
    <label>Lab data sheet <input type="text" name="sheet2" value="sh2" required /></label>
  </div>

  <h2>Dummy Identifier Format</h2>
  <div class="grid-4">
    <label>MR prefix <input type="text" name="mr_prefix" value="P" maxlength="8" /></label>
    <label>MR width  <input type="number" name="mr_width" value="3" min="1" max="10" /></label>
    <label>IP prefix <input type="text" name="ip_prefix" value="IP" maxlength="8" /></label>
    <label>IP width  <input type="number" name="ip_width" value="3" min="1" max="10" /></label>
  </div>

  <div class="preview-note">
    Dummy IPs are <strong>globally unique</strong> and bound to their MR.
    Every distinct (MR, IP) pair gets its own dummy — no two patients ever share an IP number.<br>
    Example: <code>MR smv001 → IP001</code> · <code>MR smv002 → IP002</code> · <code>MR smv003 → IP003</code>.
    <br><br>
    <strong>Duplicate detection is active:</strong> identical workbook contents are skipped.
    Individual <strong>(MR, IP)</strong> pairs are also tracked across every upload — if a pair
    reappears with identical data you'll be notified; if it reappears with different data
    it's flagged as a conflict.
    <br><br>
    <strong>Stable cross-upload numbering:</strong> the same patient always keeps the
    same dummy MR and dummy IP. Only genuinely new identifiers consume new counter slots.
    <br><br>
    <strong>Accumulating crosswalks:</strong> <code>SECURE_mr_crosswalk.csv</code> and
    <code>SECURE_ip_crosswalk.csv</code> are appended to on every upload — the full
    history of every patient ever processed is preserved on disk, never regenerated.
  </div>

  <div class="progress-wrap" id="uploadProgressWrap" style="display:none">
    <div class="progress-label">
      <span>Uploading file (network)</span>
      <span class="pct" id="uploadPctText">0%</span>
    </div>
    <div class="progress-track tall">
      <div class="progress-fill" id="uploadFill"></div>
    </div>
  </div>

  <div class="progress-wrap" id="processProgressWrap" style="display:none">
    <div class="progress-label">
      <span id="procStageLabel">Processing</span>
      <span class="pct" id="processPctText">0%</span>
    </div>
    <div class="progress-track tall">
      <div class="progress-fill striped" id="processFill"></div>
    </div>
    <div class="live-detail" id="procDetail">Starting pipeline…</div>
  </div>

  <button type="submit" id="submitBtn" class="btn-primary">
    <svg class="nav-icon" viewBox="0 0 24 24"><rect x="3" y="11" width="18" height="11" rx="2"/><path d="M7 11V7a5 5 0 0 1 10 0v4"/></svg>
    <span>De-identify &amp; Download</span>
  </button>
</form>

<div class="overlay" id="overlay">
  <div class="overlay-card">
    <div class="spinner"></div>
    <h3 id="overlayTitle">Uploading workbook…</h3>
    <p id="overlayMsg">Please wait while the file is transmitted.</p>

    <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:6px">
      <span id="overlayStage" style="font-size:.9rem;color:var(--text-primary);font-weight:600">
        Uploading
      </span>
      <span class="live-pct" id="overlayPct">0%</span>
    </div>
    <div class="progress-track tall">
      <div class="progress-fill" id="overlayFill"></div>
    </div>
    <div class="live-detail" id="overlayDetail">Transmitting bytes…</div>
  </div>
</div>

{% if my_uploads %}
<div class="card" style="margin-top:24px">
  <h2>📁 My Recent Uploads (this session)</h2>
  <div class="table-scroll">
    <table class="data-table">
      <thead><tr>
        <th>Job</th><th>When</th><th>File</th>
        <th>Status</th><th>Progress</th><th>Rows</th><th>Message</th><th>Download</th>
      </tr></thead>
      <tbody>
        {% for u in my_uploads %}
        <tr>
          <td><code>{{ u.job_id }}</code></td>
          <td>{{ u.timestamp.strftime("%Y-%m-%d %H:%M:%S") if u.timestamp else "-" }}</td>
          <td title="{{ u.original_name }}">{{ (u.original_name or "-")[:28] }}{% if u.original_name and u.original_name|length > 28 %}…{% endif %}</td>
          <td>
            {% if u.status == 'success' %}
              <span class="audit-badge badge-success">success</span>
            {% elif u.status == 'skipped' %}
              <span class="audit-badge badge-skipped">skipped</span>
            {% elif u.status == 'rejected' %}
              <span class="audit-badge badge-denied">rejected</span>
            {% else %}
              <span class="audit-badge badge-failed">failed</span>
            {% endif %}
          </td>
          <td>
            {% if u.status == 'success' %}
              <span class="progress-mini"><span class="fill" style="width:100%"></span></span>
              <span style="font-size:.72rem;color:var(--text-muted)">100%</span>
            {% elif u.status == 'skipped' %}
              <span class="progress-mini"><span class="fill skipped" style="width:100%"></span></span>
              <span style="font-size:.72rem;color:var(--text-muted)">skipped</span>
            {% elif u.status == 'rejected' %}
              <span class="progress-mini"><span class="fill rejected" style="width:15%"></span></span>
              <span style="font-size:.72rem;color:var(--text-muted)">rejected</span>
            {% else %}
              <span class="progress-mini"><span class="fill failed" style="width:0%"></span></span>
              <span style="font-size:.72rem;color:var(--text-muted)">failed</span>
            {% endif %}
          </td>
          <td>
            {% if u.status in ('success', 'skipped') %}
              {{ u.sheet1_rows }} + {{ u.sheet2_rows }}
            {% else %}—{% endif %}
          </td>
          <td title="{{ u.message or '' }}">{{ (u.message or "-")[:80] }}{% if u.message and u.message|length > 80 %}…{% endif %}</td>
          <td>
            {% if u.status in ('success', 'skipped') and u.sh1_file %}
              <a class="btn-sm" href="{{ url_for('download', filename=u.sh1_file) }}">sh1</a>
              <a class="btn-sm" href="{{ url_for('download', filename=u.sh2_file) }}">sh2</a>
            {% else %}—{% endif %}
          </td>
        </tr>
        {% endfor %}
      </tbody>
    </table>
  </div>
  <p class="preview-note" style="margin-top:12px">
    Only <strong>your</strong> uploads from this browser session are shown here.
    Admins can see all users' uploads at <code>/admin/uploads</code>.
  </p>
</div>
{% endif %}

{% if my_reports %}
<div class="card" style="margin-top:24px">
  <h2>🔍 My Recent Similarity Reports (this session)</h2>
  <div class="table-scroll">
    <table class="data-table">
      <thead><tr>
        <th>Job</th><th>When</th><th>sh1 %</th><th>sh2 %</th>
        <th>Combined</th><th>Rows</th><th>Cols</th>
      </tr></thead>
      <tbody>
        {% for r in my_reports %}
        <tr>
          <td><code>{{ r.job_id }}</code></td>
          <td>{{ r.timestamp.strftime("%Y-%m-%d %H:%M:%S") if r.timestamp else "-" }}</td>
          <td>{{ r.sh1_overall_pct }}%</td>
          <td>{{ r.sh2_overall_pct }}%</td>
          <td>
            <span class="progress-mini" style="width:80px">
              <span class="fill {% if (r.combined_pct or 0) < 99 %}failed{% endif %}"
                    style="width:{{ r.combined_pct or 0 }}%"></span>
            </span>
            <span style="font-size:.72rem;color:var(--text-muted);margin-left:6px">
              {{ r.combined_pct }}%
            </span>
          </td>
          <td>{{ '✅' if r.rows_preserved else '⚠️' }}</td>
          <td>{{ '✅' if r.columns_preserved else '⚠️' }}</td>
        </tr>
        {% endfor %}
      </tbody>
    </table>
  </div>
</div>
{% endif %}
{% endblock %}

{% block scripts %}
<script>
document.addEventListener("DOMContentLoaded", () => {
  const dropzone = document.getElementById("dropzone");
  const fileInput = document.getElementById("file");
  const dropText = document.getElementById("dropzone-text");
  const form = document.getElementById("uploadForm");
  const submitBtn = document.getElementById("submitBtn");

  const uploadWrap = document.getElementById("uploadProgressWrap");
  const uploadFill = document.getElementById("uploadFill");
  const uploadPctText = document.getElementById("uploadPctText");

  const processWrap = document.getElementById("processProgressWrap");
  const processFill = document.getElementById("processFill");
  const processPctText = document.getElementById("processPctText");
  const procStageLabel = document.getElementById("procStageLabel");
  const procDetail = document.getElementById("procDetail");

  const overlay = document.getElementById("overlay");
  const overlayFill = document.getElementById("overlayFill");
  const overlayPct = document.getElementById("overlayPct");
  const overlayTitle = document.getElementById("overlayTitle");
  const overlayMsg = document.getElementById("overlayMsg");
  const overlayStage = document.getElementById("overlayStage");
  const overlayDetail = document.getElementById("overlayDetail");

  if (!form || !fileInput) return;

  ["dragenter","dragover"].forEach(evt => dropzone.addEventListener(evt, e => {
    e.preventDefault(); dropzone.classList.add("dragover");
  }));
  ["dragleave","drop"].forEach(evt => dropzone.addEventListener(evt, e => {
    e.preventDefault(); dropzone.classList.remove("dragover");
  }));
  dropzone.addEventListener("drop", e => {
    const files = e.dataTransfer.files;
    if (files.length) {
      fileInput.files = files;
      dropText.textContent = "✅ Selected: " + files[0].name;
      dropzone.style.borderColor = "var(--accent)";
    }
  });
  fileInput.addEventListener("change", () => {
    if (fileInput.files.length) {
      dropText.textContent = "✅ Selected: " + fileInput.files[0].name;
      dropzone.style.borderColor = "var(--accent)";
    }
  });

  form.addEventListener("submit", (e) => {
    e.preventDefault();
    if (!fileInput.files.length) {
      alert("Please select an .xlsx file first.");
      return;
    }
    submitBtn.disabled = true;
    submitBtn.querySelector("span").textContent = "Working…";

    uploadWrap.style.display = "block";
    processWrap.style.display = "none";

    overlay.classList.add("on");
    overlayTitle.textContent = "Uploading workbook…";
    overlayMsg.textContent = "Please wait while the file is transmitted.";
    overlayStage.textContent = "Uploading";
    overlayDetail.textContent = "Transmitting bytes…";
    overlayPct.textContent = "0%";
    overlayFill.classList.remove("striped", "success", "warning", "danger");
    overlayFill.style.width = "0%";

    const xhr = new XMLHttpRequest();
    xhr.open("POST", form.action, true);
    xhr.withCredentials = true;
    xhr.responseType = "json";

    xhr.upload.onprogress = (ev) => {
      if (ev.lengthComputable) {
        const p = (ev.loaded / ev.total) * 100;
        uploadFill.style.width = p + "%";
        overlayFill.style.width = p + "%";
        uploadPctText.textContent = p.toFixed(1) + "%";
        overlayPct.textContent = p.toFixed(1) + "%";
        if (p >= 100) {
          overlayTitle.textContent = "Processing on the server…";
          overlayMsg.textContent = "Starting pipeline…";
          overlayStage.textContent = "Server received file";
          overlayDetail.textContent = "Waiting for worker…";
        }
      }
    };

    xhr.onreadystatechange = () => {
      if (xhr.readyState !== 4) return;

      if (xhr.status !== 202 && !(xhr.status >= 200 && xhr.status < 300)) {
        overlay.classList.remove("on");
        submitBtn.disabled = false;
        submitBtn.querySelector("span").textContent = "De-identify & Download";
        alert("Upload failed (" + xhr.status + ").");
        return;
      }

      let data = xhr.response;
      if (!data) {
        try { data = JSON.parse(xhr.responseText); } catch (err) { data = null; }
      }
      if (!data || !data.job_id) {
        overlay.classList.remove("on");
        submitBtn.disabled = false;
        submitBtn.querySelector("span").textContent = "De-identify & Download";
        alert("Server did not return a job_id.");
        return;
      }

      // Duplicate detected — server already marked this job done.
      if (data.status === "duplicate") {
        overlayFill.classList.remove("striped");
        overlayFill.classList.add("success");
        overlayFill.style.width = "100%";
        overlayPct.textContent = "100%";
        overlayStage.textContent = "Duplicate — skipping";
        overlayDetail.textContent = "This file was already processed.";
        overlayTitle.textContent = "♻️ Identical file — opening earlier result…";
        overlayMsg.textContent = "No re-processing needed.";
        setTimeout(() => {
          const url = (data.duplicate_of
                       ? `/upload/result/${data.job_id}?dup_of=${data.duplicate_of}`
                       : `/upload/result/${data.job_id}`);
          window.location.href = url;
        }, 1200);
        return;
      }

      uploadWrap.style.display = "none";
      processWrap.style.display = "block";
      overlayFill.classList.add("striped");
      overlayTitle.textContent = "Processing…";
      overlayMsg.textContent = "De-identifying, building charts, running similarity check…";

      pollProgress(data.job_id);
    };

    xhr.onerror = () => {
      overlay.classList.remove("on");
      submitBtn.disabled = false;
      submitBtn.querySelector("span").textContent = "De-identify & Download";
      alert("Network error while uploading.");
    };

    xhr.send(new FormData(form));
  });

  function pollProgress(jobId) {
    let lastPct = 0;
    const interval = setInterval(async () => {
      try {
        const res = await fetch(`/api/progress/${jobId}`, { credentials: "same-origin" });
        if (!res.ok) return;
        const p = await res.json();

        const shown = Math.max(lastPct, p.pct || 0);
        lastPct = shown;
        const pctText = shown.toFixed(1) + "%";

        processFill.style.width = shown + "%";
        processPctText.textContent = pctText;
        procStageLabel.textContent = p.stage || "Processing";
        procDetail.textContent = p.detail || "";

        overlayFill.style.width = shown + "%";
        overlayPct.textContent = pctText;
        overlayStage.textContent = p.stage || "Processing";
        overlayDetail.textContent = p.detail || "";

        if (p.status === "done") {
          clearInterval(interval);
          overlayFill.classList.remove("striped");
          overlayFill.classList.add("success");
          overlayFill.style.width = "100%";
          overlayPct.textContent = "100%";
          overlayStage.textContent = "Complete";
          overlayDetail.textContent = "Loading results…";
          overlayTitle.textContent = "✅ Done — loading results…";
          setTimeout(() => {
            window.location.href = p.result_url || "/";
          }, 500);
        } else if (p.status === "failed") {
          clearInterval(interval);
          overlayFill.classList.remove("striped");
          overlayFill.classList.add("danger");
          overlayTitle.textContent = "❌ Processing failed";
          overlayMsg.textContent = p.error || "Unknown error";
          overlayStage.textContent = "Failed";
          overlayDetail.textContent = "";
          submitBtn.disabled = false;
          submitBtn.querySelector("span").textContent = "De-identify & Download";
          setTimeout(() => overlay.classList.remove("on"), 3500);
        }
      } catch (err) {
        // silent retry
      }
    }, 500);
  }
});
</script>
{% endblock %}
"""


RESULT_TEMPLATE = """
{% extends "base" %}
{% block title %}Results · ECET × SMVMCH{% endblock %}
{% block breadcrumb %}De-identification Results{% endblock %}

{% block content %}
<script src="https://cdn.plot.ly/plotly-2.32.0.min.js"></script>

<div class="page-header">
  <h1>✅ De-identification Complete</h1>
  <p>Job ID <code>{{ r.job_id }}</code> · {{ r.timestamp }}</p>
</div>

{% if request.args.get('dup_of') %}
<div class="alert alert-warning" style="margin-bottom:16px">
  ♻️ This workbook was <strong>identical</strong> to a previously processed file
  (job <code>{{ request.args.get('dup_of') }}</code>).
  Results below are from that earlier run — no re-processing was needed.
</div>
{% endif %}

{% if r.crosswalk_mr_stats or r.crosswalk_ip_stats %}
<div class="card" style="border-left:4px solid var(--teal-700)">
  <h2 style="border:none;padding:0;margin:0 0 12px">📚 Crosswalk Append Summary</h2>
  <p class="preview-note" style="margin-bottom:16px">
    Crosswalks are <strong>append-only</strong>. Every upload grows the on-disk history;
    no existing rows were rewritten or removed.
  </p>
  <div class="stats-grid">
    {% if r.crosswalk_mr_stats %}
    <div class="stat-card">
      <div class="stat-value" style="color:var(--success)">+{{ r.crosswalk_mr_stats.added }}</div>
      <div class="stat-label">MR rows added</div>
    </div>
    <div class="stat-card">
      <div class="stat-value">{{ r.crosswalk_mr_stats.skipped }}</div>
      <div class="stat-label">MR rows already present</div>
    </div>
    <div class="stat-card">
      <div class="stat-value">{{ r.crosswalk_mr_stats.total }}</div>
      <div class="stat-label">Total MR rows on disk</div>
    </div>
    {% endif %}
    {% if r.crosswalk_ip_stats %}
    <div class="stat-card">
      <div class="stat-value" style="color:var(--success)">+{{ r.crosswalk_ip_stats.added }}</div>
      <div class="stat-label">IP rows added</div>
    </div>
    <div class="stat-card">
      <div class="stat-value">{{ r.crosswalk_ip_stats.skipped }}</div>
      <div class="stat-label">IP rows already present</div>
    </div>
    <div class="stat-card">
      <div class="stat-value">{{ r.crosswalk_ip_stats.total }}</div>
      <div class="stat-label">Total IP rows on disk</div>
    </div>
    {% endif %}
  </div>
</div>
{% endif %}

{% if mrip_classification and (mrip_classification.identical or mrip_classification.conflict) %}
<div class="card" style="border-left:4px solid var(--warning)">
  <h2 style="border:none;padding:0;margin:0 0 12px">⚠️ MR / IP Overlap Detected</h2>
  <p class="preview-note" style="margin-bottom:16px">
    The uploaded workbook contains <strong>(MR, IP)</strong> pairs that were seen in earlier uploads.
  </p>

  <div class="stats-grid">
    <div class="stat-card">
      <div class="stat-value" style="color:var(--success)">{{ mrip_classification.new|length }}</div>
      <div class="stat-label">New pairs</div>
    </div>
    <div class="stat-card">
      <div class="stat-value" style="color:#4338ca">{{ mrip_classification.identical|length }}</div>
      <div class="stat-label">Identical (dup data)</div>
    </div>
    <div class="stat-card">
      <div class="stat-value" style="color:var(--warning)">{{ mrip_classification.conflict|length }}</div>
      <div class="stat-label">Conflicting (new data)</div>
    </div>
  </div>

  {% if mrip_classification.identical %}
  <h2 style="margin-top:16px">♻️ Identical MR / IP pairs — already exist</h2>
  <p class="preview-note">
    For these identifiers, an <strong>identical</strong> dataset was already uploaded earlier.
  </p>
  <div class="table-scroll" style="max-height:300px">
    <table class="data-table">
      <thead><tr>
        <th>Original MR</th><th>Original IP</th>
        <th>Rows</th>
        <th>First seen</th><th>Uploaded by</th><th>Source job</th>
      </tr></thead>
      <tbody>
        {% for p in mrip_classification.identical %}
        <tr>
          <td><code>{{ p.raw_mr }}</code></td>
          <td><code>{{ p.raw_ip }}</code></td>
          <td>{{ p.row_count }}</td>
          <td>{{ p.existing_at or "—" }}</td>
          <td>{{ p.existing_username or "—" }}</td>
          <td><code>{{ p.existing_job or "—" }}</code></td>
        </tr>
        {% endfor %}
      </tbody>
    </table>
  </div>
  {% endif %}

  {% if mrip_classification.conflict %}
  <h2 style="margin-top:24px">🔀 Conflicting MR / IP pairs — same ID, different data</h2>
  <p class="preview-note">
    These identifiers were seen before but the lab data has changed. New data is retained
    and the registry has been updated (last writer wins). Verify with the data custodian.
  </p>
  <div class="table-scroll" style="max-height:300px">
    <table class="data-table">
      <thead><tr>
        <th>Original MR</th><th>Original IP</th>
        <th>Rows now</th>
        <th>Previous upload</th><th>Previous by</th><th>Previous job</th>
      </tr></thead>
      <tbody>
        {% for p in mrip_classification.conflict %}
        <tr>
          <td><code>{{ p.raw_mr }}</code></td>
          <td><code>{{ p.raw_ip }}</code></td>
          <td>{{ p.row_count }}</td>
          <td>{{ p.existing_at or "—" }}</td>
          <td>{{ p.existing_username or "—" }}</td>
          <td><code>{{ p.existing_job or "—" }}</code></td>
        </tr>
        {% endfor %}
      </tbody>
    </table>
  </div>
  {% endif %}
</div>
{% endif %}

{% if r.processing %}
<div class="card">
  <h2>⚙️ Processing Report</h2>
  <p class="preview-note">
    End-to-end pipeline for job <code>{{ r.job_id }}</code> — IP identifiers use globally-unique numbering.
  </p>
  <div class="progress-wrap" style="margin-bottom:20px">
    <div class="progress-label">
      <span>Overall pipeline</span>
      <span class="pct">{{ r.processing.overall_pct }}%</span>
    </div>
    <div class="progress-track tall">
      <div class="progress-fill success" style="width:{{ r.processing.overall_pct }}%"></div>
    </div>
  </div>
  <div class="table-scroll">
  <table class="data-table">
    <thead>
      <tr><th>Stage</th><th>Progress</th><th>Status</th></tr>
    </thead>
    <tbody>
      {% for s in r.processing.stages %}
      <tr>
        <td>{{ s.label }}</td>
        <td style="min-width:220px">
          <span class="progress-mini" style="width:160px">
            <span class="fill {% if not s.ok %}failed{% endif %}" style="width:{{ s.pct }}%"></span>
          </span>
          <span style="font-size:.72rem;color:var(--text-muted);margin-left:8px">{{ s.pct }}%</span>
        </td>
        <td>
          {% if s.ok %}
            <span class="audit-badge badge-success">ok</span>
          {% else %}
            <span class="audit-badge badge-failed">warn</span>
          {% endif %}
        </td>
      </tr>
      {% endfor %}
    </tbody>
  </table>
  </div>
</div>
{% endif %}

{% if r.similarity and not r.similarity.error %}
<div class="card">
  <h2>🔍 Similarity Report — Before vs After De-identification</h2>

  <div class="stats-grid">
    <div class="stat-card">
      <div class="stat-value">{{ r.similarity.combined_pct }}%</div>
      <div class="stat-label">Combined Similarity</div>
    </div>
    <div class="stat-card">
      <div class="stat-value">{{ r.similarity.sh1.overall_pct }}%</div>
      <div class="stat-label">sh1 Match</div>
    </div>
    <div class="stat-card">
      <div class="stat-value">{{ r.similarity.sh2.overall_pct }}%</div>
      <div class="stat-label">sh2 Match</div>
    </div>
    <div class="stat-card">
      <div class="stat-value">{{ '✅' if r.similarity.rows_preserved else '⚠️' }}</div>
      <div class="stat-label">Rows Preserved</div>
    </div>
    <div class="stat-card">
      <div class="stat-value">{{ '✅' if r.similarity.columns_preserved else '⚠️' }}</div>
      <div class="stat-label">Columns Preserved</div>
    </div>
  </div>

  <p class="preview-note">
    Higher similarity = only identifier columns changed. Identifier columns (MR/IP)
    are weighted 0.5× because their values <em>must</em> change; all other columns
    are expected to remain identical.
  </p>

  <div class="progress-wrap">
    <div class="progress-label">
      <span>Overall data similarity (weighted)</span>
      <span class="pct">{{ r.similarity.combined_pct }}%</span>
    </div>
    <div class="progress-track tall">
      <div class="progress-fill success" style="width:{{ r.similarity.combined_pct }}%"></div>
    </div>
  </div>

  <h2 style="margin-top:28px">📄 sh1 — Column-by-Column</h2>
  <div class="table-scroll" style="max-height:340px">
    <table class="data-table">
      <thead><tr><th>Column</th><th>Type</th><th>Match</th><th>Bar</th></tr></thead>
      <tbody>
        {% for c in r.similarity.sh1.columns %}
        <tr>
          <td><code>{{ c.name }}</code></td>
          <td>
            {% if c.kind == 'identifier' %}
              <span class="role-badge role-admin">identifier</span>
            {% else %}
              <span class="role-badge role-user">preserved</span>
            {% endif %}
          </td>
          <td>{{ c.match_pct }}%</td>
          <td style="min-width:220px">
            <span class="progress-mini" style="width:160px">
              <span class="fill {% if c.match_pct < 99 %}failed{% endif %}" style="width:{{ c.match_pct }}%"></span>
            </span>
          </td>
        </tr>
        {% endfor %}
      </tbody>
    </table>
  </div>

  {% if r.similarity.sh1.notes %}
    <p class="warn" style="margin-top:12px">
      {% for n in r.similarity.sh1.notes %}• {{ n }}<br>{% endfor %}
    </p>
  {% endif %}

  <h2 style="margin-top:28px">📄 sh2 — Column-by-Column</h2>
  <div class="table-scroll" style="max-height:340px">
    <table class="data-table">
      <thead><tr><th>Column</th><th>Type</th><th>Match</th><th>Bar</th></tr></thead>
      <tbody>
        {% for c in r.similarity.sh2.columns %}
        <tr>
          <td><code>{{ c.name }}</code></td>
          <td>
            {% if c.kind == 'identifier' %}
              <span class="role-badge role-admin">identifier</span>
            {% else %}
              <span class="role-badge role-user">preserved</span>
            {% endif %}
          </td>
          <td>{{ c.match_pct }}%</td>
          <td style="min-width:220px">
            <span class="progress-mini" style="width:160px">
              <span class="fill {% if c.match_pct < 99 %}failed{% endif %}" style="width:{{ c.match_pct }}%"></span>
            </span>
          </td>
        </tr>
        {% endfor %}
      </tbody>
    </table>
  </div>

  {% if r.similarity.sh2.notes %}
    <p class="warn" style="margin-top:12px">
      {% for n in r.similarity.sh2.notes %}• {{ n }}<br>{% endfor %}
    </p>
  {% endif %}
</div>
{% elif r.similarity and r.similarity.error %}
<div class="card">
  <h2>🔍 Similarity Report</h2>
  <p class="warn">Similarity check failed: {{ r.similarity.error }}</p>
</div>
{% endif %}

<div class="card">
  <h2>📈 Job Completion</h2>
  <div class="progress-wrap">
    <div class="progress-label">
      <span>De-identification</span>
      <span class="pct">100%</span>
    </div>
    <div class="progress-track tall">
      <div class="progress-fill success" style="width:100%"></div>
    </div>
  </div>
  <div class="progress-wrap">
    <div class="progress-label">
      <span>Charts rendered</span>
      <span class="pct">{{ r.chart_count|default(0) }} / {{ r.chart_total|default(25) }}
        ({{ r.chart_pct|default(0) }}%)</span>
    </div>
    <div class="progress-track tall">
      <div class="progress-fill navy" style="width:{{ r.chart_pct|default(0) }}%"></div>
    </div>
  </div>
  <div class="progress-wrap">
    <div class="progress-label">
      <span>Rows processed (sh1 + sh2)</span>
      <span class="pct">{{ r.sheet1_rows + r.sheet2_rows }}</span>
    </div>
    <div class="progress-track thin">
      <div class="progress-fill" style="width:100%"></div>
    </div>
  </div>
</div>

<div class="stats-grid">
  <div class="stat-card"><div class="stat-value">{{ r.unique_mr }}</div><div class="stat-label">Unique Patients</div></div>
  <div class="stat-card"><div class="stat-value">{{ r.unique_ip }}</div><div class="stat-label">Admissions</div></div>
  <div class="stat-card"><div class="stat-value">{{ r.sheet1_rows }}</div><div class="stat-label">Discharge Records</div></div>
  <div class="stat-card"><div class="stat-value">{{ r.sheet2_rows }}</div><div class="stat-label">Lab Records</div></div>
  <div class="stat-card"><div class="stat-value">{{ r.relation }}</div><div class="stat-label">MR : IP</div></div>
  <div class="stat-card"><div class="stat-value">{{ r.max_ip_per_mr }}</div><div class="stat-label">Max IPs / MR</div></div>
  <div class="stat-card"><div class="stat-value">{{ r.avg_ip_per_mr }}</div><div class="stat-label">Avg IPs / MR</div></div>
</div>

<div class="card">
  <h2>📥 Download De-identified Outputs</h2>
  <div class="download-row">
    <a class="btn-download" href="{{ url_for('download', filename=r.sh1_name) }}">
      <svg class="nav-icon" viewBox="0 0 24 24"><path d="M21 15v4a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2v-4"/><polyline points="7 10 12 15 17 10"/><line x1="12" y1="15" x2="12" y2="3"/></svg>
      <span>sh1_deidentified.xlsx</span>
    </a>
    <a class="btn-download" href="{{ url_for('download', filename=r.sh2_name) }}">
      <svg class="nav-icon" viewBox="0 0 24 24"><path d="M21 15v4a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2v-4"/><polyline points="7 10 12 15 17 10"/><line x1="12" y1="15" x2="12" y2="3"/></svg>
      <span>sh2_deidentified.xlsx</span>
    </a>
  </div>
  <p class="warn">Crosswalk files remain in the secure store and are never exposed through this interface. The crosswalks accumulate every mapping ever produced (see <code>SECURE_mr_crosswalk.csv</code> and <code>SECURE_ip_crosswalk.csv</code>).</p>
</div>

{% if r.charts and r.charts.error %}
<div class="card"><h2>📊 Data Visualizations</h2><p class="warn">{{ r.charts.error }}</p></div>
{% elif r.charts %}
<div class="card">
  <h2>📊 Interactive Data Visualizations — 25 Charts</h2>
  <p class="preview-note">Hover, zoom, pan, and export as PNG. Charts adapt to your theme.</p>
  <div class="viz-grid">
    {% if r.charts.age_sex %}<div class="viz-block"><h3 class="viz-title">Age × Sex</h3><div class="viz-body">{{ r.charts.age_sex|safe }}</div></div>{% endif %}
    {% if r.charts.sex_ratio %}<div class="viz-block"><h3 class="viz-title">Sex Ratio</h3><div class="viz-body">{{ r.charts.sex_ratio|safe }}</div></div>{% endif %}
    {% if r.charts.age_hist %}<div class="viz-block"><h3 class="viz-title">Age Histogram</h3><div class="viz-body">{{ r.charts.age_hist|safe }}</div></div>{% endif %}
    {% if r.charts.los %}<div class="viz-block viz-full"><h3 class="viz-title">Length of Stay per Patient</h3><div class="viz-body">{{ r.charts.los|safe }}</div></div>{% endif %}
    {% if r.charts.los_by_sex %}<div class="viz-block"><h3 class="viz-title">LOS by Sex</h3><div class="viz-body">{{ r.charts.los_by_sex|safe }}</div></div>{% endif %}
    {% if r.charts.age_los %}<div class="viz-block"><h3 class="viz-title">Age vs LOS</h3><div class="viz-body">{{ r.charts.age_los|safe }}</div></div>{% endif %}
    {% if r.charts.doa_hist %}<div class="viz-block"><h3 class="viz-title">Admissions by Date</h3><div class="viz-body">{{ r.charts.doa_hist|safe }}</div></div>{% endif %}
    {% if r.charts.dod_hist %}<div class="viz-block"><h3 class="viz-title">Discharges by Date</h3><div class="viz-body">{{ r.charts.dod_hist|safe }}</div></div>{% endif %}
    {% if r.charts.comorbidities %}<div class="viz-block"><h3 class="viz-title">Comorbidity Frequency</h3><div class="viz-body">{{ r.charts.comorbidities|safe }}</div></div>{% endif %}
    {% if r.charts.doctor_load %}<div class="viz-block"><h3 class="viz-title">Patients per Doctor</h3><div class="viz-body">{{ r.charts.doctor_load|safe }}</div></div>{% endif %}
    {% if r.charts.top_tests %}<div class="viz-block viz-full"><h3 class="viz-title">Top Lab Tests</h3><div class="viz-body">{{ r.charts.top_tests|safe }}</div></div>{% endif %}
    {% if r.charts.dept_pie %}<div class="viz-block"><h3 class="viz-title">Lab Tests by Department</h3><div class="viz-body">{{ r.charts.dept_pie|safe }}</div></div>{% endif %}
    {% if r.charts.sunburst %}<div class="viz-block"><h3 class="viz-title">Lab Hierarchy Sunburst</h3><div class="viz-body">{{ r.charts.sunburst|safe }}</div></div>{% endif %}
    {% if r.charts.req_time %}<div class="viz-block viz-full"><h3 class="viz-title">Lab Request Volume Over Time</h3><div class="viz-body">{{ r.charts.req_time|safe }}</div></div>{% endif %}
    {% if r.charts.hba1c %}<div class="viz-block"><h3 class="viz-title">HbA1c Distribution</h3><div class="viz-body">{{ r.charts.hba1c|safe }}</div></div>{% endif %}
    {% if r.charts.glucose_trend %}<div class="viz-block"><h3 class="viz-title">Fasting Glucose Trends</h3><div class="viz-body">{{ r.charts.glucose_trend|safe }}</div></div>{% endif %}
    {% if r.charts.urine_glucose %}<div class="viz-block"><h3 class="viz-title">Urine Glucose Categories</h3><div class="viz-body">{{ r.charts.urine_glucose|safe }}</div></div>{% endif %}
    {% if r.charts.hb_trends %}<div class="viz-block viz-full"><h3 class="viz-title">Serial Hemoglobin Trends</h3><div class="viz-body">{{ r.charts.hb_trends|safe }}</div></div>{% endif %}
    {% if r.charts.plt_trends %}<div class="viz-block viz-full"><h3 class="viz-title">Platelet Count Trajectories</h3><div class="viz-body">{{ r.charts.plt_trends|safe }}</div></div>{% endif %}
    {% if r.charts.creatinine %}<div class="viz-block"><h3 class="viz-title">Creatinine Distribution</h3><div class="viz-body">{{ r.charts.creatinine|safe }}</div></div>{% endif %}
    {% if r.charts.urine_protein %}<div class="viz-block"><h3 class="viz-title">Urine Protein Categories</h3><div class="viz-body">{{ r.charts.urine_protein|safe }}</div></div>{% endif %}
    {% if r.charts.potassium %}<div class="viz-block viz-full"><h3 class="viz-title">Potassium Distribution</h3><div class="viz-body">{{ r.charts.potassium|safe }}</div></div>{% endif %}
    {% if r.charts.sodium %}<div class="viz-block viz-full"><h3 class="viz-title">Sodium Distribution</h3><div class="viz-body">{{ r.charts.sodium|safe }}</div></div>{% endif %}
    {% if r.charts.lft_scatter %}<div class="viz-block viz-full"><h3 class="viz-title">LFT — Bilirubin vs AST</h3><div class="viz-body">{{ r.charts.lft_scatter|safe }}</div></div>{% endif %}
    {% if r.charts.corr_matrix %}<div class="viz-block viz-full"><h3 class="viz-title">Lab Value Correlation Matrix</h3><div class="viz-body">{{ r.charts.corr_matrix|safe }}</div></div>{% endif %}
  </div>
</div>
{% endif %}

<div class="card">
  <h2>📋 MR → IP Distribution</h2>
  <div class="table-scroll">
    <table class="data-table">
      <thead><tr><th>Dummy MR</th><th>Admissions (IPs)</th></tr></thead>
      <tbody>
        {% for mr, cnt in r.mr_ip_distribution.items() %}
        <tr><td>{{ mr }}</td><td>{{ cnt }}</td></tr>
        {% endfor %}
      </tbody>
    </table>
  </div>
</div>

<a href="{{ url_for('index') }}" class="btn-secondary">
  <svg class="nav-icon" viewBox="0 0 24 24"><line x1="19" y1="12" x2="5" y2="12"/><polyline points="12 19 5 12 12 5"/></svg>
  <span>Process Another File</span>
</a>
{% endblock %}
"""


PROFILE_TEMPLATE = """
{% extends "base" %}
{% block title %}My Profile · ECET × SMVMCH{% endblock %}
{% block breadcrumb %}My Profile{% endblock %}

{% block content %}
<div class="page-header">
  <h1>👤 My Profile</h1>
  <p>View and update your account information.</p>
</div>

<div class="card">
  <h2>Account Overview</h2>
  <div class="grid-3">
    <div>
      <div style="font-size:.75rem;color:var(--text-muted);text-transform:uppercase;letter-spacing:.5px">Username</div>
      <div style="font-size:1.05rem;font-weight:600;color:var(--text-primary)">{{ user.username }}</div>
    </div>
    <div>
      <div style="font-size:.75rem;color:var(--text-muted);text-transform:uppercase;letter-spacing:.5px">Role</div>
      <div><span class="role-badge role-{{ user.role }}">{{ user.role }}</span></div>
    </div>
    <div>
      <div style="font-size:.75rem;color:var(--text-muted);text-transform:uppercase;letter-spacing:.5px">Status</div>
      <div>
        <span class="status-dot {{ 'dot-active' if user.is_active else 'dot-inactive' }}"></span>
        {{ 'Active' if user.is_active else 'Inactive' }}
      </div>
    </div>
  </div>
  <div class="grid-3" style="margin-top:20px">
    <div>
      <div style="font-size:.75rem;color:var(--text-muted);text-transform:uppercase;letter-spacing:.5px">Member Since</div>
      <div>{{ user.created_at.strftime("%Y-%m-%d %H:%M") if user.created_at else "—" }}</div>
    </div>
    <div>
      <div style="font-size:.75rem;color:var(--text-muted);text-transform:uppercase;letter-spacing:.5px">Last Login</div>
      <div>{{ user.last_login.strftime("%Y-%m-%d %H:%M") if user.last_login else "—" }}</div>
    </div>
    <div>
      <div style="font-size:.75rem;color:var(--text-muted);text-transform:uppercase;letter-spacing:.5px">Account ID</div>
      <div>#{{ user.id }}</div>
    </div>
  </div>
</div>

<form method="post" action="{{ url_for('profile_update') }}" class="card">
  <h2>Update Profile</h2>
  <div class="grid-2">
    <label>Full Name <input type="text" name="full_name" value="{{ user.full_name or '' }}" maxlength="120" /></label>
    <label>Email <input type="email" name="email" value="{{ user.email or '' }}" maxlength="120" /></label>
    <label>Department <input type="text" name="department" value="{{ user.department or '' }}" maxlength="120" /></label>
    <label>Phone <input type="tel" name="phone" value="{{ user.phone or '' }}" maxlength="32" /></label>
  </div>
  <button type="submit" class="btn-primary">
    <svg class="nav-icon" viewBox="0 0 24 24"><path d="M19 21H5a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h11l5 5v11a2 2 0 0 1-2 2z"/><polyline points="17 21 17 13 7 13 7 21"/><polyline points="7 3 7 8 15 8"/></svg>
    <span>Save Profile</span>
  </button>
</form>

<form method="post" action="{{ url_for('profile_change_password') }}" class="card">
  <h2>Change Password</h2>
  <div class="grid-3">
    <label>Current Password <input type="password" name="old_password" required /></label>
    <label>New Password <input type="password" name="new_password" required minlength="6" /></label>
    <label>Confirm New <input type="password" name="confirm" required minlength="6" /></label>
  </div>
  <button type="submit" class="btn-primary">
    <svg class="nav-icon" viewBox="0 0 24 24"><rect x="3" y="11" width="18" height="11" rx="2"/><path d="M7 11V7a5 5 0 0 1 10 0v4"/></svg>
    <span>Change Password</span>
  </button>
</form>

<a href="{{ url_for('index') }}" class="btn-secondary">
  <svg class="nav-icon" viewBox="0 0 24 24"><line x1="19" y1="12" x2="5" y2="12"/><polyline points="12 19 5 12 12 5"/></svg>
  <span>Back to Console</span>
</a>
{% endblock %}
"""


ADMIN_USERS_TEMPLATE = """
{% extends "base" %}
{% block title %}User Management · ECET × SMVMCH{% endblock %}
{% block breadcrumb %}User Management (Admin){% endblock %}

{% block content %}
<div class="page-header">
  <h1>👥 User Management</h1>
  <p>Create, read, update, and deactivate user accounts. Role-Based Access Control (RBAC).</p>
</div>

<div class="stats-grid">
  <div class="stat-card"><div class="stat-value">{{ stats.total }}</div><div class="stat-label">Total Users</div></div>
  <div class="stat-card"><div class="stat-value">{{ stats.active }}</div><div class="stat-label">Active</div></div>
  <div class="stat-card"><div class="stat-value">{{ stats.inactive }}</div><div class="stat-label">Inactive</div></div>
  <div class="stat-card"><div class="stat-value">{{ stats.admins }}</div><div class="stat-label">Admins</div></div>
  <div class="stat-card"><div class="stat-value">{{ stats.auditors }}</div><div class="stat-label">Auditors</div></div>
  <div class="stat-card"><div class="stat-value">{{ stats.users }}</div><div class="stat-label">Standard Users</div></div>
</div>

<div class="card">
  <h2>📊 Active vs Inactive</h2>
  <div class="ratio-bar">
    <div class="ratio-seg s1" style="width:{{ ratio.active_pct }}%" title="Active"></div>
    <div class="ratio-seg s2" style="width:{{ ratio.inactive_pct }}%" title="Inactive"></div>
  </div>
  <div class="ratio-legend">
    <span><span class="swatch s1"></span>Active — {{ stats.active }} ({{ ratio.active_pct }}%)</span>
    <span><span class="swatch s2"></span>Inactive — {{ stats.inactive }} ({{ ratio.inactive_pct }}%)</span>
  </div>

  <div class="progress-wrap" style="margin-top:22px">
    <div class="progress-label">
      <span>Admins</span>
      <span class="pct">{{ stats.admins }} / {{ stats.total }} ({{ ratio.admin_pct }}%)</span>
    </div>
    <div class="progress-track">
      <div class="progress-fill navy" style="width:{{ ratio.admin_pct }}%"></div>
    </div>
  </div>
  <div class="progress-wrap">
    <div class="progress-label">
      <span>Auditors</span>
      <span class="pct">{{ stats.auditors }} / {{ stats.total }} ({{ ratio.auditor_pct }}%)</span>
    </div>
    <div class="progress-track">
      <div class="progress-fill warning" style="width:{{ ratio.auditor_pct }}%"></div>
    </div>
  </div>
  <div class="progress-wrap">
    <div class="progress-label">
      <span>Standard Users</span>
      <span class="pct">{{ stats.users }} / {{ stats.total }} ({{ ratio.user_pct }}%)</span>
    </div>
    <div class="progress-track">
      <div class="progress-fill" style="width:{{ ratio.user_pct }}%"></div>
    </div>
  </div>
</div>

<div class="card">
  <h2>➕ Create New User</h2>
  <form method="post" action="{{ url_for('admin_users_create') }}">
    <div class="grid-3">
      <label>Username <span class="req">*</span> <input type="text" name="username" required minlength="3" maxlength="32" /></label>
      <label>Email <input type="email" name="email" maxlength="120" /></label>
      <label>Full Name <input type="text" name="full_name" maxlength="120" /></label>
      <label>Department <input type="text" name="department" maxlength="120" /></label>
      <label>Phone <input type="tel" name="phone" maxlength="32" /></label>
      <label>Role <span class="req">*</span>
        <select name="role" required>
          <option value="user">user</option>
          <option value="auditor">auditor</option>
          <option value="admin">admin</option>
        </select>
      </label>
      <label>Password <span class="req">*</span> <input type="password" name="password" required minlength="6" /></label>
      <label>Confirm Password <span class="req">*</span> <input type="password" name="confirm" required minlength="6" /></label>
      <label>Active
        <select name="is_active"><option value="1" selected>Yes</option><option value="0">No</option></select>
      </label>
    </div>
    <button type="submit" class="btn-primary">
      <svg class="nav-icon" viewBox="0 0 24 24"><path d="M16 21v-2a4 4 0 0 0-4-4H6a4 4 0 0 0-4 4v2"/><circle cx="9" cy="7" r="4"/><line x1="19" y1="8" x2="19" y2="14"/><line x1="22" y1="11" x2="16" y2="11"/></svg>
      <span>Create User</span>
    </button>
  </form>
</div>

<form method="get" action="{{ url_for('admin_users') }}" class="card">
  <h2>🔎 Search Users</h2>
  <div class="grid-3">
    <label>Username / Name / Email <input type="text" name="q" value="{{ f_q }}" placeholder="search..." /></label>
    <label>Role
      <select name="role">
        <option value="" {% if not f_role %}selected{% endif %}>All</option>
        <option value="admin" {% if f_role == 'admin' %}selected{% endif %}>admin</option>
        <option value="auditor" {% if f_role == 'auditor' %}selected{% endif %}>auditor</option>
        <option value="user" {% if f_role == 'user' %}selected{% endif %}>user</option>
      </select>
    </label>
    <label>Status
      <select name="status">
        <option value="" {% if not f_status %}selected{% endif %}>All</option>
        <option value="active" {% if f_status == 'active' %}selected{% endif %}>Active</option>
        <option value="inactive" {% if f_status == 'inactive' %}selected{% endif %}>Inactive</option>
      </select>
    </label>
  </div>
  <button type="submit" class="btn-primary">
    <svg class="nav-icon" viewBox="0 0 24 24"><circle cx="11" cy="11" r="7"/><line x1="21" y1="21" x2="16.5" y2="16.5"/></svg>
    <span>Apply Filter</span>
  </button>
</form>

<div class="card">
  <h2>📋 Users ({{ rows|length }} shown)</h2>
  <div class="table-scroll">
    <table class="data-table">
      <thead><tr>
        <th>#</th><th>Username</th><th>Full Name</th><th>Email</th>
        <th>Department</th><th>Role</th><th>Status</th>
        <th>Created</th><th>Last Login</th><th>Actions</th>
      </tr></thead>
      <tbody>
        {% for u in rows %}
        <tr>
          <td>{{ u.id }}</td>
          <td><strong>{{ u.username }}</strong></td>
          <td>{{ u.full_name or "-" }}</td>
          <td>{{ u.email or "-" }}</td>
          <td>{{ u.department or "-" }}</td>
          <td><span class="role-badge role-{{ u.role }}">{{ u.role }}</span></td>
          <td>
            <span class="status-dot {{ 'dot-active' if u.is_active else 'dot-inactive' }}"></span>
            {{ 'Active' if u.is_active else 'Inactive' }}
          </td>
          <td>{{ u.created_at.strftime("%Y-%m-%d %H:%M") if u.created_at else "-" }}</td>
          <td>{{ u.last_login.strftime("%Y-%m-%d %H:%M") if u.last_login else "—" }}</td>
          <td>
            <div class="row-actions">
              <a class="btn-sm" href="{{ url_for('admin_users_edit', user_id=u.id) }}">Edit</a>
              <form method="post" action="{{ url_for('admin_users_toggle', user_id=u.id) }}" style="display:inline">
                <button class="btn-sm" type="submit">{{ 'Disable' if u.is_active else 'Enable' }}</button>
              </form>
              <form method="post" action="{{ url_for('admin_users_reset_pw', user_id=u.id) }}" style="display:inline"
                    onsubmit="return confirm('Reset password for {{ u.username }}?')">
                <button class="btn-sm" type="submit">Reset PW</button>
              </form>
              {% if u.id != user.id %}
              <form method="post" action="{{ url_for('admin_users_delete', user_id=u.id) }}" style="display:inline"
                    onsubmit="return confirm('DELETE user {{ u.username }}? This cannot be undone.')">
                <button class="btn-sm danger" type="submit">Delete</button>
              </form>
              {% endif %}
            </div>
          </td>
        </tr>
        {% endfor %}
      </tbody>
    </table>
  </div>
</div>

<a href="{{ url_for('index') }}" class="btn-secondary">
  <svg class="nav-icon" viewBox="0 0 24 24"><line x1="19" y1="12" x2="5" y2="12"/><polyline points="12 19 5 12 12 5"/></svg>
  <span>Back to Console</span>
</a>
{% endblock %}
"""


ADMIN_USER_EDIT_TEMPLATE = """
{% extends "base" %}
{% block title %}Edit User · ECET × SMVMCH{% endblock %}
{% block breadcrumb %}Edit User — {{ target.username }}{% endblock %}

{% block content %}
<div class="page-header">
  <h1>✏️ Edit User</h1>
  <p>Update account details, role, or status for <strong>{{ target.username }}</strong>.</p>
</div>

<form method="post" action="{{ url_for('admin_users_edit', user_id=target.id) }}" class="card">
  <h2>Account Details</h2>
  <div class="grid-2">
    <label>Username <span class="req">*</span> <input type="text" name="username" value="{{ target.username }}" required minlength="3" maxlength="32" /></label>
    <label>Email <input type="email" name="email" value="{{ target.email or '' }}" maxlength="120" /></label>
    <label>Full Name <input type="text" name="full_name" value="{{ target.full_name or '' }}" maxlength="120" /></label>
    <label>Department <input type="text" name="department" value="{{ target.department or '' }}" maxlength="120" /></label>
    <label>Phone <input type="tel" name="phone" value="{{ target.phone or '' }}" maxlength="32" /></label>
    <label>Role <span class="req">*</span>
      <select name="role" required>
        <option value="user" {% if target.role == 'user' %}selected{% endif %}>user</option>
        <option value="auditor" {% if target.role == 'auditor' %}selected{% endif %}>auditor</option>
        <option value="admin" {% if target.role == 'admin' %}selected{% endif %}>admin</option>
      </select>
    </label>
    <label>Status
      <select name="is_active">
        <option value="1" {% if target.is_active %}selected{% endif %}>Active</option>
        <option value="0" {% if not target.is_active %}selected{% endif %}>Inactive</option>
      </select>
    </label>
  </div>

  <h2 style="margin-top:24px">Change Password (optional)</h2>
  <div class="grid-2">
    <label>New Password <input type="password" name="new_password" minlength="6" placeholder="Leave blank to keep current" /></label>
    <label>Confirm New Password <input type="password" name="confirm" minlength="6" placeholder="Repeat new password" /></label>
  </div>

  <button type="submit" class="btn-primary">
    <svg class="nav-icon" viewBox="0 0 24 24"><path d="M19 21H5a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h11l5 5v11a2 2 0 0 1-2 2z"/><polyline points="17 21 17 13 7 13 7 21"/><polyline points="7 3 7 8 15 8"/></svg>
    <span>Save Changes</span>
  </button>
</form>

<a href="{{ url_for('admin_users') }}" class="btn-secondary">
  <svg class="nav-icon" viewBox="0 0 24 24"><line x1="19" y1="12" x2="5" y2="12"/><polyline points="12 19 5 12 12 5"/></svg>
  <span>Back to Users</span>
</a>
{% endblock %}
"""


REID_TEMPLATE = """
{% extends "base" %}
{% block title %}Re-identification · ECET × SMVMCH{% endblock %}
{% block breadcrumb %}Re-identification (Admin){% endblock %}

{% block content %}
<div class="page-header">
  <h1>🔓 Re-identification Console</h1>
  <p>Reverse the de-identification for audit or clinical follow-up. Every reversal is logged.</p>
</div>

<div class="card" style="background:#fffbeb;border-left:4px solid var(--warning)">
  <h2 style="border:none;padding:0;margin:0 0 6px">⚠️ Security Notice</h2>
  <p style="margin:0;color:#78350f;font-size:.9rem">
    Re-identified files contain <strong>Protected Health Information (PHI)</strong>.
    Only use for authorized clinical or audit purposes. All actions are permanently logged.
  </p>
</div>

<form method="get" action="{{ url_for('admin_reidentify') }}" class="card">
  <h2>🔎 Search Crosswalk</h2>
  <div class="grid-3">
    <label>Search term <input type="text" name="q" value="{{ q }}" placeholder="e.g. P001, IP005, smv003, smvip007" autofocus /></label>
    <label>Search in
      <select name="kind">
        <option value="both" {% if kind == 'both' %}selected{% endif %}>MR + IP</option>
        <option value="mr" {% if kind == 'mr' %}selected{% endif %}>MR only</option>
        <option value="ip" {% if kind == 'ip' %}selected{% endif %}>IP only</option>
      </select>
    </label>
    <label>Reason (required) <input type="text" name="reason" value="{{ reason }}" placeholder="e.g. audit" maxlength="255" /></label>
  </div>
  <button type="submit" class="btn-primary">
    <svg class="nav-icon" viewBox="0 0 24 24"><circle cx="11" cy="11" r="7"/><line x1="21" y1="21" x2="16.5" y2="16.5"/></svg>
    <span>Search</span>
  </button>
</form>

{% if q %}
<div class="stats-grid">
  <div class="stat-card"><div class="stat-value">{{ results.mr|length }}</div><div class="stat-label">MR Matches</div></div>
  <div class="stat-card"><div class="stat-value">{{ results.ip|length }}</div><div class="stat-label">IP Matches</div></div>
</div>

{% if results.mr %}
<div class="card">
  <h2>🧬 MR Crosswalk Matches</h2>
  <div class="table-scroll">
    <table class="data-table">
      <thead><tr><th>Dummy MR</th><th>Original MR</th></tr></thead>
      <tbody>
        {% for row in results.mr %}
        <tr><td><strong>{{ row.dummyMR }}</strong></td><td>{{ row.originalMR }}</td></tr>
        {% endfor %}
      </tbody>
    </table>
  </div>
</div>
{% endif %}

{% if results.ip %}
<div class="card">
  <h2>🏥 IP Crosswalk Matches <span style="font-size:.72rem;font-weight:500;color:var(--text-muted)">— globally unique</span></h2>
  <div class="table-scroll">
    <table class="data-table">
      <thead><tr><th>Dummy MR</th><th>Dummy IP</th><th>Original MR</th><th>Original IP</th></tr></thead>
      <tbody>
        {% for row in results.ip %}
        <tr><td>{{ row.dummyMR }}</td><td><strong>{{ row.dummyIP }}</strong></td><td>{{ row.originalMR }}</td><td>{{ row.originalIP }}</td></tr>
        {% endfor %}
      </tbody>
    </table>
  </div>
</div>
{% endif %}

{% if not results.mr and not results.ip %}
<div class="card">
  <h2>No matches</h2>
  <p class="warn">No crosswalk entries matched "<strong>{{ q }}</strong>".</p>
</div>
{% endif %}

<div class="card">
  <h2>🔓 Generate Re-identified Output</h2>
  <p class="preview-note">
    Creates re-identified copies of the de-identified datasets, restricted to
    the matched dummy MR / IP identifiers. Files are written to <code>public/</code>.
  </p>
  <form method="post" action="{{ url_for('admin_reidentify_run') }}">
    <input type="hidden" name="q" value="{{ q }}" />
    <input type="hidden" name="kind" value="{{ kind }}" />
    <div class="grid-2">
      <label>Reason <span class="req">*</span>
        <input type="text" name="reason" required maxlength="255" value="{{ reason }}" placeholder="e.g. clinician requested" /></label>
      <label>Notes (optional)
        <input type="text" name="notes" maxlength="255" placeholder="reference number, ticket ID, etc." /></label>
    </div>
    <button type="submit" class="btn-danger">
      <svg class="nav-icon" viewBox="0 0 24 24"><rect x="3" y="11" width="18" height="11" rx="2"/><path d="M7 11V7a5 5 0 0 0 10 0v4"/></svg>
      <span>Re-identify &amp; Export</span>
    </button>
  </form>
</div>
{% endif %}

{% if history %}
<div class="card">
  <h2>📜 Recent Re-identification Requests</h2>
  <div class="table-scroll">
    <table class="data-table">
      <thead><tr>
        <th>#</th><th>When</th><th>Admin</th><th>Query</th>
        <th>Mode</th><th>Matched</th><th>Reason</th><th>Download</th>
      </tr></thead>
      <tbody>
        {% for h in history %}
        <tr>
          <td>{{ h.id }}</td>
          <td>{{ h.timestamp.strftime("%Y-%m-%d %H:%M:%S") if h.timestamp else "" }}</td>
          <td>{{ h.admin_username or "-" }}</td>
          <td><code>{{ h.search_query or "-" }}</code></td>
          <td>{{ h.mode }}</td>
          <td>{{ h.match_count }}</td>
          <td>{{ h.reason or "-" }}</td>
          <td>
            {% if h.download_file %}
              <a class="btn-sm" href="{{ url_for('download', filename=h.download_file) }}">sh1</a>
              {% set f2 = h.download_file.replace('sh1_reidentified', 'sh2_reidentified') %}
              <a class="btn-sm" href="{{ url_for('download', filename=f2) }}">sh2</a>
            {% else %}—{% endif %}
          </td>
        </tr>
        {% endfor %}
      </tbody>
    </table>
  </div>
</div>
{% endif %}

<a href="{{ url_for('index') }}" class="btn-secondary">
  <svg class="nav-icon" viewBox="0 0 24 24"><line x1="19" y1="12" x2="5" y2="12"/><polyline points="12 19 5 12 12 5"/></svg>
  <span>Back to Console</span>
</a>
{% endblock %}
"""


MRIP_REGISTRY_TEMPLATE = """
{% extends "base" %}
{% block title %}MR/IP Registry · ECET × SMVMCH{% endblock %}
{% block breadcrumb %}MR/IP Registry{% endblock %}

{% block content %}
<div class="page-header">
  <h1>🔐 MR / IP Registry</h1>
  <p>Every distinct (MR, IP) pair ever processed, with its content signature.
     Used to detect cross-file duplicates and identifier conflicts.</p>
</div>

<div class="stats-grid">
  <div class="stat-card"><div class="stat-value">{{ total }}</div><div class="stat-label">Registered pairs</div></div>
</div>

<form method="get" action="{{ url_for('admin_mrip_registry') }}" class="card">
  <h2>🔎 Search</h2>
  <div class="audit-filter">
    <label>MR / IP / dummy <input type="text" name="q" value="{{ f_query }}" placeholder="e.g. smv001, P001, smvip003" /></label>
    <label>Limit <input type="number" name="limit" value="{{ f_limit }}" min="10" max="2000" /></label>
  </div>
  <button type="submit" class="btn-primary">
    <svg class="nav-icon" viewBox="0 0 24 24"><circle cx="11" cy="11" r="7"/><line x1="21" y1="21" x2="16.5" y2="16.5"/></svg>
    <span>Apply Filter</span>
  </button>
</form>

<div class="card">
  <h2>📋 Registry ({{ rows|length }} shown)</h2>
  <div class="table-scroll">
    <table class="data-table">
      <thead><tr>
        <th>#</th><th>Original MR</th><th>Original IP</th>
        <th>Dummy MR</th><th>Dummy IP</th>
        <th>Rows</th><th>Seen</th>
        <th>First job</th><th>By</th><th>Last update</th>
      </tr></thead>
      <tbody>
        {% for r in rows %}
        <tr>
          <td>{{ r.id }}</td>
          <td><code>{{ r.original_mr }}</code></td>
          <td><code>{{ r.original_ip }}</code></td>
          <td><code>{{ r.dummy_mr or "—" }}</code></td>
          <td><code>{{ r.dummy_ip or "—" }}</code></td>
          <td>{{ r.row_count if r.row_count is not none else "—" }}</td>
          <td>{{ r.seen_count or 1 }}</td>
          <td><code>{{ r.job_id or "—" }}</code></td>
          <td>{{ r.username or "—" }}</td>
          <td>{{ r.timestamp.strftime("%Y-%m-%d %H:%M:%S") if r.timestamp else "—" }}</td>
        </tr>
        {% endfor %}
      </tbody>
    </table>
  </div>
</div>

<a href="{{ url_for('index') }}" class="btn-secondary">
  <svg class="nav-icon" viewBox="0 0 24 24"><line x1="19" y1="12" x2="5" y2="12"/><polyline points="12 19 5 12 12 5"/></svg>
  <span>Back to Console</span>
</a>
{% endblock %}
"""


AUDIT_TEMPLATE = """
{% extends "base" %}
{% block title %}Audit Log · ECET × SMVMCH{% endblock %}
{% block breadcrumb %}Transaction Audit Log{% endblock %}

{% block content %}
<div class="page-header">
  <h1>📜 Transaction Audit Log</h1>
  <p>Every login, upload, download, de-identification run, and error is recorded below.</p>
</div>

<form method="get" action="{{ url_for('audit_page') }}" class="card">
  <h2>🔎 Filter</h2>
  <div class="audit-filter">
    <label>Username <input type="text" name="username" value="{{ f_username }}" placeholder="e.g. admin" /></label>
    <label>Action <input type="text" name="action" value="{{ f_action }}" placeholder="e.g. login" /></label>
    <label>Status
      <select name="status">
        <option value="" {% if not f_status %}selected{% endif %}>All</option>
        <option value="success" {% if f_status == 'success' %}selected{% endif %}>Success</option>
        <option value="failed" {% if f_status == 'failed' %}selected{% endif %}>Failed</option>
        <option value="denied" {% if f_status == 'denied' %}selected{% endif %}>Denied</option>
        <option value="info" {% if f_status == 'info' %}selected{% endif %}>Info</option>
      </select>
    </label>
    <label>Limit <input type="number" name="limit" value="{{ f_limit }}" min="10" max="2000" /></label>
  </div>
  <button type="submit" class="btn-primary">
    <svg class="nav-icon" viewBox="0 0 24 24"><circle cx="11" cy="11" r="7"/><line x1="21" y1="21" x2="16.5" y2="16.5"/></svg>
    <span>Apply Filter</span>
  </button>
</form>

<div class="stats-grid">
  <div class="stat-card"><div class="stat-value">{{ stats.total }}</div><div class="stat-label">Total Events</div></div>
  <div class="stat-card"><div class="stat-value">{{ stats.success }}</div><div class="stat-label">Success</div></div>
  <div class="stat-card"><div class="stat-value">{{ stats.failed }}</div><div class="stat-label">Failed</div></div>
  <div class="stat-card"><div class="stat-value">{{ stats.denied }}</div><div class="stat-label">Denied</div></div>
  <div class="stat-card"><div class="stat-value">{{ stats.info }}</div><div class="stat-label">Info</div></div>
</div>

<div class="card">
  <h2>📊 Event Status Distribution</h2>
  <div class="ratio-bar">
    <div class="ratio-seg s1" style="width:{{ ratio.success_pct }}%" title="Success"></div>
    <div class="ratio-seg s2" style="width:{{ ratio.failed_pct }}%" title="Failed"></div>
    <div class="ratio-seg s3" style="width:{{ ratio.denied_pct }}%" title="Denied"></div>
    <div class="ratio-seg s4" style="width:{{ ratio.info_pct }}%" title="Info"></div>
  </div>
  <div class="ratio-legend">
    <span><span class="swatch s1"></span>Success — {{ stats.success }} ({{ ratio.success_pct }}%)</span>
    <span><span class="swatch s2"></span>Failed — {{ stats.failed }} ({{ ratio.failed_pct }}%)</span>
    <span><span class="swatch s3"></span>Denied — {{ stats.denied }} ({{ ratio.denied_pct }}%)</span>
    <span><span class="swatch s4"></span>Info — {{ stats.info }} ({{ ratio.info_pct }}%)</span>
  </div>
</div>

<div class="card">
  <h2>📋 Recent Transactions ({{ rows|length }} shown)</h2>
  <div class="table-scroll">
    <table class="data-table">
      <thead><tr>
        <th>#</th><th>Timestamp</th><th>User</th><th>Role</th>
        <th>Action</th><th>Status</th><th>Entity</th>
        <th>IP</th><th>Path</th><th>Message</th><th>Details</th>
      </tr></thead>
      <tbody>
        {% for row in rows %}
        <tr>
          <td>{{ row.id }}</td>
          <td>{{ row.timestamp.strftime("%Y-%m-%d %H:%M:%S") if row.timestamp else "" }}</td>
          <td>{{ row.username or "-" }}</td>
          <td>{{ row.role or "-" }}</td>
          <td>{{ row.action }}</td>
          <td>
            <span class="audit-badge badge-{{ row.status if row.status in ('success','failed','denied') else 'info' }}">
              {{ row.status }}
            </span>
          </td>
          <td>{{ row.entity or "-" }}{% if row.entity_id %} / {{ row.entity_id }}{% endif %}</td>
          <td>{{ row.ip_address or "-" }}</td>
          <td>{{ row.path or "-" }}</td>
          <td>{{ row.message or "-" }}</td>
          <td class="audit-details">{{ row.details or "" }}</td>
        </tr>
        {% endfor %}
      </tbody>
    </table>
  </div>
</div>

<a href="{{ url_for('index') }}" class="btn-secondary">
  <svg class="nav-icon" viewBox="0 0 24 24"><line x1="19" y1="12" x2="5" y2="12"/><polyline points="12 19 5 12 12 5"/></svg>
  <span>Back to Console</span>
</a>
{% endblock %}
"""


ADMIN_UPLOADS_TEMPLATE = """
{% extends "base" %}
{% block title %}Upload Records · ECET × SMVMCH{% endblock %}
{% block breadcrumb %}Upload Records (Admin){% endblock %}

{% block content %}
<div class="page-header">
  <h1>📁 Upload Records</h1>
  <p>Every upload attempt by every user — success, failure, rejected, and deduplicated.</p>
</div>

<div class="stats-grid">
  <div class="stat-card"><div class="stat-value">{{ stats.total }}</div><div class="stat-label">Total Uploads</div></div>
  <div class="stat-card"><div class="stat-value">{{ stats.success }}</div><div class="stat-label">Success</div></div>
  <div class="stat-card"><div class="stat-value">{{ stats.failed }}</div><div class="stat-label">Failed</div></div>
  <div class="stat-card"><div class="stat-value">{{ stats.rejected }}</div><div class="stat-label">Rejected</div></div>
  <div class="stat-card"><div class="stat-value">{{ stats.skipped }}</div><div class="stat-label">Skipped (dup)</div></div>
</div>

<div class="card">
  <h2>📊 Upload Outcome Distribution</h2>
  <div class="ratio-bar">
    <div class="ratio-seg s1" style="width:{{ ratio.success_pct }}%" title="Success"></div>
    <div class="ratio-seg s2" style="width:{{ ratio.failed_pct }}%" title="Failed"></div>
    <div class="ratio-seg s3" style="width:{{ ratio.rejected_pct }}%" title="Rejected"></div>
    <div class="ratio-seg s4" style="width:{{ ratio.skipped_pct }}%" title="Skipped"></div>
  </div>
  <div class="ratio-legend">
    <span><span class="swatch s1"></span>Success — {{ stats.success }} ({{ ratio.success_pct }}%)</span>
    <span><span class="swatch s2"></span>Failed — {{ stats.failed }} ({{ ratio.failed_pct }}%)</span>
    <span><span class="swatch s3"></span>Rejected — {{ stats.rejected }} ({{ ratio.rejected_pct }}%)</span>
    <span><span class="swatch s4"></span>Skipped — {{ stats.skipped }} ({{ ratio.skipped_pct }}%)</span>
  </div>

  <div class="progress-wrap" style="margin-top:22px">
    <div class="progress-label">
      <span>Success rate</span>
      <span class="pct">{{ ratio.success_pct }}%</span>
    </div>
    <div class="progress-track tall">
      <div class="progress-fill success" style="width:{{ ratio.success_pct }}%"></div>
    </div>
  </div>
</div>

<form method="get" action="{{ url_for('admin_uploads') }}" class="card">
  <h2>🔎 Filter</h2>
  <div class="audit-filter">
    <label>Username <input type="text" name="username" value="{{ f_username }}" placeholder="e.g. admin" /></label>
    <label>Status
      <select name="status">
        <option value="" {% if not f_status %}selected{% endif %}>All</option>
        <option value="success" {% if f_status == 'success' %}selected{% endif %}>Success</option>
        <option value="failed" {% if f_status == 'failed' %}selected{% endif %}>Failed</option>
        <option value="rejected" {% if f_status == 'rejected' %}selected{% endif %}>Rejected</option>
        <option value="skipped" {% if f_status == 'skipped' %}selected{% endif %}>Skipped (duplicate)</option>
      </select>
    </label>
    <label>Limit <input type="number" name="limit" value="{{ f_limit }}" min="10" max="2000" /></label>
  </div>
  <button type="submit" class="btn-primary">
    <svg class="nav-icon" viewBox="0 0 24 24"><circle cx="11" cy="11" r="7"/><line x1="21" y1="21" x2="16.5" y2="16.5"/></svg>
    <span>Apply Filter</span>
  </button>
</form>

<div class="card">
  <h2>📋 Upload History ({{ rows|length }} shown)</h2>
  <div class="table-scroll">
    <table class="data-table">
      <thead><tr>
        <th>#</th><th>Job</th><th>When</th><th>User</th><th>Role</th>
        <th>File</th><th>Size</th><th>Status</th>
        <th>MR / IP</th><th>Rows</th><th>Message</th><th>Download</th>
      </tr></thead>
      <tbody>
        {% for r in rows %}
        <tr>
          <td>{{ r.id }}</td>
          <td><code>{{ r.job_id or "-" }}</code></td>
          <td>{{ r.timestamp.strftime("%Y-%m-%d %H:%M:%S") if r.timestamp else "-" }}</td>
          <td>{{ r.username or "-" }}</td>
          <td>{% if r.role %}<span class="role-badge role-{{ r.role }}">{{ r.role }}</span>{% else %}-{% endif %}</td>
          <td title="{{ r.original_name }}">{{ (r.original_name or "-")[:30] }}{% if r.original_name and r.original_name|length > 30 %}…{% endif %}</td>
          <td>{% if r.size_bytes %}{{ (r.size_bytes / 1024) | round(1) }} KB{% else %}-{% endif %}</td>
          <td>
            {% if r.status == 'success' %}
              <span class="audit-badge badge-success">success</span>
            {% elif r.status == 'skipped' %}
              <span class="audit-badge badge-skipped">skipped</span>
            {% elif r.status == 'rejected' %}
              <span class="audit-badge badge-denied">rejected</span>
            {% else %}
              <span class="audit-badge badge-failed">failed</span>
            {% endif %}
          </td>
          <td>{% if r.unique_mr is not none %}{{ r.unique_mr }} / {{ r.unique_ip }}{% else %}-{% endif %}</td>
          <td>{% if r.sheet1_rows is not none %}{{ r.sheet1_rows }} + {{ r.sheet2_rows }}{% else %}-{% endif %}</td>
          <td title="{{ r.message or '' }}">{{ (r.message or "-")[:60] }}{% if r.message and r.message|length > 60 %}…{% endif %}</td>
          <td>
            {% if r.status in ('success', 'skipped') and r.sh1_file %}
              <a class="btn-sm" href="{{ url_for('download', filename=r.sh1_file) }}">sh1</a>
              <a class="btn-sm" href="{{ url_for('download', filename=r.sh2_file) }}">sh2</a>
            {% else %}—{% endif %}
          </td>
        </tr>
        {% endfor %}
      </tbody>
    </table>
  </div>
</div>

<a href="{{ url_for('index') }}" class="btn-secondary">
  <svg class="nav-icon" viewBox="0 0 24 24"><line x1="19" y1="12" x2="5" y2="12"/><polyline points="12 19 5 12 12 5"/></svg>
  <span>Back to Console</span>
</a>
{% endblock %}
"""


ADMIN_REPORTS_TEMPLATE = """
{% extends "base" %}
{% block title %}Similarity Reports · ECET × SMVMCH{% endblock %}
{% block breadcrumb %}Similarity Reports (Admin){% endblock %}

{% block content %}
<div class="page-header">
  <h1>🔍 Similarity Reports</h1>
  <p>Before-vs-after comparison for every de-identification job.</p>
</div>

<div class="stats-grid">
  <div class="stat-card"><div class="stat-value">{{ stats.total }}</div><div class="stat-label">Reports</div></div>
  <div class="stat-card"><div class="stat-value">{{ stats.avg_combined }}%</div><div class="stat-label">Avg Combined</div></div>
  <div class="stat-card"><div class="stat-value">{{ stats.perfect }}</div><div class="stat-label">≥ 99% match</div></div>
  <div class="stat-card"><div class="stat-value">{{ stats.warnings }}</div><div class="stat-label">Below 99%</div></div>
</div>

<form method="get" action="{{ url_for('admin_reports') }}" class="card">
  <h2>🔎 Filter</h2>
  <div class="audit-filter">
    <label>Username <input type="text" name="username" value="{{ f_username }}" placeholder="e.g. admin" /></label>
    <label>Limit <input type="number" name="limit" value="{{ f_limit }}" min="10" max="1000" /></label>
  </div>
  <button type="submit" class="btn-primary">
    <svg class="nav-icon" viewBox="0 0 24 24"><circle cx="11" cy="11" r="7"/><line x1="21" y1="21" x2="16.5" y2="16.5"/></svg>
    <span>Apply Filter</span>
  </button>
</form>

<div class="card">
  <h2>📋 Reports ({{ rows|length }} shown)</h2>
  <div class="table-scroll">
    <table class="data-table">
      <thead><tr>
        <th>#</th><th>Job</th><th>When</th><th>User</th>
        <th>sh1 rows</th><th>sh2 rows</th>
        <th>sh1 %</th><th>sh2 %</th><th>Combined</th>
        <th>Rows</th><th>Cols</th>
      </tr></thead>
      <tbody>
        {% for r in rows %}
        <tr>
          <td>{{ r.id }}</td>
          <td><code>{{ r.job_id or "-" }}</code></td>
          <td>{{ r.timestamp.strftime("%Y-%m-%d %H:%M:%S") if r.timestamp else "-" }}</td>
          <td>{{ r.username or "-" }}</td>
          <td>{{ r.sh1_rows }}</td>
          <td>{{ r.sh2_rows }}</td>
          <td>{{ r.sh1_overall_pct }}%</td>
          <td>{{ r.sh2_overall_pct }}%</td>
          <td>
            <span class="progress-mini" style="width:80px">
              <span class="fill {% if (r.combined_pct or 0) < 99 %}failed{% endif %}"
                    style="width:{{ r.combined_pct or 0 }}%"></span>
            </span>
            <span style="font-size:.78rem;color:var(--text-muted);margin-left:6px">
              {{ r.combined_pct }}%
            </span>
          </td>
          <td>{{ '✅' if r.rows_preserved else '⚠️' }}</td>
          <td>{{ '✅' if r.columns_preserved else '⚠️' }}</td>
        </tr>
        {% endfor %}
      </tbody>
    </table>
  </div>
</div>

<a href="{{ url_for('index') }}" class="btn-secondary">
  <svg class="nav-icon" viewBox="0 0 24 24"><line x1="19" y1="12" x2="5" y2="12"/><polyline points="12 19 5 12 12 5"/></svg>
  <span>Back to Console</span>
</a>
{% endblock %}
"""


LOGIN_TEMPLATE = """
{% extends "base" %}
{% block title %}Sign In · ECET × SMVMCH{% endblock %}
{% block breadcrumb %}Authentication{% endblock %}

{% block content %}
<div class="auth-wrapper">
  <div class="auth-card">
    <h1>Sign In</h1>
    <p class="auth-subtitle">Access the clinical de-identification console</p>
    <form id="loginForm" class="auth-form">
      <label>Username <input type="text" id="username" name="username" required autofocus autocomplete="username" /></label>
      <label>Password <input type="password" id="password" name="password" required autocomplete="current-password" /></label>
      <label class="checkbox-label"><input type="checkbox" id="remember" name="remember" value="1" /><span>Keep me signed in for 7 days</span></label>
      <div id="loginError" class="alert alert-error" style="display:none;"></div>
      <div class="progress-wrap" id="loginProgress" style="display:none">
        <div class="progress-label">
          <span>Signing in…</span>
          <span class="pct" id="loginPct">0%</span>
        </div>
        <div class="progress-track">
          <div class="progress-fill striped indeterminate"></div>
        </div>
      </div>
      <button type="submit" class="btn-primary">
        <svg class="nav-icon" viewBox="0 0 24 24"><path d="M15 3h4a2 2 0 0 1 2 2v14a2 2 0 0 1-2 2h-4"/><polyline points="10 17 15 12 10 7"/><line x1="15" y1="12" x2="3" y2="12"/></svg>
        <span>Sign In</span>
      </button>
    </form>
    <p class="auth-footer">No account yet? <a href="{{ url_for('register_page') }}">Create one</a></p>
  </div>
</div>
{% endblock %}

{% block scripts %}
<script>
document.getElementById("loginForm").addEventListener("submit", async (e) => {
  e.preventDefault();
  const errBox = document.getElementById("loginError");
  const prog = document.getElementById("loginProgress");
  const pct = document.getElementById("loginPct");
  errBox.style.display = "none";
  prog.style.display = "block";
  pct.textContent = "0%";

  const payload = {
    username: document.getElementById("username").value.trim(),
    password: document.getElementById("password").value,
    remember: document.getElementById("remember").checked,
  };

  let fake = 0;
  const timer = setInterval(() => {
    fake = Math.min(fake + Math.random() * 12, 90);
    pct.textContent = fake.toFixed(0) + "%";
  }, 180);

  try {
    const res = await fetch("/api/auth/login", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      credentials: "same-origin",
      body: JSON.stringify(payload),
    });
    const data = await res.json();
    clearInterval(timer);
    if (!res.ok) {
      prog.style.display = "none";
      errBox.textContent = data.message || "Login failed";
      errBox.style.display = "block";
      return;
    }
    pct.textContent = "100%";
    window.location.href = "/";
  } catch (err) {
    clearInterval(timer);
    prog.style.display = "none";
    errBox.textContent = "Network error: " + err.message;
    errBox.style.display = "block";
  }
});
</script>
{% endblock %}
"""


REGISTER_TEMPLATE = """
{% extends "base" %}
{% block title %}Register · ECET × SMVMCH{% endblock %}
{% block breadcrumb %}Registration{% endblock %}

{% block content %}
<div class="auth-wrapper">
  <div class="auth-card">
    <h1>Create Account</h1>
    <p class="auth-subtitle">Register to use the de-identification tool</p>
    <form id="registerForm" class="auth-form">
      <label>Username <span class="req">*</span> <input type="text" id="username" name="username" required minlength="3" /></label>
      <label>Email (optional) <input type="email" id="email" name="email" /></label>
      <label>Password <span class="req">*</span> <input type="password" id="password" name="password" required minlength="6" /></label>
      <label>Confirm Password <span class="req">*</span> <input type="password" id="confirm" name="confirm" required minlength="6" /></label>
      <div id="regError" class="alert alert-error" style="display:none;"></div>
      <div id="regSuccess" class="alert alert-success" style="display:none;"></div>
      <div class="progress-wrap" id="regProgress" style="display:none">
        <div class="progress-label">
          <span>Creating account…</span>
          <span class="pct">…</span>
        </div>
        <div class="progress-track">
          <div class="progress-fill striped indeterminate"></div>
        </div>
      </div>
      <button type="submit" class="btn-primary">
        <svg class="nav-icon" viewBox="0 0 24 24"><path d="M16 21v-2a4 4 0 0 0-4-4H6a4 4 0 0 0-4 4v2"/><circle cx="9" cy="7" r="4"/><line x1="19" y1="8" x2="19" y2="14"/><line x1="22" y1="11" x2="16" y2="11"/></svg>
        <span>Create Account</span>
      </button>
    </form>
    <p class="auth-footer">Already registered? <a href="{{ url_for('login_page') }}">Sign in</a></p>
  </div>
</div>
{% endblock %}

{% block scripts %}
<script>
document.getElementById("registerForm").addEventListener("submit", async (e) => {
  e.preventDefault();
  const errBox = document.getElementById("regError");
  const okBox = document.getElementById("regSuccess");
  const prog = document.getElementById("regProgress");
  errBox.style.display = "none"; okBox.style.display = "none";
  prog.style.display = "block";

  const payload = {
    username: document.getElementById("username").value.trim(),
    email: document.getElementById("email").value.trim(),
    password: document.getElementById("password").value,
    confirm: document.getElementById("confirm").value,
  };
  try {
    const res = await fetch("/api/auth/register", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify(payload),
    });
    const data = await res.json();
    if (!res.ok) {
      prog.style.display = "none";
      errBox.textContent = data.error || "Registration failed";
      errBox.style.display = "block";
      return;
    }
    prog.style.display = "none";
    okBox.textContent = "Account created. Redirecting to sign-in…";
    okBox.style.display = "block";
    setTimeout(() => window.location.href = "/login", 1200);
  } catch (err) {
    prog.style.display = "none";
    errBox.textContent = "Network error: " + err.message;
    errBox.style.display = "block";
  }
});
</script>
{% endblock %}
"""


# ============================================================
# TEMPLATE REGISTRATION
# ============================================================
def register_inline_templates():
    existing_loader = app.jinja_env.loader
    app.jinja_env.loader = ChoiceLoader([
        DictLoader({
            "base": BASE_TEMPLATE,
            "index_page": INDEX_TEMPLATE,
            "result_page": RESULT_TEMPLATE,
            "profile_page": PROFILE_TEMPLATE,
            "admin_users_page": ADMIN_USERS_TEMPLATE,
            "admin_edit_page": ADMIN_USER_EDIT_TEMPLATE,
            "admin_uploads_page": ADMIN_UPLOADS_TEMPLATE,
            "admin_reports_page": ADMIN_REPORTS_TEMPLATE,
            "reid_page": REID_TEMPLATE,
            "mrip_registry_page": MRIP_REGISTRY_TEMPLATE,
            "audit_page": AUDIT_TEMPLATE,
            "login_page": LOGIN_TEMPLATE,
            "register_page": REGISTER_TEMPLATE,
        }),
        existing_loader,
    ])


def render_page(template_str, **ctx):
    ctx.setdefault("css", CSS)
    ctx.setdefault("copyright_year", COPYRIGHT_YEAR)
    return render_template_string(template_str, **ctx)


register_inline_templates()


# ============================================================
# GLOBAL REQUEST LOGGING
# ============================================================
@app.before_request
def _before_request_log():
    try:
        g._req_start = datetime.utcnow()
    except Exception:
        pass


@app.after_request
def _after_request_log(response):
    try:
        path = request.path or ""
        if path.startswith("/static/") or path in ("/health", "/favicon.ico"):
            return response
        if path == "/api/auth/login" and request.method == "POST":
            return response
        if path.startswith("/api/progress/"):
            return response

        skip_prefixes = (
            "/login", "/logout", "/register", "/", "/upload",
            "/api/auth/logout", "/api/auth/me", "/api/auth/refresh",
            "/api/auth/register", "/dashboard", "/audit",
            "/admin/users", "/admin/uploads", "/admin/reports",
            "/admin/reidentify", "/admin/mrip-registry", "/profile", "/download",
        )
        if any(path.startswith(p) for p in skip_prefixes):
            return response

        status_str = "success" if 200 <= response.status_code < 400 else "failed"
        log_event("http_request", status=status_str,
                  message=f"{request.method} {path} → {response.status_code}")
    except Exception:
        try:
            audit_logger.exception("after_request logging failed")
        except Exception:
            pass
    return response


# ============================================================
# API ROUTES — Progress
# ============================================================
@app.route("/api/progress/<job_id>", methods=["GET"])
@jwt_required
def api_progress(job_id):
    row = progress_get(job_id)
    if not row:
        return jsonify({"error": "unknown_job"}), 404
    return jsonify(row)


# ============================================================
# API ROUTES — Auth
# ============================================================
@app.route("/api/auth/login", methods=["POST"])
def api_login():
    data = request.get_json(silent=True) or {}
    username = data.get("username", "").strip()
    password = data.get("password", "")
    remember = bool(data.get("remember"))

    user = User.query.filter_by(username=username).first()
    if not user or not user.check_password(password):
        log_event("login", status="failed",
                  message=f"Invalid credentials for '{username}'",
                  details={"username": username})
        return jsonify({"error": "invalid_credentials",
                        "message": "Invalid username or password"}), 401
    if not user.is_active:
        log_event("login", status="denied", message="Account disabled", user=user)
        return jsonify({"error": "account_disabled",
                        "message": "Account is disabled"}), 403

    access = create_access_token(user)
    refresh = create_refresh_token(user) if remember else None
    user.last_login = datetime.utcnow()
    db.session.commit()

    log_event("login", status="success",
              message=f"User '{user.username}' logged in",
              details={"remember": remember}, user=user)

    resp = jsonify({
        "success": True, "user": user.to_dict(),
        "access_token": access,
        "expires_in": int(ACCESS_TOKEN_EXPIRY.total_seconds()),
    })
    resp.set_cookie(COOKIE_NAME, access, httponly=True, samesite="Lax",
                    max_age=int(ACCESS_TOKEN_EXPIRY.total_seconds()))
    if refresh:
        resp.set_cookie(REFRESH_COOKIE_NAME, refresh, httponly=True, samesite="Lax",
                        max_age=int(REFRESH_TOKEN_EXPIRY.total_seconds()))
    return resp


@app.route("/api/auth/logout", methods=["POST"])
def api_logout():
    log_event("logout", status="success", message="User logged out")
    resp = jsonify({"success": True, "message": "Logged out"})
    resp.delete_cookie(COOKIE_NAME)
    resp.delete_cookie(REFRESH_COOKIE_NAME)
    return resp


@app.route("/api/auth/me", methods=["GET"])
@jwt_required
def api_me():
    return jsonify({"user": g.current_user.to_dict()})


@app.route("/api/auth/refresh", methods=["POST"])
def api_refresh():
    refresh = request.cookies.get(REFRESH_COOKIE_NAME)
    if not refresh:
        log_event("token_refresh", status="failed", message="No refresh token")
        return jsonify({"error": "no_refresh_token"}), 401
    payload = decode_token(refresh)
    if not payload or payload.get("type") != "refresh":
        log_event("token_refresh", status="failed", message="Invalid refresh token")
        return jsonify({"error": "invalid_refresh_token"}), 401
    user = db.session.get(User, int(payload["sub"]))
    if not user or not user.is_active:
        log_event("token_refresh", status="failed", message="User invalid")
        return jsonify({"error": "user_invalid"}), 401
    new_access = create_access_token(user)
    log_event("token_refresh", status="success",
              message=f"Token refreshed for '{user.username}'", user=user)
    resp = jsonify({"success": True, "access_token": new_access})
    resp.set_cookie(COOKIE_NAME, new_access, httponly=True, samesite="Lax",
                    max_age=int(ACCESS_TOKEN_EXPIRY.total_seconds()))
    return resp


@app.route("/api/auth/register", methods=["POST"])
def api_register():
    data = request.get_json(silent=True) or {}
    errors, cleaned = validate_user_input(
        username=data.get("username", ""),
        email=data.get("email", ""),
        password=data.get("password", ""),
        confirm=data.get("confirm", ""),
        role="user", require_password=True,
    )
    if errors:
        log_event("register", status="failed",
                  message="; ".join(errors),
                  details={"username": data.get("username", "")})
        return jsonify({"error": errors[0]}), 400
    if User.query.filter_by(username=cleaned["username"]).first():
        log_event("register", status="failed", message="Username taken",
                  details={"username": cleaned["username"]})
        return jsonify({"error": "username_taken"}), 409
    if cleaned.get("email") and User.query.filter_by(email=cleaned["email"]).first():
        log_event("register", status="failed", message="Email taken",
                  details={"email": cleaned["email"]})
        return jsonify({"error": "email_taken"}), 409

    user = User(username=cleaned["username"], email=cleaned.get("email"), role="user")
    user.set_password(cleaned["password"])
    db.session.add(user)
    db.session.commit()

    log_event("register", status="success",
              message=f"New user '{user.username}' created",
              entity="user", entity_id=str(user.id), user=user)
    return jsonify({"success": True, "user": user.to_dict()}), 201


# ============================================================
# UI ROUTES — Auth pages
# ============================================================
@app.route("/login", methods=["GET", "POST"])
def login_page():
    token = request.cookies.get(COOKIE_NAME)
    if token and decode_token(token):
        return redirect(url_for("index"))

    if request.method == "POST":
        data = request.get_json(silent=True) if request.is_json else None
        if not data:
            data = request.form.to_dict() or {}

        username = (data.get("username") or "").strip()
        password = data.get("password") or ""
        remember = bool(data.get("remember"))

        user = User.query.filter_by(username=username).first()
        if not user or not user.check_password(password):
            log_event("login", status="failed",
                      message=f"Invalid credentials for '{username}'",
                      details={"username": username})
            flash("Invalid username or password.", "error")
            return render_page(LOGIN_TEMPLATE, user=None), 401
        if not user.is_active:
            log_event("login", status="denied", message="Account disabled", user=user)
            flash("Account is disabled. Contact an administrator.", "error")
            return render_page(LOGIN_TEMPLATE, user=None), 403

        access = create_access_token(user)
        refresh = create_refresh_token(user) if remember else None
        user.last_login = datetime.utcnow()
        db.session.commit()

        log_event("login", status="success",
                  message=f"User '{user.username}' logged in (form fallback)",
                  details={"remember": remember}, user=user)

        resp = make_response(redirect(url_for("index")))
        resp.set_cookie(COOKIE_NAME, access, httponly=True, samesite="Lax",
                        max_age=int(ACCESS_TOKEN_EXPIRY.total_seconds()))
        if refresh:
            resp.set_cookie(REFRESH_COOKIE_NAME, refresh, httponly=True, samesite="Lax",
                            max_age=int(REFRESH_TOKEN_EXPIRY.total_seconds()))
        return resp

    return render_page(LOGIN_TEMPLATE, user=None)


@app.route("/register", methods=["GET", "POST"])
def register_page():
    if request.method == "POST":
        data = request.get_json(silent=True) if request.is_json else None
        if not data:
            data = request.form.to_dict() or {}

        errors, cleaned = validate_user_input(
            username=data.get("username", ""),
            email=data.get("email", ""),
            password=data.get("password", ""),
            confirm=data.get("confirm", ""),
            role="user", require_password=True,
        )
        if errors:
            log_event("register", status="failed",
                      message="; ".join(errors),
                      details={"username": data.get("username", "")})
            flash(" | ".join(errors), "error")
            return render_page(REGISTER_TEMPLATE, user=None), 400

        if User.query.filter_by(username=cleaned["username"]).first():
            log_event("register", status="failed", message="Username taken",
                      details={"username": cleaned["username"]})
            flash("Username already taken.", "error")
            return render_page(REGISTER_TEMPLATE, user=None), 409

        if cleaned.get("email") and User.query.filter_by(email=cleaned["email"]).first():
            log_event("register", status="failed", message="Email taken",
                      details={"email": cleaned["email"]})
            flash("Email already registered.", "error")
            return render_page(REGISTER_TEMPLATE, user=None), 409

        user = User(username=cleaned["username"], email=cleaned.get("email"), role="user")
        user.set_password(cleaned["password"])
        db.session.add(user)
        db.session.commit()

        log_event("register", status="success",
                  message=f"New user '{user.username}' created (form fallback)",
                  entity="user", entity_id=str(user.id), user=user)
        flash("Account created. Please sign in.", "success")
        return redirect(url_for("login_page"))

    return render_page(REGISTER_TEMPLATE, user=None)


@app.route("/logout", methods=["GET"])
def logout_redirect():
    u = getattr(g, "current_user", None)
    if u:
        log_event("logout", status="success",
                  message=f"User '{u.username}' logged out", user=u)
    else:
        log_event("logout", status="success", message="Session ended")
    resp = make_response(redirect(url_for("login_page")))
    resp.delete_cookie(COOKIE_NAME)
    resp.delete_cookie(REFRESH_COOKIE_NAME)
    try:
        session.pop("recent_uploads", None)
    except Exception:
        pass
    flash("You have been logged out.", "success")
    return resp


# ============================================================
# UI ROUTES — Main
# ============================================================
@app.route("/")
@jwt_required
def index():
    log_event("view_index", status="success",
              message="Viewed de-identification console")

    recent_ids = session.get("recent_uploads", [])
    my_uploads = []
    my_reports = []
    if recent_ids:
        rows = (UploadRecord.query
                .filter(UploadRecord.job_id.in_(recent_ids),
                        UploadRecord.user_id == g.current_user.id)
                .all())
        order = {jid: i for i, jid in enumerate(recent_ids)}
        my_uploads = sorted(rows, key=lambda r: order.get(r.job_id, 999))

        my_reports = (SimilarityReport.query
                      .filter(SimilarityReport.job_id.in_(recent_ids),
                              SimilarityReport.user_id == g.current_user.id)
                      .order_by(SimilarityReport.timestamp.desc())
                      .limit(10).all())

    return render_page(INDEX_TEMPLATE, user=g.current_user,
                       my_uploads=my_uploads, my_reports=my_reports)


@app.route("/upload", methods=["POST"])
@jwt_required
def upload():
    if "file" not in request.files:
        flash("No file part in request.", "error")
        return redirect(url_for("index"))

    f = request.files["file"]
    if not f or f.filename == "":
        flash("No file selected.", "error")
        return redirect(url_for("index"))

    if Path(f.filename).suffix.lower() not in ALLOWED_EXT:
        flash("Only .xlsx or .xls files allowed.", "error")
        return redirect(url_for("index"))

    job_id = uuid.uuid4().hex[:8]
    safe_name = secure_filename(f.filename)
    saved_path = UPLOAD_DIR / f"{job_id}_{safe_name}"
    f.save(saved_path)
    size_bytes = saved_path.stat().st_size

    sheet1 = request.form.get("sheet1", "sh1").strip() or "sh1"
    sheet2 = request.form.get("sheet2", "sh2").strip() or "sh2"
    mr_prefix = request.form.get("mr_prefix", "P").strip() or "P"
    ip_prefix = request.form.get("ip_prefix", "IP").strip() or "IP"
    try:
        mr_width = int(request.form.get("mr_width", 3))
        ip_width = int(request.form.get("ip_width", 3))
    except ValueError:
        mr_width, ip_width = 3, 3

    user_id = g.current_user.id
    username = g.current_user.username
    role = g.current_user.role

    content_hash = compute_workbook_fingerprint(saved_path, sheet1, sheet2)

    progress_init(job_id)
    progress_set(job_id, "Received file", 1.0, f"{safe_name} ({size_bytes // 1024} KB)")
    _remember_upload_in_session(job_id)

    # ---- Per-(MR, IP) classification against cross-upload registry ----
    mrip_classification = {"new": [], "identical": [], "conflict": []}
    try:
        raw_sh1 = pd.read_excel(saved_path, sheet_name=sheet1, engine="openpyxl")
        raw_sh2 = pd.read_excel(saved_path, sheet_name=sheet2, engine="openpyxl")
        raw_sh1 = normalize_columns(raw_sh1)
        raw_sh2 = normalize_columns(raw_sh2)

        if ("duplicateMR" in raw_sh1.columns and
            "duplicateIP" in raw_sh1.columns and
            "duplicateMR" in raw_sh2.columns and
            "duplicateIP" in raw_sh2.columns):
            sigs = compute_mrip_signatures(raw_sh1, raw_sh2)
            mrip_classification = classify_mrip_pairs(sigs)
    except Exception:
        traceback.print_exc()
        log_event("mrip_classify", status="failed",
                  message="Per-pair classification failed",
                  entity="upload", entity_id=job_id)

    total_pairs = (len(mrip_classification["new"]) +
                   len(mrip_classification["identical"]) +
                   len(mrip_classification["conflict"]))
    all_identical = (total_pairs > 0
                     and len(mrip_classification["new"]) == 0
                     and len(mrip_classification["conflict"]) == 0)

    # ---- If every pair is a known-identical duplicate, skip ----
    if all_identical or (content_hash and find_previous_identical_upload(content_hash)):
        prior = None
        if content_hash:
            prior = find_previous_identical_upload(content_hash)

        if prior is None and mrip_classification["identical"]:
            first = mrip_classification["identical"][0]
            prior = (UploadRecord.query
                     .filter_by(job_id=first.get("existing_job"))
                     .order_by(UploadRecord.timestamp.desc())
                     .first())

        prior_job = prior.job_id if prior else (
            mrip_classification["identical"][0].get("existing_job")
            if mrip_classification["identical"] else None
        )

        log_event("upload_duplicate", status="info",
                  message=(f"All {total_pairs} (MR, IP) pairs already exist with identical data; "
                           f"re-using job {prior_job}"),
                  entity="upload", entity_id=job_id,
                  details={"prior_job": prior_job,
                           "identical_pairs": len(mrip_classification["identical"])})

        record_upload(
            job_id=job_id, original_name=f.filename, saved_name=saved_path.name,
            size_bytes=size_bytes, sheet1=sheet1, sheet2=sheet2,
            mr_prefix=mr_prefix, ip_prefix=ip_prefix,
            status="skipped",
            message=(f"All {total_pairs} (MR, IP) pairs identical to prior uploads "
                     f"→ job {prior_job}"),
            unique_mr=prior.unique_mr if prior else None,
            unique_ip=prior.unique_ip if prior else None,
            sheet1_rows=prior.sheet1_rows if prior else None,
            sheet2_rows=prior.sheet2_rows if prior else None,
            relation=prior.relation if prior else None,
            sh1_file=prior.sh1_file if prior else None,
            sh2_file=prior.sh2_file if prior else None,
            content_hash=content_hash,
            user=g.current_user,
        )

        progress_done(job_id, f"/upload/result/{prior_job}?dup_of={prior_job}")

        return jsonify({
            "job_id": job_id,
            "status": "duplicate",
            "duplicate_of": prior_job,
            "identical_pairs": len(mrip_classification["identical"]),
            "message": (f"All {total_pairs} (MR, IP) pairs are identical to prior uploads."),
        }), 202

    # ---- Store classification in session so results page can render it ----
    try:
        session["mrip_classification_" + job_id] = mrip_classification
        keys = [k for k in session.keys() if k.startswith("mrip_classification_")]
        if len(keys) > 5:
            for k in keys[:-5]:
                session.pop(k, None)
    except Exception:
        pass

    log_event("upload_start", status="info",
              message=f"Received '{safe_name}'",
              entity="upload", entity_id=job_id,
              details={
                  "size_bytes": size_bytes,
                  "sheet1": sheet1, "sheet2": sheet2,
                  "content_hash": content_hash,
                  "new_pairs": len(mrip_classification["new"]),
                  "identical_pairs": len(mrip_classification["identical"]),
                  "conflict_pairs": len(mrip_classification["conflict"]),
              })

    ctx = {
        "job_id": job_id,
        "saved_path": saved_path,
        "original_name": f.filename,
        "saved_name": saved_path.name,
        "size_bytes": size_bytes,
        "sheet1": sheet1, "sheet2": sheet2,
        "mr_prefix": mr_prefix, "ip_prefix": ip_prefix,
        "mr_width": mr_width, "ip_width": ip_width,
        "content_hash": content_hash,
        "user_id": user_id, "username": username, "role": role,
    }
    t = threading.Thread(target=_run_pipeline, kwargs=ctx, daemon=True)
    t.start()

    return jsonify({
        "job_id": job_id,
        "status": "started",
        "new_pairs": len(mrip_classification["new"]),
        "identical_pairs": len(mrip_classification["identical"]),
        "conflict_pairs": len(mrip_classification["conflict"]),
    }), 202


def _run_pipeline(*, job_id, saved_path, original_name, saved_name, size_bytes,
                  sheet1, sheet2, mr_prefix, ip_prefix, mr_width, ip_width,
                  content_hash=None,
                  user_id, username, role):
    """
    Background worker. Runs OUTSIDE request context.
    `user` is passed explicitly to helpers so user/role get recorded.
    """
    user = None
    try:
        with app.app_context():
            user = db.session.get(User, user_id)

            # Compute stable, cross-upload starting counters
            mr_start = next_mr_counter(mr_prefix)
            ip_start = next_ip_counter(ip_prefix)

            progress_set(
                job_id, "De-identifying", 3.0,
                f"MR from {mr_prefix}{mr_start:0{mr_width}d}, "
                f"IP from {ip_prefix}{ip_start:0{ip_width}d}"
            )

            result = deidentify(
                file_path=saved_path, output_dir=PUBLIC_DIR, secure_dir=SECURE_DIR,
                mr_prefix=mr_prefix, ip_prefix=ip_prefix,
                mr_width=mr_width, ip_width=ip_width,
                sheet1=sheet1, sheet2=sheet2,
                job_id=job_id,
                mr_start=mr_start,
                ip_start=ip_start,
            )
            result["sh1_name"] = Path(result["sh1_file"]).name
            result["sh2_name"] = Path(result["sh2_file"]).name
            result["job_id"] = job_id
            result["timestamp"] = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

            progress_advance(job_id, "similarity", "Comparing raw vs de-identified")
            similarity = None
            try:
                raw_sh1 = pd.read_excel(saved_path, sheet_name=sheet1, engine="openpyxl")
                raw_sh2 = pd.read_excel(saved_path, sheet_name=sheet2, engine="openpyxl")
                raw_sh1 = normalize_columns(raw_sh1)
                raw_sh2 = normalize_columns(raw_sh2)
                deid_sh1 = pd.read_excel(result["sh1_file"], engine="openpyxl")
                deid_sh2 = pd.read_excel(result["sh2_file"], engine="openpyxl")

                similarity = compute_similarity_report(raw_sh1, raw_sh2, deid_sh1, deid_sh2)
                record_similarity_report(job_id, similarity, user)

                log_event("similarity_check", status="success",
                          message=f"Similarity {similarity['combined_pct']}%",
                          entity="job", entity_id=job_id, user=user)
            except Exception as sim_err:
                traceback.print_exc()
                log_event("similarity_check", status="failed",
                          message=f"{type(sim_err).__name__}: {sim_err}",
                          entity="job", entity_id=job_id, user=user)
                similarity = {"error": str(sim_err)}
            result["similarity"] = similarity

            try:
                sh1_df = pd.read_excel(result["sh1_file"], engine="openpyxl")
                sh2_df = pd.read_excel(result["sh2_file"], engine="openpyxl")
                charts = build_visualizations(sh1_df, sh2_df, job_id=job_id)
                result["charts"] = charts

                built = 0
                for k, v in charts.items():
                    if k == "error":
                        continue
                    if isinstance(v, str) and not v.lstrip().startswith("<p class='warn'"):
                        built += 1
                result["chart_count"] = built
                result["chart_total"] = TOTAL_CHARTS
                result["chart_pct"] = pct(built, TOTAL_CHARTS)
            except Exception as viz_err:
                traceback.print_exc()
                result["charts"] = {"error": f"Visualization error: {viz_err}"}
                result["chart_count"] = 0
                result["chart_total"] = TOTAL_CHARTS
                result["chart_pct"] = 0

            record_upload(
                job_id=job_id, original_name=original_name, saved_name=saved_name,
                size_bytes=size_bytes, sheet1=sheet1, sheet2=sheet2,
                mr_prefix=mr_prefix, ip_prefix=ip_prefix,
                status="success",
                message=f"De-identified {result['sheet1_rows']} + {result['sheet2_rows']} rows",
                unique_mr=result["unique_mr"], unique_ip=result["unique_ip"],
                sheet1_rows=result["sheet1_rows"], sheet2_rows=result["sheet2_rows"],
                relation=result["relation"],
                sh1_file=result["sh1_name"], sh2_file=result["sh2_name"],
                content_hash=content_hash,
                user=user,
            )

            # ---- Register (MR, IP) pairs in the cross-upload registry ----
            try:
                reg_raw_sh1 = pd.read_excel(saved_path, sheet_name=sheet1, engine="openpyxl")
                reg_raw_sh2 = pd.read_excel(saved_path, sheet_name=sheet2, engine="openpyxl")
                reg_raw_sh1 = normalize_columns(reg_raw_sh1)
                reg_raw_sh2 = normalize_columns(reg_raw_sh2)

                sigs = compute_mrip_signatures(reg_raw_sh1, reg_raw_sh2)

                mr_map_final = result.get("mr_map", {})
                ip_pair_map_final = result.get("ip_pair_map", {})

                if not mr_map_final or not ip_pair_map_final:
                    # Should never happen — deidentify() always returns both.
                    # Fail loudly rather than silently re-numbering.
                    raise RuntimeError(
                        "deidentify() did not return mr_map / ip_pair_map; "
                        "cannot upsert registry without consistent mapping."
                    )

                n = upsert_mrip_registry(
                    signatures=sigs,
                    mr_map=mr_map_final,
                    ip_pair_map=ip_pair_map_final,
                    job_id=job_id,
                    username=username,
                    user_id=user_id,
                )
                log_event("mrip_registry_upsert", status="success",
                          message=f"Registered/updated {n} (MR, IP) pairs",
                          entity="job", entity_id=job_id, user=user)
            except Exception:
                traceback.print_exc()
                log_event("mrip_registry_upsert", status="failed",
                          message="Registry update failed",
                          entity="job", entity_id=job_id, user=user)

            result["processing"] = build_processing_report(
                result,
                similarity if isinstance(similarity, dict) and "error" not in similarity else None,
                result.get("chart_count", 0),
                result.get("chart_total", TOTAL_CHARTS),
            )

            log_event("deidentify", status="success",
                      message=f"Pipeline complete for job {job_id}",
                      entity="job", entity_id=job_id, user=user)

            progress_advance(job_id, "finalizing", "Rendering result page")
            progress_done(job_id, f"/upload/result/{job_id}")

    except Exception as e:
        traceback.print_exc()
        err_text = str(e).strip() or f"{type(e).__name__} (no message)"
        msg = f"{type(e).__name__}: {err_text}"

        sh1_path = PUBLIC_DIR / "sh1_deidentified.xlsx"
        sh2_path = PUBLIC_DIR / "sh2_deidentified.xlsx"
        if sh1_path.exists() and sh2_path.exists():
            try:
                with app.app_context():
                    log_event("deidentify", status="failed",
                              message=f"Post-processing failure (files OK): {msg}",
                              entity="job", entity_id=job_id,
                              details={"traceback": traceback.format_exc()[-2000:]},
                              user=user)
            except Exception:
                pass
            progress_done(job_id, f"/upload/result/{job_id}")
            return

        try:
            with app.app_context():
                if user is None:
                    user = db.session.get(User, user_id)
                record_upload(
                    job_id=job_id, original_name=original_name, saved_name=saved_name,
                    size_bytes=size_bytes, sheet1=sheet1, sheet2=sheet2,
                    mr_prefix=mr_prefix, ip_prefix=ip_prefix,
                    status="failed", message=msg,
                    content_hash=content_hash,
                    user=user,
                )
                log_event("deidentify", status="failed",
                          message=msg, entity="job", entity_id=job_id,
                          details={"traceback": traceback.format_exc()[-2000:]},
                          user=user)
        except Exception:
            pass

        progress_fail(job_id, msg)


@app.route("/upload/result/<job_id>", methods=["GET"])
@jwt_required
def upload_result(job_id):
    row = progress_get(job_id)
    if not row or row.get("status") != "done":
        flash("Result not ready yet. Please wait for processing to complete.", "warning")
        return redirect(url_for("index"))

    sh1_path = PUBLIC_DIR / "sh1_deidentified.xlsx"
    sh2_path = PUBLIC_DIR / "sh2_deidentified.xlsx"
    if not sh1_path.exists() or not sh2_path.exists():
        flash("De-identified dataset missing.", "error")
        return redirect(url_for("index"))

    sh1_df = pd.read_excel(sh1_path, engine="openpyxl")
    sh2_df = pd.read_excel(sh2_path, engine="openpyxl")

    charts = build_visualizations(sh1_df, sh2_df, job_id=None)
    built = sum(1 for k, v in charts.items()
                if k != "error" and isinstance(v, str)
                and not v.lstrip().startswith("<p class='warn'"))

    sim_row = (SimilarityReport.query
               .filter_by(job_id=job_id)
               .order_by(SimilarityReport.timestamp.desc())
               .first())

    dup_of = request.args.get("dup_of", "").strip()
    if not sim_row and dup_of:
        sim_row = (SimilarityReport.query
                   .filter_by(job_id=dup_of)
                   .order_by(SimilarityReport.timestamp.desc())
                   .first())

    similarity = None
    if sim_row:
        similarity = {
            "combined_pct": sim_row.combined_pct or 0,
            "rows_preserved": sim_row.rows_preserved,
            "columns_preserved": sim_row.columns_preserved,
            "sh1": {"overall_pct": sim_row.sh1_overall_pct or 0,
                    "rows_after": sim_row.sh1_rows, "cols_after": sim_row.sh1_cols,
                    "rows_before": sim_row.sh1_rows, "cols_before": sim_row.sh1_cols,
                    "rows_preserved": sim_row.rows_preserved,
                    "columns": [], "notes": []},
            "sh2": {"overall_pct": sim_row.sh2_overall_pct or 0,
                    "rows_after": sim_row.sh2_rows, "cols_after": sim_row.sh2_cols,
                    "rows_before": sim_row.sh2_rows, "cols_before": sim_row.sh2_cols,
                    "rows_preserved": sim_row.rows_preserved,
                    "columns": [], "notes": []},
        }
        try:
            per_col = json.loads(sim_row.per_column_json or "{}")
            similarity["sh1"]["columns"] = per_col.get("sh1", [])
            similarity["sh2"]["columns"] = per_col.get("sh2", [])
            similarity["sh1"]["notes"] = per_col.get("notes_sh1", [])
            similarity["sh2"]["notes"] = per_col.get("notes_sh2", [])
        except Exception:
            pass

    mrip_class = session.get("mrip_classification_" + job_id, None)
    if not mrip_class and dup_of:
        mrip_class = session.get("mrip_classification_" + dup_of, None)

    mr_ip_dist = sh1_df.groupby("MR")["IP"].nunique().to_dict()
    r = {
        "job_id": dup_of or job_id,
        "timestamp": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
        "unique_mr": int(sh1_df["MR"].nunique()),
        "unique_ip": int(sh1_df["IP"].nunique()),
        "sheet1_rows": int(len(sh1_df)),
        "sheet2_rows": int(len(sh2_df)),
        "relation": "1:M",
        "max_ip_per_mr": int(sh1_df.groupby("MR")["IP"].nunique().max()),
        "avg_ip_per_mr": round(sh1_df.groupby("MR")["IP"].nunique().mean(), 2),
        "mr_ip_distribution": mr_ip_dist,
        "sh1_name": sh1_path.name,
        "sh2_name": sh2_path.name,
        "charts": charts,
        "chart_count": built,
        "chart_total": TOTAL_CHARTS,
        "chart_pct": pct(built, TOTAL_CHARTS),
        "similarity": similarity,
        "crosswalk_mr_stats": None,
        "crosswalk_ip_stats": None,
    }
    r["processing"] = build_processing_report(
        r,
        similarity if similarity and "error" not in similarity else None,
        built, TOTAL_CHARTS,
    )

    return render_page(RESULT_TEMPLATE, r=r, user=g.current_user,
                       mrip_classification=mrip_class)


@app.route("/dashboard")
@jwt_required
def dashboard():
    sh1_file = PUBLIC_DIR / "sh1_deidentified.xlsx"
    sh2_file = PUBLIC_DIR / "sh2_deidentified.xlsx"
    if not sh1_file.exists() or not sh2_file.exists():
        log_event("dashboard", status="info", message="No prior dataset")
        flash("No de-identified dataset yet. Please upload a workbook first.", "warning")
        return redirect(url_for("index"))

    sh1_df = pd.read_excel(sh1_file, engine="openpyxl")
    sh2_df = pd.read_excel(sh2_file, engine="openpyxl")

    charts = build_visualizations(sh1_df, sh2_df, job_id=None)
    built = sum(1 for k, v in charts.items()
                if k != "error" and isinstance(v, str)
                and not v.lstrip().startswith("<p class='warn'"))

    r = {
        "job_id": "LAST",
        "timestamp": datetime.fromtimestamp(
            sh1_file.stat().st_mtime).strftime("%Y-%m-%d %H:%M:%S"),
        "unique_mr": int(sh1_df["MR"].nunique()),
        "unique_ip": int(sh1_df["IP"].nunique()),
        "sheet1_rows": int(len(sh1_df)),
        "sheet2_rows": int(len(sh2_df)),
        "relation": "1:M",
        "max_ip_per_mr": int(sh1_df.groupby("MR")["IP"].nunique().max()),
        "avg_ip_per_mr": round(sh1_df.groupby("MR")["IP"].nunique().mean(), 2),
        "mr_ip_distribution": sh1_df.groupby("MR")["IP"].nunique().to_dict(),
        "preview_sh1": sh1_df.head(5).to_dict(orient="records"),
        "preview_sh2": sh2_df.head(5).to_dict(orient="records"),
        "sh1_name": sh1_file.name, "sh2_name": sh2_file.name,
        "charts": charts,
        "chart_count": built,
        "chart_total": TOTAL_CHARTS,
        "chart_pct": pct(built, TOTAL_CHARTS),
        "crosswalk_mr_stats": None,
        "crosswalk_ip_stats": None,
    }
    log_event("dashboard", status="success", message="Viewed dashboard")
    return render_page(RESULT_TEMPLATE, r=r, user=g.current_user,
                       mrip_classification=None)


# ============================================================
# PROFILE ROUTES
# ============================================================
@app.route("/profile")
@jwt_required
def profile_page():
    log_event("profile_view", status="success", message="Viewed own profile")
    return render_page(PROFILE_TEMPLATE, user=g.current_user)


@app.route("/profile/update", methods=["POST"])
@jwt_required
def profile_update():
    u = g.current_user
    full_name = request.form.get("full_name", "").strip() or None
    email = request.form.get("email", "").strip() or None
    department = request.form.get("department", "").strip() or None
    phone = request.form.get("phone", "").strip() or None

    if email and not EMAIL_RE.match(email):
        log_event("profile_update", status="failed",
                  message="Invalid email", user=u)
        flash("Email address is not valid.", "error")
        return redirect(url_for("profile_page"))

    if email and User.query.filter(User.email == email, User.id != u.id).first():
        log_event("profile_update", status="failed",
                  message="Email already used", user=u)
        flash("That email is already used by another account.", "error")
        return redirect(url_for("profile_page"))

    changes = {}
    for field, new_val in [("full_name", full_name), ("email", email),
                           ("department", department), ("phone", phone)]:
        old_val = getattr(u, field)
        if old_val != new_val:
            changes[field] = {"old": old_val, "new": new_val}
            setattr(u, field, new_val)
    db.session.commit()

    log_event("profile_update", status="success",
              message=f"Updated {len(changes)} field(s)",
              entity="user", entity_id=str(u.id), details=changes, user=u)
    flash("Profile updated successfully.", "success")
    return redirect(url_for("profile_page"))


@app.route("/profile/change-password", methods=["POST"])
@jwt_required
def profile_change_password():
    u = g.current_user
    old_pw = request.form.get("old_password", "")
    new_pw = request.form.get("new_password", "")
    confirm = request.form.get("confirm", "")

    if not u.check_password(old_pw):
        log_event("profile_change_password", status="failed",
                  message="Wrong current password", user=u)
        flash("Current password is incorrect.", "error")
        return redirect(url_for("profile_page"))
    if len(new_pw) < 6:
        log_event("profile_change_password", status="failed",
                  message="New password too short", user=u)
        flash("New password must be at least 6 characters.", "error")
        return redirect(url_for("profile_page"))
    if new_pw != confirm:
        log_event("profile_change_password", status="failed",
                  message="Passwords do not match", user=u)
        flash("Passwords do not match.", "error")
        return redirect(url_for("profile_page"))

    u.set_password(new_pw)
    db.session.commit()
    log_event("profile_change_password", status="success",
              message="User changed own password", user=u)
    flash("Password changed successfully.", "success")
    return redirect(url_for("profile_page"))


# ============================================================
# ADMIN — User CRUD
# ============================================================
@app.route("/admin/users")
@admin_required
def admin_users():
    f_q = request.args.get("q", "").strip()
    f_role = request.args.get("role", "").strip()
    f_status = request.args.get("status", "").strip()

    q = User.query
    if f_q:
        like = f"%{f_q}%"
        q = q.filter((User.username.ilike(like)) |
                     (User.full_name.ilike(like)) |
                     (User.email.ilike(like)))
    if f_role:
        q = q.filter(User.role == f_role)
    if f_status == "active":
        q = q.filter(User.is_active_ == True)
    elif f_status == "inactive":
        q = q.filter(User.is_active_ == False)

    rows = q.order_by(User.id.asc()).all()
    stats = {
        "total": User.query.count(),
        "active": User.query.filter_by(is_active_=True).count(),
        "inactive": User.query.filter_by(is_active_=False).count(),
        "admins": User.query.filter_by(role="admin").count(),
        "auditors": User.query.filter_by(role="auditor").count(),
        "users": User.query.filter_by(role="user").count(),
    }

    total = stats["total"] or 1
    ratio = {
        "active_pct": pct(stats["active"], total),
        "inactive_pct": pct(stats["inactive"], total),
        "admin_pct": pct(stats["admins"], total),
        "auditor_pct": pct(stats["auditors"], total),
        "user_pct": pct(stats["users"], total),
    }

    log_event("admin_users_view", status="success",
              message=f"Viewed user list (q='{f_q}', role='{f_role}', status='{f_status}')")
    return render_page(ADMIN_USERS_TEMPLATE, user=g.current_user,
                       rows=rows, stats=stats, ratio=ratio,
                       f_q=f_q, f_role=f_role, f_status=f_status)


@app.route("/admin/users/create", methods=["POST"])
@admin_required
def admin_users_create():
    errors, cleaned = validate_user_input(
        username=request.form.get("username", ""),
        email=request.form.get("email", ""),
        password=request.form.get("password", ""),
        confirm=request.form.get("confirm", ""),
        role=request.form.get("role", "user"),
        require_password=True,
    )
    if errors:
        log_event("admin_user_create", status="failed",
                  message="; ".join(errors))
        flash(" | ".join(errors), "error")
        return redirect(url_for("admin_users"))
    if User.query.filter_by(username=cleaned["username"]).first():
        log_event("admin_user_create", status="failed", message="Username taken")
        flash("Username already exists.", "error")
        return redirect(url_for("admin_users"))
    if cleaned.get("email") and User.query.filter_by(email=cleaned["email"]).first():
        log_event("admin_user_create", status="failed", message="Email taken")
        flash("Email already exists.", "error")
        return redirect(url_for("admin_users"))

    is_active = request.form.get("is_active", "1") == "1"
    user = User(
        username=cleaned["username"], email=cleaned.get("email"),
        full_name=request.form.get("full_name", "").strip() or None,
        department=request.form.get("department", "").strip() or None,
        phone=request.form.get("phone", "").strip() or None,
        role=cleaned["role"], is_active_=is_active,
    )
    user.set_password(cleaned["password"])
    db.session.add(user)
    db.session.commit()

    log_event("admin_user_create", status="success",
              message=f"Admin created user '{user.username}' (role={user.role})",
              entity="user", entity_id=str(user.id))
    flash(f"User '{user.username}' created.", "success")
    return redirect(url_for("admin_users"))


@app.route("/admin/users/<int:user_id>/edit", methods=["GET", "POST"])
@admin_required
def admin_users_edit(user_id):
    target = db.session.get(User, user_id)
    if not target:
        log_event("admin_user_edit", status="failed",
                  message=f"User {user_id} not found")
        flash("User not found.", "error")
        return redirect(url_for("admin_users"))

    if request.method == "GET":
        log_event("admin_user_edit_view", status="success",
                  message=f"Opened edit form for user #{user_id}",
                  entity="user", entity_id=str(user_id))
        return render_page(ADMIN_USER_EDIT_TEMPLATE,
                           user=g.current_user, target=target)

    errors, cleaned = validate_user_input(
        username=request.form.get("username", ""),
        email=request.form.get("email", ""),
        role=request.form.get("role", target.role),
    )
    new_password = request.form.get("new_password", "")
    confirm = request.form.get("confirm", "")
    if new_password or confirm:
        pw_errors, _ = validate_user_input(
            password=new_password, confirm=confirm, require_password=True)
        errors.extend(pw_errors)

    if errors:
        log_event("admin_user_edit", status="failed",
                  message="; ".join(errors), entity="user", entity_id=str(user_id))
        flash(" | ".join(errors), "error")
        return redirect(url_for("admin_users_edit", user_id=user_id))

    if User.query.filter(User.username == cleaned["username"], User.id != target.id).first():
        log_event("admin_user_edit", status="failed", message="Username taken",
                  entity="user", entity_id=str(user_id))
        flash("Username already exists.", "error")
        return redirect(url_for("admin_users_edit", user_id=user_id))
    if cleaned.get("email") and User.query.filter(
        User.email == cleaned["email"], User.id != target.id
    ).first():
        log_event("admin_user_edit", status="failed", message="Email taken",
                  entity="user", entity_id=str(user_id))
        flash("Email already exists.", "error")
        return redirect(url_for("admin_users_edit", user_id=user_id))

    new_role = cleaned["role"]
    new_active = request.form.get("is_active", "1") == "1"

    if target.id == g.current_user.id:
        if new_role != "admin":
            log_event("admin_user_edit", status="denied",
                      message="Admin tried to demote self")
            flash("You cannot demote your own admin account.", "error")
            return redirect(url_for("admin_users_edit", user_id=user_id))
        if not new_active:
            log_event("admin_user_edit", status="denied",
                      message="Admin tried to deactivate self")
            flash("You cannot deactivate your own account.", "error")
            return redirect(url_for("admin_users_edit", user_id=user_id))

    changes = {}
    for field, new_val in [
        ("username", cleaned["username"]),
        ("email", cleaned.get("email")),
        ("full_name", request.form.get("full_name", "").strip() or None),
        ("department", request.form.get("department", "").strip() or None),
        ("phone", request.form.get("phone", "").strip() or None),
        ("role", new_role), ("is_active_", new_active),
    ]:
        old_val = getattr(target, field)
        if old_val != new_val:
            changes[field] = {"old": old_val, "new": new_val}
            setattr(target, field, new_val)
    if new_password:
        target.set_password(new_password)
        changes["password"] = "changed"
    db.session.commit()

    log_event("admin_user_edit", status="success",
              message=f"Admin updated user #{target.id}",
              entity="user", entity_id=str(target.id), details=changes)
    flash(f"User '{target.username}' updated.", "success")
    return redirect(url_for("admin_users"))


@app.route("/admin/users/<int:user_id>/toggle", methods=["POST"])
@admin_required
def admin_users_toggle(user_id):
    target = db.session.get(User, user_id)
    if not target:
        flash("User not found.", "error")
        return redirect(url_for("admin_users"))
    if target.id == g.current_user.id:
        log_event("admin_user_toggle", status="denied",
                  message="Admin tried to toggle own account")
        flash("You cannot toggle your own account.", "error")
        return redirect(url_for("admin_users"))

    target.is_active_ = not target.is_active_
    db.session.commit()
    log_event("admin_user_toggle", status="success",
              message=f"User #{target.id} {'enabled' if target.is_active_ else 'disabled'}",
              entity="user", entity_id=str(target.id))
    flash(f"User '{target.username}' {'enabled' if target.is_active_ else 'disabled'}.",
          "success")
    return redirect(url_for("admin_users"))


@app.route("/admin/users/<int:user_id>/reset-password", methods=["POST"])
@admin_required
def admin_users_reset_pw(user_id):
    target = db.session.get(User, user_id)
    if not target:
        flash("User not found.", "error")
        return redirect(url_for("admin_users"))
    temp_pw = "Welcome@123"
    target.set_password(temp_pw)
    db.session.commit()
    log_event("admin_user_reset_pw", status="success",
              message=f"Password reset for #{target.id} (temp password issued)",
              entity="user", entity_id=str(target.id))
    flash(f"Password for '{target.username}' reset to temporary: {temp_pw}", "warning")
    return redirect(url_for("admin_users"))


@app.route("/admin/users/<int:user_id>/delete", methods=["POST"])
@admin_required
def admin_users_delete(user_id):
    target = db.session.get(User, user_id)
    if not target:
        flash("User not found.", "error")
        return redirect(url_for("admin_users"))
    if target.id == g.current_user.id:
        log_event("admin_user_delete", status="denied",
                  message="Admin tried to delete self")
        flash("You cannot delete your own account.", "error")
        return redirect(url_for("admin_users"))
    if target.role == "admin" and User.query.filter_by(role="admin").count() <= 1:
        log_event("admin_user_delete", status="denied",
                  message="Attempt to delete last admin")
        flash("Cannot delete the last remaining admin.", "error")
        return redirect(url_for("admin_users"))

    uname, uid = target.username, target.id
    db.session.delete(target)
    db.session.commit()
    log_event("admin_user_delete", status="success",
              message=f"Deleted user '{uname}' (#{uid})",
              entity="user", entity_id=str(uid))
    flash(f"User '{uname}' deleted.", "success")
    return redirect(url_for("admin_users"))


# ============================================================
# ADMIN — Upload Records
# ============================================================
@app.route("/admin/uploads")
@admin_required
def admin_uploads():
    f_username = request.args.get("username", "").strip()
    f_status = request.args.get("status", "").strip()
    try:
        f_limit = int(request.args.get("limit", 200))
    except ValueError:
        f_limit = 200
    f_limit = max(10, min(f_limit, 2000))

    q = UploadRecord.query
    if f_username:
        q = q.filter(UploadRecord.username.ilike(f"%{f_username}%"))
    if f_status:
        q = q.filter(UploadRecord.status == f_status)

    rows = q.order_by(UploadRecord.timestamp.desc()).limit(f_limit).all()

    stats = {
        "total":    UploadRecord.query.count(),
        "success":  UploadRecord.query.filter_by(status="success").count(),
        "failed":   UploadRecord.query.filter_by(status="failed").count(),
        "rejected": UploadRecord.query.filter_by(status="rejected").count(),
        "skipped":  UploadRecord.query.filter_by(status="skipped").count(),
    }

    total = stats["total"] or 1
    ratio = {
        "success_pct":  pct(stats["success"], total),
        "failed_pct":   pct(stats["failed"], total),
        "rejected_pct": pct(stats["rejected"], total),
        "skipped_pct":  pct(stats["skipped"], total),
    }

    log_event("admin_uploads_view", status="success",
              message=f"Viewed upload records (u='{f_username}', s='{f_status}')")
    return render_page(ADMIN_UPLOADS_TEMPLATE, user=g.current_user,
                       rows=rows, stats=stats, ratio=ratio,
                       f_username=f_username, f_status=f_status, f_limit=f_limit)


# ============================================================
# ADMIN — Similarity Reports
# ============================================================
@app.route("/admin/reports")
@admin_required
def admin_reports():
    f_username = request.args.get("username", "").strip()
    try:
        f_limit = int(request.args.get("limit", 100))
    except ValueError:
        f_limit = 100
    f_limit = max(10, min(f_limit, 1000))

    q = SimilarityReport.query
    if f_username:
        q = q.filter(SimilarityReport.username.ilike(f"%{f_username}%"))

    rows = q.order_by(SimilarityReport.timestamp.desc()).limit(f_limit).all()

    all_rows = SimilarityReport.query.all()
    combined_values = [r.combined_pct or 0 for r in all_rows]
    avg_combined = round(sum(combined_values) / len(combined_values), 2) if combined_values else 0.0
    perfect = sum(1 for v in combined_values if v >= 99.0)
    warnings_ = sum(1 for v in combined_values if v < 99.0)

    stats = {
        "total": len(all_rows),
        "avg_combined": avg_combined,
        "perfect": perfect,
        "warnings": warnings_,
    }

    log_event("admin_reports_view", status="success",
              message=f"Viewed similarity reports (u='{f_username}')")
    return render_page(ADMIN_REPORTS_TEMPLATE, user=g.current_user,
                       rows=rows, stats=stats,
                       f_username=f_username, f_limit=f_limit)


# ============================================================
# ADMIN — Re-identification
# ============================================================
@app.route("/admin/reidentify")
@admin_required
def admin_reidentify():
    q = request.args.get("q", "").strip()
    kind = request.args.get("kind", "both").strip() or "both"
    reason = request.args.get("reason", "").strip()

    if kind not in ("both", "mr", "ip"):
        kind = "both"

    results = {"mr": [], "ip": [], "query": q}
    if q:
        try:
            results = _search_crosswalk(q, kind)
        except Exception as e:
            traceback.print_exc()
            flash(f"Search error: {e}", "error")

    history = (ReidentificationRequest.query
               .order_by(ReidentificationRequest.timestamp.desc())
               .limit(20).all())

    log_event("reid_view", status="success",
              message=f"Viewed re-identification console (q='{q}', kind='{kind}')")

    return render_page(REID_TEMPLATE, user=g.current_user,
                       q=q, kind=kind, reason=reason,
                       results=results, history=history)


@app.route("/admin/reidentify/run", methods=["POST"])
@admin_required
def admin_reidentify_run():
    q = request.form.get("q", "").strip()
    kind = request.form.get("kind", "both").strip() or "both"
    reason = request.form.get("reason", "").strip()
    notes = request.form.get("notes", "").strip()

    if not reason:
        log_event("reid_run", status="failed",
                  message="Missing reason for re-identification")
        flash("A reason is required for re-identification.", "error")
        return redirect(url_for("admin_reidentify", q=q, kind=kind))
    if not q:
        flash("Provide a search query first.", "error")
        return redirect(url_for("admin_reidentify"))

    try:
        results = _search_crosswalk(q, kind)
        mr_list = sorted({r["dummyMR"] for r in results["mr"]} |
                         {r["dummyMR"] for r in results["ip"]})
        ip_list = sorted({r["dummyIP"] for r in results["ip"]})

        if not mr_list and not ip_list:
            log_event("reid_run", status="failed",
                      message=f"No matches for query '{q}'")
            flash(f"No matches found for '{q}'.", "warning")
            return redirect(url_for("admin_reidentify", q=q, kind=kind))

        sh1_out, sh2_out = _reverse_dataset(mr_list, ip_list)
        f1, f2 = _write_reid_outputs(sh1_out, sh2_out, g.current_user.username)

        rec = ReidentificationRequest(
            admin_id=g.current_user.id,
            admin_username=g.current_user.username,
            search_query=q, mode=kind,
            matched_mr=json.dumps(mr_list),
            matched_ip=json.dumps(ip_list),
            match_count=len(mr_list) + len(ip_list),
            reason=reason, download_file=f1, notes=notes or None,
        )
        db.session.add(rec)
        db.session.commit()

        log_event("reid_run", status="success",
                  message=f"Re-identified {len(mr_list)} MR + {len(ip_list)} IP for query '{q}'",
                  entity="reid", entity_id=str(rec.id),
                  details={"query": q, "kind": kind, "reason": reason,
                           "notes": notes,
                           "mr_count": len(mr_list), "ip_count": len(ip_list),
                           "sh1_file": f1, "sh2_file": f2})
        flash(f"✅ Re-identified {len(mr_list)} MR + {len(ip_list)} IP. Files ready below.",
              "success")
        return redirect(url_for("admin_reidentify", q=q, kind=kind, reason=reason))

    except FileNotFoundError as e:
        log_event("reid_run", status="failed", message=f"Dataset missing: {e}")
        flash(f"Dataset missing: {e}. Upload a workbook first.", "error")
        return redirect(url_for("admin_reidentify"))
    except Exception as e:
        traceback.print_exc()
        log_event("reid_run", status="failed",
                  message=f"{type(e).__name__}: {e}",
                  details={"traceback": traceback.format_exc()[-2000:]})
        flash(f"Re-identification error: {e}", "error")
        return redirect(url_for("admin_reidentify", q=q, kind=kind))


# ============================================================
# ADMIN — MR/IP Registry viewer
# ============================================================
@app.route("/admin/mrip-registry")
@admin_required
def admin_mrip_registry():
    f_query = request.args.get("q", "").strip()
    try:
        f_limit = int(request.args.get("limit", 200))
    except ValueError:
        f_limit = 200
    f_limit = max(10, min(f_limit, 2000))

    q = MRIPRegistry.query
    if f_query:
        like = f"%{f_query}%"
        q = q.filter((MRIPRegistry.original_mr.ilike(like)) |
                     (MRIPRegistry.original_ip.ilike(like)) |
                     (MRIPRegistry.dummy_mr.ilike(like)) |
                     (MRIPRegistry.dummy_ip.ilike(like)))

    rows = q.order_by(MRIPRegistry.timestamp.desc()).limit(f_limit).all()
    total = MRIPRegistry.query.count()

    log_event("mrip_registry_view", status="success",
              message=f"Viewed MR/IP registry (q='{f_query}', total={total})")

    return render_page(MRIP_REGISTRY_TEMPLATE, user=g.current_user,
                       rows=rows, total=total,
                       f_query=f_query, f_limit=f_limit)


# ============================================================
# AUDIT — Admin
# ============================================================
@app.route("/audit")
@admin_required
def audit_page():
    f_username = request.args.get("username", "").strip()
    f_action = request.args.get("action", "").strip()
    f_status = request.args.get("status", "").strip()
    try:
        f_limit = int(request.args.get("limit", 200))
    except ValueError:
        f_limit = 200
    f_limit = max(10, min(f_limit, 2000))

    q = AuditLog.query
    if f_username:
        q = q.filter(AuditLog.username.ilike(f"%{f_username}%"))
    if f_action:
        q = q.filter(AuditLog.action.ilike(f"%{f_action}%"))
    if f_status:
        q = q.filter(AuditLog.status == f_status)

    rows = q.order_by(AuditLog.timestamp.desc()).limit(f_limit).all()
    stats = {
        "total": AuditLog.query.count(),
        "success": AuditLog.query.filter_by(status="success").count(),
        "failed": AuditLog.query.filter_by(status="failed").count(),
        "denied": AuditLog.query.filter_by(status="denied").count(),
        "info": AuditLog.query.filter_by(status="info").count(),
    }

    total = stats["total"] or 1
    ratio = {
        "success_pct": pct(stats["success"], total),
        "failed_pct":  pct(stats["failed"], total),
        "denied_pct":  pct(stats["denied"], total),
        "info_pct":    pct(stats["info"], total),
    }

    log_event("audit_view", status="success",
              message=f"Viewed audit log (u='{f_username}', a='{f_action}', s='{f_status}')")
    return render_page(AUDIT_TEMPLATE, user=g.current_user,
                       rows=rows, stats=stats, ratio=ratio,
                       f_username=f_username, f_action=f_action,
                       f_status=f_status, f_limit=f_limit)


@app.route("/download/<path:filename>")
@jwt_required
def download(filename):
    try:
        full_path = (PUBLIC_DIR / filename).resolve()
        if not str(full_path).startswith(str(PUBLIC_DIR.resolve())):
            log_event("download", status="denied",
                      message=f"Path traversal attempt: {filename}")
            flash("Invalid download path.", "error")
            return redirect(url_for("index"))
        if not full_path.exists():
            log_event("download", status="failed", message=f"File not found: {filename}")
            flash("File not found.", "error")
            return redirect(url_for("index"))
        log_event("download", status="success",
                  message=f"Downloaded '{filename}'",
                  entity="file", entity_id=filename)
        return send_from_directory(PUBLIC_DIR, filename, as_attachment=True)
    except Exception as e:
        log_event("download", status="failed", message=f"{type(e).__name__}: {e}")
        raise


@app.route("/health")
def health():
    return jsonify({"status": "ok", "time": datetime.now().isoformat()})


# ============================================================
# SCHEMA MIGRATION + BOOTSTRAP
# ============================================================
def _migrate_schema():
    from sqlalchemy import text, inspect as sa_inspect

    insp = sa_inspect(db.engine)
    tables = insp.get_table_names()

    # New table: create on demand (create_all in bootstrap does this too).
    if "mrip_registry" not in tables:
        try:
            MRIPRegistry.__table__.create(bind=db.engine, checkfirst=True)
            print("🔧 Created table: mrip_registry")
        except Exception:
            audit_logger.exception("Failed to create mrip_registry table")

    if "users" in tables:
        existing = {c["name"] for c in insp.get_columns("users")}
        additions = [
            ("full_name",  "VARCHAR(120)", "NULL"),
            ("department", "VARCHAR(120)", "NULL"),
            ("phone",      "VARCHAR(32)",  "NULL"),
            ("updated_at", "DATETIME",     "CURRENT_TIMESTAMP"),
            ("last_login", "DATETIME",     "NULL"),
        ]
        with db.engine.begin() as conn:
            for col, col_type, default in additions:
                if col not in existing:
                    print(f"🔧 Adding missing column: users.{col}")
                    conn.execute(text(
                        f"ALTER TABLE users ADD COLUMN {col} {col_type} DEFAULT {default}"
                    ))
            conn.execute(text("UPDATE users SET role='user' WHERE role IS NULL OR role=''"))

    if "reid_requests" in tables:
        cols = {c["name"] for c in insp.get_columns("reid_requests")}
        with db.engine.begin() as conn:
            if "query" in cols and "search_query" not in cols:
                print("🔧 Renaming reid_requests.query → reid_requests.search_query")
                conn.execute(text(
                    "ALTER TABLE reid_requests RENAME COLUMN query TO search_query"
                ))
            elif "search_query" not in cols:
                print("🔧 Adding missing column: reid_requests.search_query")
                conn.execute(text(
                    "ALTER TABLE reid_requests ADD COLUMN search_query VARCHAR(255) DEFAULT NULL"
                ))

    if "upload_records" in tables:
        cols = {c["name"] for c in insp.get_columns("upload_records")}
        additions = [
            ("content_hash",  "VARCHAR(64)",  "NULL"),
            ("job_id",        "VARCHAR(16)",  "NULL"),
            ("user_id",       "INTEGER",      "NULL"),
            ("username",      "VARCHAR(64)",  "NULL"),
            ("role",          "VARCHAR(20)",  "NULL"),
            ("original_name", "VARCHAR(255)", "NULL"),
            ("saved_name",    "VARCHAR(255)", "NULL"),
            ("size_bytes",    "INTEGER",      "NULL"),
            ("sheet1",        "VARCHAR(64)",  "NULL"),
            ("sheet2",        "VARCHAR(64)",  "NULL"),
            ("mr_prefix",     "VARCHAR(16)",  "NULL"),
            ("ip_prefix",     "VARCHAR(16)",  "NULL"),
            ("status",        "VARCHAR(16)",  "NULL"),
            ("message",       "TEXT",         "NULL"),
            ("unique_mr",     "INTEGER",      "NULL"),
            ("unique_ip",     "INTEGER",      "NULL"),
            ("sheet1_rows",   "INTEGER",      "NULL"),
            ("sheet2_rows",   "INTEGER",      "NULL"),
            ("relation",      "VARCHAR(8)",   "NULL"),
            ("sh1_file",      "VARCHAR(255)", "NULL"),
            ("sh2_file",      "VARCHAR(255)", "NULL"),
        ]
        with db.engine.begin() as conn:
            for col, col_type, default in additions:
                if col not in cols:
                    print(f"🔧 Adding missing column: upload_records.{col}")
                    conn.execute(text(
                        f"ALTER TABLE upload_records ADD COLUMN {col} {col_type} DEFAULT {default}"
                    ))
            conn.execute(text(
                "CREATE INDEX IF NOT EXISTS ix_upload_records_content_hash "
                "ON upload_records (content_hash)"
            ))

    if "similarity_reports" in tables:
        cols = {c["name"] for c in insp.get_columns("similarity_reports")}
        additions = [
            ("job_id",            "VARCHAR(16)",  "NULL"),
            ("user_id",           "INTEGER",      "NULL"),
            ("username",          "VARCHAR(64)",  "NULL"),
            ("sh1_rows",          "INTEGER",      "NULL"),
            ("sh2_rows",          "INTEGER",      "NULL"),
            ("sh1_cols",          "INTEGER",      "NULL"),
            ("sh2_cols",          "INTEGER",      "NULL"),
            ("sh1_overall_pct",   "FLOAT",        "NULL"),
            ("sh2_overall_pct",   "FLOAT",        "NULL"),
            ("combined_pct",      "FLOAT",        "NULL"),
            ("rows_preserved",    "BOOLEAN",      "1"),
            ("columns_preserved", "BOOLEAN",      "1"),
            ("per_column_json",   "TEXT",         "NULL"),
            ("notes",             "TEXT",         "NULL"),
        ]
        with db.engine.begin() as conn:
            for col, col_type, default in additions:
                if col not in cols:
                    print(f"🔧 Adding missing column: similarity_reports.{col}")
                    conn.execute(text(
                        f"ALTER TABLE similarity_reports ADD COLUMN {col} {col_type} DEFAULT {default}"
                    ))


def bootstrap():
    with app.app_context():
        db.create_all()
        _migrate_schema()

        if User.query.count() == 0:
            admin = User(username="admin", email="admin@local", role="admin",
                         full_name="System Administrator",
                         department="Centre of Excellence — AIMAA")
            admin.set_password("admin123")
            db.session.add(admin)

            auditor = User(username="auditor", email="auditor@local",
                           role="auditor", full_name="Audit Officer",
                           department="Data Governance")
            auditor.set_password("auditor123")
            db.session.add(auditor)

            user = User(username="user", email="user@local",
                        role="user", full_name="Standard User",
                        department="General Medicine")
            user.set_password("user123")
            db.session.add(user)

            db.session.commit()

            print("=" * 70)
            print("⚠️  DEFAULT USERS CREATED")
            print("   admin   / admin123    (role=admin)")
            print("   auditor / auditor123  (role=auditor)")
            print("   user    / user123     (role=user)")
            print("   → Change passwords immediately after first login!")
            print("=" * 70)

            try:
                log_event("bootstrap", status="success",
                          message="Seeded default users (admin, auditor, user)",
                          entity="user", entity_id=str(admin.id), user=admin)
            except Exception:
                pass


if __name__ == "__main__":
    bootstrap()

    print("=" * 70)
    print("  Clinical Data De-identification Console")
    print("  EASA College of Engineering and Technology (ECET)")
    print("  Centre of Excellence — AIMAA")
    print("  Department of Artificial Intelligence and Data Science")
    print("  Sri Manakula Vinayagar Medical College and Hospital (SMVMCH)")
    print("  Department of General Medicine")
    print("=" * 70)
    print("Registered routes:")
    for rule in sorted(app.url_map.iter_rules(), key=lambda r: r.rule):
        print(f"  {rule.rule:52} → {rule.endpoint}")
    print("=" * 70)
    print(f"Audit log file: {LOG_DIR / 'audit.log'}")
    print("Audit DB tables: audit_log, reid_requests, upload_records,")
    print("                 similarity_reports, mrip_registry, users")
    print("Progress API:   GET /api/progress/<job_id>")
    print("Duplicate detection: content-hash of sh1 + sh2 rows (SHA-256)")
    print("MR/IP registry:     per-pair signature across uploads")
    print("Numbering:          stable cross-upload MR/IP (continues from registry)")
    print("Crosswalks:         append-only — full history preserved on disk")
    print("=" * 70)
    print("🚀 Starting Flask on http://127.0.0.1:5000")
    print("=" * 70)

    app.run(host="127.0.0.1", port=5000, debug=True, use_reloader=True)