# Mektep.edu.kz Grade Monitor Bot

This is an asynchronous **Telegram** (Telegram is similar to WeChat or WhatsApp) bot designed to monitor the [mektep.edu.kz](https://mektep.edu.kz) website for real-time changes in student grades and attendance. 
It automatically scrapes the school portal, compares changes against a local database, and sends detailed notifications to subscribed users.  
Students or parents can receive instant alerts, while teachers can get a daily digest for their class.
It solves the problem of needing to manually check the website (or app) multiple times a day for new grades or attendance marks.

## 1-minute Demo video from a students's perspective

https://github.com/user-attachments/assets/5b6f04b7-3cfb-4a4b-8372-365c6a0ad1e4

## Key Features

### Real-time Grade Monitoring
Continuously checks for new, removed, or modified grades, including:

- Formative Assessments (ФО)
- Summative Assessments for Section (СОР)
- Summative Assessments for Term (СОЧ)
- Final Term/Quarter Marks

### Detailed Attendance Tracking
Detects and reports any new or removed attendance marks.

### Multi-Role System

- Personal Mode – For students or parents. Subscribe to one specific student and receive instant updates.
- Teacher Mode – For class curators. Subscribe to an entire class and receive a consolidated daily digest of all changes.

### On-Demand Reports

- `/formative` – Full report of all current formative assessments and their average.  
- `/absent` – Detailed report of all absences, grouped by date and reason.

### High-Performance & Robust Architecture

- Fully Asynchronous – Built with asyncio, aiohttp, and aiogram for efficiency.  
- Intelligent Scraping – Manages login sessions, handles expiry, and avoids IP bans using semaphores.  
- Adaptive Polling – Adjusts check intervals dynamically (60–300s) based on detected changes.

### Telegram Rate-Limit & Error Handling

- Built-in MessageQueue for managing all outgoing bot messages.  
- Automatically handles RetryAfter exceptions.  
- Includes a robust send_long() function that correctly splits long messages and HTML tags.

### Persistent Storage

- Local SQLite database (bot_data.sqlite) stores user subscriptions and last known grades.  
- Detects changes even after a restart.

## Bot Usage

### User Commands

| Command | Description |
|----------|--------------|
| `/start` | Begin setup (choose role, class, student) |
| `/me` | Check your current subscription (role, class, student) |
| `/formative` | Get instant report of formative assessments (ФО) |
| `/absent` | Get detailed report of absences |
| `/help` | Show help message |
| `/teacher_time HH:MM` | (Teacher Mode) Set daily digest time (e.g., `/teacher_time 20:30`) |

### Administrator Commands

| Command | Description |
|----------|--------------|
| `/resources` | View system resource usage and bot stats. |
| `/log` | Show latest 200 lines of the runtime log. |
| `/list` | List all registered users and subscriptions. |
| `/set <id> <mode> [args]` | Modify a user's subscription. |
| `/delete <id>` | Remove a user from the database. |
| `/notify <message>` | Broadcast to all users. |
| `/force_fetch` | Force all monitoring tasks to update immediately. |
| `/enable` / `/disable` | Turn monitoring on/off globally. |
| `/restart` | Gracefully restart the bot. |
| `/stop` | Gracefully stop the bot. |
| `/fast_stop` | Immediately stop (unsafe). |
