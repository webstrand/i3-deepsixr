#![feature(error_generic_member_access)]
use i3_ipc::{event, reply, I3Stream};
use itertools::Itertools;
use nix::sys::memfd::memfd_create;
use nix::sys::memfd::MemFdCreateFlag;
use std::backtrace::Backtrace;
use std::cmp;
use std::collections::HashMap;
use std::error::Error;
use std::fs::File;
use std::io;
use std::io::Seek;
use std::io::SeekFrom;
use std::io::Write;
use std::process::Command;

struct Handle {
	con_id: usize,
	name: String,
}

fn main() -> () {
	let mut stash: HashMap<String, Handle> = HashMap::new();

	let mut i3 = I3Stream::conn_sub(&[event::Subscribe::Binding])
		.expect("Failed to connect event listener to i3/sway ipc");

	let mut i3c =
		I3Stream::conn_sub(&[]).expect("Failed to connect command dispatcher to i3/sway ipc");

	println!("running!");
	for event in i3.listen() {
		println!("saw event");
		match event.expect("failed to read event") {
			event::Event::Binding(event::BindingData {
				binding: event::BindingObject { command, .. },
				..
			}) => match command.as_ref() {
				"nop workspace-stash-unstash" => stash_workspace(&mut i3c, &mut stash)
					.unwrap_or_else(|e| eprintln!("Failed to stash workspace: {}", e)),
				"nop workspace-switcher-right" => workspace_switch(&mut i3c, Direction::Right)
					.unwrap_or_else(|e| eprintln!("Failed to switch workspace: {}", e)),
				"nop workspace-switcher-left" => workspace_switch(&mut i3c, Direction::Left)
					.unwrap_or_else(|e| eprintln!("Failed to switch workspace: {}", e)),
				"nop workspace-switcher-swap" => workspace_swap(&mut i3c)
					.unwrap_or_else(|e| eprintln!("Failed to swap workspace: {}", e)),
				"nop workspace-switcher-swap-focus" => unimplemented!(),
				_ => (),
			},
			_ => (),
		}
	}
}

#[derive(thiserror::Error, Debug)]
enum StashWorkspaceError {
	#[error("Failed to command i3: {0}")]
	I3Error(#[source] io::Error),

	#[error("Failed to prompt with dmenu: {0}")]
	DmenuError(#[source] DmenuError<io::Error>),

	#[error("focused workspace was not found in tree")]
	FocusedWorkspaceNotInTree,
	#[error("focused workspace did not have a Con child")]
	WorkspaceMissingCon,
	#[error("dmenu did not produce a name")]
	Aborted
}


enum MyErrorReal {
    Foo(Backtrace),
    Bar(Backtrace),
}

enum MyError {
    Foo,
    Bar,
}

impl From<MyError> for MyErrorReal {
    fn from(error: MyError) -> MyErrorReal {
        match error {
            MyError::Foo => MyErrorReal::Foo(Backtrace::capture()),
            MyError::Bar => MyErrorReal::Bar(Backtrace::capture()),
        }
    }
}
fn stash_workspace(
	i3: &mut I3Stream,
	stash: &mut HashMap<String, Handle>,
) -> Result<(), StashWorkspaceError> {
	let workspaces = i3.get_workspaces().map_err(StashWorkspaceError::I3Error)?;
	let workspace = workspaces
		.iter()
		.find(|w| w.focused)
		.expect("No focused workspace was found");

	let stash_name = dmenu("stash or unstash:", |f| {
		f.write(workspace.name.as_bytes())?;
		f.write(b"\n")?;
		for key in stash.keys() {
			f.write(key.as_bytes())?;
			f.write(b"\n")?;
		}
		Ok(())
	})
	.map_err(StashWorkspaceError::DmenuError)
	.and_then(|x| x.ok_or(StashWorkspaceError::Aborted))?;

	if let Some(Handle { name, con_id }) = stash.get(&stash_name) {
		let workspace_name = dmenu("unstash as:", |f| {
			f.write(name.as_bytes())?;
			f.write(b"\n")?;
			f.write(stash_name.as_bytes())?;
			f.write(b"\n")?;
			Ok(())
		})
		.map_err(StashWorkspaceError::DmenuError)
		.and_then(|x| x.ok_or(StashWorkspaceError::Aborted))?;
	
		i3.run_command(format!(
			"[con_id={}] move to workspace {}; [con_id={}] floating disable",
			con_id, workspace_name, con_id
		))
		.map_err(StashWorkspaceError::I3Error)?;
		stash.remove(&stash_name);

		i3.run_command(format!("workspace {}", workspace_name))
			.map_err(StashWorkspaceError::I3Error)?;
	} else {


		i3.run_command(format!("[con_id={}] split toggle", workspace.id))
			.map_err(StashWorkspaceError::I3Error)?;
		let root = i3.get_tree().map_err(StashWorkspaceError::I3Error)?;

		let &reply::Node { id: con_id, .. } = find_in_tree(&root, workspace.id)
			.ok_or(StashWorkspaceError::FocusedWorkspaceNotInTree)?
			.nodes
			.get(0)
			.ok_or(StashWorkspaceError::WorkspaceMissingCon)?;

		i3.run_command(format!("[con_id={}] move scratchpad", con_id))
			.map_err(StashWorkspaceError::I3Error)?;
		let name = workspace.name.clone();
		stash.insert(stash_name, Handle { name, con_id });

      if let Err(WorkspaceSwitchError::NotFound) = workspace_switch(i3, Direction::Left) {
         let _ = workspace_switch(i3, Direction::Right);
      }
	}
	Ok(())
}

#[derive(thiserror::Error, Debug)]
enum DmenuError<E: Error> {
	#[error("Failed to write to memfd using provided writer: {0}")]
	WriterError(#[source] E),
	#[error("Failed to flush writes to memfd: {0}")]
	FlushError(#[source] io::Error),
	#[error("Failed to seek memfd: {0}")]
	SeekError(#[source] io::Error),
	#[error("Failed to open memfd: {0}")]
	FailedToOpenMemfd(#[source] nix::errno::Errno),
	#[error("Failed to capture output of dmenu: {0}")]
	CommandError(#[source] io::Error),
}

fn dmenu<F, E, R>(prompt: &str, writer: F) -> Result<Option<String>, DmenuError<E>>
where
	E: Error,
	F: FnOnce(&mut dyn Write) -> Result<R, E>,
{
	let mut mem = File::from(
		memfd_create(c"dmenu-stdin", MemFdCreateFlag::empty())
			.map_err(DmenuError::FailedToOpenMemfd)?,
	);

	writer(&mut mem).map_err(DmenuError::WriterError)?;
	mem.flush().map_err(DmenuError::FlushError)?;
	mem.seek(SeekFrom::Start(0))
		.map_err(DmenuError::SeekError)?;

	let o = Command::new("dmenu")
		.stdin(mem)
		.args(["-b", "-i", "-p", prompt])
		.output()
		.map_err(DmenuError::CommandError)?;

	if o.status.success() {
		let raw_response = String::from_utf8_lossy(&o.stdout);
		let response = raw_response.trim();
		if response.is_empty() {
			Ok(None)
		}
		else {
			Ok(Some(response.to_string()))
		}
	}
	else {
		Ok(None)
	}
}

fn find_in_tree(node: &reply::Node, id: usize) -> Option<&reply::Node> {
	if node.id == id {
		Some(node)
	} else {
		node.nodes.iter().find_map(|node| find_in_tree(node, id))
	}
}

#[derive(PartialEq)]
enum Direction {
	Left,
	Right,
}

#[derive(thiserror::Error, Debug)]
enum WorkspaceSwitchError {
	#[error("Failed to command i3: {0}")]
	I3Error(#[source] io::Error),

	#[error("No adjacent workspace found in the chosen direction")]
	NotFound,
}

fn workspace_switch(i3: &mut I3Stream, direction: Direction) -> Result<(), WorkspaceSwitchError> {
	let workspaces = i3.get_workspaces().map_err(WorkspaceSwitchError::I3Error)?;
	let adjacent = if direction == Direction::Left {
		// We don't attempt to create leftward workspaces
		find_adjacent_workspace(workspaces.iter().rev(), false)
	} else {
		find_adjacent_workspace(workspaces.iter(), true)
	};
	match adjacent {
		None => Err(WorkspaceSwitchError::NotFound),
		Some(AdjacentWorkspace::Num(num)) => {
			i3.run_command(format!("workspace number {}", num))
				.map_err(WorkspaceSwitchError::I3Error)?;
			Ok(())
		}
		Some(AdjacentWorkspace::Name(name)) => {
			i3.run_command(format!("workspace {}", name))
				.map_err(WorkspaceSwitchError::I3Error)?;
			Ok(())
		}
	}
}

fn workspace_swap(i3: &mut I3Stream) -> io::Result<()> {
	let workspaces = i3.get_workspaces()?;
	let result = workspaces
		.iter()
		.filter(|w| w.visible)
		.sorted_by_key(|w| w.focused)
		.rev()
		.collect_vec();
	println!("got {:#?}", result);
	Ok(())
}

enum AdjacentWorkspace<'a> {
	Num(i32),
	Name(&'a String),
}

fn find_adjacent_workspace<'a>(
	mut workspaces: impl Iterator<Item = &'a reply::Workspace>,
	suggest: bool,
) -> Option<AdjacentWorkspace<'a>> {
	let mut max = 0;
	let mut focused_output = Option::<&String>::None;

	// Start aggregating max workspace number
	for &reply::Workspace {
		num,
		focused,
		ref output,
		..
	} in &mut workspaces
	{
		max = cmp::max(max, num);

		// when we find the focused output, we can start looking for the next adjacent workspace
		if focused {
			focused_output = Some(output);
			break;
		}
	}

	if let Some(focused_output) = focused_output {
		// Continue aggregating max workspace number
		// look for the next workspace on the focused output, it will be adjacent to the focused workspace.
		for &reply::Workspace {
			num,
			ref name,
			ref output,
			..
		} in workspaces
		{
			max = cmp::max(max, num);
			if focused_output == output {
				// When we find the adjacent workspace it may be a numeric workspace
				// or it may have a string name and its number will be -1
				if num >= 0 {
					return Some(AdjacentWorkspace::Num(num));
				} else {
					return Some(AdjacentWorkspace::Name(name));
				}
			}
		}

		// No adjacent workspace was found, but we know what number that
		// workspace would've had. If the caller opted to "suggest" then
		// we return that number as if we'd found it.
		suggest.then(|| AdjacentWorkspace::Num(max + 1))
	} else {
		// No focused workspace, bailout
		None
	}
}
