# gol

Data structures for [Conway's Game of Life](https://en.wikipedia.org/wiki/Conway%27s_Game_of_Life)

# Usage

Add this to your project's dependencies in `Cargo.toml`:

```toml
[dependencies]
gol = { git = "https://github.com/tlrobrn/gol" }
```

and this to your crate root:

```rust
extern crate gol;
```

# Examples

```rust
use gol::{Grid, Point};

let point = Point { x: 5, y: 2 };
let mut grid = Grid::with_points(&[point]);

assert_eq!(Some(0), grid.age_of_point(&point));

grid.tick();
assert_eq!(None, grid.age_of_point(&point));
```

# Docs

Run the following to generate and open the docs in your default browser:

```
$ cargo doc --open
```

# Tests

```
$ cargo test
```

# Build

```
$ cargo build
```

