//! Data structures for [Conway's Game of Life](https://en.wikipedia.org/wiki/Conway%27s_Game_of_Life)
//!
//! The key types are `Point` and `Grid`.
//! A `Point` is an (x, y) location on the integer plane.
//! A `Grid` is a collection of `Point`s that are active.
//!
//! # Usage
//!
//! Add this to your project's dependencies in `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! gol = { git = "https://github.com/tlrobrn/gol" }
//! ```
//!
//! and this to your crate root:
//!
//! ```rust
//! extern crate gol;
//! ```
//!
//! # Examples
//!
//! ```rust
//! use gol::{Grid, Point};
//!
//! let point = Point { x: 5, y: 2 };
//! let mut grid = Grid::with_points([point].iter());
//!
//! assert_eq!(Some(0), grid.age_of_point(&point));
//!
//! grid.tick();
//! assert_eq!(None, grid.age_of_point(&point));
//! ```
#![warn(missing_docs)]

use std::ops::{Add, Sub};
use std::collections::HashMap;

/// A point on the 2D integer plane.
///
/// `Add` and `Sub` are implemented on `Point`s for convenience.
///
/// # Example
///
/// ```rust
/// use gol::Point;
///
/// let p0 = Point{x: 0, y: 1};
/// let p1 = Point{x: 1, y: 0};
///
/// assert_eq!(Point{x: 1, y: 1}, p0 + p1);
/// assert_eq!(Point{x: -1, y: 1}, p0 - p1);
/// ```
#[derive(Clone, Copy, Hash, Eq, PartialEq, Debug, PartialOrd, Ord)]
pub struct Point {
    /// `x` coordinate in the integer plane.
    pub x: i64,
    /// `y` coordinate in the integer plane.
    pub y: i64,
}

impl Add for Point {
    type Output = Point;

    fn add(self, other: Point) -> Point {
        Point {
            x: self.x + other.x,
            y: self.y + other.y,
        }
    }
}

impl Sub for Point {
    type Output = Point;

    fn sub(self, other: Point) -> Point {
        Point {
            x: self.x - other.x,
            y: self.y - other.y,
        }
    }
}

const NEIGHBORHOOD_OFFSETS: [Point; 8] = [
    Point { x: -1, y: 1 },
    Point { x: 0, y: 1 },
    Point { x: 1, y: 1 },
    Point { x: -1, y: 0 },
    Point { x: 1, y: 0 },
    Point { x: -1, y: -1 },
    Point { x: 0, y: -1 },
    Point { x: 1, y: -1 },
];

fn neighbors(point: Point) -> Vec<Point> {
    NEIGHBORHOOD_OFFSETS
        .iter()
        .map(|&offset| point + offset)
        .collect()
}

/// The set of `Point`s that are alive.
///
/// A `Grid` represents the universe for the Game of Life.
/// If a `Point` has an age, then it is alive. Otherwise it is dead.
///
/// A `tick` on the `Grid` advances the _generation_ - new `Point`s are born and old ones die
/// according to the [rules](https://en.wikipedia.org/wiki/Conway%27s_Game_of_Life#Rules).
#[derive(Debug)]
pub struct Grid {
    cells: HashMap<Point, u64>,
    generation: u64,
}

impl Grid {
    /// Create an empty `Grid`.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use gol::Grid;
    /// # #[allow(unused_variables)]
    /// let grid = Grid::empty();
    /// ```
    pub fn empty() -> Self {
        Grid {
            cells: HashMap::new(),
            generation: 0,
        }
    }

    /// Create a `Grid` with the given `points`.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use gol::{Grid, Point};
    /// let point = Point{x: 1, y: 2};
    /// let grid = Grid::with_points([point].iter());
    ///
    /// assert_eq!(Some(0), grid.age_of_point(&point));
    /// ```
    pub fn with_points<'a, I>(points: I) -> Self
    where
        I: Iterator<Item = &'a Point>,
    {
        let mut cells = HashMap::new();
        for point in points {
            cells.insert(*point, 0);
        }

        Grid {
            cells,
            generation: 0,
        }
    }

    /// Add the given `point` to the `Grid`.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use gol::{Grid, Point};
    /// let mut grid = Grid::empty();
    /// let point = Point{x: 42, y: 13};
    ///
    /// grid.add_point(point);
    ///
    /// assert_eq!(Some(0), grid.age_of_point(&point));
    /// ```
    pub fn add_point(&mut self, point: Point) -> &mut Self {
        self.cells.entry(point).or_insert(self.generation);
        self
    }

    /// Remove the given `point` from the `Grid`.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use gol::{Grid, Point};
    /// let point = Point{x: 1, y: 2};
    /// let mut grid = Grid::with_points([point].iter());
    ///
    /// grid.remove_point(&point);
    ///
    /// assert_eq!(None, grid.age_of_point(&point));
    /// ```
    pub fn remove_point(&mut self, point: &Point) -> &mut Self {
        self.cells.remove(point);
        self
    }

    /// Check the age of the given `point` in the `Grid`.
    ///
    /// Returns `None` if the point is not present or `Some(age)` if the point is alive.
    ///
    /// # Example
    ///
    /// All new points start at age 0:
    ///
    /// ```rust
    /// # use gol::{Grid, Point};
    /// let points = [
    ///     Point { x: 5, y: 1 },
    ///     Point { x: 5, y: 2 },
    ///     Point { x: 5, y: 3 },
    /// ];
    /// let mut grid = Grid::with_points(points.iter());
    ///
    /// assert_eq!(Some(0), grid.age_of_point(&points[1]));
    /// ```
    ///
    /// Their age increases with every `tick` of the grid:
    ///
    /// ```rust
    /// # use gol::{Grid, Point};
    /// # let points = [
    /// #     Point { x: 5, y: 1 },
    /// #     Point { x: 5, y: 2 },
    /// #     Point { x: 5, y: 3 },
    /// # ];
    /// # let mut grid = Grid::with_points(points.iter());
    /// grid.tick();
    ///
    /// assert_eq!(Some(1), grid.age_of_point(&points[1]));
    /// ```
    pub fn age_of_point(&self, point: &Point) -> Option<u64> {
        self.cells.get(point).map(|birth| self.generation - birth)
    }

    /// Advance the `Grid` to the next generation.
    ///
    /// `Point`s die and are born according to the to the [rules](https://en.wikipedia.org/wiki/Conway%27s_Game_of_Life#Rules).
    ///
    /// # Example
    ///
    /// ```rust
    /// # use gol::{Grid, Point};
    /// let points = [
    ///     Point { x: 5, y: 1 },
    ///     Point { x: 5, y: 2 },
    ///     Point { x: 5, y: 3 },
    /// ];
    /// let mut grid = Grid::with_points(points.iter());
    ///
    /// grid.tick();
    ///
    /// assert_eq!(None, grid.age_of_point(&points[0]));
    /// assert_eq!(Some(1), grid.age_of_point(&points[1]));
    /// ```
    pub fn tick(&mut self) -> &mut Self {
        self.generation += 1;
        let mut next_generation = HashMap::new();

        for (cell, generation) in &self.cells {
            let count = self.count_neighbors(cell);

            if count > 1 && count < 4 {
                next_generation.insert(*cell, *generation);
            }
        }

        for cell in self.dead_candidates() {
            let count = self.count_neighbors(&cell);

            if count == 3 {
                next_generation.insert(cell, self.generation);
            }
        }

        self.cells = next_generation;
        self
    }

    /// Create an iterator over the given sub-range of the `Grid`.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use gol::{Grid, Point};
    /// let points = vec![
    ///     Point { x: 5, y: 1 },
    ///     Point { x: 5, y: 2 },
    ///     Point { x: 5, y: 3 },
    /// ];
    /// let grid = Grid::with_points(points.iter());
    ///
    /// let mut result: Vec<Point> = grid
    ///     .window(Point { x: 5, y: 1 }, Point { x: 6, y: 4 })
    ///     .map(|(point, _age)| point)
    ///     .collect();
    ///
    /// result.sort();
    ///
    /// assert_eq!(points, result);
    /// ```
    pub fn window(&self, lower_left: Point, upper_right: Point) -> GridWindow {
        GridWindow {
            grid: self,
            start_x: lower_left.x,
            x: lower_left.x,
            y: lower_left.y,
            end_x: upper_right.x,
            end_y: upper_right.y,
        }
    }

    fn count_neighbors(&self, point: &Point) -> usize {
        neighbors(*point)
            .iter()
            .fold(0, |acc, point| if self.cells.contains_key(point) {
                acc + 1
            } else {
                acc
            })
    }

    fn dead_candidates(&self) -> Vec<Point> {
        self.cells
            .iter()
            .flat_map(|(cell, _gen)| neighbors(*cell))
            .filter(|cell| !self.cells.contains_key(cell))
            .collect()
    }
}

/// Subset of the `Grid` that can be iterated over.
pub struct GridWindow<'a> {
    grid: &'a Grid,
    start_x: i64,
    x: i64,
    y: i64,
    end_x: i64,
    end_y: i64,
}

impl<'a> GridWindow<'a> {
    fn step(&mut self) {
        if self.x + 1 >= self.end_x {
            self.x = self.start_x;
            self.y += 1;
        } else {
            self.x += 1;
        }
    }
}

impl<'a> Iterator for GridWindow<'a> {
    type Item = (Point, u64);

    fn next(&mut self) -> Option<Self::Item> {
        if self.y >= self.end_y {
            return None;
        }

        let point = Point {
            x: self.x,
            y: self.y,
        };

        self.step();

        if let Some(age) = self.grid.age_of_point(&point) {
            Some((point, age))
        } else {
            self.next()
        }
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn neighbors_returns_an_array_of_the_surrounding_points() {
        let p = Point { x: 1, y: 5 };
        let expected_result: Vec<Point> = vec![
            Point { x: 0, y: 6 },
            Point { x: 1, y: 6 },
            Point { x: 2, y: 6 },
            Point { x: 0, y: 5 },
            Point { x: 2, y: 5 },
            Point { x: 0, y: 4 },
            Point { x: 1, y: 4 },
            Point { x: 2, y: 4 },
        ];

        assert_eq!(expected_result, neighbors(p));
    }
}

#[cfg(test)]
mod grid_tests {
    use super::*;

    #[test]
    fn contains_point_initialized_with() {
        let points = [Point { x: 5, y: 2 }];
        let g = Grid::with_points(points.iter());

        assert!(g.cells.contains_key(&points[0]));
        assert_eq!(1, g.cells.len());
    }

    #[test]
    fn tick_will_kill_living_cells_with_less_than_two_neighbors() {
        let points = [
            Point { x: 0, y: 0 },
            Point { x: 5, y: 2 },
            Point { x: 5, y: 3 },
        ];
        let mut g = Grid::with_points(points.iter());
        g.tick();

        assert_eq!(0, g.cells.len());
    }

    #[test]
    fn tick_will_kill_living_cells_with_more_than_three_neighbors() {
        let points = [
            Point { x: 0, y: 0 },
            Point { x: 2, y: 0 },
            Point { x: 1, y: 1 },
            Point { x: 1, y: 2 },
            Point { x: 0, y: 1 },
        ];
        let mut g = Grid::with_points(points.iter());
        g.cells.insert(Point { x: 0, y: 0 }, 0);

        g.tick();
        assert!(!g.cells.contains_key(&Point { x: 1, y: 1 }));
    }

    #[test]
    fn tick_will_make_a_cell_alive_if_it_has_3_neighbors() {
        let points = [
            Point { x: 0, y: 1 },
            Point { x: -1, y: 0 },
            Point { x: 1, y: 0 },
        ];
        let mut g = Grid::with_points(points.iter());

        g.tick();

        let point = Point { x: 0, y: 0 };
        assert!(g.cells.contains_key(&point));
    }

    #[test]
    fn tick_will_preserve_cells_with_2_neighbors() {
        let points = [
            Point { x: 5, y: 1 },
            Point { x: 5, y: 2 },
            Point { x: 5, y: 3 },
        ];
        let mut g = Grid::with_points(points.iter());
        g.tick();

        assert!(g.cells.contains_key(&Point { x: 5, y: 2 }));
    }

    #[test]
    fn tick_will_preserve_cells_with_3_neighbors() {
        let points = [
            Point { x: 5, y: 1 },
            Point { x: 5, y: 2 },
            Point { x: 6, y: 2 },
            Point { x: 5, y: 3 },
        ];
        let mut g = Grid::with_points(points.iter());
        g.tick();

        let point = Point { x: 5, y: 2 };
        match g.cells.get(&point) {
            Some(generation) => assert_eq!(0, generation.clone()),
            None => panic!("Point not found"),
        }
    }

    #[test]
    fn tick_advances_the_generation() {
        let mut g = Grid::empty();
        assert_eq!(0, g.generation);
        g.tick();
        assert_eq!(1, g.generation);
    }

    #[test]
    fn tick_new_cells_are_stored_with_their_birth_generation() {
        let points = [
            Point { x: 0, y: 1 },
            Point { x: -1, y: 0 },
            Point { x: 1, y: 0 },
        ];
        let mut g = Grid::with_points(points.iter());

        match g.cells.get(&points[0]) {
            Some(generation) => assert_eq!(0, generation.clone()),
            None => panic!("Point not found"),
        }

        g.tick();

        let point = Point { x: 0, y: 0 };
        match g.cells.get(&point) {
            Some(generation) => assert_eq!(1, generation.clone()),
            None => panic!("Point not found"),
        }
    }

    #[test]
    fn age_of_point_returns_none_if_point_is_dead() {
        let g = Grid::empty();
        assert_eq!(None, g.age_of_point(&Point { x: 0, y: 0 }));
    }

    #[test]
    fn age_of_point_returns_some_age_if_point_is_alive() {
        let points = [Point { x: 0, y: 1 }];
        let g = Grid::with_points(points.iter());
        assert_eq!(Some(0), g.age_of_point(&points[0]));
    }

    #[test]
    fn add_point_creates_new_point_with_the_current_generation() {
        let point = Point { x: 0, y: 0 };
        let mut g = Grid::empty();

        g.tick().add_point(point);

        assert_eq!(Some(0), g.age_of_point(&point));
    }

    #[test]
    fn add_point_does_not_overwrite_an_existing_point() {
        let point = Point { x: 0, y: 0 };
        let mut g = Grid::with_points([point].iter());
        g.generation = 1;

        g.add_point(point);

        assert_eq!(Some(1), g.age_of_point(&point));
    }

    #[test]
    fn remove_point_removes_a_point() {
        let point = Point { x: 0, y: 0 };
        let mut g = Grid::with_points([point].iter());

        g.remove_point(&point);

        assert_eq!(None, g.age_of_point(&point));
    }

    #[test]
    fn window_iterates_over_each_point_within_it() {
        let mut points = vec![
            Point { x: 0, y: 1 },
            Point { x: -1, y: 0 },
            Point { x: 1, y: 0 },
        ];
        points.sort();

        let grid = Grid::with_points(points.iter());

        let mut result: Vec<Point> = grid.window(Point { x: -2, y: -2 }, Point { x: 2, y: 2 })
            .map(|(point, _age)| point)
            .collect();

        result.sort();

        assert_eq!(points, result);
    }
}
