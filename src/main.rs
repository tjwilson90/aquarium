use std::collections::HashMap;
use std::error::Error;
use std::fs::File;
use std::io::Read;
use bstr::ByteSlice;
use disjoint_sets::UnionFind;
use regex::bytes::Regex;
use z3::{Config, Context, SatResult, Solver};
use z3::ast::Bool;

struct Walls(u8);

impl Walls {
    fn new() -> Self {
        Self(0)
    }

    fn set_left(&mut self) {
        self.0 |= 1;
    }

    fn left(&self) -> bool {
        self.0 & 1 != 0
    }

    fn set_top(&mut self) {
        self.0 |= 2;
    }

    fn top(&self) -> bool {
        self.0 & 2 != 0
    }
}

fn parse(bytes: &[u8]) -> i32 {
    let mut val = 0;
    for b in bytes {
        val = 10 * val + (*b - b'0');
    }
    val as i32
}

fn main() -> Result<(), Box<dyn Error>> {
    let mut file = File::open("/Users/twilson/code/aquarium/aquarium.html")?;
    let mut buf = Vec::new();
    file.read_to_end(&mut buf)?;

    let fill_regex = Regex::new(r#"<div class="cell task (.*?)".*?>(.*?)</div>"#)?;
    let mut v_fill = Vec::new();
    let mut h_fill = Vec::new();
    for cap in fill_regex.captures_iter(&buf) {
        let num = parse(&cap[2]);
        if cap[1].find("h").is_some() {
            h_fill.push(num);
        } else if cap[1].find("v").is_some() {
            v_fill.push(num);
        }
    }

    let cell_regex = Regex::new(r#"<div tabindex="1" class="cell selectable (.*?)""#)?;
    let mut walls = Vec::new();
    for cap in cell_regex.captures_iter(&buf) {
        let mut cell_walls = Walls::new();
        if cap[1].find("bt").is_some() {
            cell_walls.set_top();
        }
        if cap[1].find("bl").is_some() {
            cell_walls.set_left();
        }
        walls.push(cell_walls);
    }
    let width = v_fill.len();
    let height = h_fill.len();
    let mut uf = UnionFind::new(width * height);

    for i in 0..height {
        for j in 0..width {
            let idx = width * i + j;
            let w = &walls[idx];
            if i > 0 && !w.top() {
                uf.union(idx, width * (i - 1) + j);
            }
            if j > 0 && !w.left() {
                uf.union(idx, width * i + j - 1);
            }
        }
    }
    let mut groups = HashMap::<_, Vec<_>>::new();
    for i in 0..height {
        for j in 0..width {
            let idx = width * i + j;
            let group = uf.find(idx);
            groups.entry(group).or_default().push(idx);
        }
    }

    let ctx = &Context::new(&Config::new());
    let solver = Solver::new(ctx);
    let mut cell_vars = Vec::new();
    for i in 0..height {
        for j in 0..width {
            cell_vars.push(Bool::new_const(ctx, format!("cell_{}_{}", i, j)));
        }
    }
    for i in 0..height {
        let mut vars = Vec::new();
        for j in 0..width {
            vars.push((&cell_vars[width * i + j], 1));
        }
        solver.assert(&Bool::pb_eq(ctx, &vars, h_fill[i]));
    }
    for j in 0..width {
        let mut vars = Vec::new();
        for i in 0..height {
            vars.push((&cell_vars[width * i + j], 1));
        }
        solver.assert(&Bool::pb_eq(ctx, &vars, v_fill[j]));
    }
    for i in 0..(height * width) {
        for j in 0..(height * width) {
            if uf.equiv(i, j) {
                if i / width >= j / width {
                    solver.assert(&cell_vars[j].implies(&cell_vars[i]));
                }
                if i / width <= j / width {
                    solver.assert(&cell_vars[i].implies(&cell_vars[j]));
                }
            }
        }
    }

    assert_eq!(solver.check(), SatResult::Sat);
    let model = solver.get_model().unwrap();

    print!("┌───");
    for _ in 1..width {
        print!("┬───")
    }
    println!("┐");
    for i in 0..height {
        for j in 0..width {
            let cell = model.eval(&cell_vars[width * i + j], false).unwrap().as_bool().unwrap();
            if cell {
                print!("│ █ ");
            } else {
                print!("│   ");
            }
        }
        println!("│");
        if i != height - 1 {
            print!("├───");
            for _ in 1..width {
                print!("┼───")
            }
            println!("┤");
        }
    }
    print!("└───");
    for _ in 1..width {
        print!("┴───")
    }
    println!("┘");
    Ok(())
}
