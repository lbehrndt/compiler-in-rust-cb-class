//! This module provides a [`Printer`] struct that implements the [`Visitor`]
//! trait to format and print parse trees represented by the [`Root`], [`Stmt`],
//! and [`Expr`] types.
//!
//! ## Functionality
//!
//! The `Printer` is designed to convert parsed expressions and statements into
//! a human-readable string format. It constructs a formatted string by visiting
//! each node in the parse tree and producing an appropriate string
//! representation, including handling nested expressions and variable
//! assignments.
//!
//! ## Usage
//!
//! Create an instance of `Printer`, then use it to format a parse tree by
//! passing a `Root` object to the `format` method. The method will visit each
//! node in the tree and accumulate the formatted output.
//!
//! ## Examples
//!
//! Basic usage:
//! ```
//! # use syntree::{Root, Printer};
//! let root = Root::from_str("a 3 5 + =").unwrap();
//! let mut printer = Printer::default();
//! let output = printer.format(&root);
//!
//! println!("{}", output); // prints a=(3+5)
//! ```

use crate::parse_tree::*;

/// `Printer` is a struct used for formatting parse trees into human-readable
/// strings.
///
/// ## Example
/// ```
/// # use syntree::{Root, Printer};
/// # fn doc(root: Root) {
/// let mut printer = Printer::default();
/// let formatted_output = printer.format(&root);
/// println!("{}", formatted_output);
/// # }
/// ```
#[derive(Default)]
pub struct Printer {
    infix_notation: String,
}

impl Printer {
    /// Folds the entire parse tree starting from a [`Root`] object into a
    /// single string.
    ///
    /// Traverses the tree, visiting each statement and expression to generate
    /// formatted strings, and then concatenates these strings into a single
    /// result separated by newlines.
    pub fn format(&mut self, _t: &Root) -> String {
        self.visit_root(_t);
        self.infix_notation.clone()
    }
}

impl Visitor for Printer {
    /// Visits the root of the parse tree, iterating through the statement list and
    /// visiting each statement.
    ///
    /// ## Arguments
    ///
    /// * `root: Root` - The root of the tree to be visited.
    ///
    /// ## Example
    ///
    /// ```
    /// // input (expr) = 1 2 3 + -
    /// let tree = Root::from_str(expr);
    ///
    /// let mut printer = Printer::default();
    /// println!("{}", printer.format(&tree))
    /// // output = (1-(2+3))
    /// ```
    fn visit_root(&mut self, root: &Root) {
        for (i, stmt) in root.stmt_list.iter().enumerate() {
            self.visit_stmt(stmt);
            if i + 1 < root.stmt_list.len() {
                self.infix_notation += "\n";
            }
        }
    }

    /// Visits a statement, appending its infix representation to the `infix_notation` string.
    ///
    /// ## Arguments
    ///
    /// * `stmt` - The stmt node to be visited.
    fn visit_stmt(&mut self, stmt: &Stmt) {
        match *stmt {
            Stmt::Expr(ref e) => self.visit_expr(e),
            Stmt::Set(ref var, ref expr) => {
                self.infix_notation += &var.to_string();
                self.infix_notation += "=";
                self.visit_expr(expr);
            }
        }
    }

    /// Visits an expression, appending its infix representation to the `infix_notation` string.
    ///
    /// ## Arguments
    ///
    /// * `expr` - The expression node to be visited.
    fn visit_expr(&mut self, expr: &Expr) {
        match *expr {
            Expr::Int(i) => self.infix_notation += &i.to_string(),
            Expr::Var(v) => self.infix_notation += &v.to_string(),
            Expr::Add(ref lhs, ref rhs)
            | Expr::Sub(ref lhs, ref rhs)
            | Expr::Mul(ref lhs, ref rhs)
            | Expr::Div(ref lhs, ref rhs) => {
                self.infix_notation += "(";
                self.visit_expr(lhs);
                self.infix_notation += match expr {
                    Expr::Add(_, _) => "+",
                    Expr::Sub(_, _) => "-",
                    Expr::Mul(_, _) => "*",
                    Expr::Div(_, _) => "/",
                    _ => unreachable!(),
                };
                self.visit_expr(rhs);
                self.infix_notation += ")";
            }
        }
    }
}

// unit-tests

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn add() {
        let tree = Root::from_stmt(Stmt::add(4, 2));
        assert_eq!(Printer::default().format(&tree), "(4+2)");
    }

    #[test]
    fn sub() {
        let tree = Root::from_stmt(Stmt::sub(4, 2));
        assert_eq!(Printer::default().format(&tree), "(4-2)");
    }

    #[test]
    fn mul() {
        let tree = Root::from_stmt(Stmt::mul(4, 2));
        assert_eq!(Printer::default().format(&tree), "(4*2)");
    }

    #[test]
    fn div() {
        let tree = Root::from_stmt(Stmt::div(4, 2));
        assert_eq!(Printer::default().format(&tree), "(4/2)");
    }

    #[test]
    fn set() {
        let tree = Root::from_stmt(Stmt::set('a', 1));
        assert_eq!(Printer::default().format(&tree), "a=1");
    }

    #[test]
    fn use_var() {
        let tree = Root {
            stmt_list: vec![
                Stmt::set('a', 2),
                Stmt::Expr(Expr::Add(
                    Box::new(Expr::Var('a')),
                    Box::new(Expr::Var('1')),
                )),
            ],
        };
        assert_eq!(Printer::default().format(&tree), "a=2\n(a+1)");
    }
}
