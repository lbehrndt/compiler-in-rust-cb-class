//! This module provides the [`Calculator`] struct, which is designed to
//! evaluate arithmetic expressions parsed into a [`Root`] structure from a
//! string representation. It supports operations including addition,
//! subtraction, multiplication, and division, along with variable assignments
//! from 'a' to 'z'.
//!
//! ## Example
//! ```
//! # use syntree::{Root, Visitor, Calculator};
//!
//! let mut calculator = Calculator::default();
//! let root = Root::from_str("a 1 = b 2 3 * = a b +").unwrap();
//! let result = calculator.calc(&root);
//!
//! println!("Final result: {}", result); // prints 7
//! ```

use std::collections::HashMap;

use crate::parse_tree::*;

/// `Calculator` is a struct designed to evaluate parsed arithmetic expressions.
///
/// ## Usage
/// ```
/// # use syntree::{Calculator, Root};
/// # fn doc(root: Root) {
/// let mut calculator = Calculator::default();
/// let result = calculator.calc(&root);
/// println!("The result of the calculation is: {}", result);
/// # }
/// ``````
pub struct Calculator {
    /// The solution of the calculation.
    solution: i64,
    /// A HashMap to store variable assignments.
    variables: HashMap<char, i64>,
}

impl Default for Calculator {
    /// Creates a new `Calculator` instance with default values.
    fn default() -> Self {
        Self {
            solution: 0,
            variables: HashMap::with_capacity(26), // Initialize HashMap with capacity 26 for lowercase alphabet variables
        }
    }
}

impl Calculator {
    /// Evaluates the entire parse tree starting from a [`Root`] and returns the
    /// result of the last expression evaluated.
    ///
    /// ## Arguments
    ///
    /// * `_t` - The root of the parse tree.
    ///
    /// ## Returns
    ///
    /// The result of the evaluation.
    ///
    /// ## Examples
    ///
    /// ```
    /// use calculator::{Calculator, Root};
    ///
    /// let mut calc = Calculator::default();
    /// let root = Root::from_stmt(Stmt::add(4, 2));
    /// assert_eq!(calc.calc(&root), 6);
    /// ```
    pub fn calc(&mut self, _t: &Root) -> i64 {
        self.visit_root(_t);
        self.solution
    }

    /// Evaluates a binary expression and returns the values of its operands as a tuple.
    fn evaluate_binary_expression(&mut self, lhs: &Expr, rhs: &Expr) -> (i64, i64) {
        self.visit_expr(lhs);
        let lhs_val = self.solution;
        self.visit_expr(rhs);
        let rhs_val = self.solution;

        (lhs_val, rhs_val)
    }

    /// Performs addition operation on two expressions.
    fn bin_add(&mut self, lhs: &Expr, rhs: &Expr) {
        let (left, right) = self.evaluate_binary_expression(lhs, rhs);

        self.solution = left + right;
    }

    /// Performs subtraction operation on two expressions.
    fn bin_sub(&mut self, lhs: &Expr, rhs: &Expr) {
        let (left, right) = self.evaluate_binary_expression(lhs, rhs);

        self.solution = left - right;
    }

    /// Performs multiplication operation on two expressions.
    fn bin_mul(&mut self, lhs: &Expr, rhs: &Expr) {
        let (left, right) = self.evaluate_binary_expression(lhs, rhs);

        self.solution = left * right;
    }

    /// Performs division operation on two expressions.
    fn bin_div(&mut self, lhs: &Expr, rhs: &Expr) {
        let (left, right) = self.evaluate_binary_expression(lhs, rhs);
        if right == 0 {
            panic!("Attempt to divide by zero");
        } else {
            self.solution = left / right;
        }
    }
}

impl Visitor for Calculator {
    /// Visits the root of the parse tree.
    fn visit_root(&mut self, root: &Root) {
        for stmt in root.stmt_list.iter() {
            self.visit_stmt(stmt);
        }
    }

    /// Visits a statement in the parse tree.
    fn visit_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Expr(ref e) => self.visit_expr(e),
            Stmt::Set(v, e) => {
                self.visit_expr(e);
                self.variables.insert(*v, self.solution); // add variable to hashmap
            }
        }
    }

    /// Visits an expression in the parse tree.
    ///
    /// This method recursively evaluates the expression by visiting its sub-expressions
    /// and updating the solution accordingly.
    fn visit_expr(&mut self, expr: &Expr) {
        match expr {
            Expr::Int(i) => self.solution = *i,
            Expr::Var(v) => {
                if let Some(val) = self.variables.get(v) {
                    self.solution = *val;
                } else {
                    panic!("Variable '{}' is not defined", v);
                }
            }
            Expr::Add(lhs, rhs) => self.bin_add(lhs, rhs),
            Expr::Sub(lhs, rhs) => self.bin_sub(lhs, rhs),
            Expr::Mul(lhs, rhs) => self.bin_mul(lhs, rhs),
            Expr::Div(lhs, rhs) => self.bin_div(lhs, rhs),
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
        assert_eq!(Calculator::default().calc(&tree), 6);
    }

    #[test]
    fn sub() {
        let tree = Root::from_stmt(Stmt::sub(4, 2));
        assert_eq!(Calculator::default().calc(&tree), 2);
    }

    #[test]
    fn mul() {
        let tree = Root::from_stmt(Stmt::mul(4, 2));
        assert_eq!(Calculator::default().calc(&tree), 8);
    }

    #[test]
    fn div() {
        let tree = Root::from_stmt(Stmt::div(4, 2));
        assert_eq!(Calculator::default().calc(&tree), 2);
    }

    #[test]
    #[should_panic(expected = "attempt to divide by zero")]
    fn division_by_zero() {
        let tree = Root::from_stmt(Stmt::div(4, 0));
        Calculator::default().calc(&tree);
    }

    #[test]
    fn set() {
        let tree = Root::from_stmt(Stmt::set('a', 1));
        assert_eq!(Calculator::default().calc(&tree), 0);
    }

    #[test]
    fn vars() {
        let tree = Root {
            stmt_list: vec![
                Stmt::set('i', 1),
                Stmt::set('j', 2),
                Stmt::Expr(Expr::Add(
                    Box::new(Expr::Var('i')),
                    Box::new(Expr::Var('j')),
                )),
            ],
        };
        assert_eq!(Calculator::default().calc(&tree), 3);
    }
}
