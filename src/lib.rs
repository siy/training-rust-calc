extern crate core;

use std::fmt;
use std::fmt::Formatter;
use std::str::FromStr;
use crate::EvalError::DivByZero;
use crate::Expr::Number;
use crate::ParseError::{InvalidExpr, NotANumber, StackIsEmpty};

#[derive(Debug, PartialEq)]
pub enum Expr {
    Number(i64),
    Sqr(Box<Expr>),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
}

#[derive(Debug)]
pub enum EvalError {
    DivByZero,
    IntegerOverflow,
}

impl fmt::Display for EvalError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            EvalError::DivByZero => write!(f, "Attempt to divide by zero"),
            EvalError::IntegerOverflow => write!(f, "Integer overflow")
        }
    }
}

impl std::error::Error for EvalError {}

pub trait Eval {
    fn eval(&self) -> Result<i64, EvalError>;
}

fn checked_add(pair: (i64, i64)) -> Option<i64> {
    pair.0.checked_add(pair.1)
}

fn checked_sub(pair: (i64, i64)) -> Option<i64> {
    pair.0.checked_sub(pair.1)
}

fn checked_mul(pair: (i64, i64)) -> Option<i64> {
    pair.0.checked_mul(pair.1)
}

fn checked_sqr(value: i64) -> Result<i64, EvalError> {
    value.checked_mul(value).ok_or(EvalError::IntegerOverflow)
}

fn checked_div(params: (i64, i64)) -> Result<i64, EvalError> {
    match params {
        (_, 0) => Err(DivByZero),
        _ => params.0.checked_div(params.1).ok_or(EvalError::IntegerOverflow)
    }
}

fn eval_args(left: &Expr, right: &Expr) -> Result<(i64, i64), EvalError> {
    Ok((left.eval()?, right.eval()?))
}

fn eval_args_and_then<F: FnOnce((i64, i64)) -> Option<i64>>(left: &Expr, right: &Expr, op: F) -> Result<i64, EvalError> {
    eval_args(left, right)
        .and_then(|pair| op(pair).ok_or(EvalError::IntegerOverflow))
}

impl Eval for Expr {
    fn eval(&self) -> Result<i64, EvalError> {
        match self {
            Expr::Number(number) => Ok(*number),
            Expr::Sqr(arg) => arg.eval().and_then(checked_sqr),
            Expr::Add(left, right) => eval_args_and_then(left, right, checked_add),
            Expr::Sub(left, right) => eval_args_and_then(left, right, checked_sub),
            Expr::Mul(left, right) => eval_args_and_then(left, right, checked_mul),
            Expr::Div(left, right) => eval_args(left, right).and_then(checked_div),
        }
    }
}

#[derive(Debug)]
pub enum ParseError {
    StackIsEmpty,
    NotANumber(String),
    InvalidExpr,
}

impl FromStr for Expr {
    type Err = ParseError;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        let mut stack: Vec<Expr> = Vec::new();

        for word in input.split_ascii_whitespace() {
            match word {
                "sqr" => {
                    let param = Box::from(stack.pop().ok_or(StackIsEmpty)?);
                    stack.push(Expr::Sqr(param))
                }
                "*" | "/" | "+" | "-" => {
                    let right = Box::from(stack.pop().ok_or(StackIsEmpty)?);
                    let left = Box::from(stack.pop().ok_or(StackIsEmpty)?);

                    let variant = match word {
                        "*" => Expr::Mul,
                        "/" => Expr::Div,
                        "+" => Expr::Add,
                        _ => Expr::Sub,
                    };

                    stack.push(variant(left, right))
                }

                value => {
                    let number = value.parse::<i64>().map_err(|_e| NotANumber(value.to_string()))?;
                    stack.push(Number(number))
                }
            }
        };

        if stack.len() != 1 {
            Err(InvalidExpr)
        } else {
            Ok(stack.pop().ok_or(StackIsEmpty)?)
        }
    }
}

#[derive(Debug)]
pub enum ParseOrEvalError {
    DivByZero,
    IntegerOverflow,
    StackIsEmpty,
    NotANumber(String),
    InvalidExpr,
}

impl fmt::Display for ParseOrEvalError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            ParseOrEvalError::DivByZero => write!(f, "Division by zero"),
            ParseOrEvalError::IntegerOverflow => write!(f, "Integer overflow"),
            ParseOrEvalError::StackIsEmpty => write!(f, "Stack is empty, check expression"),
            ParseOrEvalError::NotANumber(v) => write!(f, "Expected number, but found {}", v),
            ParseOrEvalError::InvalidExpr => write!(f, "Invalid expression"),
        }
    }
}

impl std::error::Error for ParseOrEvalError {}

impl From<ParseError> for ParseOrEvalError {
    fn from(value: ParseError) -> Self {
        match value {
            ParseError::StackIsEmpty => ParseOrEvalError::StackIsEmpty,
            ParseError::NotANumber(v) => ParseOrEvalError::NotANumber(v),
            ParseError::InvalidExpr => ParseOrEvalError::InvalidExpr,
        }
    }
}

impl From<EvalError> for ParseOrEvalError {
    fn from(value: EvalError) -> Self {
        match value {
            EvalError::DivByZero => ParseOrEvalError::DivByZero,
            EvalError::IntegerOverflow => ParseOrEvalError::IntegerOverflow,
        }
    }
}

pub fn eval_str(s: &str) -> Result<i64, ParseOrEvalError> {
    Ok(Expr::from_str(s)?.eval()?)
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;
    use crate::Eval;
    use crate::Expr;

    #[test]
    fn it_works() {
        let expr = Expr::Number(10);
        assert_eq!(expr.eval().unwrap(), 10);
    }

    #[test]
    fn simple_expr1() {
        let expr = Expr::Add(Box::from(Expr::Number(1)), Box::from(Expr::Number(2)));

        assert_eq!(expr.eval().unwrap(), 3);
    }

    #[test]
    fn simple_expr2() {
        let expr = Expr::Sub(Box::from(Expr::Number(3)), Box::from(Expr::Number(2)));

        assert_eq!(expr.eval().unwrap(), 1);
    }

    #[test]
    fn simple_expr3() {
        let expr = Expr::Mul(Box::from(Expr::Number(3)), Box::from(Expr::Number(2)));

        assert_eq!(expr.eval().unwrap(), 6);
    }

    #[test]
    fn simple_expr4() {
        let expr = Expr::Div(Box::from(Expr::Number(6)), Box::from(Expr::Number(3)));

        assert_eq!(expr.eval().unwrap(), 2);
    }

    #[test]
    fn simple_expr5() {
        let expr = Expr::Sqr(Box::from(Expr::Number(6)));

        assert_eq!(expr.eval().unwrap(), 36);
    }

    #[test]
    #[should_panic]
    fn cant_div_by_zero() {
        let expr = Expr::Div(Box::from(Expr::Number(1)), Box::from(Expr::Number(0)));

        expr.eval().unwrap();
    }

    #[test]
    fn simple_expr_parsed0() {
        let expr = Expr::from_str("2 3 *").unwrap();

        assert_eq!(expr.eval().unwrap(), 6);
    }

    #[test]
    fn simple_expr_parsed1() {
        let expr = Expr::from_str("3 sqr 4 sqr + 5 sqr -").unwrap();

        assert_eq!(expr.eval().unwrap(), 0);
    }

    #[test]
    fn mul_test() {
        let expr = Expr::from_str("3 5 * 2 -").unwrap();

        assert_eq!(expr.eval().unwrap(), 13);
    }

    #[test]
    fn div_test() {
        let expr = Expr::from_str("3 5 * 1 + 4 /").unwrap();

        assert_eq!(expr.eval().unwrap(), 4);
    }
}

