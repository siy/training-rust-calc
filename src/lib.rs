extern crate core;

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
pub enum  EvalError {
    DivByZero
}

pub fn eval(expr: &Expr) -> Result<i64, EvalError> {
    match expr {
        Expr::Number(number) => Ok(*number),
        Expr::Sqr(arg) => eval(arg).map(|value| value * value),
        Expr::Add(left, right) => eval_args(left, right).map(|(one, two)| one + two),
        Expr::Sub(left, right) => eval_args(left, right).map(|(one, two)| one - two),
        Expr::Mul(left, right) => eval_args(left, right).map(|(one, two)| one * two),
        Expr::Div(left, right) => eval_args(left, right).and_then(|params| check_divisor(params)).map(|(one, two)| one / two),
    }
}

fn check_divisor(params: (i64, i64)) -> Result<(i64, i64), EvalError> {
    match params {
        (_, 0) => Err(DivByZero),
        _ => Ok(params),
    }
}

fn eval_args(left: &Expr, right: &Expr) -> Result<(i64, i64), EvalError> {
    Ok((eval(left)?, eval(right)?))
}

#[derive(Debug)]
pub enum ParseError {
    StackIsEmpty,
    NotANumber(String),
    InvalidExpr,
}

pub fn parse(input: &str) -> Result<Expr, ParseError> {
    let mut stack: Vec<Expr> = Vec::new();

    for word in input.split_ascii_whitespace() {
        match word {
            "sqr" => {
                let param = Box::from(stack.pop().ok_or(StackIsEmpty)?);
                stack.push(Expr::Sqr(param))
            },
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
            },

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

#[cfg(test)]
mod tests {
    use crate::{eval, parse};
    use crate::Expr;

    #[test]
    fn it_works() {
        let expr = Expr::Number(10);
        assert_eq!(eval(&expr).unwrap(), 10);
    }

    #[test]
    fn simple_expr1() {
        let expr = Expr::Add(Box::from(Expr::Number(1)), Box::from(Expr::Number(2)));

        assert_eq!(eval(&expr).unwrap(), 3);
    }

    #[test]
    fn simple_expr2() {
        let expr = Expr::Sub(Box::from(Expr::Number(3)), Box::from(Expr::Number(2)));

        assert_eq!(eval(&expr).unwrap(), 1);
    }

    #[test]
    fn simple_expr3() {
        let expr = Expr::Mul(Box::from(Expr::Number(3)), Box::from(Expr::Number(2)));

        assert_eq!(eval(&expr).unwrap(), 6);
    }

    #[test]
    fn simple_expr4() {
        let expr = Expr::Div(Box::from(Expr::Number(6)), Box::from(Expr::Number(3)));

        assert_eq!(eval(&expr).unwrap(), 2);
    }

    #[test]
    fn simple_expr5() {
        let expr = Expr::Sqr(Box::from(Expr::Number(6)));

        assert_eq!(eval(&expr).unwrap(), 36);
    }

    #[test]
    #[should_panic]
    fn cant_div_by_zero() {
        let expr = Expr::Div(Box::from(Expr::Number(1)), Box::from(Expr::Number(0)));

        eval(&expr).unwrap();
    }

    #[test]
    fn simple_expr_parsed0() {
        let expr = parse("2 3 *").unwrap();

        assert_eq!(eval(&expr).unwrap(), 6);
    }

    #[test]
    fn simple_expr_parsed1() {
        let expr = parse("3 sqr 4 sqr + 5 sqr -").unwrap();

        assert_eq!(eval(&expr).unwrap(), 0);
    }

    #[test]
    fn mul_test() {
        let expr = parse("3 5 * 2 -").unwrap();

        assert_eq!(eval(&expr).unwrap(), 13);
    }

    #[test]
    fn div_test() {
        let expr = parse("3 5 * 1 + 4 /").unwrap();

        assert_eq!(eval(&expr).unwrap(), 4);
    }
}

