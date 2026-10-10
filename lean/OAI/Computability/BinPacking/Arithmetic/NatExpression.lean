import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Embedding.Basic

namespace OAI

namespace BinPackingGap.NatExpressionCompiler

universe u

inductive Expr (α : Type u) : Type u
  | constant (value : Nat)
  | input (index : α)
  | add (left right : Expr α)
  | mul (left right : Expr α)
  | monus (left right : Expr α)

variable {α : Type u}

def eval (values : α → Nat) : Expr α → Nat
  | .constant value => value
  | .input index => values index
  | .add left right => eval values left + eval values right
  | .mul left right => eval values left * eval values right
  | .monus left right => eval values left - eval values right

@[simp] theorem eval_constant (values : α → Nat) (value : Nat) :
    eval values (.constant value) = value := rfl

@[simp] theorem eval_input (values : α → Nat) (index : α) :
    eval values (.input index) = values index := rfl

@[simp] theorem eval_add (values : α → Nat) (left right : Expr α) :
    eval values (.add left right) = eval values left + eval values right := rfl

@[simp] theorem eval_mul (values : α → Nat) (left right : Expr α) :
    eval values (.mul left right) = eval values left * eval values right := rfl

@[simp] theorem eval_monus (values : α → Nat) (left right : Expr α) :
    eval values (.monus left right) = eval values left - eval values right := rfl

def Node : Expr α → Type
  | .constant _ => Unit
  | .input _ => Unit
  | .add left right => Unit ⊕ (Node left ⊕ Node right)
  | .mul left right => Unit ⊕ (Node left ⊕ Node right)
  | .monus left right => Unit ⊕ (Node left ⊕ Node right)

instance nodeFintype : (expression : Expr α) → Fintype (Node expression)
  | .constant _ => inferInstanceAs (Fintype Unit)
  | .input _ => inferInstanceAs (Fintype Unit)
  | .add left right =>
      letI : Fintype (Node left) := nodeFintype left
      letI : Fintype (Node right) := nodeFintype right
      inferInstanceAs (Fintype (Unit ⊕ (Node left ⊕ Node right)))
  | .mul left right =>
      letI : Fintype (Node left) := nodeFintype left
      letI : Fintype (Node right) := nodeFintype right
      inferInstanceAs (Fintype (Unit ⊕ (Node left ⊕ Node right)))
  | .monus left right =>
      letI : Fintype (Node left) := nodeFintype left
      letI : Fintype (Node right) := nodeFintype right
      inferInstanceAs (Fintype (Unit ⊕ (Node left ⊕ Node right)))

instance nodeDecidableEq : (expression : Expr α) → DecidableEq (Node expression)
  | .constant _ => inferInstanceAs (DecidableEq Unit)
  | .input _ => inferInstanceAs (DecidableEq Unit)
  | .add left right =>
      letI : DecidableEq (Node left) := nodeDecidableEq left
      letI : DecidableEq (Node right) := nodeDecidableEq right
      inferInstanceAs (DecidableEq (Unit ⊕ (Node left ⊕ Node right)))
  | .mul left right =>
      letI : DecidableEq (Node left) := nodeDecidableEq left
      letI : DecidableEq (Node right) := nodeDecidableEq right
      inferInstanceAs (DecidableEq (Unit ⊕ (Node left ⊕ Node right)))
  | .monus left right =>
      letI : DecidableEq (Node left) := nodeDecidableEq left
      letI : DecidableEq (Node right) := nodeDecidableEq right
      inferInstanceAs (DecidableEq (Unit ⊕ (Node left ⊕ Node right)))

def rootBranch (left right : Expr α) : Unit ⊕ (Node left ⊕ Node right) :=
  .inl ()

def root : (expression : Expr α) → Node expression
  | .constant _ => ()
  | .input _ => ()
  | .add left right => rootBranch left right
  | .mul left right => rootBranch left right
  | .monus left right => rootBranch left right

@[simp] theorem rootBranch_eq (left right : Expr α) :
    rootBranch left right = Sum.inl () := rfl

@[simp] theorem root_constant (value : Nat) :
    root (.constant (α := α) value) = () := rfl

@[simp] theorem root_input (index : α) : root (.input index) = () := rfl

@[simp] theorem root_add (left right : Expr α) :
    root (.add left right) = rootBranch left right := rfl

@[simp] theorem root_mul (left right : Expr α) :
    root (.mul left right) = rootBranch left right := rfl

@[simp] theorem root_monus (left right : Expr α) :
    root (.monus left right) = rootBranch left right := rfl

def leftNode (left right : Expr α) : Node left ↪ Unit ⊕ (Node left ⊕ Node right) where
  toFun node := .inr (.inl node)
  inj' := by
    intro a b h
    exact Sum.inl.inj (Sum.inr.inj h)

def rightNode (left right : Expr α) : Node right ↪ Unit ⊕ (Node left ⊕ Node right) where
  toFun node := .inr (.inr node)
  inj' := by
    intro a b h
    exact Sum.inr.inj (Sum.inr.inj h)

@[simp] theorem leftNode_apply (left right : Expr α) (node : Node left) :
    leftNode left right node = Sum.inr (Sum.inl node) := rfl

@[simp] theorem rightNode_apply (left right : Expr α) (node : Node right) :
    rightNode left right node = Sum.inr (Sum.inr node) := rfl

end BinPackingGap.NatExpressionCompiler

end OAI
