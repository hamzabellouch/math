import Std

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

namespace MatrixMultiplication.Foundation.Elementary

inductive BoundaryTerm where
  | a0 | a1 | b0 | b1 | c
  deriving DecidableEq, BEq, Repr

namespace BoundaryTerm

def x : BoundaryTerm → Nat
  | .a0 | .a1 | .c => 0
  | .b0 => 2
  | .b1 => 1

def y : BoundaryTerm → Nat
  | .a0 | .b0 => 0
  | .a1 | .b1 => 1
  | .c => 2

def z : BoundaryTerm → Nat
  | .a0 => 2
  | .a1 => 1
  | .b0 | .b1 | .c => 0

def all : List BoundaryTerm := [.a0, .a1, .b0, .b1, .c]

end BoundaryTerm

def testA (w : List BoundaryTerm) : Bool := w.all (fun s => s.z != 0)
def testB (w : List BoundaryTerm) : Bool := w.any (fun s => s.x != 0)
def testC (w : List BoundaryTerm) : Bool := w.any (fun s => s.y == 2)

theorem local_tests_exhaust (w : List BoundaryTerm) :
    testA w = (!testB w && !testC w) := by
  induction w with
  | nil => rfl
  | cons s w ih =>
    cases s <;>
      simp_all [testA, testB, testC, BoundaryTerm.x, BoundaryTerm.y, BoundaryTerm.z]

def localDegree (w : List BoundaryTerm) : Nat :=
  (testA w).toNat + (testB w).toNat + (testC w).toNat

theorem localDegree_eq (w : List BoundaryTerm) :
    localDegree w = if testB w && testC w then 2 else 1 := by
  unfold localDegree
  rw [local_tests_exhaust]
  cases testB w <;> cases testC w <;> rfl

def retained (w : List BoundaryTerm) : Bool :=
  !(testB w && testC w) && !testA w

def triples : List (List BoundaryTerm) :=
  BoundaryTerm.all.flatMap fun a =>
    BoundaryTerm.all.flatMap fun b =>
      BoundaryTerm.all.map fun third => [a, b, third]

theorem retained_triples_count : (triples.filter retained).length = 75 := by decide

theorem retained_b_triples_count :
    (triples.filter (fun w => retained w && testB w)).length = 56 := by decide

theorem retained_c_triples_count :
    (triples.filter (fun w => retained w && testC w)).length = 19 := by decide

end MatrixMultiplication.Foundation.Elementary

end OAI
