import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.RationalElimination

namespace OAI

section

namespace KS.W17

inductive RationalExpr where
  | value : ℚ → RationalExpr
  | add : RationalExpr → RationalExpr → RationalExpr
  | sub : RationalExpr → RationalExpr → RationalExpr
  | mul : RationalExpr → RationalExpr → RationalExpr
  | div : RationalExpr → RationalExpr → RationalExpr
  | neg : RationalExpr → RationalExpr

def RationalExpr.eval : RationalExpr → ℚ
  | .value q => q
  | .add x y => x.eval + y.eval
  | .sub x y => x.eval - y.eval
  | .mul x y => x.eval * y.eval
  | .div x y => x.eval / y.eval
  | .neg x => -x.eval

def RationalExpr.operations : RationalExpr → ℕ
  | .value _ => 0
  | .add x y | .sub x y | .mul x y | .div x y => x.operations + y.operations + 1
  | .neg x => x.operations + 1

def sumExpr : List RationalExpr → RationalExpr
  | [] => .value 0
  | x :: xs => .add x (sumExpr xs)

@[simp] theorem sumExpr_eval (xs : List RationalExpr) :
    (sumExpr xs).eval = (xs.map RationalExpr.eval).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sumExpr, RationalExpr.eval, ih]

@[simp] theorem sumExpr_operations (xs : List RationalExpr) :
    (sumExpr xs).operations = (xs.map RationalExpr.operations).sum + xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sumExpr, RationalExpr.operations, ih]; omega

def dotExpr {n : ℕ} (x y : Fin n → ℚ) : RationalExpr :=
  sumExpr (List.ofFn (fun i => .mul (.value (x i)) (.value (y i))))

@[simp] theorem dotExpr_eval {n : ℕ} (x y : Fin n → ℚ) :
    (dotExpr x y).eval = ∑ i, x i * y i := by
  simp [dotExpr, RationalExpr.eval, List.sum_ofFn]

@[simp] theorem dotExpr_operations {n : ℕ} (x y : Fin n → ℚ) :
    (dotExpr x y).operations = 2 * n := by
  simp [dotExpr, RationalExpr.operations, List.sum_ofFn, two_mul]

def schurEntryExpr {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (i j : Fin n) : RationalExpr :=
  .sub (.value (M i.succ j.succ))
    (.div (.mul (.value (M i.succ 0)) (.value (M 0 j.succ))) (.value (M 0 0)))

@[simp] theorem schurEntryExpr_eval {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (i j : Fin n) :
    (schurEntryExpr M i j).eval = schurTail M i j := rfl

@[simp] theorem schurEntryExpr_operations {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (i j : Fin n) :
    (schurEntryExpr M i j).operations = 3 := rfl

def liftHeadExpr {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (y : Fin n → ℚ) : RationalExpr :=
  .div (.neg (dotExpr (fun j => M 0 j.succ) y)) (.value (M 0 0))

@[simp] theorem liftHeadExpr_eval {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (y : Fin n → ℚ) :
    (liftHeadExpr M y).eval = schurWitnessLift M y 0 := by
  simp [liftHeadExpr, RationalExpr.eval, schurWitnessLift]

@[simp] theorem liftHeadExpr_operations {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (y : Fin n → ℚ) :
    (liftHeadExpr M y).operations = 2 * n + 2 := by
  simp [liftHeadExpr, RationalExpr.operations]

def zeroPivotExpr (q r : ℚ) : RationalExpr :=
  .div (.neg (.add (.value q) (.value 1))) (.mul (.value 2) (.value r))

@[simp] theorem zeroPivotExpr_eval (q r : ℚ) :
    (zeroPivotExpr q r).eval = -(q + 1) / (2 * r) := rfl

@[simp] theorem zeroPivotExpr_operations (q r : ℚ) :
    (zeroPivotExpr q r).operations = 4 := rfl

end KS.W17

end

end OAI
