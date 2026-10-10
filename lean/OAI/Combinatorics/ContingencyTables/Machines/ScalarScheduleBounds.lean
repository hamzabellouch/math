import OAI.Combinatorics.ContingencyTables.Machines.ScalarScheduleProgram

namespace OAI

/-! # Numeric bounds for the fixed arithmetic circuits -/

namespace ContingencyTables.ScalarScheduleProgram
open Polynomial
noncomputable section

def Expr.bound : Expr → Polynomial ℕ
  | .input _ => X
  | .number n => C n
  | .plus a b => a.bound+b.bound
  | .times a b => a.bound*b.bound

lemma Expr.eval_le (e : Expr) (xs : List ℕ) (M : ℕ)
    (h : ∀ i,xs.getD i 0 ≤ M) : e.eval xs ≤ e.bound.eval M := by
  induction e with
  | input i => simpa only [Expr.eval,Expr.bound,Polynomial.eval_X] using h i
  | number n => simp only [Expr.eval,Expr.bound,eval_C,le_refl]
  | plus a b ha hb =>
    simp only [Expr.eval,Expr.bound,Polynomial.eval_add]
    exact Nat.add_le_add ha hb
  | times a b ha hb =>
    simp only [Expr.eval,Expr.bound,Polynomial.eval_mul]
    exact Nat.mul_le_mul ha hb

lemma getD_le_of_mem (xs : List ℕ) (M : ℕ) (h : ∀ x∈xs,x ≤ M) :
    ∀ i,xs.getD i 0 ≤ M := by
  induction xs with
  | nil => intro i; simp
  | cons x xs ih =>
    intro i
    cases i with
    | zero => simpa using h x (by simp)
    | succ i =>
      simpa using ih (fun y hy => h y (by simp only [List.mem_cons]; exact Or.inr hy)) i

lemma Expr.eval_le_of_mem (e : Expr) (xs : List ℕ) (M : ℕ) (h : ∀ x∈xs,x ≤ M) :
    e.eval xs ≤ e.bound.eval M := e.eval_le xs M (getD_le_of_mem xs M h)

end
end ContingencyTables.ScalarScheduleProgram

end OAI
