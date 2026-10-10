import Mathlib.Tactic.Ring
import OAI.Analysis.MutuallyUnbiased.Certificate.Integer

namespace OAI

/-! Evaluation-preserving sparse integer merge. Its soundness needs no sorting
hypothesis: ordering is only used to make generated witnesses short. Each merge
can be checked independently by a finite integer-list equality. -/
namespace MUB6.Certificate.Integer.Sparse

variable {ι : Type*}

@[simp] theorem eval_append (a b : Sparse ι) (x : ι → ℝ) :
    eval (a ++ b) x = eval a x + eval b x := by simp [eval]

theorem eval_perm {a b : Sparse ι} (h : a.Perm b) (x : ι → ℝ) :
    eval a x = eval b x := by
  unfold eval
  exact (h.map fun p : ι × ℤ => (p.2 : ℝ) * x p.1).sum_eq

def scale (q : ℤ) (a : Sparse ι) : Sparse ι := a.map fun p => (p.1, q * p.2)

@[simp] theorem eval_scale (q : ℤ) (a : Sparse ι) (x : ι → ℝ) :
    eval (scale q a) x = (q : ℝ) * eval a x := by
  induction a with
  | nil => simp [scale]
  | cons p a ih =>
    change ((q * p.2 : ℤ) : ℝ) * x p.1 + eval (scale q a) x =
      (q : ℝ) * ((p.2 : ℝ) * x p.1 + eval a x)
    rw [ih]
    simp only [Int.cast_mul, mul_add, mul_assoc]

def mergeFuel [LinearOrder ι] : ℕ → Sparse ι → Sparse ι → Sparse ι
  | 0, a, b => a ++ b
  | _ + 1, [], b => b
  | _ + 1, a, [] => a
  | fuel + 1, a :: as, b :: bs =>
      if a.1 < b.1 then a :: mergeFuel fuel as (b :: bs)
      else if a.1 = b.1 then
        if a.2 + b.2 = 0 then mergeFuel fuel as bs
        else (a.1, a.2 + b.2) :: mergeFuel fuel as bs
      else b :: mergeFuel fuel (a :: as) bs

theorem eval_mergeFuel [LinearOrder ι] (fuel : ℕ) (a b : Sparse ι) (x : ι → ℝ) :
    eval (mergeFuel fuel a b) x = eval a x + eval b x := by
  induction fuel generalizing a b with
  | zero => simp [mergeFuel]
  | succ fuel ih =>
    cases a with
    | nil => simp [mergeFuel]
    | cons a as =>
      cases b with
      | nil => simp [mergeFuel]
      | cons b bs =>
        simp only [mergeFuel]
        split_ifs with hlt heq hz
        · simp only [eval_cons, ih]
          ring
        · simp only [ih, eval_cons]
          have hc : (a.2 : ℝ) + (b.2 : ℝ) = 0 := by exact_mod_cast hz
          have hcx := congrArg (fun z : ℝ => z * x b.1) hc
          simp only [add_mul, zero_mul] at hcx
          rw [heq]
          linarith
        · simp only [eval_cons, ih, Int.cast_add]
          rw [heq]
          ring
        · simp only [eval_cons, ih]
          ring

def merge [LinearOrder ι] (a b : Sparse ι) : Sparse ι :=
  mergeFuel (a.length + b.length) a b

@[simp] theorem eval_merge [LinearOrder ι] (a b : Sparse ι) (x : ι → ℝ) :
    eval (merge a b) x = eval a x + eval b x := eval_mergeFuel _ _ _ _

end MUB6.Certificate.Integer.Sparse

end OAI
