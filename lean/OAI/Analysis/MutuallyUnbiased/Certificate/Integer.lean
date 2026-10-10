import OAI.Analysis.MutuallyUnbiased.Certificate.Algebra

namespace OAI

/-! Integer coefficient checking after denominator clearing. The arithmetic
checker uses only integer operations; its interpretation remains over arbitrary
real moment vectors. -/
namespace MUB6.Certificate.Integer

open scoped BigOperators

abbrev Sparse (ι : Type*) := List (ι × ℤ)

namespace Sparse

variable {ι : Type*}

noncomputable def eval (v : Sparse ι) (x : ι → ℝ) : ℝ :=
  (v.map fun p => (p.2 : ℝ) * x p.1).sum

def coeff [DecidableEq ι] (v : Sparse ι) (i : ι) : ℤ :=
  (v.map fun p => if p.1 = i then p.2 else 0).sum

@[simp] theorem eval_nil (x : ι → ℝ) : eval [] x = 0 := rfl
@[simp] theorem eval_cons (p : ι × ℤ) (v : Sparse ι) (x : ι → ℝ) :
    eval (p :: v) x = (p.2 : ℝ) * x p.1 + eval v x := rfl
@[simp] theorem coeff_nil [DecidableEq ι] (i : ι) : coeff [] i = 0 := rfl
@[simp] theorem coeff_cons [DecidableEq ι] (p : ι × ℤ) (v : Sparse ι) (i : ι) :
    coeff (p :: v) i = (if p.1 = i then p.2 else 0) + coeff v i := rfl

theorem eval_eq_sum_coeff [Fintype ι] [DecidableEq ι]
    (v : Sparse ι) (x : ι → ℝ) : eval v x = ∑ i, (coeff v i : ℝ) * x i := by
  induction v with
  | nil => simp
  | cons p v ih =>
    simp only [eval_cons, coeff_cons, Int.cast_add, add_mul, Finset.sum_add_distrib]
    rw [← ih]
    congr 1
    simp only [apply_ite, Int.cast_zero, ite_mul, zero_mul]
    simp

theorem eval_le_abs_sum (v : Sparse ι) (x : ι → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    eval v x ≤ (v.map fun p => |(p.2 : ℝ)|).sum := by
  induction v with
  | nil => simp
  | cons p v ih =>
    simp only [eval_cons, List.map_cons, List.sum_cons]
    apply add_le_add _ ih
    calc
      (p.2 : ℝ) * x p.1 ≤ |(p.2 : ℝ) * x p.1| := le_abs_self _
      _ = |(p.2 : ℝ)| * |x p.1| := abs_mul _ _
      _ ≤ |(p.2 : ℝ)| * 1 := mul_le_mul_of_nonneg_left (hx p.1) (abs_nonneg _)
      _ = |(p.2 : ℝ)| := mul_one _

end Sparse

inductive Combination (κ : Type*) where
  | leaf : κ → Combination κ
  | add : Combination κ → Combination κ → Combination κ
  | scale : ℤ → Combination κ → Combination κ

namespace Combination

variable {ι κ η : Type*}

noncomputable def eval (rows : κ → Sparse ι) (x : ι → ℝ) : Combination κ → ℝ
  | .leaf k => Sparse.eval (rows k) x
  | .add a b => eval rows x a + eval rows x b
  | .scale q a => (q : ℝ) * eval rows x a

def coeff [DecidableEq ι] (rows : κ → Sparse ι) (i : ι) : Combination κ → ℤ
  | .leaf k => Sparse.coeff (rows k) i
  | .add a b => coeff rows i a + coeff rows i b
  | .scale q a => q * coeff rows i a

theorem eval_eq_sum_coeff [Fintype ι] [DecidableEq ι]
    (rows : κ → Sparse ι) (x : ι → ℝ) (c : Combination κ) :
    eval rows x c = ∑ i, (coeff rows i c : ℝ) * x i := by
  induction c with
  | leaf k => exact Sparse.eval_eq_sum_coeff (rows k) x
  | add a b ha hb =>
    simp only [eval, coeff, ha, hb, Int.cast_add, add_mul, Finset.sum_add_distrib]
  | scale q a ha =>
    simp only [eval, coeff, ha, Int.cast_mul, mul_assoc, Finset.mul_sum]

theorem eval_zero_of_rows (rows : κ → Sparse ι) (x : ι → ℝ)
    (h : ∀ k, Sparse.eval (rows k) x = 0) (c : Combination κ) : eval rows x c = 0 := by
  induction c with
  | leaf k => exact h k
  | add a b ha hb => simp [eval, ha, hb]
  | scale q a ha => simp [eval, ha]

theorem eval_eq_of_coeff_eq [Fintype ι] [DecidableEq ι]
    (leftRows : κ → Sparse ι) (rightRows : η → Sparse ι)
    (left : Combination κ) (right : Combination η)
    (h : ∀ i, coeff leftRows i left = coeff rightRows i right)
    (x : ι → ℝ) : eval leftRows x left = eval rightRows x right := by
  simp_rw [eval_eq_sum_coeff, h]

theorem target_zero_of_coeff_eq [Fintype ι] [DecidableEq ι]
    (sources : κ → Sparse ι) (targets : η → Sparse ι)
    (source : Combination κ) (target : Combination η)
    (h : ∀ i, coeff targets i target = coeff sources i source)
    (x : ι → ℝ) (hsource : ∀ k, Sparse.eval (sources k) x = 0) :
    eval targets x target = 0 := by
  rw [eval_eq_of_coeff_eq targets sources target source h x]
  exact eval_zero_of_rows sources x hsource source

/-- An integer coefficient comparison proves a sparse target relation. -/
theorem consequence [Fintype ι] [DecidableEq ι]
    (rows : κ → Sparse ι) (source : Combination κ) (target : Sparse ι)
    (h : ∀ i, Sparse.coeff target i = coeff rows i source)
    (x : ι → ℝ) (hrows : ∀ k, Sparse.eval (rows k) x = 0) :
    Sparse.eval target x = 0 := by
  rw [Sparse.eval_eq_sum_coeff]
  simp_rw [h]
  rw [← eval_eq_sum_coeff]
  exact eval_zero_of_rows rows x hrows source

end Combination
end MUB6.Certificate.Integer

end OAI
