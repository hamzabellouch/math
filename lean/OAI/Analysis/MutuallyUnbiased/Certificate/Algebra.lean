import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

namespace OAI

/-!
# Exact-certificate algebra

These lemmas interpret finite rational coefficient lists over real moment vectors.
They do not assert that any particular list is a true Hadamard or MUB relation.
Such relations must be proved from the mathematical moment definitions.
-/
namespace MUB6.Certificate

open scoped BigOperators

abbrev Sparse (ι : Type*) := List (ι × ℚ)

namespace Sparse

variable {ι : Type*}

/-- Evaluate a sparse rational linear form on a real vector. Repeated keys add. -/
noncomputable def eval (v : Sparse ι) (x : ι → ℝ) : ℝ :=
  (v.map fun p => (p.2 : ℝ) * x p.1).sum

/-- The exact coefficient at one key, including all repeated occurrences. -/
def coeff [DecidableEq ι] (v : Sparse ι) (i : ι) : ℚ :=
  (v.map fun p => if p.1 = i then p.2 else 0).sum

def scale (q : ℚ) (v : Sparse ι) : Sparse ι :=
  v.map fun p => (p.1, q * p.2)

@[simp] theorem eval_nil (x : ι → ℝ) : eval [] x = 0 := rfl

@[simp] theorem eval_cons (p : ι × ℚ) (v : Sparse ι) (x : ι → ℝ) :
    eval (p :: v) x = (p.2 : ℝ) * x p.1 + eval v x := rfl

@[simp] theorem eval_append (v w : Sparse ι) (x : ι → ℝ) :
    eval (v ++ w) x = eval v x + eval w x := by
  simp [eval]

@[simp] theorem eval_scale (q : ℚ) (v : Sparse ι) (x : ι → ℝ) :
    eval (scale q v) x = (q : ℝ) * eval v x := by
  induction v with
  | nil => simp [scale]
  | cons p v ih =>
    change ((q * p.2 : ℚ) : ℝ) * x p.1 + eval (scale q v) x =
      (q : ℝ) * ((p.2 : ℝ) * x p.1 + eval v x)
    rw [ih]
    simp only [Rat.cast_mul, mul_add, mul_assoc]

@[simp] theorem coeff_nil [DecidableEq ι] (i : ι) : coeff [] i = 0 := rfl

@[simp] theorem coeff_cons [DecidableEq ι] (p : ι × ℚ) (v : Sparse ι) (i : ι) :
    coeff (p :: v) i = (if p.1 = i then p.2 else 0) + coeff v i := rfl

/-- Coefficient collection is valid for arbitrary real values of the variables. -/
theorem eval_eq_sum_coeff [Fintype ι] [DecidableEq ι]
    (v : Sparse ι) (x : ι → ℝ) :
    eval v x = ∑ i, (coeff v i : ℝ) * x i := by
  induction v with
  | nil => simp
  | cons p v ih =>
    simp only [eval_cons, coeff_cons, Rat.cast_add, add_mul, Finset.sum_add_distrib]
    rw [← ih]
    congr 1
    simp only [apply_ite, Rat.cast_zero, ite_mul, zero_mul]
    simp

/-- A kernel-checked coefficient comparison transports the interpretation. -/
theorem eval_eq_of_coeff_eq [Fintype ι] [DecidableEq ι]
    (v w : Sparse ι) (h : ∀ i, coeff v i = coeff w i) (x : ι → ℝ) :
    eval v x = eval w x := by
  simp_rw [eval_eq_sum_coeff, h]

/-- Assemble a proposed linear-combination witness. -/
def combine {κ : Type*} (rows : κ → Sparse ι) (w : Sparse κ) : Sparse ι :=
  w.flatMap fun p => scale p.2 (rows p.1)

theorem eval_combine {κ : Type*} (rows : κ → Sparse ι) (w : Sparse κ) (x : ι → ℝ) :
    eval (combine rows w) x = eval w (fun j => eval (rows j) x) := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    change eval (scale p.2 (rows p.1) ++ combine rows w) x =
      (p.2 : ℝ) * eval (rows p.1) x + eval w (fun j => eval (rows j) x)
    rw [eval_append, eval_scale, ih]

/-- Soundness of an exact rational linear consequence certificate. -/
theorem consequence [Fintype ι] [DecidableEq ι] {κ : Type*}
    (rows : κ → Sparse ι) (w : Sparse κ) (target : Sparse ι)
    (hcoeff : ∀ i, coeff target i = coeff (combine rows w) i)
    (x : ι → ℝ) (hrows : ∀ j, eval (rows j) x = 0) :
    eval target x = 0 := by
  rw [eval_eq_of_coeff_eq _ _ hcoeff, eval_combine]
  simp only [hrows]
  simp [eval]

/-- A residual coefficient list is bounded by its absolute coefficient sum. -/
theorem eval_le_abs_sum (v : Sparse ι) (x : ι → ℝ)
    (hx : ∀ i, |x i| ≤ 1) :
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

/-- The exact final constant and residual norm from the manuscript are separated
from any claim that a particular form has these coefficients. -/
theorem residual_arithmetic :
    (-613302797399911 + 179721388988719 : ℚ) / 6480 =
      -2007321335237 / 30 := by norm_num

theorem residual_strictly_negative : (-2007321335237 / 30 : ℝ) < 0 := by norm_num

/-- The last step of the mixed certificate, once its interpreted residual identity
and coefficient norm have both been proved. -/
theorem contradiction_of_residual {ι : Type*} (v : Sparse ι) (x : ι → ℝ)
    (Q : ℝ) (hx : ∀ i, |x i| ≤ 1)
    (hQ : Q = -613302797399911 / 6480 + Sparse.eval v x)
    (hnorm : (v.map fun p => |(p.2 : ℝ)|).sum = 179721388988719 / 6480)
    (hpos : 0 ≤ Q) : False := by
  have hb := Sparse.eval_le_abs_sum v x hx
  rw [hnorm] at hb
  linarith

/-- A balanced tree of linear combinations avoids a long flattened list during
kernel reduction. Each leaf refers to one independently justified equation. -/
inductive Combination (κ : Type*) where
  | leaf : κ → Combination κ
  | add : Combination κ → Combination κ → Combination κ
  | scale : ℚ → Combination κ → Combination κ

namespace Combination

variable {κ ι : Type*}

noncomputable def eval (rows : κ → Sparse ι) (x : ι → ℝ) : Combination κ → ℝ
  | .leaf k => Sparse.eval (rows k) x
  | .add a b => eval rows x a + eval rows x b
  | .scale q a => (q : ℝ) * eval rows x a

def coeff [DecidableEq ι] (rows : κ → Sparse ι) (i : ι) : Combination κ → ℚ
  | .leaf k => Sparse.coeff (rows k) i
  | .add a b => coeff rows i a + coeff rows i b
  | .scale q a => q * coeff rows i a

theorem eval_eq_sum_coeff [Fintype ι] [DecidableEq ι]
    (rows : κ → Sparse ι) (x : ι → ℝ) (c : Combination κ) :
    eval rows x c = ∑ i, (coeff rows i c : ℝ) * x i := by
  induction c with
  | leaf k => exact Sparse.eval_eq_sum_coeff (rows k) x
  | add a b ha hb =>
    simp only [eval, coeff, ha, hb, Rat.cast_add, add_mul, Finset.sum_add_distrib]
  | scale q a ha =>
    simp only [eval, coeff, ha, Rat.cast_mul, mul_assoc, Finset.mul_sum]

theorem eval_zero_of_rows (rows : κ → Sparse ι) (x : ι → ℝ)
    (h : ∀ k, Sparse.eval (rows k) x = 0) (c : Combination κ) :
    eval rows x c = 0 := by
  induction c with
  | leaf k => exact h k
  | add a b ha hb => simp [eval, ha, hb]
  | scale q a ha => simp [eval, ha]

/-- Pointwise checks of a balanced combination certify a real linear consequence. -/
theorem consequence [Fintype ι] [DecidableEq ι]
    (rows : κ → Sparse ι) (c : Combination κ) (target : Sparse ι)
    (hcoeff : ∀ i, Sparse.coeff target i = coeff rows i c)
    (x : ι → ℝ) (hrows : ∀ k, Sparse.eval (rows k) x = 0) :
    Sparse.eval target x = 0 := by
  rw [Sparse.eval_eq_sum_coeff]
  simp_rw [hcoeff]
  rw [← eval_eq_sum_coeff]
  exact eval_zero_of_rows rows x hrows c

end Combination

end MUB6.Certificate

end OAI
