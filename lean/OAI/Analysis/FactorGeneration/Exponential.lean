import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

namespace Generator

/-! The homogeneous expansion of an ordered exponential product,
with factorial weights and multiplication order retained. -/
noncomputable section
open scoped BigOperators
section Algebra
variable {R : Type*} [Ring R] [Algebra ℝ R]

def exponentialDegree : List R → ℕ → R
  | [], d => if d = 0 then 1 else 0
  | a :: as, d => ∑ k ∈ Finset.range (d + 1),
      ((k.factorial : ℝ)⁻¹ • a ^ k) * exponentialDegree as (d - k)

@[simp] theorem exponentialDegree_zero (xs : List R) : exponentialDegree xs 0 = 1 := by
  induction xs with
  | nil => simp [exponentialDegree]
  | cons a as ih => simp [exponentialDegree, ih]

@[simp] theorem exponentialDegree_one (xs : List R) : exponentialDegree xs 1 = xs.sum := by
  induction xs with
  | nil => simp [exponentialDegree]
  | cons a as ih =>
    simp [exponentialDegree, Finset.sum_range_succ, ih, add_comm]

/-- Transport the finite original-degree polynomial through an algebra map. -/
theorem exponentialDegree_map {S : Type*} [Ring S] [Algebra ℝ S]
    (φ : R →ₐ[ℝ] S) (xs : List R) (d : ℕ) :
    φ (exponentialDegree xs d) = exponentialDegree (xs.map φ) d := by
  induction xs generalizing d with
  | nil => by_cases hd : d = 0 <;> simp [exponentialDegree, hd]
  | cons a as ih => simp [exponentialDegree, ih]

end Algebra

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

/-- Absolute convergence for fixed row count. This is not the uniform bound. -/
theorem exponentialDegree_summable_norm (xs : List R) :
    Summable (fun d => ‖exponentialDegree xs d‖) := by
  induction xs with
  | nil =>
    have he : (fun d => ‖exponentialDegree ([] : List R) d‖) =
        (fun d : ℕ => if d = 0 then ‖(1 : R)‖ else 0) := by
      funext d
      by_cases hd : d = 0 <;> simp [exponentialDegree, hd]
    rw [he]
    exact (hasSum_ite_eq (0 : ℕ) ‖(1 : R)‖).summable
  | cons a as ih =>
    exact summable_norm_sum_mul_range_of_summable_norm
      (NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) a) ih

variable [CompleteSpace R]

/-- The series sums to the ordered product, without requiring commuting rows. -/
theorem exponentialDegree_hasSum (xs : List R) :
    HasSum (exponentialDegree xs) ((xs.map NormedSpace.exp).prod) := by
  induction xs with
  | nil => simpa [exponentialDegree] using (hasSum_ite_eq (0 : ℕ) (1 : R))
  | cons a as ih =>
    have h := hasSum_sum_range_mul_of_summable_norm
      (NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) a)
      (exponentialDegree_summable_norm as)
    rw [(NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) a).tsum_eq, ih.tsum_eq] at h
    exact h

end

/-! Summation of homogeneous-degree remainder bounds, given the expansion and its coefficient estimates. -/
variable {E : Type*} [NormedAddCommGroup E]

theorem geometric_second_order_remainder {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (f : ℕ → E) {S : E} (hs : HasSum f S)
    (hb : ∀ n : ℕ, ‖f (n + 2)‖ ≤ q ^ (n + 2)) :
    ‖S - f 0 - f 1‖ ≤ q ^ 2 / (1 - q) := by
  have hg : HasSum (fun n : ℕ => q ^ (n + 2)) (q ^ 2 / (1 - q)) := by
    simpa only [pow_add, div_eq_mul_inv, mul_comm] using
      (hasSum_geometric_of_lt_one hq0 hq1).mul_right (q ^ 2)
  have ht : HasSum (fun n : ℕ => f (n + 2)) (S - f 0 - f 1) := by
    simpa [Finset.sum_range_succ, sub_add_eq_sub_sub] using (hasSum_nat_add_iff' 2).mpr hs
  exact ht.norm_le_of_bounded hg hb

/-- The source's 4α²/(1−2α) expression, with precisely 0 < α < 1/2. -/
theorem perturbation_remainder_from_degree_bounds {α : ℝ} (hα : 0 < α) (hhalf : α < 1 / 2)
    (f : ℕ → E) {S : E} (hs : HasSum f S)
    (hb : ∀ n : ℕ, ‖f (n + 2)‖ ≤ (2 * α) ^ (n + 2)) :
    ‖S - f 0 - f 1‖ ≤ 4 * α ^ 2 / (1 - 2 * α) := by
  have h := geometric_second_order_remainder (by linarith : 0 ≤ 2 * α)
    (by linarith : 2 * α < 1) f hs hb
  convert h using 1
  ring

end Generator

end OAI
