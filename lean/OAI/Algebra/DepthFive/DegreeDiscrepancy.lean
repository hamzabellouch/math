import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- For a zero-sum finite family, its total positive discrepancy is half of
its total absolute discrepancy.  This is the algebraic identity used when
ordering the factors in the product-rank argument. -/
theorem sum_positive_eq_half_sum_abs {ι : Type*} (s : Finset ι) (δ : ι → ℝ)
    (hδ : ∑ j ∈ s, δ j = 0) :
    ∑ j ∈ s.filter (fun j => 0 < δ j), δ j =
      (∑ j ∈ s, |δ j|) / 2 := by
  classical
  have habs : ∀ j, |δ j| = 2 * (if 0 < δ j then δ j else 0) - δ j := by
    intro j
    by_cases h : 0 < δ j
    · rw [ite_eq_left h, abs_of_pos h]
      ring
    · rw [ite_eq_right h, abs_of_nonpos (le_of_not_gt h)]
      ring
  have hs : (∑ j ∈ s, |δ j|) =
      2 * (∑ j ∈ s.filter (fun j => 0 < δ j), δ j) := by
    simp_rw [habs]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hδ, sub_zero,
      Finset.sum_filter]
  linarith

/-- The proportional bidegree discrepancies sum to zero. -/
theorem sum_degree_discrepancy_eq_zero {ι : Type*} (s : Finset ι)
    (e i : ι → ℝ) (lam n k : ℝ)
    (he : ∑ j ∈ s, e j = n) (hi : ∑ j ∈ s, i j = k)
    (hlam : lam * n = k) :
    ∑ j ∈ s, (i j - lam * e j) = 0 := by
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, he, hi, hlam, sub_self]

/-- Collecting factors with positive proportional discrepancy expresses
precisely the dimension-saving exponent in terms of absolute discrepancies. -/
theorem positive_bidegree_identity {ι : Type*} (s : Finset ι)
    (e i : ι → ℝ) (ρ lam : ℝ)
    (hlam : (1 + ρ) * lam = ρ)
    (hδ : ∑ j ∈ s, (i j - lam * e j) = 0) :
    (∑ j ∈ s.filter (fun j => 0 < i j - lam * e j), i j) -
      ρ * (∑ j ∈ s.filter (fun j => 0 < i j - lam * e j), (e j - i j)) =
      (1 + ρ) / 2 * (∑ j ∈ s, |i j - lam * e j|) := by
  classical
  have hpoint : ∀ j, i j - ρ * (e j - i j) =
      (1 + ρ) * (i j - lam * e j) := by
    intro j
    nlinarith [congrArg (fun x : ℝ => x * e j) hlam]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp_rw [hpoint]
  rw [← Finset.mul_sum, sum_positive_eq_half_sum_abs s (fun j => i j - lam * e j) hδ]
  ring

/-- Conversion of the intermediate-dimension exponent to a product of
individual discrepancy weights. -/
theorem positive_bidegree_rpow {ι : Type*} (s : Finset ι)
    (e i : ι → ℝ) (ρ lam α : ℝ) (hα : 0 < α)
    (hlam : (1 + ρ) * lam = ρ)
    (hδ : ∑ j ∈ s, (i j - lam * e j) = 0) :
    α ^ ((∑ j ∈ s.filter (fun j => 0 < i j - lam * e j), i j) -
      ρ * (∑ j ∈ s.filter (fun j => 0 < i j - lam * e j), (e j - i j))) =
      ∏ j ∈ s, (α ^ ((1 + ρ) / 2)) ^ |i j - lam * e j| := by
  rw [positive_bidegree_identity s e i ρ lam hlam hδ,
    Real.rpow_mul hα.le,
    Real.rpow_sum_of_pos (Real.rpow_pos_of_pos hα _) _ s]

/-- Dropping a constraint on independent choices and then distributing the
finite sums is valid for nonnegative weights. -/
theorem constrained_sum_prod_le_prod_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} (t : (j : ι) → Finset (κ j))
    (w : (j : ι) → κ j → ℝ)
    (hw : ∀ j x, x ∈ t j → 0 ≤ w j x)
    (P : ((j : ι) → κ j) → Prop) [DecidablePred P] :
    (∑ x ∈ (Fintype.piFinset t).filter P, ∏ j, w j (x j)) ≤
      ∏ j, ∑ x ∈ t j, w j x := by
  classical
  rw [Finset.prod_univ_sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro x hx _
  apply Finset.prod_nonneg
  intro j _
  exact hw j (x j) ((Fintype.mem_piFinset.mp hx) j)

/-- The one-factor bidegree weight used in the manuscript. -/
def degreeWeight (q lam : ℝ) (e : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (e + 1), q ^ |(i : ℝ) - lam * e|

/-- The bidegree-constrained sum in the product-rank bound is at most the
product of the individual degree weights. -/
theorem bidegree_weight_sum_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → ℕ) (k : ℕ) (q lam : ℝ) (hq : 0 ≤ q) :
    (∑ i ∈ (Fintype.piFinset (fun j => Finset.range (e j + 1))).filter
        (fun i => ∑ j, i j = k),
      ∏ j, q ^ |(i j : ℝ) - lam * e j|) ≤
      ∏ j, degreeWeight q lam (e j) := by
  classical
  exact constrained_sum_prod_le_prod_sum
    (fun j => Finset.range (e j + 1))
    (fun j i => q ^ |(i : ℝ) - lam * e j|)
    (fun _ _ _ => Real.rpow_nonneg hq _) _

end Problem335

end

end OAI
