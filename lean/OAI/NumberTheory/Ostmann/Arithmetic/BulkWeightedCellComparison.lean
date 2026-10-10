import OAI.NumberTheory.Ostmann.Arithmetic.BulkKernelIntegralComparison
import OAI.NumberTheory.Ostmann.Arithmetic.BulkSeparatedKernelBound

namespace OAI

/-! # Keep all cell and residue costs in the prime replacement error -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

/-- A residue-dependent arithmetic coefficient is held fixed during prime
replacement. Its absolute value only multiplies the replacement error. -/
theorem bulk_weighted_cell_comparison {J C R : Type*}
    [Fintype J] [Fintype C] [Fintype R]
    (K : BulkIntegrand J) (a : R → ℂ) (Z : J → ℝ) (hZ : ∀ j, 0 ≤ Z j)
    (μ ν : (J → C) → R → J → Measure ℝ)
    [∀ c z j, IsFiniteMeasure (μ c z j)] [∀ c z j, IsFiniteMeasure (ν c z j)]
    (E : (J → C) → R → ℝ)
    (hE : ∀ c z, ‖(∫ y, K y ∂Measure.pi (μ c z)) -
      ∫ y, K y ∂Measure.pi (ν c z)‖ ≤ E c z) :
    ‖((∏ j, Z j : ℝ) : ℂ) * ∑ c : J → C, ∑ z,
        ∫ y, (K.constMul (a z)) y ∂Measure.pi (μ c z) -
      ((∏ j, Z j : ℝ) : ℂ) * ∑ c : J → C, ∑ z,
        ∫ y, (K.constMul (a z)) y ∂Measure.pi (ν c z)‖ ≤
      (∏ j, Z j) * ∑ c : J → C, ∑ z, ‖a z‖ * E c z := by
  have hprod : 0 ≤ ∏ j, Z j := Finset.prod_nonneg fun j _ => hZ j
  simp only [BulkIntegrand.constMul, integral_const_mul]
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hprod]
  apply mul_le_mul_of_nonneg_left _ hprod
  rw [← Finset.sum_sub_distrib]
  apply norm_sum_le_of_le
  intro c _
  rw [← Finset.sum_sub_distrib]
  apply norm_sum_le_of_le
  intro z _
  rw [← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left (hE c z) (norm_nonneg _)

/-- Combine the separately derived signed main term and replacement error. -/
theorem bulk_weighted_cell_bound {J C R : Type*}
    [Fintype J] [Fintype C] [Fintype R]
    (K : BulkIntegrand J) (a : R → ℂ) (Z : J → ℝ) (hZ : ∀ j, 0 ≤ Z j)
    (μ ν : (J → C) → R → J → Measure ℝ)
    [∀ c z j, IsFiniteMeasure (μ c z j)] [∀ c z j, IsFiniteMeasure (ν c z j)]
    (E : (J → C) → R → ℝ)
    (hE : ∀ c z, ‖(∫ y, K y ∂Measure.pi (μ c z)) -
      ∫ y, K y ∂Measure.pi (ν c z)‖ ≤ E c z)
    (B : ℝ)
    (hmain : ‖((∏ j, Z j : ℝ) : ℂ) * ∑ c : J → C, ∑ z,
      ∫ y, (K.constMul (a z)) y ∂Measure.pi (ν c z)‖ ≤ B) :
    ‖((∏ j, Z j : ℝ) : ℂ) * ∑ c : J → C, ∑ z,
      ∫ y, (K.constMul (a z)) y ∂Measure.pi (μ c z)‖ ≤
      B + (∏ j, Z j) * ∑ c : J → C, ∑ z, ‖a z‖ * E c z := by
  have he := bulk_weighted_cell_comparison K a Z hZ μ ν E hE
  rw [norm_sub_rev] at he
  exact (norm_le_norm_add_norm_sub _ _).trans (add_le_add hmain he)

end Ostmann

end OAI
