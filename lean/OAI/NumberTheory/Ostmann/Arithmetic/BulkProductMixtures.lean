import Mathlib.MeasureTheory.Integral.Pi
import OAI.NumberTheory.Ostmann.Arithmetic.BulkCellMixtures

namespace OAI

/-! # Exact reassembly of the joint bulk cells -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

/-- Expanding all cell mixtures counts each joint box once and keeps the
original product of harmonic normalization constants. -/
theorem bulk_product_mixtures {J C : Type*} [Fintype J] [Fintype C]
    (Z : J → ℝ) (hZ : ∀ j, 0 ≤ Z j)
    (μ : J → C → Measure ℝ) [∀ j c, IsFiniteMeasure (μ j c)] :
    Measure.pi (fun j => bulkCellMixture (Z j) (μ j)) =
      ENNReal.ofReal (∏ j, Z j) • ∑ c : J → C, Measure.pi (fun j => μ j (c j)) := by
  apply Measure.pi_eq
  intro s hs
  simp only [Measure.smul_apply, Measure.finsetSum_apply, Measure.pi_pi,
    bulkCellMixture, smul_eq_mul]
  rw [ENNReal.ofReal_prod_of_nonneg (fun j _ => hZ j), Finset.prod_mul_distrib,
    Fintype.prod_sum]

/-- The exact joint integral corresponding to the original normalized cell
mixture; cell counts enter through a sum of integrals, not as a main-term loss. -/
theorem BulkIntegrand.integral_product_mixtures {J C : Type*} [Fintype J] [Fintype C]
    (f : BulkIntegrand J) (Z : J → ℝ) (hZ : ∀ j, 0 ≤ Z j)
    (μ : J → C → Measure ℝ) [∀ j c, IsFiniteMeasure (μ j c)] :
    (∫ x, f x ∂Measure.pi (fun j => bulkCellMixture (Z j) (μ j))) =
      ((∏ j, Z j : ℝ) : ℂ) * ∑ c : J → C, ∫ x, f x ∂Measure.pi (fun j => μ j (c j)) := by
  rw [bulk_product_mixtures Z hZ μ, integral_smul_measure,
    ENNReal.toReal_ofReal (Finset.prod_nonneg fun j _ => hZ j), Complex.real_smul,
    integral_finsetSum_measure]
  intro c _
  exact f.integrable _

end Ostmann

end OAI
