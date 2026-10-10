import OAI.NumberTheory.Ostmann.Arithmetic.BulkProductMixtures
import OAI.NumberTheory.Ostmann.Arithmetic.BulkCoordinateEnumeration

namespace OAI

/-! # Exact joint cell and residue reconstruction -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

/-- Sum the residue classes before estimating. The common original
normalization stays outside the sum, and the cell boxes are counted once. -/
theorem bulk_residue_mixture_integral {J C R : Type*}
    [Fintype J] [Fintype C] [Fintype R]
    (Z : J → ℝ) (hZ : ∀ j, 0 ≤ Z j)
    (μ : R → J → C → Measure ℝ) [∀ z j c, IsFiniteMeasure (μ z j c)]
    (f : R → BulkIntegrand J) :
    (∑ z, ∫ y, f z y ∂Measure.pi (fun j => bulkCellMixture (Z j) (μ z j))) =
      ((∏ j, Z j : ℝ) : ℂ) * ∑ c : J → C, ∑ z,
        ∫ y, f z y ∂Measure.pi (fun j => μ z j (c j)) := by
  simp_rw [BulkIntegrand.integral_product_mixtures _ Z hZ]
  rw [← Finset.mul_sum, Finset.sum_comm]

end Ostmann

end OAI
