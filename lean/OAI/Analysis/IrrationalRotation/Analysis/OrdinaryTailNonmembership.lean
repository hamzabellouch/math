import OAI.Analysis.IrrationalRotation.Analysis.OrdinaryTailSubspaces
import OAI.Analysis.IrrationalRotation.Product.ProductCovariance
import OAI.Analysis.IrrationalRotation.Rotation.RotationHalfline

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.ProductModel

theorem fieldTailProjection_not_mem_factor (θ : ℕ → ℝ) (m : ℤ) :
    WeightedShift.fieldTailProjection (μ := baseMeasure) m ∉ factor θ := by
  intro hmem
  have hcov := field_covariance hmem (fun _ => WeightedShift.tailProjection m)
    (WeightedShift.fieldTailProjection_ae m)
  obtain ⟨x, hx⟩ := hcov.exists
  exact WeightedShift.tailProjection_not_commute_shift m (hx 1)

theorem ordinary_tail_projection (θ c : ℕ → ℝ) (m : ℤ) :
    IsStarProjection (WeightedShift.fieldTailProjection (μ := baseMeasure) m) ∧
      WeightedShift.fieldTailProjection (μ := baseMeasure) m ≠ 0 ∧
      WeightedShift.fieldTailProjection (μ := baseMeasure) m ≠ 1 ∧
      (1 - WeightedShift.fieldTailProjection (μ := baseMeasure) m) * weightedOperator θ c *
        WeightedShift.fieldTailProjection (μ := baseMeasure) m = 0 ∧
      WeightedShift.fieldTailProjection (μ := baseMeasure) m ∉ factor θ :=
  ⟨WeightedShift.fieldTailProjection_isStarProjection m,
    WeightedShift.fieldTailProjection_ne_zero m,
    WeightedShift.fieldTailProjection_ne_one m,
    WeightedShift.fieldTailProjection_invariant _ _ _ _ _ m,
    fieldTailProjection_not_mem_factor θ m⟩

end Invariant233.ProductModel

end

end OAI
