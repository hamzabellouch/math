import OAI.Analysis.CircleDomains.Probability.AffinePhysicalTimeMeasure

namespace OAI

/-! Weighted physical costs of restricted paths are the old costs on the
retained interval, with full multiplicity and no endpoint atoms. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  {G : Set Y} {U : Set X}

theorem physicalOccupation_affine (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) {a b : PathTime} (hab : a < b) :
    dyadicPhysicalOccupation e y₀ (affineFinitePhysicalPath e hU y₀ γ hab) =
      ((physicalTimeLength e y₀ γ).restrict (Icc a b)).map (physicalValue e y₀ ∘ γ.val) := by
  have hf := (measurable_physicalValue e hU y₀).comp
    (affineRestrictedPath a b γ.val).continuous.measurable
  rw [← physicalTimeLength_map e hU y₀, physicalTimeLength_affine e hU y₀ γ hab]
  change (((physicalTimeLength e y₀ γ).restrict (Icc a b)).map (rescalePathTime a b)).map
    (physicalValue e y₀ ∘ affineRestrictedPath a b γ.val) = _
  rw [Measure.map_map hf (rescalePathTime a b).continuous.measurable]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  change physicalValue e y₀ (γ.val (affinePathTime a b (rescalePathTime a b t))) =
    physicalValue e y₀ (γ.val t)
  rw [affine_rescalePathTime hab ht]

theorem physicalCost_affine (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) {a b : PathTime} (hab : a < b)
    (g : Y → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ y, g y ∂dyadicPhysicalOccupation e y₀ (affineFinitePhysicalPath e hU y₀ γ hab)) =
      ∫⁻ t in Icc a b, g (physicalValue e y₀ (γ.val t)) ∂physicalTimeLength e y₀ γ := by
  rw [physicalOccupation_affine e hU y₀ γ hab]
  exact lintegral_map hg ((measurable_physicalValue e hU y₀).comp γ.val.continuous.measurable)

end CircleDomainRigidity

end

end OAI
