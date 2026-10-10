import OAI.Analysis.CircleDomains.Probability.TagPaymentMeasure
import OAI.Analysis.CircleDomains.Probability.AffinePhysicalOccupation

namespace OAI

/-! The local payment measure is formed from actual physical time length
and the flagged visit toll. Its total mass is bounded by the selected
path law’s cost. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  {G : Set Y} {U : Set X}

def physicalTagPayment (e : G ≃ₜ U) (y₀ : Y) (γ : FinitePhysicalPath e y₀)
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) : Measure PathTime :=
  tagPaymentMeasure (physicalTimeLength e y₀ γ)
    (fun t => g (physicalValue e y₀ (γ.val t))) γ.val m

theorem physicalTagPayment_univ (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) (g : Y → ℝ≥0∞) (hg : Measurable g)
    (m : X → ℝ≥0∞) :
    physicalTagPayment e y₀ γ g m univ =
      (∫⁻ y, g y ∂dyadicPhysicalOccupation e y₀ γ) + boundaryToll γ.val m := by
  rw [physicalTagPayment, tagPaymentMeasure_univ, physicalOccupation_integral e hU y₀ γ g hg]

theorem physicalTagPayment_finite (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) (g : Y → ℝ≥0∞) (hg : Measurable g)
    (m : X → ℝ≥0∞)
    (hcost : (∫⁻ y, g y ∂dyadicPhysicalOccupation e y₀ γ) + boundaryToll γ.val m < ∞) :
    IsFiniteMeasure (physicalTagPayment e y₀ γ g m) := by
  constructor
  rwa [physicalTagPayment_univ e hU y₀ γ g hg m]

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in
theorem physicalTagPayment_null_free (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    {F : Set PathTime} (hF : MeasurableSet F) (hout : ∀ t ∈ F, γ.val t ∉ U)
    (hm : ∀ t ∈ F, m (γ.val t) = 0) :
    physicalTagPayment e y₀ γ g m F = 0 := by
  apply tagPaymentMeasure_null_free _ _ _ _ hF _ hm
  exact measure_mono_null hout (physicalTimeLength_compl e hU y₀ γ)

theorem physicalTagPayment_interval (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) (g : Y → ℝ≥0∞) (hg : Measurable g)
    (m : X → ℝ≥0∞) {a b : PathTime} (hab : a < b) :
    physicalTagPayment e y₀ γ g m (Icc a b) =
      (∫⁻ y, g y ∂dyadicPhysicalOccupation e y₀ (affineFinitePhysicalPath e hU y₀ γ hab)) +
      boundaryTimeMeasure γ.val m (Icc a b) := by
  rw [physicalTagPayment, tagPaymentMeasure, Measure.add_apply, withDensity_apply _ measurableSet_Icc,
    physicalCost_affine e hU y₀ γ hab g hg]

end CircleDomainRigidity

end

end OAI
