import OAI.Geometry.RCD.Coordinates.PullbackDensityLaws

namespace OAI

/-! # The normalized density laws are supported where their density is nonzero -/

open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X]

theorem normalizedDensityLaw_ae_ne_zero (μ : Measure X) {f : X → ℝ}
    (hf : Measurable f) (hi : Integrable f μ) (hn : ∀ x, 0≤f x) (hp : 0<∫ x, f x ∂μ) :
    ∀ᵐ x ∂(normalizedDensityLaw μ hi hn hp : Measure X), f x≠0 := by
  change ∀ᵐ x ∂μ.withDensity (fun x => ENNReal.ofReal ((∫ y, f y ∂μ)⁻¹*f x)), f x≠0
  apply (ae_withDensity_iff (hf.const_mul _).ennreal_ofReal).mpr
  exact Eventually.of_forall fun x hx hz => hx (by simp only [hz,mul_zero,ENNReal.ofReal_zero])

theorem pullbackDensityLaw_ae_ne_zero {Y : Type*} [MetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (P : ProbabilityMeasure X) (v : X → Y) (hv : Measurable v)
    (f : Y →ᵇ ℝ) (hn : ∀ y, 0≤f y) (hp : 0<∫ x, f (v x) ∂(P : Measure X)) :
    ∀ᵐ x ∂(pullbackDensityLaw P v hv f hn hp : Measure X), f (v x)≠0 :=
  normalizedDensityLaw_ae_ne_zero _ (f.continuous.measurable.comp hv) _ _ _

end RegularPointCoordinates

end

end OAI
