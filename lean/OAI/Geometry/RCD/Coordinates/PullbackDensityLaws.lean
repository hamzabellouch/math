import OAI.Geometry.RCD.Coordinates.NormalizedDensityLaw

namespace OAI

/-! # Actual source probability densities with prescribed Euclidean limits -/

open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MeasurableSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

private theorem pullback_density_integrable (P : ProbabilityMeasure X)
    (v : X → Y) (hv : Measurable v) (f : Y →ᵇ ℝ) :
    Integrable (fun x => f (v x)) (P : Measure X) :=
  (integrable_const ‖f‖).mono' (f.continuous.measurable.comp hv).aestronglyMeasurable
    (Eventually.of_forall fun x => f.norm_coe_le_norm (v x))

def pullbackDensityLaw (P : ProbabilityMeasure X) (v : X → Y) (hv : Measurable v)
    (f : Y →ᵇ ℝ) (hn : ∀ y, 0≤f y) (hp : 0<∫ x, f (v x) ∂(P : Measure X)) :
    ProbabilityMeasure X :=
  normalizedDensityLaw (P : Measure X)
    (pullback_density_integrable P v hv f) (fun x => hn (v x)) hp

theorem pullbackDensityLaw_integral (P : ProbabilityMeasure X) (v : X → Y) (hv : Measurable v)
    (f : Y →ᵇ ℝ) (hn : ∀ y, 0≤f y) (hp : 0<∫ x, f (v x) ∂(P : Measure X)) (g : X → ℝ) :
    (∫ x, g x ∂(pullbackDensityLaw P v hv f hn hp : Measure X))=
      (∫ x, f (v x) ∂(P : Measure X))⁻¹*(∫ x, f (v x)*g x ∂(P : Measure X)) :=
  normalizedDensityLaw_integral _ (f.continuous.measurable.comp hv) _ _ _ g

theorem pullback_density_mass_tendsto (P : ℕ → ProbabilityMeasure X) (v : ℕ → X → Y)
    (hv : ∀ k, Measurable (v k)) {ν : ProbabilityMeasure Y}
    (hweak : Tendsto (fun k => (P k).map (v k)) atTop (𝓝 ν)) (f : Y →ᵇ ℝ) :
    Tendsto (fun k => ∫ x, f (v k x) ∂(P k : Measure X)) atTop
      (𝓝 (∫ y, f y ∂(ν : Measure Y))) := by
  have ht := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak f
  simp_rw [ProbabilityMeasure.toMeasure_map,integral_map (hv _).aemeasurable
    f.continuous.aestronglyMeasurable] at ht
  exact ht

theorem pullback_density_laws_tendsto (P : ℕ → ProbabilityMeasure X) (v : ℕ → X → Y)
    (hv : ∀ k, Measurable (v k)) {ν : ProbabilityMeasure Y}
    (hweak : Tendsto (fun k => (P k).map (v k)) atTop (𝓝 ν))
    (f : Y →ᵇ ℝ) (hn : ∀ y, 0≤f y) (hp : 0<∫ y, f y ∂(ν : Measure Y))
    (hps : ∀ k, 0<∫ x, f (v k x) ∂(P k : Measure X)) :
    Tendsto (fun k => (pullbackDensityLaw (P k) (v k) (hv k) f hn (hps k)).map (v k)) atTop
      (𝓝 (normalizedDensityLaw (ν : Measure Y) (f.integrable _) hn hp)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro g
  have hnum := pullback_density_mass_tendsto P v hv hweak (f*g)
  have hden := pullback_density_mass_tendsto P v hv hweak f
  have ht := (hden.inv₀ hp.ne').mul hnum
  simpa only [ProbabilityMeasure.toMeasure_map,
    integral_map (hv _).aemeasurable g.continuous.aestronglyMeasurable,
    pullbackDensityLaw_integral,normalizedDensityLaw_integral _ f.continuous.measurable,
    BoundedContinuousFunction.mul_apply] using ht

end RegularPointCoordinates

end

end OAI
