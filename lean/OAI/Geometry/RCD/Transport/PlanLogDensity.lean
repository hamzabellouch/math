import OAI.Geometry.RCD.Metric.LogInverseDensity
import OAI.Geometry.RCD.Transport.BoundedPlanEntropyBounds

namespace OAI

/-! # Logarithmic density identities along the actual bounded transport law -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem bounded_plan_log_density (μ : Measure X) [SigmaFinite μ] [IsLocallyFiniteMeasure μ]
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π] (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ} (hC : 0 < C) (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ ENNReal.ofReal C • μ)
    (hs₀ : ∀ᵐ x ∂π.map (fun γ => γ 0), dist x p ≤ R)
    (hs₁ : ∀ᵐ x ∂π.map (fun γ => γ 1), dist x p ≤ R) (N : ℝ) (t : Time) :
    Integrable (fun γ => Real.log (((π.map (fun γ => γ t)).rnDeriv μ (γ t))^(-(1/N))).toReal) π ∧
      (∫ γ, Real.log (((π.map (fun γ => γ t)).rnDeriv μ (γ t))^(-(1/N))).toReal ∂π)=
        -(boltzmannEntropy μ (π.map (fun γ => γ t)))/N := by
  have he := (bounded_plan_entropy_bounds μ p hR π hg hp hC hc hs₀ hs₁ t).2.2
  have hl := log_inverse_density_integral μ (π.map (fun γ => γ t))
    (Measure.absolutelyContinuous_of_le_smul (hc t)) he N
  refine ⟨hl.1.comp_measurable (measurable_path_eval t),?_⟩
  rw [←integral_map (measurable_path_eval t).aemeasurable
    ((((π.map (fun γ => γ t)).measurable_rnDeriv μ).pow_const _).ennreal_toReal.log).aestronglyMeasurable]
  exact hl.2

end RegularPointCoordinates

end

end OAI
