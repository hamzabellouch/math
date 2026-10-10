import OAI.Geometry.RCD.Transport.CompressedSubplanNode

namespace OAI

/-! # The actual normalized subplan with its common compression and support -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem normalized_subplan_data (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    (hfin : transportCost (π.map (fun γ => (γ 0,γ 1))) ≠ ∞)
    (μ : Measure X) {C : ℝ≥0∞} (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (p : X) {R : ℝ}
    (hs₀ : ∀ᵐ x ∂π.map (fun γ => γ 0), dist x p ≤ R)
    (hs₁ : ∀ᵐ x ∂π.map (fun γ => γ 1), dist x p ≤ R)
    (κ : Measure C(Time,X)) (hk : κ ≤ π) (hk0 : κ univ ≠ 0) :
    let ρ := (κ univ)⁻¹ • κ
    IsProbabilityMeasure ρ ∧ (∀ᵐ γ ∂ρ, IsGeodesic γ) ∧
      IsOptimalCoupling (ρ.map (fun γ => γ 0)) (ρ.map (fun γ => γ 1))
        (ρ.map (fun γ => (γ 0,γ 1))) ∧
      (∀ t : Time, ρ.map (fun γ => γ t) ≤ ((κ univ)⁻¹*C) • μ) ∧
      (∀ᵐ x ∂ρ.map (fun γ => γ 0), dist x p ≤ R) ∧
      (∀ᵐ x ∂ρ.map (fun γ => γ 1), dist x p ≤ R) := by
  obtain ⟨hρ,hgρ,hpρ,_⟩ := normalized_optimal_subplan π hg hp hfin κ hk hk0
  refine ⟨hρ,hgρ,hpρ,normalized_subplan_compression π κ hk hc,?_,?_⟩
  · rw [Measure.map_smul _ (measurable_path_eval 0).aemeasurable]
    exact (hs₀.filter_mono (Measure.map_mono hk (measurable_path_eval 0)).absolutelyContinuous.ae_le).filter_mono
      Measure.smul_absolutelyContinuous.ae_le
  · rw [Measure.map_smul _ (measurable_path_eval 1).aemeasurable]
    exact (hs₁.filter_mono (Measure.map_mono hk (measurable_path_eval 1)).absolutelyContinuous.ae_le).filter_mono
      Measure.smul_absolutelyContinuous.ae_le

end RegularPointCoordinates

end

end OAI
