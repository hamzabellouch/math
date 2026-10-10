import OAI.Geometry.RCD.Transport.CompressedInitialInverse
import OAI.Geometry.RCD.Metric.InverseMeasureUnique

namespace OAI

/-! # Uniqueness among bounded compressed optimal dynamical plans -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X] {K : ℝ} {n : ℕ}
  [IsLocallyFiniteMeasure (hausdorff n X)] (hX : NoncollapsedRCD K n X)
include hX
attribute [local instance] pathBorel pathBorelSpace

theorem compressed_plan_unique (hn : 2 ≤ n) (p : X) {R : ℝ} (hR : 0 ≤ R)
    {ν₀ ν₁ : Measure X}
    (π ρ : Measure C(Time,X)) [IsProbabilityMeasure π] [IsProbabilityMeasure ρ]
    (hgπ : ∀ᵐ γ ∂π, IsGeodesic γ) (hgρ : ∀ᵐ γ ∂ρ, IsGeodesic γ)
    (hpπ : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0,γ 1))))
    (hpρ : IsOptimalCoupling ν₀ ν₁ (ρ.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0} (hC : 0 < C)
    (hcπ : ∀ t : Time, π.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X)
    (hcρ : ∀ t : Time, ρ.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X)
    (hs₀ : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs₁ : ∀ᵐ x ∂ν₁, dist x p ≤ R) : π=ρ := by
  let ξ := (2:ℝ≥0∞)⁻¹ • (π+ρ)
  obtain ⟨hprob,hgξ,hpξ,hπξ,hρξ⟩ := half_mixture_plan_data π ρ hgπ hgρ hpπ hpρ
  let : IsProbabilityMeasure ξ := hprob
  have heπ := optimalPlan_endpoints ν₀ ν₁ π hpπ
  have heρ := optimalPlan_endpoints ν₀ ν₁ ρ hpρ
  have heξ := optimalPlan_endpoints ν₀ ν₁ ξ hpξ
  have hcξ := half_mixture_compression (hausdorff n X) π ρ hcπ hcρ
  have hpξ' : IsOptimalCoupling (ξ.map (fun γ => γ 0)) (ξ.map (fun γ => γ 1))
      (ξ.map (fun γ => (γ 0,γ 1))) := by rwa [heξ.1,heξ.2]
  obtain ⟨g,hg,hgi⟩ := hX.compressed_initial_inverse hn p hR ξ hgξ hpξ' hC hcξ
    (by rwa [heξ.1]) (by rwa [heξ.2])
  have hhalf : (2:ℝ≥0∞)⁻¹ ≠ 0 := by norm_num
  exact measure_eq_of_common_ae_inverse ξ π ρ (measurable_path_eval 0) hg hgi
    ((Measure.absolutelyContinuous_smul hhalf).trans hπξ.absolutelyContinuous)
    ((Measure.absolutelyContinuous_smul hhalf).trans hρξ.absolutelyContinuous)
    (heπ.1.trans heρ.1.symm)

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
