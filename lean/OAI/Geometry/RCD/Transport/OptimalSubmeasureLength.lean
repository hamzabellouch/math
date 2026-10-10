import OAI.Geometry.RCD.Transport.OptimalLengthLaw

namespace OAI

/-! # Length labels transfer to submeasures through one interior marginal

The common contact set determines geodesic length from any interior
position. Equality of the component marginals at that time therefore
preserves each measurable length class under optimal-plan replacement.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.optimal_submeasure_length_transfer
    (K : ℝ) (n : ℕ) (hn : 2≤n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (hac : ν₀ ≪ hausdorff n X) (p : X) {R : ℝ} (hR : 0≤R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p≤R) (hs1 : ∀ᵐ x ∂ν₁, dist x p≤R)
    (π ρ : Measure C(Time,X)) [IsProbabilityMeasure π] [IsProbabilityMeasure ρ]
    (hgπ : ∀ᵐ γ ∂π, IsGeodesic γ) (hgρ : ∀ᵐ γ ∂ρ, IsGeodesic γ)
    (hpπ : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0,γ 1))))
    (hpρ : IsOptimalCoupling ν₀ ν₁ (ρ.map (fun γ => (γ 0,γ 1))))
    (η ζ : Measure C(Time,X)) (hη : η≤π) (hζ : ζ≤ρ)
    {t : Time} (ht0 : 0<(t:ℝ)) (ht1 : (t:ℝ)<1)
    (he : η.map (fun γ => γ t)=ζ.map (fun γ => γ t))
    {S : Set ℝ} (hS : MeasurableSet S)
    (hηS : ∀ᵐ γ ∂η, dist (γ 0) (γ 1)∈S) :
    ∀ᵐ γ ∂ζ, dist (γ 0) (γ 1)∈S := by
  obtain ⟨L,hL⟩ := hX.common_optimal_length_observable K n hn ν₀ ν₁ hac p hR hs0 hs1
    π hgπ hpπ ht0 ht1
  have hLη : ∀ᵐ γ ∂η, L (γ t)=dist (γ 0) (γ 1) :=
    (hL π inferInstance hgπ hpπ).filter_mono hη.absolutelyContinuous.ae_le
  have hLζ : ∀ᵐ γ ∂ζ, L (γ t)=dist (γ 0) (γ 1) :=
    (hL ρ inferInstance hgρ hpρ).filter_mono hζ.absolutelyContinuous.ae_le
  have heη : ∀ᵐ x ∂η.map (fun γ => γ t), L x∈S := by
    apply (ae_map_iff (measurable_path_eval t).aemeasurable
      (hS.preimage L.continuous.measurable)).mpr
    filter_upwards [hLη,hηS] with γ hγ hγS
    rwa [hγ]
  rw [he] at heη
  have heζ := ae_of_ae_map (measurable_path_eval t).aemeasurable heη
  filter_upwards [hLζ,heζ] with γ hγ hγS
  rwa [←hγ]

end RegularPointCoordinates

end

end OAI
