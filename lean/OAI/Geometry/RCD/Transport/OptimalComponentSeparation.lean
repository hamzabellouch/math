import OAI.Geometry.RCD.Transport.OptimalSubmeasureLength

namespace OAI

/-! # Spatial separation of arbitrary length-labelled subcomponents -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem length_labelled_marginals_mutuallySingular
    (η ζ : Measure C(Time,X)) (t : Time) (L : C(X,ℝ))
    (hLη : ∀ᵐ γ ∂η, L (γ t)=dist (γ 0) (γ 1))
    (hLζ : ∀ᵐ γ ∂ζ, L (γ t)=dist (γ 0) (γ 1))
    {S : Set ℝ} (hS : MeasurableSet S)
    (hη : ∀ᵐ γ ∂η, dist (γ 0) (γ 1)∈S)
    (hζ : ∀ᵐ γ ∂ζ, dist (γ 0) (γ 1)∉S) :
    η.map (fun γ => γ t) ⟂ₘ ζ.map (fun γ => γ t) := by
  have hη' : ∀ᵐ x ∂η.map (fun γ => γ t), x∈L ⁻¹' S := by
    apply (ae_map_iff (measurable_path_eval t).aemeasurable
      (hS.preimage L.continuous.measurable)).mpr
    filter_upwards [hLη,hη] with γ hγ hγS
    change L (γ t)∈S
    rwa [hγ]
  have hζ' : ∀ᵐ x ∂ζ.map (fun γ => γ t), x∉L ⁻¹' S := by
    apply (ae_map_iff (measurable_path_eval t).aemeasurable
      (hS.preimage L.continuous.measurable).compl).mpr
    filter_upwards [hLζ,hζ] with γ hγ hγS
    change L (γ t)∉S
    rwa [hγ]
  refine ⟨(L ⁻¹' S)ᶜ,(hS.preimage L.continuous.measurable).compl,?_,?_⟩
  · exact ae_iff.mp hη'
  · rw [compl_compl]
    simpa only [not_not,Set.ofPred_mem_eq] using ae_iff.mp hζ'

theorem NoncollapsedRCD.optimal_components_mutuallySingular
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
    {S : Set ℝ} (hS : MeasurableSet S)
    (hηS : ∀ᵐ γ ∂η, dist (γ 0) (γ 1)∈S)
    (hζS : ∀ᵐ γ ∂ζ, dist (γ 0) (γ 1)∉S) :
    η.map (fun γ => γ t) ⟂ₘ ζ.map (fun γ => γ t) := by
  obtain ⟨L,hL⟩ := hX.common_optimal_length_observable K n hn ν₀ ν₁ hac p hR hs0 hs1
    π hgπ hpπ ht0 ht1
  exact length_labelled_marginals_mutuallySingular η ζ t L
    ((hL π inferInstance hgπ hpπ).filter_mono hη.absolutelyContinuous.ae_le)
    ((hL ρ inferInstance hgρ hpρ).filter_mono hζ.absolutelyContinuous.ae_le) hS hηS hζS

end RegularPointCoordinates

end

end OAI
