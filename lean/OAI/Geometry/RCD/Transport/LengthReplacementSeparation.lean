import OAI.Geometry.RCD.Transport.OptimalComponentSeparation

namespace OAI

/-! # Length-preserving replacements remain separated from untouched mass

Fixing one interior component marginal preserves its length class. Every
other interior marginal of that replacement is therefore singular to the
untouched complementary component. This supplies the geometric premise
of the proved Rényi subplan comparison.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.length_replacement_separated
    (K : ℝ) (n : ℕ) (hn : 2≤n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (hac : ν₀ ≪ hausdorff n X) (p : X) {R : ℝ} (hR : 0≤R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p≤R) (hs1 : ∀ᵐ x ∂ν₁, dist x p≤R)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hgπ : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hpπ : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0,γ 1))))
    {S : Set ℝ} (hS : MeasurableSet S)
    (κ τ : Measure C(Time,X)) (hκeq : κ=π.restrict {γ | dist (γ 0) (γ 1)∈S})
    (ht : IsOptimalCoupling (κ.map (fun γ => γ 0)) (κ.map (fun γ => γ 1))
      (τ.map (fun γ => (γ 0,γ 1)))) (hgt : ∀ᵐ γ ∂τ, IsGeodesic γ)
    {t u : Time} (ht0 : 0<(t:ℝ)) (ht1 : (t:ℝ)<1)
    (he : κ.map (fun γ => γ t)=τ.map (fun γ => γ t))
    (hu0 : 0<(u:ℝ)) (hu1 : (u:ℝ)<1) :
    (π-κ).map (fun γ => γ u) ⟂ₘ τ.map (fun γ => γ u) := by
  let : SeparableSpace X := hX.separable
  have hA : MeasurableSet {γ : C(Time,X) | dist (γ 0) (γ 1)∈S} :=
    hS.preimage ((measurable_path_eval 0).dist (measurable_path_eval 1))
  have hκ : κ≤π := by rw [hκeq]; exact Measure.restrict_le_self
  let : IsFiniteMeasure κ := isFiniteMeasure_of_le π hκ
  obtain ⟨hρ,hgρ,hpρ⟩ := optimalPlan_replace_subplan hpπ hgπ hκ ht hgt
  let ρ := π-κ+τ
  let : IsProbabilityMeasure ρ := hρ
  have hτ : τ≤ρ := Measure.le_add_left le_rfl
  have hκS : ∀ᵐ γ ∂κ, dist (γ 0) (γ 1)∈S := by
    rw [hκeq]
    exact ae_restrict_mem hA
  have hτS := hX.optimal_submeasure_length_transfer K n hn ν₀ ν₁ hac p hR hs0 hs1
    π ρ hgπ hgρ hpπ hpρ κ τ hκ hτ ht0 ht1 he hS hκS
  have hresid : ∀ᵐ γ ∂π-κ, dist (γ 0) (γ 1)∉S := by
    apply ae_iff.mpr
    simp only [not_not]
    rw [Measure.sub_apply hA hκ,hκeq,Measure.restrict_apply hA,inter_self,tsub_self]
  exact (hX.optimal_components_mutuallySingular K n hn ν₀ ν₁ hac p hR hs0 hs1
    ρ π hgρ hgπ hpρ hpπ τ (π-κ) hτ Measure.sub_le hu0 hu1 hS hτS hresid).symm

end RegularPointCoordinates

end

end OAI
