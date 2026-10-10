import OAI.Geometry.RCD.Transport.OptimalGeodesicLengths

namespace OAI

/-! # Spatial localization of length-truncated optimal plans

Each length threshold is detected by a compact set at any interior time.
Consequently the two length-truncated marginals are mutually singular.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem length_sublevel_evaluation (π : Measure C(Time,X))
    {E : Set C(Time,X)} (hE : IsCompact E) (hfull : ∀ᵐ γ ∂π, γ∈E)
    {t : Time} (hfib : ∀ γ∈E, ∀ ζ∈E, γ t=ζ t →
      dist (γ 0) (γ 1)=dist (ζ 0) (ζ 1)) (C : ℝ) :
    ∃ A : Set X, IsCompact A ∧
      (π.restrict {γ | dist (γ 0) (γ 1) ≤ C}).map (fun γ => γ t) =
        (π.map (fun γ => γ t)).restrict A ∧
      (π.restrict {γ | C < dist (γ 0) (γ 1)}).map (fun γ => γ t) =
        (π.map (fun γ => γ t)).restrict Aᶜ := by
  let L := {γ : C(Time,X) | dist (γ 0) (γ 1) ≤ C}
  have hL : IsClosed L := isClosed_le ((continuous_eval_const 0).dist
    (continuous_eval_const 1)) continuous_const
  let A := (fun γ => γ t) '' (E∩L)
  have hA : IsCompact A := (hE.inter_right hL).image (continuous_eval_const t)
  have he (γ : C(Time,X)) (hγ : γ∈E) : γ t∈A ↔ γ∈L := by
    constructor
    · rintro ⟨ζ,⟨hζ,hζL⟩,heq⟩
      change dist (γ 0) (γ 1) ≤ C
      rw [hfib γ hγ ζ hζ heq.symm]
      exact hζL
    · intro hγL
      exact ⟨γ,⟨hγ,hγL⟩,rfl⟩
  have hlow : L =ᵐ[π] (fun γ => γ t) ⁻¹' A := by
    filter_upwards [hfull] with γ hγ
    exact propext (he γ hγ).symm
  have hhigh : {γ : C(Time,X) | C < dist (γ 0) (γ 1)} =ᵐ[π]
      (fun γ => γ t) ⁻¹' Aᶜ := by
    filter_upwards [hfull] with γ hγ
    apply propext
    change C < dist (γ 0) (γ 1) ↔ ¬γ t∈A
    rw [he γ hγ]
    exact lt_iff_not_ge
  refine ⟨A,hA,?_,?_⟩
  · rw [Measure.restrict_map (measurable_path_eval t) hA.measurableSet]
    exact congrArg (fun m : Measure C(Time,X) => m.map (fun γ => γ t))
      (Measure.restrict_congr_set hlow)
  · rw [Measure.restrict_map (measurable_path_eval t) hA.measurableSet.compl]
    exact congrArg (fun m : Measure C(Time,X) => m.map (fun γ => γ t))
      (Measure.restrict_congr_set hhigh)

theorem NoncollapsedRCD.optimal_length_marginals_mutuallySingular
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (hac : ν₀ ≪ hausdorff n X) (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (π : Measure C(Time,X)) (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0,γ 1))))
    {t : Time} (ht0 : 0 < (t:ℝ)) (ht1 : (t:ℝ) < 1) (C : ℝ) :
    ((π.restrict {γ | dist (γ 0) (γ 1) ≤ C}).map (fun γ => γ t)) ⟂ₘ
      ((π.restrict {γ | C < dist (γ 0) (γ 1)}).map (fun γ => γ t)) := by
  obtain ⟨E,hE,hfull,hfib⟩ := hX.optimal_length_fibers K n hn ν₀ ν₁ hac p hR hs0 hs1 π hg hp
  obtain ⟨A,hA,hlo,hhi⟩ := length_sublevel_evaluation π hE hfull
    (fun γ hγ ζ hζ => hfib γ hγ ζ hζ t ht0 ht1) C
  rw [hlo,hhi]
  refine ⟨Aᶜ,hA.measurableSet.compl,?_,?_⟩
  · rw [Measure.restrict_apply hA.measurableSet.compl]
    simp
  · rw [Measure.restrict_apply hA.measurableSet.compl.compl]
    simp

end RegularPointCoordinates

end

end OAI
