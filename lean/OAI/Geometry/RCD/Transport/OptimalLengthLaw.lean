import OAI.Geometry.RCD.Transport.OptimalLengthObservable

namespace OAI

/-! # Length labels survive optimal-plan replacement

An interior marginal fixes the joint law of position and total geodesic
length. Consequently every measurable length restriction has the same
interior marginal before and after replacement.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem eval_length_law (π : Measure C(Time,X)) (t : Time) (L : C(X,ℝ))
    (hL : ∀ᵐ γ ∂π, L (γ t)=dist (γ 0) (γ 1)) :
    π.map (fun γ => (γ t,dist (γ 0) (γ 1))) =
      (π.map (fun γ => γ t)).map (fun x => (x,L x)) := by
  have he : π.map (fun γ => (γ t,dist (γ 0) (γ 1))) =
      π.map ((fun x : X => (x,L x)) ∘ (fun γ : C(Time,X) => γ t)) :=
    Measure.map_congr (hL.mono (fun γ hγ => Prod.ext rfl hγ.symm))
  exact he.trans (Measure.map_map
    (show Measurable (fun x : X => (x,L x)) from measurable_id.prodMk L.continuous.measurable)
    (measurable_path_eval t)).symm

theorem length_restriction_eval (π : Measure C(Time,X)) (t : Time) (L : C(X,ℝ))
    (hL : ∀ᵐ γ ∂π, L (γ t)=dist (γ 0) (γ 1))
    {S : Set ℝ} (hS : MeasurableSet S) :
    (π.restrict {γ | dist (γ 0) (γ 1)∈S}).map (fun γ => γ t) =
      (π.map (fun γ => γ t)).restrict (L ⁻¹' S) := by
  rw [Measure.restrict_map (measurable_path_eval t) (hS.preimage L.continuous.measurable)]
  apply congrArg (fun m : Measure C(Time,X) => m.map (fun γ => γ t))
  apply Measure.restrict_congr_set
  filter_upwards [hL] with γ hγ
  exact propext (by change dist (γ 0) (γ 1)∈S ↔ L (γ t)∈S; rw [hγ])

theorem NoncollapsedRCD.optimal_eval_length_law_eq
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (hac : ν₀ ≪ hausdorff n X) (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (π σ : Measure C(Time,X)) [IsProbabilityMeasure π] [IsProbabilityMeasure σ]
    (hgπ : ∀ᵐ γ ∂π, IsGeodesic γ) (hgσ : ∀ᵐ γ ∂σ, IsGeodesic γ)
    (hpπ : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0,γ 1))))
    (hpσ : IsOptimalCoupling ν₀ ν₁ (σ.map (fun γ => (γ 0,γ 1))))
    {t : Time} (ht0 : 0 < (t:ℝ)) (ht1 : (t:ℝ) < 1)
    (heq : π.map (fun γ => γ t)=σ.map (fun γ => γ t)) :
    π.map (fun γ => (γ t,dist (γ 0) (γ 1))) =
      σ.map (fun γ => (γ t,dist (γ 0) (γ 1))) := by
  obtain ⟨L,hL⟩ := hX.common_optimal_length_observable K n hn ν₀ ν₁ hac p hR hs0 hs1
    π hgπ hpπ ht0 ht1
  rw [eval_length_law π t L (hL π inferInstance hgπ hpπ),
    eval_length_law σ t L (hL σ inferInstance hgσ hpσ),heq]

theorem NoncollapsedRCD.optimal_length_restriction_eval_eq
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (hac : ν₀ ≪ hausdorff n X) (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (π σ : Measure C(Time,X)) [IsProbabilityMeasure π] [IsProbabilityMeasure σ]
    (hgπ : ∀ᵐ γ ∂π, IsGeodesic γ) (hgσ : ∀ᵐ γ ∂σ, IsGeodesic γ)
    (hpπ : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0,γ 1))))
    (hpσ : IsOptimalCoupling ν₀ ν₁ (σ.map (fun γ => (γ 0,γ 1))))
    {t : Time} (ht0 : 0 < (t:ℝ)) (ht1 : (t:ℝ) < 1)
    (heq : π.map (fun γ => γ t)=σ.map (fun γ => γ t))
    {S : Set ℝ} (hS : MeasurableSet S) :
    (π.restrict {γ | dist (γ 0) (γ 1)∈S}).map (fun γ => γ t) =
      (σ.restrict {γ | dist (γ 0) (γ 1)∈S}).map (fun γ => γ t) := by
  obtain ⟨L,hL⟩ := hX.common_optimal_length_observable K n hn ν₀ ν₁ hac p hR hs0 hs1
    π hgπ hpπ ht0 ht1
  rw [length_restriction_eval π t L (hL π inferInstance hgπ hpπ) hS,
    length_restriction_eval σ t L (hL σ inferInstance hgσ hpσ) hS,heq]

end RegularPointCoordinates

end

end OAI
