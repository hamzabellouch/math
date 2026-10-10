import OAI.Geometry.RCD.Transport.OptimalCommonContactSet
import Mathlib.Topology.TietzeExtension

namespace OAI

/-! # The length of an optimal geodesic is visible at every interior time

On the common compact contact set, length is constant on evaluation fibers.
The quotient map and Tietze extension give one continuous spatial observable
for every optimal plan with the prescribed endpoints. This retains variable
length weights when segments of the plan are replaced.
-/

open Set Filter MeasureTheory Metric TopologicalSpace Topology
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

omit [MeasurableSpace X] [BorelSpace X] in
theorem compact_length_observable {E : Set C(Time,X)} (hE : IsCompact E)
    {t : Time} (hfib : ∀ γ∈E, ∀ ζ∈E, γ t=ζ t →
      dist (γ 0) (γ 1)=dist (ζ 0) (ζ 1)) :
    ∃ L : C(X,ℝ), ∀ γ∈E, L (γ t)=dist (γ 0) (γ 1) := by
  let A := (fun γ : C(Time,X) => γ t) '' E
  let e : C(E,A) := ⟨fun γ => ⟨γ.val t,⟨γ.val,γ.property,rfl⟩⟩,
    ((continuous_eval_const t).comp continuous_subtype_val).subtype_mk _⟩
  let l : C(E,ℝ) := ⟨fun γ => dist (γ.val 0) (γ.val 1),
    ((continuous_eval_const 0).comp continuous_subtype_val).dist
      ((continuous_eval_const 1).comp continuous_subtype_val)⟩
  let : CompactSpace E := isCompact_iff_compactSpace.mp hE
  have he : Function.Surjective e := by
    rintro ⟨x,γ,hγ,rfl⟩
    exact ⟨⟨γ,hγ⟩,rfl⟩
  have hq : IsQuotientMap e := IsQuotientMap.of_surjective_continuous he e.continuous
  have hl : Function.FactorsThrough l e := by
    intro γ ζ heq
    exact hfib γ γ.property ζ ζ.property (congrArg Subtype.val heq)
  let lA := hq.lift l hl
  have hA : IsCompact A := hE.image (continuous_eval_const t)
  obtain ⟨L,hL⟩ := ContinuousMap.exists_restrict_eq hA.isClosed lA
  refine ⟨L,?_⟩
  intro γ hγ
  have h1 := congrArg (fun f : C(A,ℝ) => f (e ⟨γ,hγ⟩)) hL
  have h2 := congrArg (fun f : C(E,ℝ) => f ⟨γ,hγ⟩) (hq.lift_comp l hl)
  exact h1.trans h2

theorem NoncollapsedRCD.common_optimal_length_observable
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (hac : ν₀ ≪ hausdorff n X) (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0,γ 1))))
    {t : Time} (ht0 : 0 < (t:ℝ)) (ht1 : (t:ℝ) < 1) :
    ∃ L : C(X,ℝ), ∀ σ : Measure C(Time,X), IsProbabilityMeasure σ →
      (∀ᵐ γ ∂σ, IsGeodesic γ) →
      IsOptimalCoupling ν₀ ν₁ (σ.map (fun γ => (γ 0,γ 1))) →
      ∀ᵐ γ ∂σ, L (γ t)=dist (γ 0) (γ 1) := by
  obtain ⟨E,hE,hfull,hfib⟩ := hX.common_optimal_length_set K n hn ν₀ ν₁ hac p hR
    hs0 hs1 π hg hp
  obtain ⟨L,hL⟩ := compact_length_observable hE
    (fun γ hγ ζ hζ => hfib γ hγ ζ hζ t ht0 ht1)
  exact ⟨L,fun σ hσ hgσ hpσ => (hfull σ hσ hgσ hpσ).mono (fun γ hγ => hL γ hγ)⟩

end RegularPointCoordinates

end

end OAI
