import OAI.Geometry.RCD.Transport.OptimalLengthLocalization

namespace OAI

/-! # One contact set for all optimal plans with fixed endpoints

The same optimal dual pair contacts every optimal coupling. Consequently
the compact set used for length localization can be fixed before replacing
or refining any segment of a plan.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem optimalPlan_contact_transfer [SeparableSpace X] {ν₀ ν₁ : Measure X}
    {π σ : Measure C(Time,X)} [IsProbabilityMeasure π] [IsProbabilityMeasure σ]
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0,γ 1))))
    (hs : IsOptimalCoupling ν₀ ν₁ (σ.map (fun γ => (γ 0,γ 1))))
    (hdiπ : Integrable (fun γ : C(Time,X) => dist (γ 0) (γ 1)^2) π)
    (hdiσ : Integrable (fun γ : C(Time,X) => dist (γ 0) (γ 1)^2) σ)
    {φ ψ : X → ℝ} (hφ : Integrable φ ν₀) (hψ : Integrable ψ ν₁)
    (had : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    (hcontact : ∀ᵐ γ ∂π, φ (γ 0)+ψ (γ 1)=dist (γ 0) (γ 1)^2/2) :
    ∀ᵐ γ ∂σ, φ (γ 0)+ψ (γ 1)=dist (γ 0) (γ 1)^2/2 := by
  have he := optimalPlan_endpoints ν₀ ν₁ σ hs
  have hiφ : Integrable (fun γ : C(Time,X) => φ (γ 0)) σ :=
    Integrable.comp_measurable (he.1.symm ▸ hφ) (measurable_path_eval 0)
  have hiψ : Integrable (fun γ : C(Time,X) => ψ (γ 1)) σ :=
    Integrable.comp_measurable (he.2.symm ▸ hψ) (measurable_path_eval 1)
  have hsum : Integrable (fun γ : C(Time,X) => φ (γ 0)+ψ (γ 1)) σ := hiφ.add hiψ
  have hid := (hdiσ.div_const 2).sub hsum
  have hnonneg : ∀ γ : C(Time,X), 0 ≤ dist (γ 0) (γ 1)^2/2-(φ (γ 0)+ψ (γ 1)) :=
    fun γ => sub_nonneg.mpr (had (γ 0) (γ 1))
  have hcost := optimal_plan_cost_real hs hdiσ
  have hdual := optimal_plan_dual_eq hp hdiπ hφ hψ hcontact
  have hint : (∫ γ, dist (γ 0) (γ 1)^2/2-(φ (γ 0)+ψ (γ 1)) ∂σ)=0 := by
    rw [integral_sub (hdiσ.div_const 2) hsum,integral_add hiφ hiψ,integral_div]
    rw [←integral_map (measurable_path_eval 0).aemeasurable
        (he.1.symm ▸ hφ.aestronglyMeasurable),
      ←integral_map (measurable_path_eval 1).aemeasurable
        (he.2.symm ▸ hψ.aestronglyMeasurable),he.1,he.2]
    rw [hdual,←hcost,sub_self]
  have hz := (integral_eq_zero_iff_of_nonneg hnonneg hid).mp hint
  filter_upwards [hz] with γ hγ
  exact (sub_eq_zero.mp hγ).symm

theorem NoncollapsedRCD.common_optimal_length_set
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (hac : ν₀ ≪ hausdorff n X) (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π] (_hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0,γ 1)))) :
    ∃ E : Set C(Time,X), IsCompact E ∧
      (∀ σ : Measure C(Time,X), IsProbabilityMeasure σ →
        (∀ᵐ γ ∂σ, IsGeodesic γ) → IsOptimalCoupling ν₀ ν₁ (σ.map (fun γ => (γ 0,γ 1))) →
        ∀ᵐ γ ∂σ, γ∈E) ∧
      ∀ γ∈E, ∀ ζ∈E, ∀ t : Time, 0 < (t:ℝ) → (t:ℝ) < 1 → γ t=ζ t →
        dist (γ 0) (γ 1)=dist (ζ 0) (ζ 1) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  obtain ⟨u,φ,ψ,L,hφ,hψ,hsφ,hsψ,_,had,hcontact,_⟩ := hp.bounded_sobolev_potential
    μ hX.quadratic hX.geodesic ν₀ ν₁ hac p hR hs0 hs1
  have hcae : ∀ᵐ γ ∂π, φ (γ 0)+ψ (γ 1)=dist (γ 0) (γ 1)^2/2 :=
    ae_of_ae_map ((measurable_path_eval 0).prodMk (measurable_path_eval 1)).aemeasurable hcontact
  have hip := optimalPlan_dist_sq_integrable ν₀ ν₁ π hp p
    (integrable_dist_sq_of_ae_bounded ν₀ p hs0) (integrable_dist_sq_of_ae_bounded ν₁ p hs1)
  let G := {γ : C(Time,X) | IsGeodesic γ ∧ ∀ t, dist (γ t) p ≤ 3*R}
  let F := {γ : C(Time,X) | φ (γ 0)+ψ (γ 1)=dist (γ 0) (γ 1)^2/2}
  have hG : IsCompact G := isCompact_bounded_geodesics p (by positivity)
  have hF : IsClosed F := isClosed_eq
    ((hφ.continuous.comp (continuous_eval_const 0)).add
      (hψ.continuous.comp (continuous_eval_const 1)))
    ((((continuous_eval_const 0).dist (continuous_eval_const 1)).pow 2).div_const 2)
  refine ⟨G∩F,hG.inter_right hF,?_,?_⟩
  · intro σ hσ hgeo hopt
    let := hσ
    have his := optimalPlan_dist_sq_integrable ν₀ ν₁ σ hopt p
      (integrable_dist_sq_of_ae_bounded ν₀ p hs0) (integrable_dist_sq_of_ae_bounded ν₁ p hs1)
    have hscontact := optimalPlan_contact_transfer hp hopt hip his
      (hφ.continuous.integrable_of_hasCompactSupport hsφ)
      (hψ.continuous.integrable_of_hasCompactSupport hsψ) had hcae
    exact (optimal_geodesic_plan_bounded ν₀ ν₁ σ hgeo hopt p hR hs0 hs1).and hscontact
  · intro γ hγ ζ hζ t ht0 ht1 hm
    exact contacting_geodesics_equal_length had hγ.1.1 hζ.1.1 hγ.2 hζ.2 ht0 ht1 hm

end RegularPointCoordinates

end

end OAI
