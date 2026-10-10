import OAI.Geometry.RCD.Transport.MeetingPairCollapse
import OAI.Geometry.RCD.Heat.ConditionalPairInverse

namespace OAI

/-! # Measurable inversion of interior evaluation for the actual compressed plan -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X] {K : ℝ} {n : ℕ}
  [IsLocallyFiniteMeasure (hausdorff n X)] (hX : NoncollapsedRCD K n X)
include hX
attribute [local instance] pathBorel pathBorelSpace

theorem compressed_evaluation_inverse (hn : 2 ≤ n) (p : X) {R : ℝ} (hR : 0 ≤ R)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π] (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0} (hC : 0 < C)
    (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X)
    (hs₀ : ∀ᵐ x ∂π.map (fun γ => γ 0), dist x p ≤ R)
    (hs₁ : ∀ᵐ x ∂π.map (fun γ => γ 1), dist x p ≤ R)
    (t : Time) (ht0 : 0 < (t:ℝ)) (ht1 : (t:ℝ) < 1) :
    ∃ g : X → C(Time,X), Measurable g ∧ ∀ᵐ γ ∂π, g (γ t)=γ := by
  let : CompleteSpace X := hX.complete
  let : Nonempty C(Time,X) := nonempty_of_isProbabilityMeasure π
  have hac := Measure.absolutelyContinuous_of_le_smul (hc 0)
  obtain ⟨u,φ,ψ,L,hφ,hψ,_,_,_,had,hcontact,_⟩ := hp.bounded_sobolev_potential
    (hausdorff n X) hX.quadratic hX.geodesic _ _ hac p hR hs₀ hs₁
  have hct : ∀ᵐ γ ∂π, φ (γ 0)+ψ (γ 1)=dist (γ 0) (γ 1)^2/2 :=
    ae_of_ae_map ((measurable_path_eval 0).prodMk (measurable_path_eval 1)).aemeasurable hcontact
  let σ := conditionalSelfPair π (fun γ => γ t) (measurable_path_eval t)
  obtain ⟨hσ₀,hσ₁⟩ := conditionalSelfPair_marginals π (fun γ => γ t) (measurable_path_eval t)
  let : IsProbabilityMeasure σ := ⟨by
    have h := congrArg (fun m : Measure C(Time,X) => m univ) hσ₀
    simpa only [Measure.map_apply measurable_fst MeasurableSet.univ,preimage_univ,measure_univ] using h⟩
  have hmeet : ∀ᵐ z ∂σ, z.1 t=z.2 t :=
    conditionalSelfPair_common π (fun γ => γ t) (measurable_path_eval t)
  have hdiag := hX.contacting_pair_collapse hn p hR π hg hp hC hc hs₀ hs₁
    hφ.continuous.measurable hψ.continuous.measurable had hct σ hσ₀ hσ₁ t ht0 ht1 hmeet
  exact measurable_inverse_of_conditional_diagonal π (fun γ => γ t) (measurable_path_eval t) hdiag

theorem compressed_evaluation_injective (hn : 2 ≤ n) (p : X) {R : ℝ} (hR : 0 ≤ R)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π] (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0} (hC : 0 < C)
    (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X)
    (hs₀ : ∀ᵐ x ∂π.map (fun γ => γ 0), dist x p ≤ R)
    (hs₁ : ∀ᵐ x ∂π.map (fun γ => γ 1), dist x p ≤ R)
    (t : Time) (ht0 : 0 < (t:ℝ)) (ht1 : (t:ℝ) < 1) :
    ∃ S : Set C(Time,X), MeasurableSet S ∧ (∀ᵐ γ ∂π, γ ∈ S) ∧ InjOn (fun γ => γ t) S := by
  obtain ⟨g,hg,hgπ⟩ := hX.compressed_evaluation_inverse hn p hR π hg hp hC hc hs₀ hs₁ t ht0 ht1
  refine ⟨{γ | g (γ t)=γ},measurableSet_eq_fun (hg.comp (measurable_path_eval t)) measurable_id,hgπ,?_⟩
  intro γ hγ ζ hζ he
  exact hγ.symm.trans ((congrArg g he).trans hζ)

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
