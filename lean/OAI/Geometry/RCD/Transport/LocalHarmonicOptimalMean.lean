import OAI.Geometry.RCD.Transport.HarmonicOptimalPlanMean
import OAI.Geometry.RCD.Coordinates.LocalPoissonRegularExtension
import OAI.Geometry.RCD.Transport.CompressedFiniteUnique

namespace OAI

/-! # Local harmonic coordinates need no global compact extension hypothesis -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {n : ℕ} (hX : NoncollapsedRCD 0 n X) (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
attribute [local instance] pathBorel pathBorelSpace

include hn in
theorem local_harmonic_mean_on_optimal_plan (a₀ : S) (b₀ : T)
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    {R : ℝ} (hR : 1 ≤ R) (hS : ∀ y:S, dist p y ≤ R) (hT : ∀ y:T, dist p y ≤ R)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hopt : IsOptimalCoupling (μ.map Subtype.val) (ν.map Subtype.val)
      (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • hausdorff n X)
    (u : SobolevSpace (hausdorff n X) hX.quadratic) (V : X → ℝ)
    {b : ℝ} (hb : 50*R < b)
    (hu : SobolevSpace.toLp (hausdorff n X) hX.quadratic u
      =ᵐ[(hausdorff n X).restrict (ball p b)] V)
    (hH : IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p b) u)
    (L : ℝ≥0) (hL : ∀ᵐ x ∂(hausdorff n X).restrict (ball p b),
      localGamma (hausdorff n X) hX.quadratic u u x ≤ (L:ℝ)^2)
    (c : ℝ) (hc : localGamma (hausdorff n X) hX.quadratic u u
      =ᵐ[(hausdorff n X).restrict (ball p b)] fun _ => c) :
    ∀ t : Time, (∫ γ, V (γ t) ∂π) =
      (1-(t:ℝ))*(∫ γ, V (γ 0) ∂π)+(t:ℝ)*(∫ γ, V (γ 1) ∂π) := by
  let m := hausdorff n X
  let q := hX.quadratic
  have h25 : 0 < 25*R := by linarith
  obtain ⟨F,d,hd,hFu,hd0⟩ := hX.local_poisson_regular_extension hn u 0 h25
    (show 2*(25*R)<b by linarith) ((isConstantLaplacianOn_zero_iff m q _ u).mpr hH) L hL
  obtain ⟨U,M,hU,hUc,_hUs,hFU⟩ := F.property.1
  obtain ⟨A,hAb⟩ := hUc.exists_bound_of_continuous hU.continuous
  let A' : ℝ≥0 := ⟨max A 0,le_max_right _ _⟩
  have hA : ∀ᵐ x ∂m, |SobolevSpace.toLp m q F.val x| ≤ A' := by
    filter_upwards [hFU] with x hx
    rw [hx]
    exact (show |U x| ≤ A by simpa only [Real.norm_eq_abs] using hAb x).trans (le_max_left _ _)
  have hsmall : ball p (25*R) ⊆ ball p b := ball_subset_ball (by linarith)
  have hFc : localGamma m q F.val F.val =ᵐ[m.restrict (ball p (25*R))] fun _ => c :=
    (localGamma_pair_congr_ae m q hFu hFu).trans
      (ae_restrict_of_ae_restrict_of_subset hsmall hc)
  have haff := hX.compact_harmonic_mean_on_optimal_plan hn p a₀ b₀
    ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν hR hS hT π hgeo hopt hC hcomp
    F.val d hd U M A' hU hUc hFU hA (show 24*R<25*R by linarith) hd0 c hFc
  have hs₀ : ∀ᵐ x ∂μ.map Subtype.val, dist x p ≤ R := by
    apply (ae_map_iff measurable_subtype_coe.aemeasurable
      (measurableSet_le (by fun_prop) measurable_const)).mpr
    exact Eventually.of_forall fun y => by simpa only [dist_comm] using hS y
  have hs₁ : ∀ᵐ x ∂ν.map Subtype.val, dist x p ≤ R := by
    apply (ae_map_iff measurable_subtype_coe.aemeasurable
      (measurableSet_le (by fun_prop) measurable_const)).mpr
    exact Eventually.of_forall fun y => by simpa only [dist_comm] using hT y
  have hbounded := optimal_geodesic_plan_bounded (μ.map Subtype.val) (ν.map Subtype.val)
    π hgeo hopt p (zero_le_one.trans hR) hs₀ hs₁
  have hUV : U =ᵐ[m.restrict (ball p (25*R))] V :=
    (Filter.EventuallyEq.symm (ae_restrict_of_ae hFU)).trans
      (hFu.trans (ae_restrict_of_ae_restrict_of_subset hsmall hu))
  have hsame (t : Time) : (fun γ => U (γ t)) =ᵐ[π] fun γ => V (γ t) := by
    have he := (Measure.absolutelyContinuous_of_le_smul (hcomp t)).restrict (ball p (25*R)) |>.ae_eq hUV
    change ∀ᵐ x ∂(π.map (fun γ => γ t)).restrict (ball p (25*R)), U x=V x at he
    rw [ae_restrict_iff' measurableSet_ball] at he
    have he' := ae_of_ae_map (measurable_path_eval t).aemeasurable he
    filter_upwards [he',hbounded] with γ heγ hγ
    apply heγ
    rw [mem_ball]
    exact (hγ.2 t).trans_lt (show 3*R<25*R by linarith)
  have hends := optimalPlan_endpoints (μ.map Subtype.val) (ν.map Subtype.val) π hopt
  have he0 : (∫ x:S, U x ∂μ)=∫ γ, U (γ 0) ∂π := by
    rw [← integral_map (measurable_path_eval 0).aemeasurable hU.continuous.aestronglyMeasurable,hends.1]
    exact (integral_map measurable_subtype_coe.aemeasurable hU.continuous.aestronglyMeasurable).symm
  have he1 : (∫ x:T, U x ∂ν)=∫ γ, U (γ 1) ∂π := by
    rw [← integral_map (measurable_path_eval 1).aemeasurable hU.continuous.aestronglyMeasurable,hends.2]
    exact (integral_map measurable_subtype_coe.aemeasurable hU.continuous.aestronglyMeasurable).symm
  intro t
  have hh := haff t
  rw [he0,he1,integral_congr_ae (hsame t),integral_congr_ae (hsame 0),integral_congr_ae (hsame 1)] at hh
  exact hh

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
