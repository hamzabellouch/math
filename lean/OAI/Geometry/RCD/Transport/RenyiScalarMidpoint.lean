import OAI.Geometry.RCD.Transport.RenyiTreeMaximality
import OAI.Geometry.RCD.Transport.RenyiInverseDensity

namespace OAI

/-! # The scalar reduced-CD bound at each selected midpoint

The original FullCD witness and the selected midpoint may have different
couplings. The uniform length bound removes the coupling dependence in
this scalar estimate. No equality of the two plans is assumed.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

omit [BorelSpace X] in
theorem RenyiMaximizingPlan.renyiIntegral_le_of_integrable
    (μ : Measure X) [SigmaFinite μ] {ν₀ ν₁ : Measure X}
    {π κ : Measure C(Time,X)} [IsProbabilityMeasure π] [IsProbabilityMeasure κ]
    {t : Time} {N : ℝ} (hN : 1 < N)
    (hmax : RenyiMaximizingPlan μ ν₀ ν₁ π t (1-1/N))
    (hgκ : ∀ᵐ γ ∂κ, IsGeodesic γ)
    (hpκ : IsOptimalCoupling ν₀ ν₁ (κ.map (fun γ => (γ 0,γ 1))))
    (hiπ : Integrable (fun x => ((π.map (fun γ => γ t)).rnDeriv μ x).toReal^(1-1/N)) μ)
    (hiκ : Integrable (fun x => ((κ.map (fun γ => γ t)).rnDeriv μ x).toReal^(1-1/N)) μ) :
    renyiIntegral μ (κ.map (fun γ => γ t)) N ≤ renyiIntegral μ (π.map (fun γ => γ t)) N := by
  have hq : 0 ≤ 1-1/N := sub_nonneg.mpr ((div_le_one (by linarith : 0<N)).mpr hN.le)
  rw [renyiIntegral,renyiIntegral,rnDeriv_power_lintegral_eq_of_integrable μ _ hq hiκ,
    rnDeriv_power_lintegral_eq_of_integrable μ _ hq hiπ]
  exact ENNReal.ofReal_le_ofReal (hmax κ inferInstance hgκ hpκ)

theorem NoncollapsedRCD.renyiNode_scalar_midpoint
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X) (hK : K ≤ 0)
    {N : ℝ} (hN : (n:ℝ) ≤ N) (a : RenyiTransportNode n X)
    (s : RenyiNodeSplit K (1-1/N) a) :
    sigma K (N+1) (1/2) a.distance *
      (renyiIntegral (hausdorff n X) a.left N+renyiIntegral (hausdorff n X) a.right N) ≤
      renyiIntegral (hausdorff n X) (s.plan.map (fun γ => γ midpointTime)) N := by
  let : SeparableSpace X := hX.separable
  let := a.left_probability
  let := a.right_probability
  let := s.probability
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hN1 : 1 < N := by linarith
  have hNplus : 1 < N+1 := by linarith
  have hq0 : 0 < 1-1/N := sub_pos.mpr ((div_lt_one (by linarith : 0<N)).mpr hN1)
  have hq1 : 1-1/N ≤ 1 := by have := one_div_pos.mpr (by linarith : 0<N); linarith
  have hac0 : a.left ≪ μ := Measure.absolutelyContinuous_of_le_smul a.left_bound
  have hac1 : a.right ≪ μ := Measure.absolutelyContinuous_of_le_smul a.right_bound
  obtain ⟨κ,hκ,hgκ,hpκ,hcd⟩ := hX.cd a.left a.right inferInstance inferInstance hac0 hac1
    (finiteSecondMoment_of_bounded _ a.center a.left_support)
    (finiteSecondMoment_of_bounded _ a.center a.right_support)
  let := hκ
  let B := closedBall a.center (3*a.radius)
  let : IsFiniteMeasure (μ.restrict B) := ⟨by
    simpa [μ,B] using hX.finiteOnBounded B isBounded_closedBall⟩
  have hs (π : Measure C(Time,X)) (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
      (hp : IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1)))) :
      ∀ᵐ x ∂π.map (fun γ => γ midpointTime), x∈B := by
    apply (ae_map_iff (measurable_path_eval midpointTime).aemeasurable measurableSet_closedBall).mpr
    exact (optimal_geodesic_plan_bounded a.left a.right π hg hp a.center a.radius_nonneg
      a.left_support a.right_support).mono (fun γ hγ => hγ.2 midpointTime)
  have hmax := s.maximal.renyiIntegral_le_of_integrable μ hN1 hgκ hpκ
    (renyiPower_localized μ _ measurableSet_closedBall (hs s.plan s.geodesic s.optimal) hq0 hq1).1
    (renyiPower_localized μ _ measurableSet_closedBall (hs κ hgκ hpκ) hq0 hq1).1
  have hend := optimalPlan_endpoints a.left a.right κ hpκ
  have hd := a.distance_bound κ inferInstance hgκ hpκ
  let c := sigma K (N+1) (1/2) a.distance
  have hme0 := ((a.left.measurable_rnDeriv μ).comp (measurable_path_eval 0)).pow_const (-(1/N))
  have hme1 := ((a.right.measurable_rnDeriv μ).comp (measurable_path_eval 1)).pow_const (-(1/N))
  dsimp only [Function.comp_def] at hme0 hme1
  have he0 : (∫⁻ γ : C(Time,X), (a.left.rnDeriv μ (γ 0))^(-(1/N)) ∂κ)=renyiIntegral μ a.left N := by
    rw [←lintegral_map ((a.left.measurable_rnDeriv μ).pow_const _)
      (measurable_path_eval 0),hend.1,←renyiIntegral_eq_inverse_density μ a.left hac0 hN1]
  have he1 : (∫⁻ γ : C(Time,X), (a.right.rnDeriv μ (γ 1))^(-(1/N)) ∂κ)=renyiIntegral μ a.right N := by
    rw [←lintegral_map ((a.right.measurable_rnDeriv μ).pow_const _)
      (measurable_path_eval 1),hend.2,←renyiIntegral_eq_inverse_density μ a.right hac1 hN1]
  calc
    _ = ∫⁻ γ : C(Time,X), c*(a.left.rnDeriv μ (γ 0))^(-(1/N))+
        c*(a.right.rnDeriv μ (γ 1))^(-(1/N)) ∂κ := by
      rw [lintegral_add_left (hme0.const_mul c),lintegral_const_mul c hme0,
        lintegral_const_mul c hme1,he0,he1,mul_add]
    _ ≤ ∫⁻ γ : C(Time,X), tau K N (1/2) (dist (γ 0) (γ 1))*(a.left.rnDeriv μ (γ 0))^(-(1/N))+
        tau K N (1/2) (dist (γ 0) (γ 1))*(a.right.rnDeriv μ (γ 1))^(-(1/N)) ∂κ := by
      apply lintegral_mono_ae
      filter_upwards [hd] with γ hγ
      have hcoeff := (sigma_antitone_distance_nonpos_curvature hK hNplus (by norm_num)
        (by norm_num) dist_nonneg hγ).trans (reduced_midpoint_le_tau hN1 dist_nonneg)
      exact add_le_add (mul_le_mul' hcoeff le_rfl) (mul_le_mul' hcoeff le_rfl)
    _ ≤ renyiIntegral μ (κ.map (fun γ => γ midpointTime)) N := by
      simpa only [midpointTime,show (1-(1/2:ℝ))=1/2 by norm_num] using hcd N hN midpointTime
    _ ≤ _ := hmax

end RegularPointCoordinates

end

end OAI
