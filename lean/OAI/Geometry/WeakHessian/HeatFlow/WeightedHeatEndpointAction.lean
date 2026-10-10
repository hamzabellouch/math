import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.WeightedHeatPlanAction

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile226
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma IsTestPlan.heat_integral_difference_bounded (hfin : FiniteOnBoundedSets m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (h : QuadraticCheegerEnergy m) {f g : X →ᵇ ℝ} {u v : Lp ℝ 2 m}
    (hu : u =ᵐ[m] f) (hv : v =ᵐ[m] g) {T : ℝ} (hT : 0 ≤ T) (t : Time) :
    |(∫ γ,cheegerHeat h T u (γ t) ∂π)-(∫ γ,cheegerHeat h T v (γ t) ∂π)| ≤ dist f g := by
  let : IsProbabilityMeasure π := hπ.1
  have hi (w : Lp ℝ 2 m) : Integrable (fun γ => cheegerHeat h T w (γ t)) π :=
    (show LocallyL2 m (cheegerHeat h T w) from fun o R _ =>
      (Lp.memLp _).restrict (Metric.ball o R)).integrable_eval hfin hπ hb t
  have huv : ∀ᵐ x ∂m,|(u-v) x| ≤ dist f g := by
    filter_upwards [Lp.coeFn_sub u v,hu,hv] with x hx he hf
    simp only [hx,Pi.sub_apply,he,hf]
    simpa only [Real.dist_eq] using (BoundedContinuousFunction.dist_coe_le_dist (f := f) (g := g) x)
  have HB := cheegerHeat_bounded h hT dist_nonneg (u-v) huv
  rw [map_sub] at HB
  have H : ∀ᵐ γ ∂π,|cheegerHeat h T u (γ t)-cheegerHeat h T v (γ t)| ≤ dist f g := by
    have H' : ∀ᵐ x ∂m,|cheegerHeat h T u x-cheegerHeat h T v x| ≤ dist f g := by
      filter_upwards [HB,Lp.coeFn_sub (cheegerHeat h T u) (cheegerHeat h T v)] with x hx he
      simpa only [he,Pi.sub_apply] using hx
    exact hπ.ae_eval_of_ae H' t
  rw [← integral_sub (hi u) (hi v)]
  have Hn : ∀ᵐ γ ∂π,‖cheegerHeat h T u (γ t)-cheegerHeat h T v (γ t)‖ ≤ dist f g := by
    simpa only [Real.norm_eq_abs] using H
  simpa [Real.norm_eq_abs,MeasureTheory.measureReal_def] using norm_integral_le_of_norm_le_const Hn

omit [CompleteSpace X] in
lemma WeakHessianUpperBound.rcd_weighted_heat_endpoint_action {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    (φ : X →ᵇ ℝ) (hφ : HasCompactSupport (φ : X → ℝ)) {D : ℝ≥0} (hφL : LipschitzWith D φ)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ u v : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x)),
      u =ᵐ[exponentialMeasure m (fun x => a*F x)] φ ∧
      v =ᵐ[exponentialMeasure m (fun x => a*F x)] boundedHopfMap φ 1 ∧
      ∀ π : Measure (Curve X),
        IsTestPlan (exponentialMeasure m (fun x => a*F x)) π → BoundedTracks π →
        (∀ᵐ γ ∂π,IsGeodesic γ) →
        (∫ γ,cheegerHeat h T v (γ timeOne) ∂π)-
          (∫ γ,cheegerHeat h T u (γ timeZero) ∂π) ≤
        (∫ γ,dist (γ timeZero) (γ timeOne)^2 ∂π)/(2*Real.exp (2*(K-a*CG)*T)) := by
  let ν := exponentialMeasure m (fun x => a*F x)
  have hVB : ∀ x,|a*F x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal)
    (exponentialMeasure_comparable (m := m) hVB).2
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  let : IsFiniteMeasureOnCompacts ν := ⟨fun S hS => hnfin S hS.isBounded⟩
  have hφ2 : MemLp (φ : X → ℝ) 2 ν := φ.continuous.memLp_of_hasCompactSupport hφ
  let u := hφ2.toLp (φ : X → ℝ)
  have hu : u =ᵐ[ν] φ := hφ2.coeFn_toLp
  obtain ⟨U,hU,hA⟩ := hHess.rcd_weighted_heat_hopf_plan_action hN hrcd hfull hfin o
    hF hFb hGb hGc ha h φ hφ hT
  refine ⟨u,U 1,hu,hU 1 zero_lt_one,?_⟩
  intro π hπ hb hgeo
  let J := fun q : ℝ => (∫ γ,cheegerHeat h T (U (q+1)) (γ timeOne) ∂π)-
    (∫ γ,cheegerHeat h T (U q) (γ timeZero) ∂π)
  have hlim1 : Tendsto (fun q : ℝ => ∫ γ,cheegerHeat h T (U (q+1)) (γ timeOne) ∂π)
      (𝓝[>] 0) (𝓝 (∫ γ,cheegerHeat h T (U 1) (γ timeOne) ∂π)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have he : ∀ᶠ q : ℝ in 𝓝[>] 0,
        dist (∫ γ,cheegerHeat h T (U (q+1)) (γ timeOne) ∂π)
          (∫ γ,cheegerHeat h T (U 1) (γ timeOne) ∂π) ≤
        dist (boundedHopfMap φ (q+1)) (boundedHopfMap φ 1) := by
      filter_upwards [self_mem_nhdsWithin] with q hq
      change 0 < q at hq
      simpa only [Real.dist_eq] using
        hπ.heat_hopf_integral_difference hnfin hb h φ hU (by linarith : 0 < q+1) zero_lt_one hT timeOne
    apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) he
    have hc : ContinuousAt (boundedHopfMap φ) 1 :=
      (continuousOn_boundedHopfMap hφL).continuousAt (Ici_mem_nhds zero_lt_one)
    have H := (hc.tendsto.comp (show Tendsto (fun q : ℝ => q+1) (𝓝[>] 0) (𝓝 1) by
      simpa using ((by fun_prop : Continuous (fun q : ℝ => q+1)).tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds)).dist
        (tendsto_const_nhds (x := boundedHopfMap φ 1))
    simpa only [dist_self,Function.comp_def] using H
  have hlim0 : Tendsto (fun q : ℝ => ∫ γ,cheegerHeat h T (U q) (γ timeZero) ∂π)
      (𝓝[>] 0) (𝓝 (∫ γ,cheegerHeat h T u (γ timeZero) ∂π)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have he : ∀ᶠ q : ℝ in 𝓝[>] 0,
        dist (∫ γ,cheegerHeat h T (U q) (γ timeZero) ∂π)
          (∫ γ,cheegerHeat h T u (γ timeZero) ∂π) ≤ dist (boundedHopfMap φ q) φ := by
      filter_upwards [self_mem_nhdsWithin] with q hq
      simpa only [Real.dist_eq] using
        hπ.heat_integral_difference_bounded hnfin hb h (hU q hq) hu hT timeZero
    apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) he
    have H := ((continuousOn_boundedHopfMap hφL) 0 (by simp)).tendsto.mono_left
      (nhdsWithin_mono (0:ℝ) (Ioi_subset_Ici_self))
    simpa only [boundedHopfMap_zero,dist_self] using H.dist (tendsto_const_nhds (x := φ))
  apply le_of_tendsto (hlim1.sub hlim0)
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact hA q hq π hπ hb hgeo
end WeakHessian

end
end InlinedFile226

end OAI
