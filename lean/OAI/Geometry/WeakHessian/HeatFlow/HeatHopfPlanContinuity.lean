import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.CheegerHeat
import OAI.Geometry.WeakHessian.Entropy.EntropyContact

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile224
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma IsTestPlan.heat_hopf_integral_difference (hfin : FiniteOnBoundedSets m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (h : QuadraticCheegerEnergy m) (φ : X →ᵇ ℝ) {U : ℝ → Lp ℝ 2 m}
    (hU : ∀ r,0 < r → U r =ᵐ[m] boundedHopfMap φ r)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) {T : ℝ} (hT : 0 ≤ T) (t : Time) :
    |(∫ γ,cheegerHeat h T (U r) (γ t) ∂π)-(∫ γ,cheegerHeat h T (U s) (γ t) ∂π)| ≤
      dist (boundedHopfMap φ r) (boundedHopfMap φ s) := by
  let : IsProbabilityMeasure π := hπ.1
  let B := dist (boundedHopfMap φ r) (boundedHopfMap φ s)
  have hi (v : Lp ℝ 2 m) : Integrable (fun γ => cheegerHeat h T v (γ t)) π :=
    (show LocallyL2 m (cheegerHeat h T v) from fun o R _ =>
      (Lp.memLp _).restrict (Metric.ball o R)).integrable_eval hfin hπ hb t
  have hvB : ∀ᵐ x ∂m,|(U r-U s) x| ≤ B := by
    filter_upwards [Lp.coeFn_sub (U r) (U s),hU r hr,hU s hs] with x hx he hf
    simp only [hx,Pi.sub_apply,he,hf]
    simpa only [Real.dist_eq,B] using (BoundedContinuousFunction.dist_coe_le_dist (f := boundedHopfMap φ r) (g := boundedHopfMap φ s) x)
  have HB := cheegerHeat_bounded h hT dist_nonneg (U r-U s) hvB
  rw [map_sub] at HB
  have H : ∀ᵐ γ ∂π,|cheegerHeat h T (U r) (γ t)-cheegerHeat h T (U s) (γ t)| ≤ B := by
    have H' : ∀ᵐ x ∂m,|cheegerHeat h T (U r) x-cheegerHeat h T (U s) x| ≤ B := by
      filter_upwards [HB,Lp.coeFn_sub (cheegerHeat h T (U r)) (cheegerHeat h T (U s))] with x hx he
      simpa only [he,Pi.sub_apply,B] using hx
    exact hπ.ae_eval_of_ae H' t
  rw [← integral_sub (hi (U r)) (hi (U s))]
  have Hn : ∀ᵐ γ ∂π,‖cheegerHeat h T (U r) (γ t)-cheegerHeat h T (U s) (γ t)‖ ≤ B := by
    simpa only [Real.norm_eq_abs] using H
  simpa [Real.norm_eq_abs,MeasureTheory.measureReal_def,B] using
    norm_integral_le_of_norm_le_const Hn

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma IsTestPlan.continuousOn_heat_hopf_integral (hfin : FiniteOnBoundedSets m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (h : QuadraticCheegerEnergy m) (φ : X →ᵇ ℝ) {U : ℝ → Lp ℝ 2 m}
    (hU : ∀ r,0 < r → U r =ᵐ[m] boundedHopfMap φ r)
    {T : ℝ} (hT : 0 ≤ T) (q : ℝ) :
    ContinuousOn (fun r : ℝ => ∫ γ,cheegerHeat h T (U r) (evalReal γ (r-q)) ∂π) (Ioi 0) := by
  intro s hs
  change 0 < s at hs
  have hQc : ContinuousAt (boundedHopfMap φ) s :=
    (boundedHopfMap_time_lipschitz φ (by positivity : 0 < s/2)).continuousOn.continuousAt
      (Ici_mem_nhds (by linarith : s/2 < s))
  have hfix : Continuous (fun r : ℝ => ∫ γ,cheegerHeat h T (U s) (evalReal γ (r-q)) ∂π) := by
    have H := hπ.continuous_integral_eval_local hfin hb (f := (cheegerHeat h T (U s) : X → ℝ)) (by
      intro o R _
      let : IsFiniteMeasure (m.restrict (Metric.ball o R)) := ⟨by
        simpa only [Measure.restrict_apply_univ] using hfin _ Metric.isBounded_ball⟩
      exact ((Lp.memLp _).restrict _).integrable (by norm_num))
    exact H.comp (continuous_clampTime.comp (by fun_prop))
  apply ContinuousAt.continuousWithinAt
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hbound : ∀ᶠ r : ℝ in 𝓝 s,
      dist (∫ γ,cheegerHeat h T (U r) (evalReal γ (r-q)) ∂π)
        (∫ γ,cheegerHeat h T (U s) (evalReal γ (s-q)) ∂π) ≤
      dist (boundedHopfMap φ r) (boundedHopfMap φ s)+
      dist (∫ γ,cheegerHeat h T (U s) (evalReal γ (r-q)) ∂π)
        (∫ γ,cheegerHeat h T (U s) (evalReal γ (s-q)) ∂π) := by
    filter_upwards [Ioi_mem_nhds hs] with r hr
    have H : dist (∫ γ,cheegerHeat h T (U r) (evalReal γ (r-q)) ∂π)
        (∫ γ,cheegerHeat h T (U s) (evalReal γ (r-q)) ∂π) ≤
        dist (boundedHopfMap φ r) (boundedHopfMap φ s) := by
      simpa only [Real.dist_eq,evalReal] using
        hπ.heat_hopf_integral_difference hfin hb h φ hU hr hs hT (clampTime (r-q))
    exact (dist_triangle _ _ _).trans (add_le_add H le_rfl)
  apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) hbound
  simpa only [dist_self,zero_add] using
    (hQc.tendsto.dist (tendsto_const_nhds (x := boundedHopfMap φ s))).add
      ((hfix.tendsto s).dist (tendsto_const_nhds (x := ∫ γ,cheegerHeat h T (U s) (evalReal γ (s-q)) ∂π)))
end WeakHessian

end
end InlinedFile224

end OAI
