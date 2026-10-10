import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.WeightedHeatHopfPointwise
import OAI.Geometry.WeakHessian.Transport.PlanHamiltonJacobiAction
import OAI.Geometry.WeakHessian.HeatFlow.HeatHopfPlanContinuity

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile225
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_weighted_heat_hopf_plan_action {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    (φ : X →ᵇ ℝ) (hφ : HasCompactSupport (φ : X → ℝ)) {T : ℝ} (hT : 0 ≤ T) :
    ∃ U : ℝ → Lp ℝ 2 (exponentialMeasure m (fun x => a*F x)),
      (∀ r,0 < r → U r =ᵐ[exponentialMeasure m (fun x => a*F x)] boundedHopfMap φ r) ∧
      ∀ q,0 < q → ∀ π : Measure (Curve X),
        IsTestPlan (exponentialMeasure m (fun x => a*F x)) π → BoundedTracks π →
        (∀ᵐ γ ∂π,IsGeodesic γ) →
        (∫ γ,cheegerHeat h T (U (q+1)) (γ timeOne) ∂π)-
          (∫ γ,cheegerHeat h T (U q) (γ timeZero) ∂π) ≤
        (∫ γ,dist (γ timeZero) (γ timeOne)^2 ∂π)/(2*Real.exp (2*(K-a*CG)*T)) := by
  let ν := exponentialMeasure m (fun x => a*F x)
  have hVB : ∀ x,|a*F x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal)
    (exponentialMeasure_comparable (m := m) hVB).2
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  let U : ℝ → Lp ℝ 2 ν := fun r => if hr : 0 < r then
    (boundedHopfMap_memLp_compact hnfin φ o hφ hr).toLp (boundedHopfMap φ r) else 0
  have hU (r : ℝ) (hr : 0 < r) : U r =ᵐ[ν] boundedHopfMap φ r := by
    dsimp only [U]
    rw [dite_eq_left hr]
    exact MemLp.coeFn_toLp _
  have hSob (r : ℝ) (hr : 0 < r) : Sobolev ν (U r : X → ℝ) :=
    (sobolev_congr_ae (hU r hr)).mpr
      (sobolev_of_lipschitz_compactSupport hnfin (boundedHopfMap_lipschitz φ hr).choose_spec
        (boundedHopfMap_compactSupport φ o hφ hr))
  have hID := fun f hf => hrcd.weighted_cheegerEnergy_integral hfin o hVB (f := f) hf
  let W := fun r : ℝ => (cheegerHeat h T (U r) : X → ℝ)
  have hW (r : ℝ) : LocallyL2 ν (W r) := fun o R _ => (Lp.memLp _).restrict (Metric.ball o R)
  have hWS (r : ℝ) (hr : 0 < r) : LocalSobolev ν (W r) := by
    have H : Sobolev ν (W r) := (identified_sobolev_iff_energy hnfin hID).mpr
      (((cheeger_closedQuadraticEnergy h).heat_energy_le ν hT (U r)).trans_lt
        ((identified_sobolev_iff_energy hnfin hID).mp (hSob r hr)))
    exact H.2.1
  have hHJ (r s : ℝ) (hr : 0 < r) (hrs : r ≤ s) : ∀ᵐ x ∂ν,
      W s x-W r x ≤ (-(s-r)*r/(2*s))*Real.exp (2*(K-a*CG)*T)*(weakGradient ν (W r) x)^2 := by
    have H := hHess.rcd_weighted_heat_hopf_pointwise hN hrcd hfull hfin o hF hFb hGb hGc ha h
      φ hr hrs (hSob r hr) (hU r hr) (hU s (hr.trans_le hrs)) hT
    filter_upwards [H,gamma_self (m := ν) (cheegerHeat h T (U r) : X → ℝ)] with x hx he
    dsimp only [ν] at he
    simpa only [W,he] using hx
  refine ⟨U,hU,?_⟩
  intro q hq π hπ hb hgeo
  have hc := (hπ.continuousOn_heat_hopf_integral hnfin hb h φ hU hT q).comp
    (by fun_prop : ContinuousOn (fun t : ℝ => q+t) (Icc 0 1))
    (show MapsTo (fun t : ℝ => q+t) (Icc 0 1) (Ioi 0) from fun t ht =>
      add_pos_of_pos_of_nonneg hq ht.1)
  have hc' : ContinuousOn (fun t : ℝ => ∫ γ,W (q+t) (evalReal γ t) ∂π) (Icc 0 1) := by
    simpa only [Function.comp_def,add_sub_cancel_left,W] using hc
  exact hπ.hamiltonJacobi_action_bound hnfin hb hgeo hW hWS
    (Real.exp_pos (2*(K-a*CG)*T)) hq hHJ hc'
end WeakHessian

end
end InlinedFile225

end OAI
