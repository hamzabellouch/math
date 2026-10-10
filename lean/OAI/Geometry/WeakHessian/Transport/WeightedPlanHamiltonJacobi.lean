import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.WeightedHeatHopfPointwise
import OAI.Geometry.WeakHessian.Transport.PlanHamiltonJacobi

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile222
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_weighted_heat_hopf_plan_slope {K N : ℝ}
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
        (∀ᵐ γ ∂π,IsGeodesic γ) → ∀ b : ℝ,
        (∫ γ,dist (γ timeZero) (γ timeOne)^2 ∂π)/(2*Real.exp (2*(K-a*CG)*T)) < b →
        ∀ᶠ t : ℝ in 𝓝[>] 0,
          ((∫ γ,cheegerHeat h T (U (q+t)) (evalReal γ t) ∂π)-
            (∫ γ,cheegerHeat h T (U q) (γ timeZero) ∂π))/t < b := by
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
  refine ⟨U,hU,?_⟩
  intro q hq π hπ hb hgeo b hbb
  have hqSob : Sobolev ν (U q : X → ℝ) := (sobolev_congr_ae (hU q hq)).mpr
    (sobolev_of_lipschitz_compactSupport hnfin (boundedHopfMap_lipschitz φ hq).choose_spec
      (boundedHopfMap_compactSupport φ o hφ hq))
  have hID := fun f hf => hrcd.weighted_cheegerEnergy_integral hfin o hVB (f := f) hf
  have hHSob : Sobolev ν (cheegerHeat h T (U q)) := (identified_sobolev_iff_energy hnfin hID).mpr
    (((cheeger_closedQuadraticEnergy h).heat_energy_le ν hT (U q)).trans_lt
      ((identified_sobolev_iff_energy hnfin hID).mp hqSob))
  let W := fun t : ℝ => (cheegerHeat h T (U (q+t)) : X → ℝ)
  have hW (t : ℝ) : LocallyL2 ν (W t) := fun o R _ => (Lp.memLp _).restrict (Metric.ball o R)
  have hW0 : LocalSobolev ν (W 0) := by simpa only [W,add_zero] using hHSob.2.1
  have hHJ (t : ℝ) (ht : 0 < t) (_ht1 : t ≤ 1) : ∀ᵐ x ∂ν,
      W t x-W 0 x ≤ (-t*q/(2*(q+t)))*Real.exp (2*(K-a*CG)*T)*(weakGradient ν (W 0) x)^2 := by
    have H := hHess.rcd_weighted_heat_hopf_pointwise hN hrcd hfull hfin o hF hFb hGb hGc ha h
      φ hq (show q ≤ q+t by linarith) hqSob (hU q hq) (hU (q+t) (by linarith)) hT
    filter_upwards [H,gamma_self (m := ν) (cheegerHeat h T (U q) : X → ℝ)] with x hx he
    dsimp only [ν] at he
    simpa only [W,add_zero,add_sub_cancel_left,he] using hx
  have H := hπ.hamiltonJacobi_upper_slope hnfin hb hgeo hW hW0 hq
    (Real.exp_pos (2*(K-a*CG)*T)) hHJ hbb
  simpa only [W,add_zero] using H
end WeakHessian

end
end InlinedFile222

end OAI
