import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.WeightedHeatSmoothingCore

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile215
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_weighted_heat_smoothing {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    (f : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x)))
    {Cf : ℝ} (hCf : 0 ≤ Cf) (hfb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|f x| ≤ Cf)
    {T : ℝ} (hT : 0 < T) :
    ∃ g : X → ℝ,LipschitzWith (Real.toNNReal (Real.sqrt (Cf^2/(2*T*Real.exp (-2*|K-a*CG| *T))))) g ∧
      g =ᵐ[exponentialMeasure m (fun x => a*F x)] cheegerHeat h T f := by
  let V := fun x => a*F x
  let ν := exponentialMeasure m V
  have hVB : ∀ x,|V x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal)
    (exponentialMeasure_comparable (m := m) hVB).2
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  let : IsLocallyFiniteMeasure ν := ⟨fun x =>
    ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,hnfin _ Metric.isBounded_ball⟩⟩
  let ts : ℕ → ℝ := fun n => ((n:ℝ)+1)⁻¹
  have hts (n : ℕ) : 0 < ts n := by dsimp [ts]; positivity
  have ht0 : Tendsto ts atTop (𝓝 0) := by
    simpa only [ts,one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  choose vs As AAs he hg hAg hvb hAb hAAb using
    (fun n => cheeger_double_resolvent_core h (hts n) hCf f hfb)
  have hvs : Tendsto vs atTop (𝓝 f) := by
    have H := cheeger_double_resolvent_tendsto h hts ht0 f
    exact H.congr (fun n => (he n).symm)
  have hex (n : ℕ) := hHess.rcd_weighted_heat_smoothing_core hN hrcd hfull hfin o hF hFb hGb hGc ha h
    (hg n) hCf (by positivity : 0 ≤ |(ts n)⁻¹| *(Cf+Cf)) (hvb n) (hAb n) hT
  choose gs hLip heq using hex
  have HT := (cheegerHeat h T).continuous.tendsto f |>.comp hvs
  exact exists_lipschitz_of_tendsto_Lp HT hLip heq
end WeakHessian

end
end InlinedFile215

end OAI
