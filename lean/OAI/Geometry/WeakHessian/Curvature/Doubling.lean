import Mathlib
import OAI.Geometry.WeakHessian.Geodesics.CdLogMidpointBall

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile79
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X]

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma CurvatureDimension.uniform_local_doubling {K N : ℝ} (hcd : CurvatureDimension m K N)
    (hN : 1 < N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) :
    IsUnifLocDoublingMeasure m := by
  let A : ℝ := 4*N*Real.log 2+24*Real.sqrt (|K|/(N-1))*(N-1)
  let C : ℝ≥0 := ⟨Real.exp A,(Real.exp_pos _).le⟩
  refine ⟨C,?_⟩
  filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with r hr hr1 x
  have hr0 : 0 < r := hr
  have hp (R : ℝ) (hR : 0 < R) : 0 < (m (Metric.ball x R)).toReal :=
    ENNReal.toReal_pos (hfull _ Metric.isOpen_ball ⟨x,Metric.mem_ball_self hR⟩).ne' (hfin _ Metric.isBounded_ball).ne
  have H := cd_log_iterated_ball hN hcd hfull hfin x (by positivity : 0 < 3*r) 4
  have hsmall : (3/4:ℝ)^4*(3*r) ≤ r := by nlinarith
  have hlog : Real.log (m (Metric.ball x ((3/4:ℝ)^4*(3*r)))).toReal ≤ Real.log (m (Metric.closedBall x r)).toReal := by
    apply Real.log_le_log (hp _ (by positivity))
    exact ENNReal.toReal_mono (hfin _ Metric.isBounded_closedBall).ne
      (measure_mono ((Metric.ball_subset_ball hsmall).trans Metric.ball_subset_closedBall))
  have hcpos : 0 < (m (Metric.closedBall x r)).toReal :=
    (hp r hr0).trans_le (ENNReal.toReal_mono (hfin _ Metric.isBounded_closedBall).ne (measure_mono Metric.ball_subset_closedBall))
  have hS : 0 ≤ Real.sqrt (|K|/(N-1))*(N-1) := mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  have H' : Real.log (m (Metric.ball x (3*r))).toReal ≤ Real.log (m (Metric.closedBall x r)).toReal+A := by
    norm_num only [Nat.cast_ofNat] at H
    have hprod : 8*Real.sqrt (|K|/(N-1))*(N-1)*(3*r)*(1-(3/4:ℝ)^4) ≤ 24*Real.sqrt (|K|/(N-1))*(N-1) := by
      nlinarith
    dsimp only [A]
    linarith
  have HE := Real.exp_le_exp.mpr H'
  rw [Real.exp_log (hp _ (by positivity)),Real.exp_add,Real.exp_log hcpos] at HE
  calc
    m (Metric.closedBall x (2*r)) ≤ m (Metric.ball x (3*r)) := measure_mono (Metric.closedBall_subset_ball (by linarith))
    _ ≤ (C:ℝ≥0∞)*m (Metric.closedBall x r) := by
      rw [← ENNReal.ofReal_toReal (hfin (Metric.ball x (3*r)) Metric.isBounded_ball).ne,
        ← ENNReal.ofReal_toReal (hfin (Metric.closedBall x r) Metric.isBounded_closedBall).ne]
      rw [← ENNReal.ofReal_coe_nnreal]
      change ENNReal.ofReal _ ≤ ENNReal.ofReal (Real.exp A)*ENNReal.ofReal _
      rw [← ENNReal.ofReal_mul (Real.exp_pos A).le,mul_comm (Real.exp A)]
      exact ENNReal.ofReal_le_ofReal HE
end WeakHessian

end
end InlinedFile79

end OAI
