import Mathlib
import OAI.Geometry.WeakHessian.Geodesics.CdLogMidpointBall

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile113
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

lemma CurvatureDimension.ball_measure_lower_exp {K N : ℝ} (hcd : CurvatureDimension m K N)
    (hN : 1 < N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {r : ℝ} (hr : 0 < r) :
    ∃ A B : ℝ,0 < A ∧ 0 ≤ B ∧ ∀ x : X,
      A*Real.exp (-B*dist x o) ≤ (m (Metric.ball x r)).toReal := by
  let C := N*Real.log 2+4*Real.sqrt (|K|/(N-1))*(N-1)*r
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact add_nonneg (mul_nonneg (by linarith) (Real.log_nonneg (by norm_num)))
      (by positivity)
  have hp (x : X) (s : ℝ) (hs : 0 < s) : 0 < (m (Metric.ball x s)).toReal :=
    ENNReal.toReal_pos (hfull _ Metric.isOpen_ball ⟨x,Metric.mem_ball_self hs⟩).ne'
      (hfin _ Metric.isBounded_ball).ne
  refine ⟨(m (Metric.ball o (r/2))).toReal*Real.exp (-3*C),2*C/r,
    mul_pos (hp o _ (by positivity)) (Real.exp_pos _),by positivity,?_⟩
  intro x
  let n := ⌈2*dist x o/r+1⌉₊+1
  have hd : 0 ≤ 2*dist x o/r+1 := by positivity
  have hnL : 2*dist x o/r+1 < (n:ℝ) := by
    have h := Nat.le_ceil (2*dist x o/r+1)
    dsimp only [n]
    push_cast
    linarith
  have hnU : (n:ℝ) < 2*dist x o/r+3 := by
    have h := Nat.ceil_lt_add_one hd
    dsimp only [n]
    push_cast
    linarith
  have hn : 0 < (n:ℝ) := lt_of_le_of_lt hd hnL
  have hR : 0 < r/2*(n:ℝ) := by positivity
  have hsub : Metric.ball o (r/2) ⊆ Metric.ball x (r/2*(n:ℝ)) := by
    apply Metric.ball_subset_ball'
    rw [dist_comm o]
    have hh := (div_lt_iff₀ hr).mp (by linarith : 2*dist x o/r < (n:ℝ)-1)
    linarith
  have hsmall : (3/4:ℝ)^n*(r/2*(n:ℝ)) ≤ r := by
    have hh := mul_le_mul_of_nonneg_left (decay_times_nat_le_two n) (show 0 ≤ r/2 by positivity)
    nlinarith
  have H := cd_log_iterated_ball hN hcd hfull hfin x hR n
  have HS := Real.log_le_log (hp x _ (by positivity : 0 < (3/4:ℝ)^n*(r/2*(n:ℝ))))
    (ENNReal.toReal_mono (hfin _ Metric.isBounded_ball).ne
      (measure_mono (Metric.ball_subset_ball hsmall)))
  have HB := Real.log_le_log (hp o _ (by positivity))
    (ENNReal.toReal_mono (hfin _ Metric.isBounded_ball).ne (measure_mono hsub))
  have hS : 0 ≤ 4*Real.sqrt (|K|/(N-1))*(N-1)*r*(n:ℝ) := by positivity
  have HI : Real.log (m (Metric.ball o (r/2))).toReal ≤
      Real.log (m (Metric.ball x r)).toReal+C*(n:ℝ) := by
    have hprod := mul_nonneg hS (pow_nonneg (by norm_num : 0 ≤ (3/4:ℝ)) n)
    dsimp only [C]
    nlinarith
  have HU := mul_le_mul_of_nonneg_left hnU.le hC
  have HE := Real.exp_le_exp.mpr (show
      Real.log (m (Metric.ball o (r/2))).toReal-3*C-(2*C/r)*dist x o ≤
        Real.log (m (Metric.ball x r)).toReal from by
      have he : C*(2*dist x o/r+3) = 3*C+(2*C/r)*dist x o := by ring
      rw [he] at HU
      linarith)
  rw [Real.exp_log (hp x r hr),Real.exp_sub,Real.exp_sub,
    Real.exp_log (hp o _ (by positivity))] at HE
  simpa only [neg_mul,Real.exp_neg,div_eq_mul_inv] using HE
end WeakHessian

end
end InlinedFile113

end OAI
