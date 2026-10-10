import Mathlib
import OAI.Geometry.WeakHessian.Geodesics.MidpointSigmaLower

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

lemma decay_times_nat_le_two (n : ℕ) : (3/4:ℝ)^n*(n:ℝ) ≤ 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    by_cases hn : 3 ≤ n
    · have hc : (3/4:ℝ)*((n:ℝ)+1) ≤ n := by
        have H : (3:ℝ)*((n:ℝ)+1) ≤ 4*(n:ℝ) := by exact_mod_cast (by omega : 3*(n+1) ≤ 4*n)
        linarith
      have hp := mul_le_mul_of_nonneg_left hc (pow_nonneg (by norm_num : 0 ≤ (3/4:ℝ)) n)
      simp only [pow_succ,Nat.cast_add,Nat.cast_one]
      nlinarith [hp]
    · interval_cases n <;> norm_num

lemma log_midpointTauLower {K N D : ℝ} (hN : 1 < N) :
    Real.log (midpointTauLower K N D).toReal =
      -Real.log 2-D*Real.sqrt (|K|/(N-1))*(N-1)/N := by
  have hN0 : N ≠ 0 := ne_of_gt (by linarith)
  have hs := midpointSigmaLower_pos K (N-1) D
  rw [midpointTauLower,ENNReal.toReal_mul,← ENNReal.toReal_rpow,← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (by norm_num : 0 ≤ (1/2:ℝ)),ENNReal.toReal_ofReal hs.le,
    Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos (by norm_num : 0 < (1/2:ℝ)) _))
      (ne_of_gt (Real.rpow_pos_of_pos hs _)),
    Real.log_rpow (by norm_num : 0 < (1/2:ℝ)),Real.log_rpow hs]
  rw [midpointSigmaLower,
    Real.log_div (by norm_num : (1:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0),
    Real.log_div (by norm_num : (1:ℝ) ≠ 0) (mul_ne_zero (by norm_num) (Real.exp_ne_zero _)),
    Real.log_mul (by norm_num) (Real.exp_ne_zero _),Real.log_one,Real.log_exp]
  field_simp
  ring

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

lemma cd_log_ball_volume_le_quadratic {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {n : ℕ} (hn : 0 < n) :
    Real.log (m (Metric.ball o (n:ℝ))).toReal ≤
      Real.log (m (Metric.ball o 2)).toReal+N*Real.log 2*(n:ℝ)+
        2*Real.sqrt (|K|/(N-1))*(N-1)*(n:ℝ)^2 := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hN0 : 0 < N := by linarith
  have hmn := hfull _ Metric.isOpen_ball ⟨o,Metric.mem_ball_self hnR⟩
  have hm2 := hfull _ Metric.isOpen_ball ⟨o,Metric.mem_ball_self (by norm_num : (0:ℝ) < 2)⟩
  have hmnfin := hfin (Metric.ball o (n:ℝ)) Metric.isBounded_ball
  have hm2fin := hfin (Metric.ball o 2) Metric.isBounded_ball
  have H := cd_iterated_ball_volume hN hcd hfull hfin o hnR n
  have HS : (m (Metric.ball o ((3/4:ℝ)^n*(n:ℝ))))^(1/N) ≤
      (m (Metric.ball o 2))^(1/N) :=
    ENNReal.rpow_le_rpow (measure_mono (Metric.ball_subset_ball (decay_times_nat_le_two n))) (by positivity)
  have H' := ENNReal.toReal_mono (ENNReal.rpow_ne_top_of_nonneg (by positivity) hm2fin.ne) (H.trans HS)
  rw [ENNReal.toReal_mul,ENNReal.toReal_pow,← ENNReal.toReal_rpow,← ENNReal.toReal_rpow] at H'
  have htpos : 0 < (midpointTauLower K N (2*(n:ℝ))).toReal :=
    ENNReal.toReal_pos (midpointTauLower_pos _ _ _).ne' (midpointTauLower_ne_top hN)
  have hnp : 0 < (m (Metric.ball o (n:ℝ))).toReal := ENNReal.toReal_pos hmn.ne' hmnfin.ne
  have h2p : 0 < (m (Metric.ball o 2)).toReal := ENNReal.toReal_pos hm2.ne' hm2fin.ne
  have HH := Real.log_le_log (mul_pos (pow_pos htpos _) (Real.rpow_pos_of_pos hnp _)) H'
  rw [Real.log_mul (ne_of_gt (pow_pos htpos _)) (ne_of_gt (Real.rpow_pos_of_pos hnp _)),
    Real.log_pow,Real.log_rpow hnp,Real.log_rpow h2p,log_midpointTauLower hN] at HH
  have HN := mul_le_mul_of_nonneg_left HH hN0.le
  field_simp at HN
  nlinarith

end WeakHessian

end
end InlinedFile0

end OAI
