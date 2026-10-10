import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.DecayTimesNatTwo

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

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

lemma cd_log_midpoint_ball {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {R : ℝ} (hR : 0 < R) :
    Real.log (m (Metric.ball o R)).toReal ≤
      Real.log (m (Metric.ball o (3*R/4))).toReal+N*Real.log 2+
        2*Real.sqrt (|K|/(N-1))*(N-1)*R := by
  have hN0 : 0 < N := by linarith
  have hp (r : ℝ) (hr : 0 < r) : 0 < (m (Metric.ball o r)).toReal :=
    ENNReal.toReal_pos (hfull _ Metric.isOpen_ball ⟨o,Metric.mem_ball_self hr⟩).ne'
      (hfin _ Metric.isBounded_ball).ne
  have hfin' := hfin (Metric.ball o (3*R/4)) Metric.isBounded_ball
  have H := ENNReal.toReal_mono (ENNReal.rpow_ne_top_of_nonneg (by positivity : 0 ≤ 1/N) hfin'.ne)
    (cd_midpoint_ball_volume hN hcd hfull hfin o hR (le_refl (2*R)))
  rw [ENNReal.toReal_mul,← ENNReal.toReal_rpow,← ENNReal.toReal_rpow] at H
  have htpos : 0 < (midpointTauLower K N (2*R)).toReal :=
    ENNReal.toReal_pos (midpointTauLower_pos _ _ _).ne' (midpointTauLower_ne_top hN)
  have HH := Real.log_le_log (mul_pos htpos (Real.rpow_pos_of_pos (hp R hR) _)) H
  rw [Real.log_mul htpos.ne' (Real.rpow_pos_of_pos (hp R hR) _).ne',
    Real.log_rpow (hp R hR),Real.log_rpow (hp (3*R/4) (by positivity)),log_midpointTauLower hN] at HH
  have HN := mul_le_mul_of_nonneg_left HH hN0.le
  field_simp at HN
  rw [mul_comm R 3] at HN
  nlinarith

lemma cd_log_iterated_ball {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {R : ℝ} (hR : 0 < R) (n : ℕ) :
    Real.log (m (Metric.ball o R)).toReal ≤
      Real.log (m (Metric.ball o ((3/4:ℝ)^n*R))).toReal+N*Real.log 2*(n:ℝ)+
        8*Real.sqrt (|K|/(N-1))*(N-1)*R*(1-(3/4:ℝ)^n) := by
  induction n generalizing R with
  | zero => simp
  | succ n ih =>
    have HI := ih (R := 3*R/4) (by positivity)
    have HM := cd_log_midpoint_ball hN hcd hfull hfin o hR
    have he : (3/4:ℝ)^n*(3*R/4) = (3/4:ℝ)^(n+1)*R := by rw [pow_succ]; ring
    rw [he] at HI
    simp only [Nat.cast_add,Nat.cast_one,pow_succ] at HI ⊢
    nlinarith

lemma cd_log_ball_volume_le_linear {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {n : ℕ} (hn : 0 < n) :
    Real.log (m (Metric.ball o (n:ℝ))).toReal ≤
      Real.log (m (Metric.ball o 2)).toReal+
        (N*Real.log 2+8*Real.sqrt (|K|/(N-1))*(N-1))*(n:ℝ) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hr : 0 < (3/4:ℝ)^n*(n:ℝ) := by positivity
  have H := cd_log_iterated_ball hN hcd hfull hfin o hnR n
  have hp : 0 < (m (Metric.ball o ((3/4:ℝ)^n*(n:ℝ)))).toReal :=
    ENNReal.toReal_pos (hfull _ Metric.isOpen_ball ⟨o,Metric.mem_ball_self hr⟩).ne'
      (hfin _ Metric.isBounded_ball).ne
  have Hlog := Real.log_le_log hp (ENNReal.toReal_mono (hfin (Metric.ball o 2) Metric.isBounded_ball).ne
    (measure_mono (Metric.ball_subset_ball (decay_times_nat_le_two n))))
  have HC : 0 ≤ 8*Real.sqrt (|K|/(N-1))*(N-1)*(n:ℝ) := by positivity
  nlinarith [mul_nonneg HC (pow_nonneg (by norm_num : 0 ≤ (3/4:ℝ)) n)]

lemma cd_ball_volume_bound {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) (n : ℕ) :
    m (Metric.ball o (n:ℝ)) ≤ ENNReal.ofReal ((m (Metric.ball o 2)).toReal*
      Real.exp ((N*Real.log 2+8*Real.sqrt (|K|/(N-1))*(N-1))*(n:ℝ))) := by
  by_cases hn : n = 0
  · subst n; simp
  have hnR : 0 < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hp : 0 < (m (Metric.ball o (n:ℝ))).toReal :=
    ENNReal.toReal_pos (hfull _ Metric.isOpen_ball ⟨o,Metric.mem_ball_self hnR⟩).ne'
      (hfin _ Metric.isBounded_ball).ne
  have hp2 : 0 < (m (Metric.ball o 2)).toReal :=
    ENNReal.toReal_pos (hfull _ Metric.isOpen_ball ⟨o,Metric.mem_ball_self (by norm_num : (0:ℝ) < 2)⟩).ne'
      (hfin _ Metric.isBounded_ball).ne
  have H := Real.exp_le_exp.mpr (cd_log_ball_volume_le_linear hN hcd hfull hfin o (Nat.pos_of_ne_zero hn))
  rw [Real.exp_log hp,Real.exp_add,Real.exp_log hp2] at H
  rw [← ENNReal.ofReal_toReal (hfin (Metric.ball o (n:ℝ)) Metric.isBounded_ball).ne]
  exact ENNReal.ofReal_le_ofReal H

end WeakHessian

end
end InlinedFile0

end OAI
