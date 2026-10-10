import OAI.Analysis.LipschitzHilbert.Estimates.TopAreaAverage
import OAI.Analysis.LipschitzHilbert.Estimates.ExponentialThreshold

namespace OAI

/-! One common moment order sums all actual top exceptional sets with
the total top area. This is independent of the number of tops. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert

def topExceptionMoment (M J L : ℝ) : ℕ := ⌈(J*L+Real.log M)/Real.log 4⌉₊+1

theorem topExceptionMoment_pos (M J L : ℝ) : 1 ≤ topExceptionMoment M J L := by
  unfold topExceptionMoment
  omega

theorem top_family_exception_area {ι : Type*} [Fintype ι]
    (T : ι → SlopeBox) (bad : ι → Set (ℝ × ℝ)) (M J L : ℝ) (hM : 0 < M)
    (hbad : ∀ i, (volume.prod volume) (bad i) ≤
      (1/4:ℝ≥0∞)^(topExceptionMoment M J L)*ENNReal.ofReal M*ENNReal.ofReal (T i).area) :
    (volume.prod volume) (⋃ i, bad i) ≤
      ENNReal.ofReal (Real.exp (-J*L)*(∑ i, (T i).area)) := by
  classical
  have hs : (1/4:ℝ≥0∞)^(topExceptionMoment M J L)*ENNReal.ofReal M ≤
      ENNReal.ofReal (Real.exp (-J*L)) := by
    have h := ENNReal.ofReal_le_ofReal (prefactor_quarter_successor_bound M (J*L) hM)
    rw [ENNReal.ofReal_mul hM.le, ENNReal.ofReal_pow (by norm_num)] at h
    have hq : ENNReal.ofReal (1/4:ℝ) = (1/4:ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num
    rw [hq] at h
    rw [show -(J*L) = -J*L by ring] at h
    simpa only [topExceptionMoment, mul_comm] using h
  calc
    _ ≤ ∑ i, (volume.prod volume) (bad i) := by
      simpa only [tsum_fintype] using measure_iUnion_le bad
    _ ≤ ∑ i, (1/4:ℝ≥0∞)^(topExceptionMoment M J L)*ENNReal.ofReal M*
        ENNReal.ofReal (T i).area := Finset.sum_le_sum (fun i _ => hbad i)
    _ = ((1/4:ℝ≥0∞)^(topExceptionMoment M J L)*ENNReal.ofReal M)*
        ENNReal.ofReal (∑ i, (T i).area) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => (T i).area_pos.le), Finset.mul_sum]
    _ ≤ ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal (∑ i, (T i).area) :=
      mul_le_mul' hs le_rfl
    _ = _ := (ENNReal.ofReal_mul (Real.exp_pos _).le).symm

theorem topExceptionMoment_le (M J L c : ℝ) (hJ : 0 ≤ J) (hL : 1 ≤ L)
    (hM : 1 ≤ M) (hlog : Real.log M ≤ c*L) :
    (topExceptionMoment M J L:ℝ) ≤ ((J+c)/Real.log 4+2)*L :=
  exponential_moment_order_le J c L M hJ hL hM hlog

end LipschitzHilbert

end

end OAI
