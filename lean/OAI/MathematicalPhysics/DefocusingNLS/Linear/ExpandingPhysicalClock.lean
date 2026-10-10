import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPhysicalAmplitude
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace OAI

/-! # The inverse clock for the physical Schrödinger solution -/

namespace DefocusingNLS

noncomputable def expandingInverseClock (L t : ℝ) : ℝ :=
  -Real.log (1 - L ^ 2 * t)

theorem exp_neg_expandingInverseClock (L t : ℝ) (ht : 0 < 1 - L ^ 2 * t) :
    Real.exp (-expandingInverseClock L t) = 1 - L ^ 2 * t := by
  simp only [expandingInverseClock, neg_neg]
  exact Real.exp_log ht

private theorem radius_clock_cancel (L : ℝ) (hL : 0 < L) :
    L ^ 2 * L ^ (-2 : ℝ) = 1 := by
  rw [← Real.rpow_two, ← Real.rpow_add hL]
  norm_num

theorem expandingInverseClock_freeTime (L s : ℝ) (hL : 0 < L) :
    expandingInverseClock L (expandingFreeTime L s) = s := by
  have he : 1 - L ^ 2 * expandingFreeTime L s = Real.exp (-s) := by
    unfold expandingFreeTime
    rw [← mul_assoc, radius_clock_cancel L hL]
    ring
  rw [expandingInverseClock, he, Real.log_exp, neg_neg]

theorem expandingFreeTime_inverseClock (L t : ℝ) (hL : 0 < L)
    (ht : 0 < 1 - L ^ 2 * t) :
    expandingFreeTime L (expandingInverseClock L t) = t := by
  rw [expandingFreeTime, exp_neg_expandingInverseClock L t ht]
  have hc : L ^ (-2 : ℝ) * L ^ 2 = 1 := by
    rw [mul_comm]
    exact radius_clock_cancel L hL
  calc
    _ = (L ^ (-2 : ℝ) * L ^ 2) * t := by ring
    _ = t := by rw [hc, one_mul]

theorem hasDerivAt_expandingInverseClock (L t : ℝ) (ht : 0 < 1 - L ^ 2 * t) :
    HasDerivAt (expandingInverseClock L) (L ^ 2 / (1 - L ^ 2 * t)) t := by
  have h := ((((hasDerivAt_const t (1 : ℝ)).sub
    ((hasDerivAt_id t).const_mul (L ^ 2))).log ht.ne').neg)
  convert h using 1
  · rfl
  · dsimp
    ring

theorem expandingInverseClock_derivative_cancel (L t : ℝ) (hL : 0 < L)
    (ht : 0 < 1 - L ^ 2 * t) :
    (L ^ (-2 : ℝ) * Real.exp (-expandingInverseClock L t)) *
      (L ^ 2 / (1 - L ^ 2 * t)) = 1 := by
  rw [exp_neg_expandingInverseClock L t ht]
  have hc := radius_clock_cancel L hL
  have hb := ht.ne'
  calc
    _ = (L ^ (-2 : ℝ) * L ^ 2) * ((1 - L ^ 2 * t) / (1 - L ^ 2 * t)) := by ring
    _ = 1 := by rw [mul_comm (L ^ (-2 : ℝ)) (L ^ 2), hc, div_self hb, one_mul]

end DefocusingNLS

end OAI
