import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

/-! # The diagonal exponent and the parameter order in (7.1), (9.6)–(9.8) -/

namespace Ostmann

noncomputable def spectatorBaseGap (Bs z m : ℝ) : ℝ := (Bs + 8 * Real.log z) * m

noncomputable def spectatorStepGap (BD Bz z r m : ℝ) : ℝ :=
  r * (BD + Bz * Real.log z + (2 / 5 : ℝ) * Real.log r) * m

theorem spectator_diagonal_exponent (Bs BD Bz z r m C : ℝ) :
    -spectatorStepGap BD Bz z r m +
      r * (spectatorBaseGap Bs z m + (Real.log z + Real.log r / 4 + C) * m) =
    (Bs - BD + (9 - Bz) * Real.log z - (3 / 20 : ℝ) * Real.log r + C) * r * m := by
  unfold spectatorBaseGap spectatorStepGap
  ring

theorem spectator_diagonal_exponent_bound (Bs BD Bz z r m C B : ℝ)
    (hz : 1 ≤ z) (hr : 1 ≤ r) (hm : 0 ≤ m)
    (hBz : 9 ≤ Bz) (hBD : Bs + 2 * B + C + 6 ≤ BD) :
    -spectatorStepGap BD Bz z r m +
      r * (spectatorBaseGap Bs z m + (Real.log z + Real.log r / 4 + C) * m) ≤
        -(2 * B + 6) * r * m := by
  rw [spectator_diagonal_exponent]
  have hzlog : 0 ≤ Real.log z := Real.log_nonneg hz
  have hrlog : 0 ≤ Real.log r := Real.log_nonneg hr
  have hzterm : (9 - Bz) * Real.log z ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hzlog
  have hcoeff : Bs - BD + (9 - Bz) * Real.log z - (3 / 20 : ℝ) * Real.log r + C ≤
      -(2 * B + 6) := by linarith
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff (by linarith)) hm

theorem bad_diagonal_reserve (bad prefactor Bs BD Bz z r m C E B : ℝ)
    (hz : 1 ≤ z) (hr : 1 ≤ r) (hm : 0 ≤ m)
    (hBz : 9 ≤ Bz) (hBD : Bs + 2 * B + C + 9 ≤ BD)
    (hprefactor : prefactor ≤ Real.exp (r * m))
    (henergy : E ≤ r * (spectatorBaseGap Bs z m + C * m))
    (hbad : bad ≤ Real.exp (-spectatorStepGap BD Bz z r m) * prefactor *
      Real.exp ((Real.log z + Real.log r / 4 + 2) * r * m + E)) :
    bad ≤ Real.exp (-(2 * B + 6) * r * m) := by
  have hgap := spectator_diagonal_exponent_bound Bs BD Bz z r m (C + 3) B
    hz hr hm hBz (by linarith)
  calc
    bad ≤ Real.exp (-spectatorStepGap BD Bz z r m) * Real.exp (r * m) *
        Real.exp ((Real.log z + Real.log r / 4 + 2) * r * m + E) := by
      apply hbad.trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hprefactor (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = Real.exp (-spectatorStepGap BD Bz z r m + r * m +
        ((Real.log z + Real.log r / 4 + 2) * r * m + E)) := by
      rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp (-spectatorStepGap BD Bz z r m +
        r * (spectatorBaseGap Bs z m + (Real.log z + Real.log r / 4 + (C + 3)) * m)) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [henergy]
    _ ≤ _ := Real.exp_le_exp.mpr hgap

/-- One unit of exponential reserve absorbs both nonnegative contributions. -/
theorem two_diagonal_terms_le (bad good B t : ℝ) (ht : Real.log 2 ≤ t)
    (hbad : bad ≤ Real.exp (-(2 * B + 4) * t))
    (hgood : good ≤ Real.exp (-(2 * B + 4) * t)) :
    bad + good ≤ Real.exp (-(2 * B + 3) * t) := by
  calc
    bad + good ≤ 2 * Real.exp (-(2 * B + 4) * t) := by linarith
    _ = Real.exp (Real.log 2 - (2 * B + 4) * t) := by
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      rw [show -(2 * B + 4) * t = -((2 * B + 4) * t) by ring, Real.exp_neg]
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end Ostmann

end OAI
