import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.BisectionProgram

namespace OAI

/-! A literal rational clamp preserves approximation error to values in
[0,1]. It keeps numerical density samples nonnegative and bounded. -/

namespace ContinuumCoulomb
open ExactQuantumFactoring.BitStackProgram

def rationalUnitClamp (q : ℚ) : ℚ := max 0 (min 1 q)

theorem rationalUnitClamp_nonnegative (q : ℚ) : 0 ≤ rationalUnitClamp q :=
  le_max_left _ _

theorem rationalUnitClamp_le_one (q : ℚ) : rationalUnitClamp q ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)

theorem rationalUnitClamp_error (q : ℚ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    |(rationalUnitClamp q : ℝ) - r| ≤ |(q : ℝ) - r| := by
  by_cases hq0 : q < 0
  · have hq : (q : ℝ) < 0 := by exact_mod_cast hq0
    have he : rationalUnitClamp q = 0 := by
      unfold rationalUnitClamp
      rw [min_eq_right (by linarith), max_eq_left hq0.le]
    rw [he, Rat.cast_zero, zero_sub, abs_neg, abs_of_nonneg hr0,
      abs_of_nonpos (by linarith : (q : ℝ) - r ≤ 0)]
    linarith
  · by_cases hq1 : 1 < q
    · have hq : (1 : ℝ) < q := by exact_mod_cast hq1
      have he : rationalUnitClamp q = 1 := by
        unfold rationalUnitClamp
        rw [min_eq_left hq1.le, max_eq_right (by norm_num)]
      rw [he, Rat.cast_one, abs_of_nonneg (by linarith : 0 ≤ 1 - r),
        abs_of_nonneg (by linarith : 0 ≤ (q : ℝ) - r)]
      linarith
    · have he : rationalUnitClamp q = q := by
        unfold rationalUnitClamp
        rw [min_eq_right (le_of_not_gt hq1), max_eq_right (le_of_not_gt hq0)]
      rw [he]

noncomputable opaque rationalUnitClampProgram : Procedure ratCode ratCode rationalUnitClamp := by
  let q := Procedure.identity ratCode
  let zero := Procedure.constant ratCode ratCode (0 : ℚ)
  let one := Procedure.constant ratCode ratCode (1 : ℚ)
  let below := BisectionProgram.rationalLess.comp (q.pair zero)
  let above := BisectionProgram.rationalLess.comp (one.pair q)
  exact (Procedure.conditional below zero (Procedure.conditional above one q)).congrFun (by
    intro q
    simp only [Function.comp_apply, id_eq, decide_eq_true_eq]
    split_ifs with h0 h1
    · simp [rationalUnitClamp, min_eq_right (by linarith : q ≤ 1), max_eq_left h0.le]
    · simp [rationalUnitClamp, min_eq_left h1.le]
    · simp [rationalUnitClamp, min_eq_right (le_of_not_gt h1), max_eq_right (le_of_not_gt h0)])

end ContinuumCoulomb

end OAI
