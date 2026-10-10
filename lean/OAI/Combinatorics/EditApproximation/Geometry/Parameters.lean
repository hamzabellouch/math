import OAI.Combinatorics.EditApproximation.Geometry.ParameterSlack
import OAI.Combinatorics.EditApproximation.Probability.ExactSampling
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# Integer-computed parameters

The logarithms and fourth roots in Section 2 are computed by natural bit
lengths and nested integer square roots. No real arithmetic oracle is
used to form the algorithm's parameters.
-/

namespace EditApproximation
















theorem heightExponent_pos (N : ℕ) (hN : 0 < N) : 0 < heightExponent N := by
  apply Nat.clog_pos (by decide)
  have hlog : 1 < Nat.clog 2 (N + 2) := by
    exact (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).2 (by norm_num; omega)
  exact hlog

theorem inputHeight_covers_length (N : ℕ) : N + 2 ≤ 2 ^ inputHeight N := by
  have hlog := Nat.le_pow_clog (by decide : 1 < 2) (N + 2)
  have hheight := Nat.le_pow_clog (by decide : 1 < 2) (Nat.clog 2 (N + 2))
  exact hlog.trans (pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hheight)

theorem inputSmallLog_bounds (N : ℕ) (hN : 0 < N) :
    heightExponent N ≤ inputSmallLog N ∧ inputSmallLog N < 2 * heightExponent N := by
  have hpos := heightExponent_pos N hN
  have hone : 1 ≤ heightExponent N := hpos
  have hrange := rejectionWord_range (heightExponent N) hpos
  simpa only [inputSmallLog, smallLogExponent, rejectionBitCount, max_eq_right hone] using hrange

theorem inputHeight_binary_slack (N : ℕ) (hN : 0 < N) :
    (2 : ℝ) ^ (inputSmallLog N / 2) ≤ inputHeight N := by
  have hlogs := inputSmallLog_bounds N hN
  have hexponent : inputSmallLog N / 2 ≤ heightExponent N := by omega
  have hpower := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexponent
  simpa only [inputHeight, Nat.cast_pow, Nat.cast_ofNat] using hpower

theorem inputHeight_polynomial_slack (N : ℕ) (hN : 0 < N)
    (hell : 2 ^ 1000 ≤ inputSmallLog N) :
    (inputSmallLog N : ℝ) ^ 20000 ≤ inputHeight N :=
  astronomical_parameter_slack _ _ hell (inputHeight_binary_slack N hN)

theorem coarseExponent_fourth_power (ell : ℕ) :
    coarseExponent ell ^ 4 ≤ Nat.log 2 ell := by
  have ha := Nat.sqrt_le' (Nat.sqrt (Nat.log 2 ell))
  have hb := Nat.sqrt_le' (Nat.log 2 ell)
  have hsq := Nat.pow_le_pow_left ha 2
  rw [← pow_mul] at hsq
  exact hsq.trans hb

theorem coarseExponent_maximal (ell p : ℕ) (hp : p ^ 4 ≤ Nat.log 2 ell) :
    p ≤ coarseExponent ell := by
  apply Nat.le_sqrt'.2
  apply Nat.le_sqrt'.2
  simpa only [← pow_mul] using hp

theorem coarseExponent_shift_square (ell : ℕ) (hell : 1764 ≤ ell) :
    ((coarseExponent ell : ℝ) + 21) ^ 2 ≤ ell := by
  have hp : (coarseExponent ell : ℝ) ^ 4 ≤ ell := by
    exact_mod_cast (coarseExponent_fourth_power ell).trans (Nat.log_le_self 2 ell)
  have hellR : (1764 : ℝ) ≤ ell := by exact_mod_cast hell
  have hscaled : (4 * (coarseExponent ell : ℝ) ^ 2) ^ 2 ≤ (ell : ℝ) ^ 2 := by
    have ha := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 16)
    have hb : 16 * (ell : ℝ) ≤ (ell : ℝ) ^ 2 := by nlinarith
    nlinarith
  have hquarter : 4 * (coarseExponent ell : ℝ) ^ 2 ≤ ell :=
    (sq_le_sq₀ (by positivity) (Nat.cast_nonneg ell)).mp hscaled
  nlinarith [sq_nonneg ((coarseExponent ell : ℝ) - 21)]

noncomputable def heightQuarterRoot (N : ℕ) : ℝ :=
  Real.sqrt (Real.sqrt (inputHeight N : ℝ))

theorem heightQuarterRoot_fourth_power (N : ℕ) :
    heightQuarterRoot N ^ 4 = inputHeight N := by
  unfold heightQuarterRoot
  rw [show (Real.sqrt (Real.sqrt (inputHeight N : ℝ))) ^ 4 =
    ((Real.sqrt (Real.sqrt (inputHeight N : ℝ))) ^ 2) ^ 2 by ring]
  rw [Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]

theorem inputParameters_error_envelope (N : ℕ) (hN : 0 < N)
    (hell : 2 ^ 1000 ≤ inputSmallLog N) :
    let H := (inputHeight N : ℝ)
    let ell := (inputSmallLog N : ℝ)
    let root := heightQuarterRoot N
    let q := (coarseExponent (inputSmallLog N) : ℝ) + 21
    52000 / H ^ 18 + 8040000 * ell ^ 4 / root ^ 2 +
      200 * ell / root + 1000000 * q / ell ^ 2 + 13200 / H ^ 2 < 1 / ell := by
  dsimp only
  have hcut : 64000000000000 ≤ inputSmallLog N := by
    have hsmall : 64000000000000 ≤ (2 : ℕ) ^ 46 := by norm_num
    exact hsmall.trans ((pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ))
      (by decide : 46 ≤ 1000)).trans hell)
  have hlarge : (64000000000000 : ℝ) ≤ inputSmallLog N := by exact_mod_cast hcut
  have hellone : (1 : ℝ) ≤ inputSmallLog N := by linarith
  have hpoly := inputHeight_polynomial_slack N hN hell
  have hroot := fourth_root_polynomial_slack hellone hpoly
    (Real.sqrt_nonneg _) (heightQuarterRoot_fourth_power N)
  apply refinement_error_envelope hlarge
  · exact (pow_le_pow_right₀ hellone (by decide : 2 ≤ 20000)).trans hpoly
  · exact (pow_le_pow_right₀ hellone (by decide : 4 ≤ 5000)).trans hroot
  · exact add_nonneg (Nat.cast_nonneg _) (by norm_num)
  · exact coarseExponent_shift_square _ ((by decide : 1764 ≤ 64000000000000).trans hcut)

end EditApproximation

end OAI
