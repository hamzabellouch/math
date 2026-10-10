import OAI.Combinatorics.EditApproximation.Geometry.BandRounding
import OAI.Combinatorics.EditApproximation.Geometry.Parameters

namespace OAI

/-! The input-computed dyadic parameters discharge all spacing and basic rounding premises. -/

namespace EditApproximation

theorem computed_theta_dyadic (N : ℕ) :
    (rationalParameters (inputSmallLog N)).theta =
      (2 : ℚ) ^ (-((40 * smallLogExponent N : ℕ) : ℤ)) := by
  change 1 / (((2 ^ smallLogExponent N : ℕ) : ℚ) ^ 40) = _
  rw [Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
  rw [zpow_neg, zpow_natCast]
  rw [Nat.mul_comm (smallLogExponent N) 40, one_div]

theorem computed_P_dyadic (N : ℕ) :
    (integerParameters N).P =
      2 ^ (heightExponent N * (coarseExponent (inputSmallLog N) + 20)) := by
  change (2 ^ heightExponent N) ^ (coarseExponent (inputSmallLog N) + 20) = _
  rw [pow_mul]

theorem basic_band_small_constants {ell : ℚ} (hell : 2 ≤ ell) :
    0 < 1 / ell ^ 4 ∧ 0 < 1 / ell ^ 40 ∧ 1 / ell ^ 40 ≤ 1 / 2 ∧
      32 * ell * (1 / ell ^ 40) ≤ 1 ∧ 64 * ell * (1 / ell ^ 40) ≤ 1 := by
  have hellpos : 0 < ell := by linarith
  have hellone : 1 ≤ ell := by linarith
  have hcoef : (64 : ℚ) ≤ ell ^ 6 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 2) hell 6
    norm_num at h
    exact h
  have hpower : (64 : ℚ) ≤ ell ^ 39 :=
    hcoef.trans (pow_le_pow_right₀ hellone (by decide : 6 ≤ 39))
  have hscale : 64 * ell ≤ ell ^ 40 := by
    calc
      64 * ell ≤ ell ^ 39 * ell := mul_le_mul_of_nonneg_right hpower hellpos.le
      _ = ell ^ 40 := (pow_succ ell 39).symm
  have h64 : 64 * ell * (1 / ell ^ 40) ≤ 1 := by
    rw [mul_one_div]
    exact (div_le_one₀ (pow_pos hellpos 40)).2 hscale
  have h32 : 32 * ell * (1 / ell ^ 40) ≤ 1 := by
    have hnonneg : 0 ≤ ell * (1 / ell ^ 40) := by positivity
    nlinarith only [h64, hnonneg]
  have htheta : 1 / ell ^ 40 ≤ 1 / 2 := by
    apply (div_le_div_iff₀ (pow_pos hellpos 40) (by norm_num : (0 : ℚ) < 2)).2
    have h := pow_le_pow_right₀ hellone (by decide : 1 ≤ 40)
    simp only [pow_one] at h
    linarith only [hell, h]
  exact ⟨by positivity, by positivity, htheta, h32, h64⟩

theorem computed_band_basic_constants (N : ℕ) (hell : 2 ≤ inputSmallLog N) :
    0 < (rationalParameters (inputSmallLog N)).tau ∧
      0 < (rationalParameters (inputSmallLog N)).theta ∧
      (rationalParameters (inputSmallLog N)).theta ≤ 1 / 2 ∧
      (32 * inputSmallLog N : ℚ) * (rationalParameters (inputSmallLog N)).theta ≤ 1 ∧
      (64 * inputSmallLog N : ℚ) * (rationalParameters (inputSmallLog N)).theta ≤ 4 := by
  have h := basic_band_small_constants (show (2 : ℚ) ≤ inputSmallLog N by exact_mod_cast hell)
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.trans (by norm_num)⟩

theorem computed_band_spacing_dominates (N : ℕ) (hN : 0 < N)
    (hell : 2 ^ 1000 ≤ inputSmallLog N) :
    ((integerParameters N).M : ℚ) ≤
      (rationalParameters (inputSmallLog N)).theta * (integerParameters N).P := by
  have hellone : (1 : ℝ) ≤ inputSmallLog N := by
    have h : 1 ≤ inputSmallLog N := Nat.one_le_two_pow
    exact_mod_cast h
  have hH40 : (inputSmallLog N : ℝ) ^ 40 ≤ inputHeight N :=
    (pow_le_pow_right₀ hellone (by decide : 40 ≤ 20000)).trans (inputHeight_polynomial_slack N hN hell)
  have hH40Q : (inputSmallLog N : ℚ) ^ 40 ≤ inputHeight N := by exact_mod_cast hH40
  have hM : (integerParameters N).M ≤ inputHeight N :=
    pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (Nat.div_le_self _ _)
  have hMQ : ((integerParameters N).M : ℚ) ≤ inputHeight N := by exact_mod_cast hM
  have hHone : 1 ≤ inputHeight N := Nat.one_le_two_pow
  have hPtwo : inputHeight N ^ 2 ≤ (integerParameters N).P :=
    pow_le_pow_right₀ hHone (by omega : 2 ≤ coarseExponent (inputSmallLog N) + 20)
  have hPtwoQ : (inputHeight N : ℚ) ^ 2 ≤ (integerParameters N).P := by exact_mod_cast hPtwo
  have hproduct : ((integerParameters N).M : ℚ) * (inputSmallLog N : ℚ) ^ 40 ≤
      (integerParameters N).P := by
    have h := mul_le_mul hMQ hH40Q (pow_nonneg (Nat.cast_nonneg (inputSmallLog N)) 40)
      (Nat.cast_nonneg (inputHeight N))
    exact h.trans (by simpa only [pow_two] using hPtwoQ)
  change ((integerParameters N).M : ℚ) ≤ (1 / (inputSmallLog N : ℚ) ^ 40) * (integerParameters N).P
  rw [one_div_mul_eq_div]
  have hellpos : (0 : ℚ) < inputSmallLog N := by exact_mod_cast (Nat.two_pow_pos (smallLogExponent N))
  apply (le_div_iff₀ (pow_pos hellpos 40)).2
  exact hproduct

end EditApproximation

end OAI
