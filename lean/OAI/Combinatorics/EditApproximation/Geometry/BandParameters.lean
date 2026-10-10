import OAI.Combinatorics.EditApproximation.Geometry.Parameters

namespace OAI

/-! Computed numerical slack for comparison-band coverage at non-bad nodes. -/

namespace EditApproximation

theorem computed_branching_fourth_power_le_quarterRoot (N : ℕ) :
    ((integerParameters N).M : ℝ) ^ 4 ≤ heightQuarterRoot N := by
  have hexponent : 16 * (heightExponent N / 20) ≤ heightExponent N := by
    have h := Nat.div_mul_le_self (heightExponent N) 20
    omega
  have hpower : ((integerParameters N).M : ℝ) ^ 16 ≤ inputHeight N := by
    simp only [integerParameters, Nat.cast_pow, Nat.cast_ofNat, inputHeight]
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  apply (pow_le_pow_iff_left₀ (by positivity : (0 : ℝ) ≤ ((integerParameters N).M : ℝ) ^ 4)
    (Real.sqrt_nonneg _) (by decide : 4 ≠ 0)).mp
  change (((integerParameters N).M : ℝ) ^ 4) ^ 4 ≤ heightQuarterRoot N ^ 4
  rw [← pow_mul, heightQuarterRoot_fourth_power]
  exact hpower

theorem band_root_slack {ell root M : ℝ} (hell : 2 ≤ ell) (hroot : 0 ≤ root)
    (hlarge : ell ^ 5000 ≤ root) (_hM : 0 ≤ M) (hMfour : M ^ 4 ≤ root) :
    128 * ell ^ 90 * M ^ 2 ≤ root := by
  have hellone : 1 ≤ ell := by linarith
  have hcoef : (16384 : ℝ) ≤ ell ^ 14 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hell 14
    norm_num at h
    exact h
  have hbig : 16384 * ell ^ 180 ≤ root := by
    calc
      16384 * ell ^ 180 ≤ ell ^ 14 * ell ^ 180 :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = ell ^ 194 := by rw [← pow_add]
      _ ≤ ell ^ 5000 := pow_le_pow_right₀ hellone (by decide)
      _ ≤ root := hlarge
  have hproduct := mul_le_mul hMfour hbig (by positivity : (0 : ℝ) ≤ 16384 * ell ^ 180) hroot
  apply (sq_le_sq₀ (by positivity : 0 ≤ 128 * ell ^ 90 * M ^ 2) hroot).mp
  calc
    (128 * ell ^ 90 * M ^ 2) ^ 2 = M ^ 4 * (16384 * ell ^ 180) := by ring
    _ ≤ root * root := hproduct
    _ = root ^ 2 := by ring

theorem nonbad_band_numerical_bound {ell root M b K G W : ℝ}
    (hell : 2 ≤ ell) (hM : 1 ≤ M) (hb : 0 ≤ b)
    (hroot : 128 * ell ^ 90 * M ^ 2 ≤ root)
    (_hK : 0 ≤ K) (_hG : 0 ≤ G) (hW : 0 ≤ W)
    (hKsmall : K ≤ b / root) (hGsmall : G ≤ b / root) (hWsmall : W ≤ 8 * ell * b) :
    Real.sqrt (K * W) + 2 * G ≤ (1 / ell ^ 4) * (1 / ell ^ 40) * b / M := by
  have hellpos : 0 < ell := by linarith
  have hellone : 1 ≤ ell := by linarith
  have hMpos : 0 < M := by linarith
  have hMtwo : M ≤ M ^ 2 := by nlinarith only [hM]
  have hrootpos : 0 < root := (by positivity : 0 < 128 * ell ^ 90 * M ^ 2).trans_le hroot
  have hscale : 32 * ell ^ 89 * M ^ 2 ≤ root := by
    calc
      32 * ell ^ 89 * M ^ 2 ≤ 128 * ell ^ 90 * M ^ 2 := by
        have hp : ell ^ 89 ≤ ell ^ 90 := pow_le_pow_right₀ hellone (by decide : 89 ≤ 90)
        have hc : 32 * ell ^ 89 ≤ 128 * ell ^ 90 :=
          mul_le_mul (by norm_num : (32 : ℝ) ≤ 128) hp (by positivity) (by norm_num)
        exact mul_le_mul_of_nonneg_right hc (sq_nonneg M)
      _ ≤ root := hroot
  have hscale' : 4 * ell ^ 44 * M ≤ root := by
    calc
      4 * ell ^ 44 * M ≤ 128 * ell ^ 90 * M ^ 2 := by
        have hp : ell ^ 44 ≤ ell ^ 90 := pow_le_pow_right₀ hellone (by decide : 44 ≤ 90)
        have hc : 4 * ell ^ 44 ≤ 128 * ell ^ 90 :=
          mul_le_mul (by norm_num : (4 : ℝ) ≤ 128) hp (by positivity) (by norm_num)
        exact mul_le_mul hc hMtwo hMpos.le (by positivity)
      _ ≤ root := hroot
  have hKW : K * W ≤ (8 * ell * b ^ 2) / root := by
    calc
      K * W ≤ (b / root) * (8 * ell * b) :=
        mul_le_mul hKsmall hWsmall hW (div_nonneg hb hrootpos.le)
      _ = (8 * ell * b ^ 2) / root := by ring
  have hsquare : K * W ≤ (b / (2 * ell ^ 44 * M)) ^ 2 := by
    calc
      K * W ≤ (8 * ell * b ^ 2) / root := hKW
      _ ≤ b ^ 2 / (4 * ell ^ 88 * M ^ 2) := by
        apply (div_le_div_iff₀ hrootpos (by positivity : 0 < 4 * ell ^ 88 * M ^ 2)).2
        have h := mul_le_mul_of_nonneg_right hscale (sq_nonneg b)
        nlinarith only [h, show (8 * ell * b ^ 2) * (4 * ell ^ 88 * M ^ 2) =
          (32 * ell ^ 89 * M ^ 2) * b ^ 2 by ring]
      _ = (b / (2 * ell ^ 44 * M)) ^ 2 := by field_simp; ring
  have hsqrt : Real.sqrt (K * W) ≤ b / (2 * ell ^ 44 * M) :=
    (Real.sqrt_le_left (by positivity)).2 hsquare
  have htwice : 2 * G ≤ b / (2 * ell ^ 44 * M) := by
    calc
      2 * G ≤ 2 * (b / root) := mul_le_mul_of_nonneg_left hGsmall (by norm_num)
      _ = (2 * b) / root := by ring
      _ ≤ b / (2 * ell ^ 44 * M) := by
        apply (div_le_div_iff₀ hrootpos (by positivity : 0 < 2 * ell ^ 44 * M)).2
        have h := mul_le_mul_of_nonneg_right hscale' hb
        nlinarith only [h]
  have hid : b / (2 * ell ^ 44 * M) + b / (2 * ell ^ 44 * M) =
      (1 / ell ^ 4) * (1 / ell ^ 40) * b / M := by
    field_simp
    ring
  exact (add_le_add hsqrt htwice).trans_eq hid

theorem computed_nonbad_band_numerical_bound (N : ℕ) (hN : 0 < N)
    (hell : 2 ^ 1000 ≤ inputSmallLog N) {b K G W : ℝ}
    (hb : 0 ≤ b) (hK : 0 ≤ K) (hG : 0 ≤ G) (hW : 0 ≤ W)
    (hKsmall : K ≤ b / heightQuarterRoot N) (hGsmall : G ≤ b / heightQuarterRoot N)
    (hWsmall : W ≤ 8 * inputSmallLog N * b) :
    Real.sqrt (K * W) + 2 * G ≤
      ((rationalParameters (inputSmallLog N)).tau : ℝ) *
        ((rationalParameters (inputSmallLog N)).theta : ℝ) * b / (integerParameters N).M := by
  have helltwo : (2 : ℝ) ≤ inputSmallLog N := by
    have htwo : 2 ≤ (2 : ℕ) ^ 1000 := by
      simpa only [pow_one] using pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by decide : 1 ≤ 1000)
    exact_mod_cast htwo.trans hell
  have hroot := band_root_slack helltwo (Real.sqrt_nonneg _)
    (fourth_root_polynomial_slack (by linarith) (inputHeight_polynomial_slack N hN hell)
      (Real.sqrt_nonneg _) (heightQuarterRoot_fourth_power N))
    (Nat.cast_nonneg (integerParameters N).M) (computed_branching_fourth_power_le_quarterRoot N)
  have hM : (1 : ℝ) ≤ (integerParameters N).M := by
    exact_mod_cast (Nat.one_le_two_pow (n := heightExponent N / 20))
  have h := nonbad_band_numerical_bound helltwo hM hb hroot hK hG hW hKsmall hGsmall hWsmall
  simpa only [rationalParameters, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_natCast] using h

end EditApproximation

end OAI
