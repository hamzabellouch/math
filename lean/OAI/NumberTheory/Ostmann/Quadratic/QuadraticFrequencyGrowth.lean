import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallCorrectionGrowth

namespace OAI

/-! # A uniform current-exponent bound over all frequency blocks -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_frequency_root_power {ξ : ℝ} {B K : ℕ}
    (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) (hB : 0 < B) (hBK : B ≤ K) :
    (((2 * B : ℕ) : ℝ) ^ ξ) / Real.sqrt B ≤ 4 * (K : ℝ) ^ (ξ - 1 / 2) := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hpow := Real.rpow_le_rpow hBr.le (show (B : ℝ) ≤ K by exact_mod_cast hBK)
    (show 0 ≤ ξ - 1 / 2 by linarith)
  have htwo : (2 : ℝ) ^ ξ ≤ 4 := by
    apply (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hξ').trans_eq
    norm_num
  calc
    _ = (2 : ℝ) ^ ξ * (B : ℝ) ^ (ξ - 1 / 2) := by
      rw [Nat.cast_mul, Nat.cast_ofNat, Real.mul_rpow (by norm_num) hBr.le,
        Real.rpow_sub hBr, ← Real.sqrt_eq_rpow]
      ring
    _ ≤ _ := mul_le_mul htwo hpow (by positivity) (by norm_num)

theorem quadratic_frequency_power_cost {ε : ℝ} (hε : 0 ≤ ε) {B N K R : ℕ}
    (hBK : B ≤ K) (hNR : N ≤ R) :
    ((((2 * B : ℕ) : ℝ) * (2 * N : ℕ)) ^ ε) ≤
      (4 * (K : ℝ) * R) ^ ε := by
  apply Real.rpow_le_rpow (by positivity) _ hε
  have hh := mul_le_mul (show (B : ℝ) ≤ K by exact_mod_cast hBK)
    (show (N : ℝ) ≤ R by exact_mod_cast hNR) (Nat.cast_nonneg N) (Nat.cast_nonneg K)
  push_cast
  nlinarith

theorem quadratic_correction_growth_uniform {C ε ξ M : ℝ}
    (hC : 0 ≤ C) (hε : 0 ≤ ε) (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) (hM : 0 < M)
    {e B N K R : ℕ} (he : 0 < e) (hB : 0 < B) (hBK : B ≤ K) (hNR : N ≤ R)
    (v w : ℕ → ℂ) :
    quadraticCorrectionGrowthScale C ε ξ M e B N v w ≤
      10 * C * (4 * (K : ℝ) * R) ^ ε *
        (M + Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2)) *
          (Real.sqrt (quadraticDivisorMoment (2 * N) v) *
            Real.sqrt (quadraticDivisorMoment (2 * N) w)) := by
  have heR : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hdiv : M / e ≤ M := div_le_self hM.le heR
  have hroot : Real.sqrt (2 * (M / e)) ≤ 2 * Real.sqrt M := by
    have hs := Real.sq_sqrt (show 0 ≤ 2 * (M / e) by positivity)
    have hsM := Real.sq_sqrt hM.le
    have hs₀ := Real.sqrt_nonneg (2 * (M / e))
    have hsM₀ := Real.sqrt_nonneg M
    nlinarith
  have hp := quadratic_frequency_root_power hξ hξ' hB hBK
  have hinner : 2 * (M / e) + Real.sqrt (2 * (M / e)) / Real.sqrt B * ((2 * B : ℕ) : ℝ) ^ ξ ≤
      10 * (M + Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2)) := by
    calc
      _ = 2 * (M / e) + Real.sqrt (2 * (M / e)) *
          ((((2 * B : ℕ) : ℝ) ^ ξ) / Real.sqrt B) := by ring
      _ ≤ 2 * M + (2 * Real.sqrt M) * (4 * (K : ℝ) ^ (ξ - 1 / 2)) :=
        add_le_add (by linarith) (mul_le_mul hroot hp (by positivity) (by positivity))
      _ ≤ _ := by nlinarith [mul_nonneg (Real.sqrt_nonneg M) (Real.rpow_nonneg (Nat.cast_nonneg K) (ξ - 1 / 2))]
  have hfactor := mul_le_mul_of_nonneg_left (quadratic_frequency_power_cost hε hBK hNR) hC
  unfold quadraticCorrectionGrowthScale
  apply le_trans (mul_le_mul_of_nonneg_right
    (mul_le_mul hfactor hinner (by positivity) (by positivity)) (by positivity))
  apply le_of_eq
  ring

theorem quadratic_small_growth_uniform {C ε ξ M A : ℝ}
    (hC : 0 ≤ C) (hε : 0 ≤ ε) (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) (_hM : 0 ≤ M) (hA : 0 ≤ A)
    {B N K R : ℕ} (hB : 0 < B) (hBK : B ≤ K) (hNR : N ≤ R)
    (v w : ℕ → ℂ) :
    quadraticSmallCorrectionGrowthScale C ε ξ M A B N v w ≤
      4 * C * (4 * (K : ℝ) * R) ^ ε *
        (Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2) + A * R) *
          (Real.sqrt (quadraticDivisorMoment (2 * N) v) *
            Real.sqrt (quadraticDivisorMoment (2 * N) w)) := by
  have hp := quadratic_frequency_root_power hξ hξ' hB hBK
  have hinner : Real.sqrt M / Real.sqrt B * ((2 * B : ℕ) : ℝ) ^ ξ + A * (2 * N) ≤
      4 * (Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2) + A * R) := by
    calc
      _ = Real.sqrt M * ((((2 * B : ℕ) : ℝ) ^ ξ) / Real.sqrt B) + A * (2 * N) := by ring
      _ ≤ Real.sqrt M * (4 * (K : ℝ) ^ (ξ - 1 / 2)) + A * (2 * R) :=
        add_le_add (mul_le_mul_of_nonneg_left hp (Real.sqrt_nonneg M)) (by gcongr)
      _ ≤ _ := by nlinarith [mul_nonneg hA (Nat.cast_nonneg R)]
  have hfactor := mul_le_mul_of_nonneg_left (quadratic_frequency_power_cost hε hBK hNR) hC
  unfold quadraticSmallCorrectionGrowthScale
  apply le_trans (mul_le_mul_of_nonneg_right
    (mul_le_mul hfactor hinner (by positivity) (by positivity)) (by positivity))
  apply le_of_eq
  ring

end Ostmann

end OAI
