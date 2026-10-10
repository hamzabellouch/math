import Mathlib.Analysis.SpecialFunctions.Pow.Real
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticComparisonEnvelope

namespace OAI

/-! # The numerical small-kernel error and the literal exponent factors -/

namespace Ostmann

theorem quadratic_small_kernel_envelope {M N B P Y D : ℝ}
    (hM : 0 < M) (hN : 0 ≤ N) (hB : 0 < B) (hP : 1 ≤ P) (hY : 0 ≤ Y)
    (hD : 0 ≤ D) (hcut : Real.sqrt M / (Real.sqrt B * P) ≤ D) :
    (Real.sqrt M / (Real.sqrt B * Real.sqrt P)) *
      (Y + Real.sqrt (Y * N) + N / Real.sqrt P) ≤
        2 * (Real.sqrt M / Real.sqrt B * Y + D * N) := by
  have hP₀ : 0 < P := lt_of_lt_of_le zero_lt_one hP
  let R := Real.sqrt M / (Real.sqrt B * Real.sqrt P)
  let A := Real.sqrt M / Real.sqrt B * Y
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hsp : Real.sqrt P ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hP₀)
  have hsb : Real.sqrt B ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hB)
  have hsp₁ : 1 ≤ Real.sqrt P := (Real.le_sqrt (by norm_num) hP₀.le).2 (by simpa using hP)
  have hfirst : R * Y ≤ A := by
    dsimp [R, A]
    apply mul_le_mul_of_nonneg_right _ hY
    exact div_le_div_of_nonneg_left (Real.sqrt_nonneg M) (Real.sqrt_pos.2 hB)
      (by nlinarith [Real.sqrt_nonneg B])
  have hthird : R * (N / Real.sqrt P) ≤ D * N := by
    calc
      _ = (Real.sqrt M / (Real.sqrt B * P)) * N := by
        dsimp [R]
        rw [div_mul_div_comm]
        have hs : Real.sqrt B * Real.sqrt P * Real.sqrt P = Real.sqrt B * P := by
          rw [mul_assoc, ← pow_two, Real.sq_sqrt hP₀.le]
        rw [hs]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcut hN
  have hcrosssq : (R * Real.sqrt (Y * N)) ^ 2 ≤ A * (D * N) := by
    calc
      _ = A * ((Real.sqrt M / (Real.sqrt B * P)) * N) := by
        rw [mul_pow, Real.sq_sqrt (mul_nonneg hY hN)]
        dsimp [R, A]
        field_simp
        nlinarith only [congrArg (fun z : ℝ => z * Y * N) (Real.sq_sqrt hP₀.le)]
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcut hN) hA
  have hcross : R * Real.sqrt (Y * N) ≤ (A + D * N) / 2 := by
    have hc : 0 ≤ R * Real.sqrt (Y * N) := mul_nonneg hR (Real.sqrt_nonneg _)
    nlinarith [sq_nonneg (A - D * N), mul_nonneg hD hN]
  change R * (Y + Real.sqrt (Y * N) + N / Real.sqrt P) ≤ 2 * (A + D * N)
  nlinarith

theorem quadratic_comparison_power_envelope {M N B P : ℝ} (ξ : ℝ)
    (hM : 0 < M) (hN : 0 < N) (hB : 0 < B) (hP : 1 ≤ P) :
    (M / N * Real.sqrt P * min 1 (N / (Real.sqrt M * Real.sqrt B * P))) *
      (B ^ ξ + Real.sqrt (B ^ ξ * N) + N / Real.sqrt P) ≤
        2 * (M + Real.sqrt M * B ^ (ξ - 1 / 2)) := by
  have h := quadratic_comparison_envelope hM hN hB hP (Real.rpow_nonneg hB.le ξ)
  rw [Real.rpow_sub hB, ← Real.sqrt_eq_rpow]
  convert h using 1
  ring

theorem quadratic_small_kernel_power_envelope {M N B P D : ℝ} (ξ : ℝ)
    (hM : 0 < M) (hN : 0 ≤ N) (hB : 0 < B) (hP : 1 ≤ P)
    (hD : 0 ≤ D) (hcut : Real.sqrt M / (Real.sqrt B * P) ≤ D) :
    (Real.sqrt M / (Real.sqrt B * Real.sqrt P)) *
      (B ^ ξ + Real.sqrt (B ^ ξ * N) + N / Real.sqrt P) ≤
        2 * (Real.sqrt M * B ^ (ξ - 1 / 2) + D * N) := by
  have h := quadratic_small_kernel_envelope hM hN hB hP (Real.rpow_nonneg hB.le ξ) hD hcut
  rw [Real.rpow_sub hB, ← Real.sqrt_eq_rpow]
  convert h using 1
  ring

end Ostmann

end OAI
