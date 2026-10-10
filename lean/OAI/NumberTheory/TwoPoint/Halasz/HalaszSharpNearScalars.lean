import OAI.NumberTheory.TwoPoint.Halasz.HalaszCenteredEnergy

namespace OAI

/-! Scalar bounds for the near-center argument with a renormalized
typical prefix. Its exceptional-density contribution is squared. -/

namespace TwoPointCorrelations

lemma halasz_sharp_near_scalar (C₁ C₂ D L M R : ℝ)
    (hL : 1 ≤ L) :
    50 * Real.pi * (C₁ * (Real.exp (-M / 2) + Real.log L / L) + C₂ * R) ^ 2 +
      100 * L ^ (1/16:ℝ) * (D * L ^ (-3/50:ℝ)) ^ 2 ≤
      (600 * Real.pi * C₁ ^ 2 + 300 * Real.pi * C₂ ^ 2 + 100 * D ^ 2) *
        (R ^ 2 + Real.exp (-M) + L ^ (-1/32:ℝ)) := by
  have hL0 : 0 < L := by linarith
  have he : Real.exp (-M / 2) ^ 2 = Real.exp (-M) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hr : (Real.log L / L) ^ 2 ≤ 2 * L ^ (-1/32:ℝ) := by
    apply (halasz_log_error_square L hL).trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (-1/(16:ℝ)) ≤ -1/32))
      (by norm_num)
  have hs : (C₁ * (Real.exp (-M / 2) + Real.log L / L) + C₂ * R) ^ 2 ≤
      3 * C₁ ^ 2 * Real.exp (-M) +
      6 * C₁ ^ 2 * L ^ (-1/32:ℝ) + 3 * C₂ ^ 2 * R ^ 2 := by
    have hh : (C₁ * (Real.exp (-M / 2) + Real.log L / L) + C₂ * R) ^ 2 ≤
        3 * (C₁ * Real.exp (-M / 2)) ^ 2 +
        3 * (C₁ * (Real.log L / L)) ^ 2 + 3 * (C₂ * R) ^ 2 := by
      nlinarith [sq_nonneg (C₁ * Real.exp (-M / 2) - C₁ * (Real.log L / L)),
        sq_nonneg (C₁ * Real.exp (-M / 2) - C₂ * R),
        sq_nonneg (C₁ * (Real.log L / L) - C₂ * R)]
    have hh' := mul_le_mul_of_nonneg_left hr (show 0 ≤ 3 * C₁ ^ 2 by positivity)
    simp only [mul_pow, he] at hh
    nlinarith
  have hpow : L ^ (1/16:ℝ) * (D * L ^ (-3/50:ℝ)) ^ 2 ≤
      D ^ 2 * L ^ (-1/32:ℝ) := by
    have hp : L ^ (1/16:ℝ) * (L ^ (-3/50:ℝ)) ^ 2 = L ^ (-23/400:ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le, ← Real.rpow_add hL0]
      norm_num
    calc
      _ = D ^ 2 * (L ^ (1/16:ℝ) * (L ^ (-3/50:ℝ)) ^ 2) := by ring
      _ = D ^ 2 * L ^ (-23/400:ℝ) := by rw [hp]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL (by norm_num)) (sq_nonneg D)
  have hs' := mul_le_mul_of_nonneg_left hs (show 0 ≤ 50 * Real.pi by positivity)
  have hp' := mul_le_mul_of_nonneg_left hpow (show (0:ℝ) ≤ 100 by norm_num)
  have hR : 0 ≤ R ^ 2 := sq_nonneg R
  have hE : 0 ≤ Real.exp (-M) := (Real.exp_pos _).le
  have hP : 0 ≤ L ^ (-1/32:ℝ) := Real.rpow_nonneg hL0.le _
  have h₁ : 0 ≤ Real.pi * C₁ ^ 2 := by positivity
  have h₂ : 0 ≤ Real.pi * C₂ ^ 2 := by positivity
  have h₃ : 0 ≤ D ^ 2 := sq_nonneg D
  nlinarith [mul_nonneg h₁ hR, mul_nonneg h₁ hE, mul_nonneg h₁ hP,
    mul_nonneg h₂ hR, mul_nonneg h₂ hE, mul_nonneg h₂ hP,
    mul_nonneg h₃ hR, mul_nonneg h₃ hE]

end TwoPointCorrelations

end OAI
