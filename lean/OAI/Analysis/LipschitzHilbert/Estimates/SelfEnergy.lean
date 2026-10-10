import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

namespace OAI

/-! Removing the dual coefficient norm from the self-pairing estimate. -/

noncomputable section
open scoped ENNReal

namespace LipschitzHilbert

theorem energy_le_of_sqrt_self {B A D : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (h : ENNReal.ofReal B ≤ ENNReal.ofReal A ^ (1/2:ℝ) *
      ENNReal.ofReal (D * B) ^ (1/2:ℝ)) : B ≤ A * D := by
  have hs := ENNReal.rpow_le_rpow h (by norm_num : (0:ℝ) ≤ 2)
  have hsq (x : ℝ≥0∞) : (x^(1/2:ℝ))^2 = x := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  simp only [ENNReal.rpow_two, mul_pow, hsq] at hs
  have ht := ENNReal.toReal_mono (by finiteness) hs
  simp only [ENNReal.toReal_pow, ENNReal.toReal_ofReal hB, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hA, ENNReal.toReal_ofReal (mul_nonneg hD hB)] at ht
  by_cases hz : B = 0
  · rw [hz]
    exact mul_nonneg hA hD
  · have hp : 0 < B := lt_of_le_of_ne hB (Ne.symm hz)
    nlinarith

end LipschitzHilbert

end

end OAI
