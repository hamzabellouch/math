import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace OAI

/-! # Exact exponential cardinality bounds from a box volume ratio -/

namespace PolycyclicRecognition

open scoped ENNReal

/-- The fixed determinant and coordinate-cube factors cancel exactly.
This includes zero-dimensional ideals. -/
theorem card_le_of_exponential_box_volume {n d : ℕ} {D R p q : ℝ}
    (hD : 0 < D) (hR : 0 ≤ R)
    (h : (n : ℝ≥0∞) *
        (ENNReal.ofReal D * ENNReal.ofReal (Real.exp q) * ENNReal.ofReal 2 ^ d) ≤
      ENNReal.ofReal D * ENNReal.ofReal (Real.exp p) * ENNReal.ofReal (2 * R) ^ d) :
    (n : ℝ) ≤ R ^ d * Real.exp (p - q) := by
  have htop : ENNReal.ofReal D * ENNReal.ofReal (Real.exp p) *
      ENNReal.ofReal (2 * R) ^ d ≠ ⊤ := by finiteness
  have ht := ENNReal.toReal_mono htop h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hD.le, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 2 by norm_num),
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hR)] at ht
  have hf : 0 < D * Real.exp q * 2 ^ d := by positivity
  apply (mul_le_mul_iff_left₀ hf).mp
  calc
    (n : ℝ) * (D * Real.exp q * 2 ^ d) ≤ D * Real.exp p * (2 * R) ^ d := ht
    _ = (R ^ d * Real.exp (p - q)) * (D * Real.exp q * 2 ^ d) := by
      rw [mul_pow, Real.exp_sub]
      field_simp

end PolycyclicRecognition

end OAI
