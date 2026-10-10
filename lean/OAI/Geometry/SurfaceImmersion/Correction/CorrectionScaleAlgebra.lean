import OAI.Geometry.SurfaceImmersion.Correction.ExactCorrectionRecurrence
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

/-! Exact scale arithmetic in the normalized metric-error estimate. -/
noncomputable section

namespace ClosedSurfaceR4.ExactCorrection

lemma scale_quotient_product {t : ℝ} (ht : 0 < t) (a b c : ℝ) :
    (t ^ a * t ^ b) / t ^ c = t ^ (a + b - c) := by
  rw [← Real.rpow_add ht, Real.rpow_sub ht]

lemma scale_ratio_power {t : ℝ} (ht : 0 < t) (a b c d e : ℝ) :
    (t ^ a * (t ^ b / t ^ c) ^ d) / (t ^ e) ^ (2 : ℕ) =
      t ^ (a + (b - c) * d - 2 * e) := by
  rw [← Real.rpow_sub ht, ← Real.rpow_mul ht.le]
  rw [← Real.rpow_natCast (t ^ e) 2, ← Real.rpow_mul ht.le]
  rw [scale_quotient_product ht]
  congr 1
  ring

lemma scale_ratio_power_linear {t : ℝ} (ht : 0 < t) (a b d e : ℝ) :
    (t ^ a * (t ^ b / t) ^ d) / (t ^ e) ^ (2 : ℕ) =
      t ^ (a + (b - 1) * d - 2 * e) := by
  simpa only [Real.rpow_one] using scale_ratio_power ht a b 1 d e

lemma scale_cubic_quotient {t : ℝ} (ht : 0 < t) (a b c : ℝ) :
    ((t ^ a) ^ (3 : ℕ) / t ^ b) / (t ^ c) ^ (2 : ℕ) =
      t ^ (3 * a - b - 2 * c) := by
  rw [← Real.rpow_natCast (t ^ a) 3, ← Real.rpow_mul ht.le]
  rw [← Real.rpow_natCast (t ^ c) 2, ← Real.rpow_mul ht.le]
  rw [← Real.rpow_sub ht, ← Real.rpow_sub ht]
  congr 1
  ring

/-- The six exponents remain above the common exponent used in the
all-order recurrence, including the smaller next-block amplitude. -/
theorem error_exponents_ge_common {k : ℝ} (hk : 10 ≤ k) :
    (1 / 5 : ℝ) ≤ (13 * k + 8) / 5 ∧
    (1 / 5 : ℝ) ≤ (3 * k - 18) / 5 ∧
    (1 / 5 : ℝ) ≤ (18 * k + 8) / 5 ∧
    (1 / 5 : ℝ) ≤ (38 * k + 28) / 5 ∧
    (1 / 5 : ℝ) ≤ (13 * k + 8) / 5 ∧
    (1 / 5 : ℝ) ≤ (33 * k + 28) / 5 := by
  constructor <;> [linarith; skip]
  constructor <;> [linarith; skip]
  constructor <;> [linarith; skip]
  constructor <;> [linarith; skip]
  constructor <;> linarith

/-- Exact normalization of the small-mode error term. -/
theorem normalized_mode_scale {t : ℝ} (ht : 0 < t) (k : ℝ) :
    (t ^ k * (t ^ (6 / 5 : ℝ) / t ^ (11 / 10 : ℝ)) ^ (40 * (k + 1))) /
      (t ^ ((6 / 5 : ℝ) * (k + 1))) ^ (2 : ℕ) = t ^ ((13 * k + 8) / 5) := by
  rw [scale_ratio_power ht]
  congr 1
  ring

/-- Exact normalization of the cubic error term. -/
theorem normalized_cubic_scale {t : ℝ} (ht : 0 < t) (k : ℝ) :
    ((t ^ k) ^ (3 : ℕ) / t ^ (6 / 5 : ℝ)) /
      (t ^ ((6 / 5 : ℝ) * (k + 1))) ^ (2 : ℕ) = t ^ ((3 * k - 18) / 5) := by
  rw [scale_cubic_quotient ht]
  congr 1
  ring

/-- The two powers in the smoothing defect, before their coefficients. -/
theorem normalized_defect_tail_scales {t : ℝ} (ht : 0 < t) (k : ℝ) :
    ((t ^ k) ^ (2 : ℕ) * (t ^ (11 / 10 : ℝ) / t) ^ (40 * (k + 1))) /
        (t ^ ((6 / 5 : ℝ) * (k + 1))) ^ (2 : ℕ) = t ^ ((18 * k + 8) / 5) ∧
    ((t ^ k) ^ (2 : ℕ) * (t ^ (6 / 5 : ℝ) / t) ^ (40 * (k + 1))) /
        (t ^ ((6 / 5 : ℝ) * (k + 1))) ^ (2 : ℕ) = t ^ ((38 * k + 28) / 5) := by
  rw [← Real.rpow_natCast (t ^ k) 2, ← Real.rpow_mul ht.le]
  constructor
  · rw [scale_ratio_power_linear ht]
    congr 1
    ring
  · rw [scale_ratio_power_linear ht]
    congr 1
    ring

/-- The two powers in the bilinear cross term, before their coefficients. -/
theorem normalized_cross_tail_scales {t : ℝ} (ht : 0 < t) (k : ℝ) :
    (t ^ k * (t ^ (11 / 10 : ℝ) / t) ^ (40 * (k + 1))) /
        (t ^ ((6 / 5 : ℝ) * (k + 1))) ^ (2 : ℕ) = t ^ ((13 * k + 8) / 5) ∧
    (t ^ k * (t ^ (6 / 5 : ℝ) / t) ^ (40 * (k + 1))) /
        (t ^ ((6 / 5 : ℝ) * (k + 1))) ^ (2 : ℕ) = t ^ ((33 * k + 28) / 5) := by
  constructor
  · rw [scale_ratio_power_linear ht]
    congr 1
    ring
  · rw [scale_ratio_power_linear ht]
    congr 1
    ring

end ClosedSurfaceR4.ExactCorrection

end

end OAI
