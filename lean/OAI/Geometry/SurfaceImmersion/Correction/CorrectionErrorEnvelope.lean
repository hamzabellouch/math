import OAI.Geometry.SurfaceImmersion.Correction.CorrectionScaleAlgebra

namespace OAI

/-! The six normalized errors satisfy the common all-order recurrence bound. -/
noncomputable section

namespace ClosedSurfaceR4.ExactCorrection

/-- A common envelope for the six powers in the exact-correction error table.
The coefficients of both high-derivative terms remain linear. -/
theorem normalized_error_envelope {t k B C P Q R : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hk : 10 ≤ k)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hR : 0 ≤ R) :
    P * (B * t ^ ((18 * k + 8) / 5) + C * t ^ ((38 * k + 28) / 5)) +
      Q * (t ^ ((13 * k + 8) / 5) + t ^ ((3 * k - 18) / 5)) +
      R * (B * t ^ ((13 * k + 8) / 5) + C * t ^ ((33 * k + 28) / 5)) ≤
      (P + 2 * Q + R) * (1 + B + C) * t ^ (1 / 5 : ℝ) := by
  obtain ⟨h1, h2, h3, h4, _, h6⟩ := error_exponents_ge_common hk
  have b1 := Real.rpow_le_rpow_of_exponent_ge ht ht1 h1
  have b2 := Real.rpow_le_rpow_of_exponent_ge ht ht1 h2
  have b3 := Real.rpow_le_rpow_of_exponent_ge ht ht1 h3
  have b4 := Real.rpow_le_rpow_of_exponent_ge ht ht1 h4
  have b6 := Real.rpow_le_rpow_of_exponent_ge ht ht1 h6
  calc
    _ ≤ P * (B * t ^ (1 / 5 : ℝ) + C * t ^ (1 / 5 : ℝ)) +
        Q * (t ^ (1 / 5 : ℝ) + t ^ (1 / 5 : ℝ)) +
        R * (B * t ^ (1 / 5 : ℝ) + C * t ^ (1 / 5 : ℝ)) := by gcongr
    _ = (P * (B + C) + 2 * Q + R * (B + C)) * t ^ (1 / 5 : ℝ) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht.le _)
      nlinarith [mul_nonneg hQ hB, mul_nonneg hQ hC]

end ClosedSurfaceR4.ExactCorrection

end

end OAI
