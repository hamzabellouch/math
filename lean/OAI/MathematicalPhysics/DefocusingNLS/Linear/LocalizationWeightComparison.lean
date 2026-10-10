import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingSobolevWeights

namespace OAI

/-! # Exact expanding-weight comparisons for localization

The high-order localized norm produces a harmless additional zero-frequency
term. It is absorbed by the regularized low-order part of the exact Y_L weight.
-/

namespace DefocusingNLS

private theorem localization_high_bessel_le (k r : ℝ) (hk : 0 ≤ k) (hr : 0 ≤ r) :
    (1 + r ^ 2) ^ k ≤ 2 ^ k * (1 + r ^ (2 * k)) := by
  have hbase : 1 + r ^ 2 ≤ 2 * max 1 (r ^ 2) := by
    linarith [le_max_left (1 : ℝ) (r ^ 2), le_max_right (1 : ℝ) (r ^ 2)]
  have hpow : (r ^ 2) ^ k = r ^ (2 * k) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr]
    norm_num
  calc
    _ ≤ (2 * max 1 (r ^ 2)) ^ k := Real.rpow_le_rpow (by positivity) hbase hk
    _ = 2 ^ k * max 1 (r ^ (2 * k)) := by
      rw [Real.mul_rpow (by norm_num) (by positivity),
        Real.rpow_max (by norm_num) (by positivity) hk, Real.one_rpow, hpow]
    _ ≤ _ := mul_le_mul_of_nonneg_left (max_le
      (le_add_of_nonneg_right (by positivity)) (le_add_of_nonneg_left zero_le_one)) (by positivity)

theorem localization_low_weight_le (a k L : ℝ) (hL : 1 ≤ L) (n : frequencyLattice) :
    L ^ (2 * a) * (1 + ‖n‖ ^ 2) ^ (6 - a) ≤ expandingSobolevWeightSq a k L n := by
  unfold expandingSobolevWeightSq
  exact le_add_of_nonneg_right (by positivity)

/-- The extra high-order Bessel term is uniformly absorbed by the exact Y_L weight. -/
theorem localization_high_weight_le (a k L : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hk : 8 < k) (hL : 1 ≤ L) (n : frequencyLattice) :
    L ^ (12 - 2 * k) * (1 + ‖n‖ ^ 2) ^ k ≤
      2 ^ k * expandingSobolevWeightSq a k L n := by
  have hscale : L ^ (12 - 2 * k) ≤ L ^ (2 * a) :=
    Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hlow : 1 ≤ (1 + ‖n‖ ^ 2) ^ (6 - a) :=
    Real.one_le_rpow (by linarith [sq_nonneg ‖n‖]) (by linarith)
  have hconstant : L ^ (12 - 2 * k) ≤ L ^ (2 * a) * (1 + ‖n‖ ^ 2) ^ (6 - a) :=
    hscale.trans (le_mul_of_one_le_right (by positivity) hlow)
  calc
    _ ≤ L ^ (12 - 2 * k) * (2 ^ k * (1 + ‖n‖ ^ (2 * k))) :=
      mul_le_mul_of_nonneg_left (localization_high_bessel_le k ‖n‖ (by linarith) (norm_nonneg n))
        (by positivity)
    _ = 2 ^ k * (L ^ (12 - 2 * k) + L ^ (12 - 2 * k) * ‖n‖ ^ (2 * k)) := by ring
    _ ≤ 2 ^ k * (L ^ (2 * a) * (1 + ‖n‖ ^ 2) ^ (6 - a) +
        L ^ (12 - 2 * k) * ‖n‖ ^ (2 * k)) := by gcongr
    _ = _ := rfl

end DefocusingNLS

end OAI
