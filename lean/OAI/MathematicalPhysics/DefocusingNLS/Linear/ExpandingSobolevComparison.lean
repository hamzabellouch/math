import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingWeightIdentification

namespace OAI

/-! # The fixed expanding norm is equivalent to the usual Sobolev norm

The weight comparison at radius one identifies the expanding-space
solution with the standard Sobolev flow.
-/

namespace DefocusingNLS

theorem expandingSobolevWeightSq_one_le_standard (a k : ℝ)
    (ha : 0 < a) (hk : 8 < k) (n : frequencyLattice) :
    expandingSobolevWeightSq a k 1 n ≤ 2 * (1 + ‖n‖ ^ 2) ^ k := by
  have hpow : ‖n‖ ^ (2 * k) = (‖n‖ ^ 2) ^ k := by
    simpa using Real.rpow_natCast_mul (norm_nonneg n) 2 k
  have hlo : (1 + ‖n‖ ^ 2) ^ (6 - a) ≤ (1 + ‖n‖ ^ 2) ^ k :=
    Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖n‖]) (by linarith)
  have hhi : (‖n‖ ^ 2) ^ k ≤ (1 + ‖n‖ ^ 2) ^ k :=
    Real.rpow_le_rpow (sq_nonneg _) (by linarith) (by linarith)
  simp only [expandingSobolevWeightSq, Real.one_rpow, one_mul, hpow]
  linarith

theorem standard_le_expandingSobolevWeightSq_one (a k : ℝ)
    (ha1 : a < 1) (hk : 8 < k) (n : frequencyLattice) :
    (1 + ‖n‖ ^ 2) ^ k ≤ 2 ^ k * expandingSobolevWeightSq a k 1 n := by
  have hpow : ‖n‖ ^ (2 * k) = (‖n‖ ^ 2) ^ k := by
    simpa using Real.rpow_natCast_mul (norm_nonneg n) 2 k
  have hnonneg : 0 ≤ (1 + ‖n‖ ^ 2) ^ (6 - a) := by positivity
  simp only [expandingSobolevWeightSq, Real.one_rpow, one_mul, hpow]
  by_cases hn : ‖n‖ ≤ 1
  · have hn2 : ‖n‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg n]
    have hstd : (1 + ‖n‖ ^ 2) ^ k ≤ (2 : ℝ) ^ k :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
    have hlo : 1 ≤ (1 + ‖n‖ ^ 2) ^ (6 - a) :=
      Real.one_le_rpow (by nlinarith [sq_nonneg ‖n‖]) (by linarith)
    exact hstd.trans (le_mul_of_one_le_right (by positivity)
      (hlo.trans (le_add_of_nonneg_right (by positivity))))
  · have hn2 : 1 ≤ ‖n‖ ^ 2 := by nlinarith [norm_nonneg n]
    calc
      (1 + ‖n‖ ^ 2) ^ k ≤ (2 * ‖n‖ ^ 2) ^ k :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
      _ = 2 ^ k * (‖n‖ ^ 2) ^ k := Real.mul_rpow (by norm_num) (sq_nonneg _)
      _ ≤ 2 ^ k * ((1 + ‖n‖ ^ 2) ^ (6 - a) + (‖n‖ ^ 2) ^ k) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hnonneg) (by positivity)

private theorem sqrt_standard_power (k : ℝ) (n : frequencyLattice) :
    Real.sqrt ((1 + ‖n‖ ^ 2) ^ k) = (1 + ‖n‖ ^ 2) ^ (k / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

theorem expandingSobolevWeight_one_le_standard (a k : ℝ)
    (ha : 0 < a) (hk : 8 < k) (n : frequencyLattice) :
    expandingSobolevWeight a k 1 n ≤
      ((2 * Real.pi) ^ 6 * Real.sqrt 2) * (1 + ‖n‖ ^ 2) ^ (k / 2) := by
  have h := Real.sqrt_le_sqrt (expandingSobolevWeightSq_one_le_standard a k ha hk n)
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), sqrt_standard_power] at h
  exact (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (by
    ring)

theorem standard_le_expandingSobolevWeight_one (a k : ℝ)
    (ha1 : a < 1) (hk : 8 < k) (n : frequencyLattice) :
    (1 + ‖n‖ ^ 2) ^ (k / 2) ≤
      ((2 * Real.pi) ^ 6)⁻¹ * Real.sqrt (2 ^ k) * expandingSobolevWeight a k 1 n := by
  have h := Real.sqrt_le_sqrt (standard_le_expandingSobolevWeightSq_one a k ha1 hk n)
  rw [sqrt_standard_power, Real.sqrt_mul (by positivity)] at h
  calc
    _ ≤ Real.sqrt (2 ^ k) * Real.sqrt (expandingSobolevWeightSq a k 1 n) := h
    _ = _ := by
      unfold expandingSobolevWeight
      have hp : (2 * Real.pi) ^ 6 ≠ 0 := by positivity
      field_simp

end DefocusingNLS

end OAI
