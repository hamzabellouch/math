import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingOrderedPhysicalSymbol

namespace OAI

/-! # Lower-order frequency weight controlled by mass and top derivatives -/

namespace DefocusingNLS

theorem lowerFrequencyWeight_le_mass_top (x r s : ℝ) (N : ℕ)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hr : 0 ≤ r) (hs : 0 ≤ s) (hsN : s ≤ N) :
    (x + r ^ 2) ^ s ≤ (2 : ℝ) ^ N * (1 + r ^ (2 * N)) := by
  by_cases hr1 : r ≤ 1
  · have hr2 : r ^ 2 ≤ 1 := by nlinarith
    calc
      _ ≤ (2 : ℝ) ^ s := Real.rpow_le_rpow (by positivity) (by linarith) hs
      _ ≤ (2 : ℝ) ^ (N : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hsN
      _ = (2 : ℝ) ^ N := Real.rpow_natCast 2 N
      _ ≤ _ := le_mul_of_one_le_right (by positivity)
        (le_add_of_nonneg_right (pow_nonneg hr _))
  · have hr1' : 1 ≤ r := (lt_of_not_ge hr1).le
    have hr2 : 1 ≤ r ^ 2 := by nlinarith
    calc
      _ ≤ (x + r ^ 2) ^ (N : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hsN
      _ = (x + r ^ 2) ^ N := Real.rpow_natCast _ N
      _ ≤ (2 * r ^ 2) ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
      _ = (2 : ℝ) ^ N * r ^ (2 * N) := by rw [mul_pow, ← pow_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by norm_num)) (by positivity)

theorem expandingLowerWeight_le_mass_top (a L : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < (N : ℝ)) (hL : 1 ≤ L)
    (n : frequencyLattice) :
    (L ^ (-2 : ℝ) + (‖n‖ / L) ^ 2) ^ (6 - a) ≤
      (2 : ℝ) ^ N * (1 + (‖n‖ / L) ^ (2 * N)) := by
  apply lowerFrequencyWeight_le_mass_top _ _ _ N
  · positivity
  · exact Real.rpow_le_one_of_one_le_of_nonpos hL (by norm_num)
  · exact div_nonneg (norm_nonneg _) (by linarith)
  · linarith
  · linarith

end DefocusingNLS

end OAI
