import OAI.Combinatorics.EditApproximation.Binary.BinaryOnlineParameters
import OAI.Combinatorics.EditApproximation.Refinement.ComputedCacheWords

namespace OAI

/-! The actual binary online constants fit the same polynomial word cap as
the normalized local cache. No input-probability or good-seed assumption is
used here. -/

namespace EditApproximation

private theorem online_parameter_width_cap (H B : ℕ) (hH : 64 ≤ H) (hB : B ≤ H) :
    5 * B + 1 ≤ H ^ 2 ∧ 4 * B + 1 ≤ H ^ 2 := by
  constructor <;> nlinarith

theorem computedBinaryOnlineParameters_caps (N : ℕ) (word : List Bool)
    (hvalue : bitWordValue word = inputSmallLog N)
    (hwidth : word.length ≤ Nat.size (inputSmallLog N)) (hH : 64 ≤ inputHeight N)
    (hpositive : 0 < bitWordValue word) :
    (BinaryFraction.onlineParametersWithWork word hpositive).1.1.width ≤ inputHeight N ^ 2 ∧
      (BinaryFraction.onlineParametersWithWork word hpositive).1.2.width ≤ inputHeight N ^ 2 ∧
      |(BinaryFraction.onlineParametersWithWork word hpositive).1.1.value| ≤
        ((inputHeight N ^ 5 : ℕ) : ℚ) ∧
      0 ≤ (BinaryFraction.onlineParametersWithWork word hpositive).1.2.value ∧
      (BinaryFraction.onlineParametersWithWork word hpositive).1.2.value ≤ 1 := by
  have hsmall : Nat.size (inputSmallLog N) ≤ inputHeight N :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (computed_smallLog_le_height N)
  have hw := BinaryFraction.onlineParametersWithWork_width word hpositive
    (Nat.size (inputSmallLog N)) hwidth
  have hr := BinaryFraction.onlineParametersWithWork_range word hpositive (inputHeight N)
    (by rw [hvalue]; exact computed_smallLog_le_height N)
  have hc := online_parameter_width_cap _ _ hH hsmall
  exact ⟨hw.1.trans hc.1, hw.2.trans hc.2, hr.1, hr.2⟩

theorem computedBinaryOnlineParameters_cost (N : ℕ) (word : List Bool)
    (hwidth : word.length ≤ Nat.size (inputSmallLog N)) (hH : 64 ≤ inputHeight N)
    (hpositive : 0 < bitWordValue word) :
    (BinaryFraction.onlineParametersWithWork word hpositive).2 ≤ inputHeight N ^ 8 := by
  have hsmall : Nat.size (inputSmallLog N) ≤ inputHeight N :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (computed_smallLog_le_height N)
  have hw : word.length ≤ inputHeight N := hwidth.trans hsmall
  have hc := BinaryFraction.onlineParametersWithWork_cost word hpositive (inputHeight N) hw
  have hbound (H : ℕ) (h : 64 ≤ H) :
      bitPowerBitBudget 5 H + bitPowerBitBudget 4 H + 2 ≤ H ^ 8 := by
    have h5 : 6 * (H + 1) + 1 ≤ 7 * H := by omega
    have h4 : 5 * (H + 1) + 1 ≤ 6 * H := by omega
    have hs5 := Nat.pow_le_pow_left h5 2
    have hs4 := Nat.pow_le_pow_left h4 2
    have hc : 5 * (200 * (6 * (H + 1) + 1) ^ 2) +
        4 * (200 * (5 * (H + 1) + 1) ^ 2) + 4 ≤ 100000 * H ^ 2 := by nlinarith
    have h6 : 100000 ≤ H ^ 6 := by
      exact (by norm_num : 100000 ≤ 64 ^ 6).trans (Nat.pow_le_pow_left h 6)
    change 1 + 5 * (200 * (6 * (H + 1) + 1) ^ 2) +
      (1 + 4 * (200 * (5 * (H + 1) + 1) ^ 2)) + 2 ≤ H ^ 8
    calc
      _ ≤ 100000 * H ^ 2 := by omega
      _ ≤ H ^ 6 * H ^ 2 := Nat.mul_le_mul_right _ h6
      _ = _ := by ring
  exact hc.trans (hbound _ hH)

end EditApproximation

end OAI
