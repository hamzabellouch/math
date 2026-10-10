import OAI.Combinatorics.EditApproximation.Binary.BinaryBandInputs
import OAI.Combinatorics.EditApproximation.Geometry.BandEnvelopes
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The dyadic envelope is found by a bounded sequence of exact Boolean
comparisons.  The scan starts at `2⁻ᴮ`, doubles at most `2B` times, and uses
the stored fraction width `B`; no real logarithm is evaluated. -/

namespace EditApproximation



theorem powerTwoWord_value (n : ℕ) : bitWordValue (powerTwoWord n) = 2 ^ n := by
  induction n with
  | zero => simp [powerTwoWord, bitWordValue]
  | succ n ih =>
    simp only [powerTwoWord, List.replicate_succ, List.cons_append, bitWordValue,
      Bool.toNat_false, zero_add] at *
    rw [ih, pow_succ]
    omega

theorem powerTwoWord_length (n : ℕ) : (powerTwoWord n).length = n + 1 := by
  simp [powerTwoWord]

namespace BinaryFraction



theorem inversePowerTwo_value (n : ℕ) : (inversePowerTwo n).value = (2 : ℚ) ^ (-(n : ℤ)) := by
  simp only [inversePowerTwo, value, SignedBinary.value, signedMagnitude, Bool.false_eq_true,
    ↓reduceIte, bitWordValue, Bool.toNat_true,
    Int.cast_natCast, powerTwoWord_value, Nat.cast_pow, Nat.cast_ofNat, zpow_neg, zpow_natCast]
  norm_num [one_div]

theorem inversePowerTwo_width (n : ℕ) : (inversePowerTwo n).width = n + 1 := by
  simp [inversePowerTwo, width, powerTwoWord_length]



theorem doubleFraction_value (a : BinaryFraction) : (doubleFraction a).value = 2 * a.value := by
  cases h : a.numerator.negative <;>
    simp [doubleFraction, value, SignedBinary.value, signedMagnitude, h, bitWordValue] <;> ring

theorem doubleFraction_width (a : BinaryFraction) : (doubleFraction a).width ≤ a.width + 1 := by
  unfold doubleFraction width
  simp only [List.length_cons]
  omega



private theorem dyadicCeiling_eq_of_bounds (r : ℚ) (e : ℤ) (hr : 0 < r)
    (hlower : (2 : ℚ) ^ (e - 1) < r) (hupper : r ≤ (2 : ℚ) ^ e) :
    rationalDyadicCeiling r = (2 : ℚ) ^ e := by
  have hl := (Int.zpow_lt_iff_lt_clog (by decide : 1 < 2) hr).mp hlower
  have hu := (Int.le_zpow_iff_clog_le (by decide : 1 < 2) hr).mp hupper
  have he : Int.clog 2 r = e := by omega
  rw [rationalDyadicCeiling, he]

theorem dyadicScanWithWork_value (a candidate : BinaryFraction) (n : ℕ) (e : ℤ)
    (ha : 0 < a.value) (hc : candidate.value = (2 : ℚ) ^ e)
    (hlower : (2 : ℚ) ^ (e - 1) < a.value)
    (hupper : a.value ≤ candidate.value * (2 : ℚ) ^ n) :
    (dyadicScanWithWork a candidate n).1.value = rationalDyadicCeiling a.value := by
  induction n generalizing candidate e with
  | zero =>
    simp only [pow_zero, mul_one] at hupper
    exact hc.trans (dyadicCeiling_eq_of_bounds a.value e ha hlower (hc ▸ hupper)).symm
  | succ n ih =>
    unfold dyadicScanWithWork
    dsimp only
    split_ifs with hlt
    · have hlt' := (ltWithWork_value candidate a).mp hlt
      have hc' : (doubleFraction candidate).value = (2 : ℚ) ^ (e + 1) := by
        rw [doubleFraction_value, hc, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_one]
        ring
      apply ih _ (e + 1) hc'
      · simpa only [add_sub_cancel_right, ← hc] using hlt'
      · rw [doubleFraction_value]
        simpa only [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hupper
    · have hupper' : a.value ≤ candidate.value :=
        le_of_not_gt (fun h => hlt ((ltWithWork_value candidate a).mpr h))
      exact hc.trans (dyadicCeiling_eq_of_bounds a.value e ha hlower (hc ▸ hupper')).symm

theorem dyadicScanWithWork_width (a candidate : BinaryFraction) (n : ℕ) :
    (dyadicScanWithWork a candidate n).1.width ≤ candidate.width + n := by
  induction n generalizing candidate with
  | zero => simp [dyadicScanWithWork]
  | succ n ih =>
    unfold dyadicScanWithWork
    dsimp only
    split_ifs
    · exact (ih _).trans (by have h := doubleFraction_width candidate; omega)
    · change candidate.width ≤ candidate.width + (n + 1)
      omega

theorem dyadicScanWithWork_cost (a candidate : BinaryFraction) (n W : ℕ)
    (ha : a.width ≤ W) (hc : candidate.width + n ≤ W) :
    (dyadicScanWithWork a candidate n).2 ≤ 1 + n * (1000 * (W + 1) ^ 2 + 2) := by
  induction n generalizing candidate with
  | zero => simp [dyadicScanWithWork]
  | succ n ih =>
    have hcmp := ltWithWork_cost candidate a W (by omega) ha
    have hdouble := doubleFraction_width candidate
    have hnext := ih (doubleFraction candidate) (by omega)
    unfold dyadicScanWithWork
    dsimp only
    split_ifs
    · rw [Nat.add_mul, Nat.one_mul]
      omega
    · have hp : 1000 * (W + 1) ^ 2 + 2 ≤ (n + 1) * (1000 * (W + 1) ^ 2 + 2) :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega

theorem positive_value_lower (a : BinaryFraction) (ha : 0 < a.value) :
    (2 : ℚ) ^ (-(a.width : ℤ)) ≤ a.value := by
  have hd : (0 : ℚ) < bitWordValue a.denominator := by exact_mod_cast a.denominator_pos
  have hn : (0 : ℚ) < a.numerator.value := (div_pos_iff_of_pos_right hd).mp ha
  have hnum : (1 : ℚ) ≤ a.numerator.value := by
    have hnZ : (0 : ℤ) < a.numerator.value := by exact_mod_cast hn
    exact_mod_cast (show (1 : ℤ) ≤ a.numerator.value by omega)
  have hden : (bitWordValue a.denominator : ℚ) ≤ (2 : ℚ) ^ a.width := by
    exact_mod_cast (bitWordValue_lt_pow_length a.denominator).le.trans
      (Nat.pow_le_pow_right (by decide) (le_max_right _ _))
  rw [zpow_neg, zpow_natCast, ← one_div]
  change 1 / (2 : ℚ) ^ a.width ≤ (a.numerator.value : ℚ) / bitWordValue a.denominator
  apply (div_le_div_iff₀ (pow_pos (by norm_num : (0 : ℚ) < 2) _) hd).mpr
  simpa only [one_mul] using
    hden.trans (le_mul_of_one_le_left (pow_nonneg (by norm_num) _) hnum)



theorem dyadicCeilingWithWork_value (a : BinaryFraction) (ha : 0 < a.value) :
    (dyadicCeilingWithWork a).1.value = rationalDyadicCeiling a.value := by
  apply dyadicScanWithWork_value a (inversePowerTwo a.width) (2 * a.width) (-(a.width : ℤ)) ha
    (inversePowerTwo_value _)
  · have hpos : (0 : ℚ) < (2 : ℚ) ^ (-(a.width : ℤ) - 1) := zpow_pos (by norm_num) _
    have hdouble : (2 : ℚ) ^ (-(a.width : ℤ) - 1) * 2 = (2 : ℚ) ^ (-(a.width : ℤ)) := by
      rw [← zpow_add_one₀ (by norm_num : (2 : ℚ) ≠ 0)]
      congr 1
      omega
    have hl := positive_value_lower a ha
    nlinarith only [hpos, hdouble, hl]
  · rw [inversePowerTwo_value, ← zpow_natCast]
    rw [← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
    have he : -(a.width : ℤ) + (2 * a.width : ℕ) = (a.width : ℤ) := by omega
    rw [he, zpow_natCast]
    exact (le_abs_self _).trans (value_abs_le_pow_width a)

theorem dyadicCeilingWithWork_width (a : BinaryFraction) :
    (dyadicCeilingWithWork a).1.width ≤ 3 * a.width + 1 := by
  have h := dyadicScanWithWork_width a (inversePowerTwo a.width) (2 * a.width)
  rw [inversePowerTwo_width] at h
  exact h.trans (by omega)

theorem dyadicCeilingWithWork_cost (a : BinaryFraction) :
    (dyadicCeilingWithWork a).2 ≤
      1 + 2 * a.width * (1000 * (3 * a.width + 2) ^ 2 + 2) + 3 * a.width + 5 := by
  have h := dyadicScanWithWork_cost a (inversePowerTwo a.width) (2 * a.width) (3 * a.width + 1)
    (by omega) (by rw [inversePowerTwo_width]; omega)
  rw [show 3 * a.width + 1 + 1 = 3 * a.width + 2 by omega] at h
  exact Nat.add_le_add_right (Nat.add_le_add_right h (3 * a.width)) 5


theorem dyadicCeilingWithWork_cost_le (a : BinaryFraction) (B : ℕ) (hB : a.width ≤ B) :
    (dyadicCeilingWithWork a).2 ≤
      1 + 2 * B * (1000 * (3 * B + 2) ^ 2 + 2) + 3 * B + 5 := by
  have h := dyadicCeilingWithWork_cost a
  have hs := Nat.pow_le_pow_left (show 3 * a.width + 2 ≤ 3 * B + 2 by omega) 2
  have hp := Nat.mul_le_mul (show 2 * a.width ≤ 2 * B by omega)
    (show 1000 * (3 * a.width + 2) ^ 2 + 2 ≤ 1000 * (3 * B + 2) ^ 2 + 2 by omega)
  omega

end BinaryFraction
end EditApproximation

end OAI
