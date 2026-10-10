import OAI.Combinatorics.EditApproximation.Binary.BinarySubtractWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Binary long division. A high-prefix quotient and remainder are extended
by one source bit, then compared with the positive divisor and reduced by
at most one ripple-borrow subtraction. -/

namespace EditApproximation



theorem bitDivModWithWork_value (divisor bits : List Bool) (hd : 0 < bitWordValue divisor) :
    bitWordValue bits = bitWordValue divisor * bitWordValue (bitDivModWithWork divisor bits).1 +
      bitWordValue (bitDivModWithWork divisor bits).2.1 ∧
      bitWordValue (bitDivModWithWork divisor bits).2.1 < bitWordValue divisor := by
  induction bits with
  | nil => simp [bitDivModWithWork, bitWordValue, hd]
  | cons bit bits ih =>
    let previous := bitDivModWithWork divisor bits
    let candidate := bit :: previous.2.1
    have hp : bitWordValue bits = bitWordValue divisor * bitWordValue previous.1 +
        bitWordValue previous.2.1 := ih.1
    have hr : bitWordValue previous.2.1 < bitWordValue divisor := ih.2
    have hc : bitWordValue candidate < 2 * bitWordValue divisor := by
      dsimp only [candidate, bitWordValue]
      cases bit <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
    by_cases hlt : (bitCompareWithWork candidate divisor).1 = .lt
    · have hv := (bitCompareWithWork_lt candidate divisor).1 hlt
      simp only [bitDivModWithWork, show (bitCompareWithWork (bit :: (bitDivModWithWork divisor bits).2.1)
        divisor).1 = .lt from hlt, ↓reduceIte]
      change bitWordValue (bit :: bits) = bitWordValue divisor *
        bitWordValue (false :: previous.1) + bitWordValue candidate ∧ bitWordValue candidate < _
      constructor
      · simp only [bitWordValue, Bool.toNat_false]
        dsimp only [candidate, bitWordValue]
        nlinarith only [hp]
      · exact hv
    · have hv : bitWordValue divisor ≤ bitWordValue candidate := by
        exact Nat.le_of_not_gt (fun h => hlt ((bitCompareWithWork_lt candidate divisor).2 h))
      have hs := bitSubtractWithWork_sub candidate divisor hv
      simp only [bitDivModWithWork, show (bitCompareWithWork (bit :: (bitDivModWithWork divisor bits).2.1)
        divisor).1 ≠ .lt from hlt, ↓reduceIte]
      change bitWordValue (bit :: bits) = bitWordValue divisor * bitWordValue (true :: previous.1) +
        bitWordValue (bitSubtractWithWork candidate divisor false).1 ∧
        bitWordValue (bitSubtractWithWork candidate divisor false).1 < _
      rw [hs]
      constructor
      · simp only [bitWordValue, Bool.toNat_true]
        have he := Nat.sub_add_cancel hv
        dsimp only [candidate, bitWordValue] at he ⊢
        nlinarith only [hp, he]
      · omega

theorem bitDivModWithWork_lengths (divisor bits : List Bool) :
    (bitDivModWithWork divisor bits).1.length = bits.length ∧
      (bitDivModWithWork divisor bits).2.1.length ≤ bits.length + divisor.length := by
  induction bits with
  | nil => simp [bitDivModWithWork]
  | cons bit bits ih =>
    simp only [bitDivModWithWork]
    split_ifs
    · simp only [List.length_cons]
      exact ⟨by omega, by omega⟩
    · have hs := bitSubtractWithWork_length (bit :: (bitDivModWithWork divisor bits).2.1) divisor false
      simp only [List.length_cons] at hs ⊢
      exact ⟨by omega, by omega⟩

theorem bitDivModWithWork_cost (divisor bits : List Bool) :
    (bitDivModWithWork divisor bits).2.2 ≤
      30 * (bits.length + 1) * (bits.length + divisor.length + 1) := by
  induction bits with
  | nil => simp [bitDivModWithWork]; omega
  | cons bit bits ih =>
    have hl := (bitDivModWithWork_lengths divisor bits).2
    have hc := bitCompareWithWork_cost (bit :: (bitDivModWithWork divisor bits).2.1) divisor
    have hs := bitSubtractWithWork_cost (bit :: (bitDivModWithWork divisor bits).2.1) divisor false
    simp only [List.length_cons] at hc hs
    simp only [bitDivModWithWork, List.length_cons]
    split_ifs <;> nlinarith only [ih, hl, hc, hs]



theorem binaryNaturalDivModWithWork_spec (n d : ℕ) (hd : 0 < d) :
    bitWordValue (binaryNaturalDivModWithWork n d).1 = n / d ∧
      bitWordValue (binaryNaturalDivModWithWork n d).2.1 = n % d := by
  have h := bitDivModWithWork_value d.bits n.bits (by simpa only [bitWordValue_bits] using hd)
  simp only [bitWordValue_bits] at h
  have hmod : n % d = bitWordValue (bitDivModWithWork d.bits n.bits).2.1 := by
    conv_lhs => rw [h.1]
    simp only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_eq_of_lt h.2]
  have hdiv : n / d = bitWordValue (bitDivModWithWork d.bits n.bits).1 := by
    conv_lhs => rw [h.1]
    rw [Nat.mul_add_div hd, Nat.div_eq_of_lt h.2, Nat.add_zero]
  exact ⟨hdiv.symm, hmod.symm⟩

theorem binaryNaturalDivModWithWork_cost (n d : ℕ) :
    (binaryNaturalDivModWithWork n d).2.2 ≤
      30 * (Nat.size n + 1) * (Nat.size n + Nat.size d + 1) := by
  simpa only [binaryNaturalDivModWithWork, Nat.size_eq_bits_len] using bitDivModWithWork_cost d.bits n.bits

end EditApproximation

end OAI
