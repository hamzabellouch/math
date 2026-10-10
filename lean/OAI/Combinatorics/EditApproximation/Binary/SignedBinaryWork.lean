import OAI.Combinatorics.EditApproximation.Binary.BinarySubtractWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Signed integers represented by a sign bit and a Boolean magnitude word.
Arithmetic uses Boolean ripple and shift-add routines. -/

namespace EditApproximation





namespace SignedBinary











@[simp] theorem value_ofInt (a : ℤ) : (ofInt a).value = a := by
  by_cases h : a < 0
  · simpa only [ofInt, value, bitWordValue_bits, signedMagnitude, h, decide_true,
      ↓reduceIte] using (Int.eq_neg_natAbs_of_nonpos (by omega : a ≤ 0)).symm
  · simpa only [ofInt, value, bitWordValue_bits, signedMagnitude, h, decide_false,
      Bool.false_eq_true, ↓reduceIte] using (Int.eq_natAbs_of_nonneg (by omega : 0 ≤ a)).symm

@[simp] theorem value_neg (a : SignedBinary) : a.neg.value = -a.value := by
  cases a with
  | mk negative bits => cases negative <;> simp [neg, value, signedMagnitude]

private theorem subtract_signed_value (negative : Bool) (a b : List Bool)
    (h : bitWordValue b ≤ bitWordValue a) :
    signedMagnitude negative (bitWordValue (bitSubtractWithWork a b false).1) =
      signedMagnitude negative (bitWordValue a) - signedMagnitude negative (bitWordValue b) := by
  rw [bitSubtractWithWork_sub a b h]
  cases negative <;> simp only [signedMagnitude, Bool.false_eq_true, ↓reduceIte ]
  · exact Int.ofNat_sub h
  · rw [Int.ofNat_sub h]
    ring

theorem addWithWork_value (a b : SignedBinary) :
    (a.addWithWork b).1.value = a.value + b.value := by
  by_cases hsign : a.negative = b.negative
  · simp only [addWithWork, hsign, ↓reduceIte, value, bitAddWithWork_value,
      Bool.toNat_false, Nat.add_zero]
    rw [← hsign]
    cases a.negative <;> simp [signedMagnitude, add_comm]
  · simp only [addWithWork, hsign, ↓reduceIte]
    have hcomparison := bitCompareWithWork_matches a.bits b.bits
    rcases hcomparison with ⟨hcompare, hlt⟩ | ⟨hcompare, heq⟩ | ⟨hcompare, hgt⟩
    · rw [hcompare]
      change signedMagnitude b.negative (bitWordValue (bitSubtractWithWork b.bits a.bits false).1) = _
      rw [subtract_signed_value b.negative b.bits a.bits hlt.le]
      cases ha : a.negative <;> cases hb : b.negative <;>
        simp_all [value, signedMagnitude]
      all_goals ring
    · rw [hcompare]
      cases ha : a.negative <;> cases hb : b.negative <;>
        simp_all [value, signedMagnitude, bitWordValue]
    · rw [hcompare]
      change signedMagnitude a.negative (bitWordValue (bitSubtractWithWork a.bits b.bits false).1) = _
      rw [subtract_signed_value a.negative a.bits b.bits hgt.le]
      cases ha : a.negative <;> cases hb : b.negative <;>
        simp_all [value, signedMagnitude]
      all_goals ring

theorem mulWithWork_value (a b : SignedBinary) :
    (a.mulWithWork b).1.value = a.value * b.value := by
  simp only [mulWithWork, value, bitMulWithWork_value]
  cases a.negative <;> cases b.negative <;> simp [signedMagnitude]

theorem addWithWork_cost (a b : SignedBinary) :
    (a.addWithWork b).2 ≤ 20 * (a.bits.length + b.bits.length + 1) := by
  have hadd := bitAddWithWork_cost a.bits b.bits false
  have hcompare := bitCompareWithWork_cost a.bits b.bits
  have hsub1 := bitSubtractWithWork_cost a.bits b.bits false
  have hsub2 := bitSubtractWithWork_cost b.bits a.bits false
  unfold addWithWork
  split_ifs
  · change (bitAddWithWork a.bits b.bits false).2 + 4 ≤ _
    omega
  · dsimp only
    cases (bitCompareWithWork a.bits b.bits).1 <;> simp only [] <;> omega

theorem mulWithWork_cost (a b : SignedBinary) :
    (a.mulWithWork b).2 ≤ 24 * (a.bits.length + b.bits.length + 1) ^ 2 := by
  have hmul := bitMulWithWork_cost a.bits b.bits
  change (bitMulWithWork a.bits b.bits).2 + 4 ≤ _
  nlinarith only [hmul]

theorem addWithWork_length (a b : SignedBinary) :
    (a.addWithWork b).1.bits.length ≤ max a.bits.length b.bits.length + 1 := by
  have hadd := bitAddWithWork_length a.bits b.bits false
  have hsub1 := bitSubtractWithWork_length a.bits b.bits false
  have hsub2 := bitSubtractWithWork_length b.bits a.bits false
  unfold addWithWork
  split_ifs
  · exact hadd
  · dsimp only
    cases (bitCompareWithWork a.bits b.bits).1 <;> simp only [List.length_nil] <;> omega

theorem mulWithWork_length (a b : SignedBinary) :
    (a.mulWithWork b).1.bits.length ≤ 2 * a.bits.length + b.bits.length + 1 :=
  bitMulWithWork_length a.bits b.bits

end SignedBinary
end EditApproximation

end OAI
