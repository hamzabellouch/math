import OAI.Combinatorics.EditApproximation.Binary.UnreducedRational
import OAI.Combinatorics.EditApproximation.Binary.SignedBinaryOrderWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Unreduced fractions stored as Boolean words. Every numerator operation
below runs the literal signed ripple/shift-add code; denominator products
run the literal Boolean multiplication routine. -/

namespace EditApproximation



namespace BinaryFraction





@[simp] theorem representation_value (a : BinaryFraction) : a.representation.value = a.value := rfl





@[simp] theorem denominatorInteger_value (a : BinaryFraction) :
    a.denominatorInteger.value = (bitWordValue a.denominator : ℤ) := rfl





theorem addWithWork_value (a b : BinaryFraction) :
    (a.addWithWork b).1.value = a.value + b.value := by
  simp only [addWithWork, value, SignedBinary.addWithWork_value, SignedBinary.mulWithWork_value,
    denominatorInteger_value, bitMulWithWork_value]
  push_cast
  have ha : (bitWordValue a.denominator : ℚ) ≠ 0 := by exact_mod_cast a.denominator_pos.ne'
  have hb : (bitWordValue b.denominator : ℚ) ≠ 0 := by exact_mod_cast b.denominator_pos.ne'
  field_simp [ha, hb]

theorem mulWithWork_value (a b : BinaryFraction) :
    (a.mulWithWork b).1.value = a.value * b.value := by
  simp only [mulWithWork, value, SignedBinary.mulWithWork_value, bitMulWithWork_value]
  push_cast
  exact mul_div_mul_comm _ _ _ _

theorem addWithWork_representation (a b : BinaryFraction) :
    (a.addWithWork b).1.representation = a.representation.add b.representation := by
  apply UnreducedRational.eq_of_num_den
  · simp only [addWithWork, representation, UnreducedRational.add,
      SignedBinary.addWithWork_value, SignedBinary.mulWithWork_value, denominatorInteger_value]
  · exact bitMulWithWork_value a.denominator b.denominator

theorem mulWithWork_representation (a b : BinaryFraction) :
    (a.mulWithWork b).1.representation = a.representation.mul b.representation := by
  apply UnreducedRational.eq_of_num_den
  · exact SignedBinary.mulWithWork_value a.numerator b.numerator
  · exact bitMulWithWork_value a.denominator b.denominator

theorem addWithWork_cost (a b : BinaryFraction) (B : ℕ) (ha : a.width ≤ B) (hb : b.width ≤ B) :
    (a.addWithWork b).2 ≤ 5000 * (B + 1) ^ 2 := by
  have han : a.numerator.bits.length ≤ B := (le_max_left _ _).trans ha
  have had : a.denominator.length ≤ B := (le_max_right _ _).trans ha
  have hbn : b.numerator.bits.length ≤ B := (le_max_left _ _).trans hb
  have hbd : b.denominator.length ≤ B := (le_max_right _ _).trans hb
  have hfirst := SignedBinary.mulWithWork_cost a.numerator b.denominatorInteger
  have hsecond := SignedBinary.mulWithWork_cost b.numerator a.denominatorInteger
  have hfl := SignedBinary.mulWithWork_length a.numerator b.denominatorInteger
  have hsl := SignedBinary.mulWithWork_length b.numerator a.denominatorInteger
  have hsum := SignedBinary.addWithWork_cost (a.numerator.mulWithWork b.denominatorInteger).1
    (b.numerator.mulWithWork a.denominatorInteger).1
  have hden := bitMulWithWork_cost a.denominator b.denominator
  simp only [denominatorInteger] at hfirst hsecond hfl hsl
  change (a.numerator.mulWithWork b.denominatorInteger).2 +
    (b.numerator.mulWithWork a.denominatorInteger).2 +
    ((a.numerator.mulWithWork b.denominatorInteger).1.addWithWork
      (b.numerator.mulWithWork a.denominatorInteger).1).2 +
    (bitMulWithWork a.denominator b.denominator).2 + 8 ≤ _
  simp only [denominatorInteger] at hsum ⊢
  nlinarith only [han, had, hbn, hbd, hfirst, hsecond, hfl, hsl, hsum, hden,
    Nat.mul_self_le_mul_self (show a.numerator.bits.length + b.denominator.length + 1 ≤ 2 * B + 1 by omega),
    Nat.mul_self_le_mul_self (show b.numerator.bits.length + a.denominator.length + 1 ≤ 2 * B + 1 by omega),
    Nat.mul_le_mul (show a.denominator.length + 1 ≤ B + 1 by omega)
      (show a.denominator.length + b.denominator.length + 1 ≤ 2 * B + 1 by omega)]

theorem mulWithWork_cost (a b : BinaryFraction) (B : ℕ) (ha : a.width ≤ B) (hb : b.width ≤ B) :
    (a.mulWithWork b).2 ≤ 1000 * (B + 1) ^ 2 := by
  have han : a.numerator.bits.length ≤ B := (le_max_left _ _).trans ha
  have had : a.denominator.length ≤ B := (le_max_right _ _).trans ha
  have hbn : b.numerator.bits.length ≤ B := (le_max_left _ _).trans hb
  have hbd : b.denominator.length ≤ B := (le_max_right _ _).trans hb
  have hnum := SignedBinary.mulWithWork_cost a.numerator b.numerator
  have hden := bitMulWithWork_cost a.denominator b.denominator
  change (a.numerator.mulWithWork b.numerator).2 + (bitMulWithWork a.denominator b.denominator).2 + 4 ≤ _
  nlinarith only [han, had, hbn, hbd, hnum, hden,
    Nat.mul_self_le_mul_self (show a.numerator.bits.length + b.numerator.bits.length + 1 ≤ 2 * B + 1 by omega),
    Nat.mul_le_mul (show a.denominator.length + 1 ≤ B + 1 by omega)
      (show a.denominator.length + b.denominator.length + 1 ≤ 2 * B + 1 by omega)]







theorem neg_value (a : BinaryFraction) : a.neg.value = -a.value := by
  simp [neg, value, neg_div]

theorem invWithWork_value (a : BinaryFraction) : (a.invWithWork).1.value = a.value⁻¹ := by
  unfold invWithWork
  dsimp only
  split_ifs with h
  · have hnum : bitWordValue a.numerator.bits = 0 := by
      simpa only [bitWordValue] using (bitCompareWithWork_eq a.numerator.bits []).1 h
    simp [zero, value, SignedBinary.value, signedMagnitude, hnum, bitWordValue]
  · have hn : bitWordValue a.numerator.bits ≠ 0 := by
      intro hzero
      exact h ((bitCompareWithWork_eq a.numerator.bits []).2 (by simpa [bitWordValue] using hzero))
    cases hsign : a.numerator.negative <;>
      simp [value, SignedBinary.value, signedMagnitude, hsign, inv_div, neg_div]

theorem invWithWork_cost (a : BinaryFraction) :
    (a.invWithWork).2 ≤ 4 * a.width + 3 := by
  have h := bitCompareWithWork_cost a.numerator.bits []
  have hn : a.numerator.bits.length ≤ a.width := le_max_left _ _
  simp only [List.length_nil, Nat.add_zero] at h
  unfold invWithWork
  dsimp only
  split_ifs <;> omega

theorem zero_representation : zero.representation = UnreducedRational.zero := by
  apply UnreducedRational.eq_of_num_den <;> rfl

theorem neg_representation (a : BinaryFraction) :
    a.neg.representation = a.representation.neg := by
  apply UnreducedRational.eq_of_num_den
  · exact SignedBinary.value_neg a.numerator
  · rfl

theorem invWithWork_representation (a : BinaryFraction) :
    (a.invWithWork).1.representation = a.representation.inv := by
  unfold invWithWork
  dsimp only
  split_ifs with h
  · have hz : bitWordValue a.numerator.bits = 0 := by
      simpa only [bitWordValue] using (bitCompareWithWork_eq a.numerator.bits []).1 h
    have hv : a.numerator.value = 0 := by simp [SignedBinary.value, signedMagnitude, hz]
    simp only [UnreducedRational.inv, representation, hv, ↓reduceDIte]
    exact zero_representation
  · have hn : bitWordValue a.numerator.bits ≠ 0 := by
      intro hz
      exact h ((bitCompareWithWork_eq a.numerator.bits []).2 (by simpa [bitWordValue] using hz))
    have hv : a.numerator.value ≠ 0 := by
      cases hs : a.numerator.negative <;> simp [SignedBinary.value, signedMagnitude, hs, hn]
    simp only [UnreducedRational.inv, representation, hv, ↓reduceDIte]
    apply UnreducedRational.eq_of_num_den
    · cases hs : a.numerator.negative <;>
        simp [SignedBinary.value, signedMagnitude, hs, Int.sign_natCast_of_ne_zero hn]
    · cases hs : a.numerator.negative <;> simp [SignedBinary.value, signedMagnitude, hs]



theorem ltWithWork_representation (a b : BinaryFraction) :
    (a.ltWithWork b).1 = a.representation.lt b.representation := by
  apply Bool.eq_iff_iff.mpr
  rw [UnreducedRational.lt_eq_true]
  simp only [ltWithWork, SignedBinary.ltWithWork_value, SignedBinary.mulWithWork_value,
    denominatorInteger_value, representation_value]
  unfold value
  rw [div_lt_div_iff₀ (by exact_mod_cast a.denominator_pos : (0 : ℚ) < bitWordValue a.denominator)
    (by exact_mod_cast b.denominator_pos : (0 : ℚ) < bitWordValue b.denominator)]
  exact_mod_cast (Iff.rfl :
    a.numerator.value * (bitWordValue b.denominator : ℤ) <
      b.numerator.value * (bitWordValue a.denominator : ℤ) ↔ _)

theorem ltWithWork_value (a b : BinaryFraction) :
    (a.ltWithWork b).1 = true ↔ a.value < b.value := by
  rw [ltWithWork_representation, UnreducedRational.lt_eq_true]
  rfl

theorem ltWithWork_cost (a b : BinaryFraction) (B : ℕ) (ha : a.width ≤ B) (hb : b.width ≤ B) :
    (a.ltWithWork b).2 ≤ 1000 * (B + 1) ^ 2 := by
  have han : a.numerator.bits.length ≤ B := (le_max_left _ _).trans ha
  have had : a.denominator.length ≤ B := (le_max_right _ _).trans ha
  have hbn : b.numerator.bits.length ≤ B := (le_max_left _ _).trans hb
  have hbd : b.denominator.length ≤ B := (le_max_right _ _).trans hb
  have hl := SignedBinary.mulWithWork_cost a.numerator b.denominatorInteger
  have hr := SignedBinary.mulWithWork_cost b.numerator a.denominatorInteger
  have hll := SignedBinary.mulWithWork_length a.numerator b.denominatorInteger
  have hrl := SignedBinary.mulWithWork_length b.numerator a.denominatorInteger
  have hc := SignedBinary.ltWithWork_cost (a.numerator.mulWithWork b.denominatorInteger).1
    (b.numerator.mulWithWork a.denominatorInteger).1
  simp only [denominatorInteger] at hl hr hll hrl
  change (a.numerator.mulWithWork b.denominatorInteger).2 +
    (b.numerator.mulWithWork a.denominatorInteger).2 +
    ((a.numerator.mulWithWork b.denominatorInteger).1.ltWithWork
      (b.numerator.mulWithWork a.denominatorInteger).1).2 + 4 ≤ _
  simp only [denominatorInteger] at hc ⊢
  nlinarith only [hl, hr, hll, hrl, hc, han, had, hbn, hbd,
    Nat.mul_self_le_mul_self (show a.numerator.bits.length + b.denominator.length + 1 ≤ 2 * B + 1 by omega),
    Nat.mul_self_le_mul_self (show b.numerator.bits.length + a.denominator.length + 1 ≤ 2 * B + 1 by omega)]

end BinaryFraction
end EditApproximation

end OAI
