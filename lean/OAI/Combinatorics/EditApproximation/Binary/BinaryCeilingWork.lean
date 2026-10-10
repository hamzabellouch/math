import OAI.Combinatorics.EditApproximation.Binary.BinaryDivisionWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryRawCost
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Exact natural ceilings from the executed binary quotient and remainder.
Negative fractions have natural ceiling zero, as in the seed update. -/

namespace EditApproximation



theorem bitCeilDivWithWork_value (divisor bits : List Bool) (hd : 0 < bitWordValue divisor) :
    bitWordValue (bitCeilDivWithWork divisor bits).1 =
      ⌈((bitWordValue bits : ℚ) / bitWordValue divisor)⌉₊ := by
  let q := bitWordValue (bitDivModWithWork divisor bits).1
  let r := bitWordValue (bitDivModWithWork divisor bits).2.1
  have h := bitDivModWithWork_value divisor bits hd
  have heq : bitWordValue bits = bitWordValue divisor * q + r := h.1
  have hr : r < bitWordValue divisor := h.2
  have hdQ : (0 : ℚ) < bitWordValue divisor := by exact_mod_cast hd
  unfold bitCeilDivWithWork
  dsimp only
  split_ifs with hz
  · have hr0 : r = 0 := by
      exact (bitCompareWithWork_eq (bitDivModWithWork divisor bits).2.1 []).1 hz
    have hratio : (bitWordValue bits : ℚ) / bitWordValue divisor = (q : ℚ) := by
      apply (div_eq_iff hdQ.ne').mpr
      exact_mod_cast (show bitWordValue bits = q * bitWordValue divisor by nlinarith only [heq, hr0])
    rw [hratio]
    exact (Nat.ceil_natCast q).symm
  · have hr0 : r ≠ 0 := by
      intro hzero
      exact hz ((bitCompareWithWork_eq (bitDivModWithWork divisor bits).2.1 []).2 hzero)
    rw [bitAddWithWork_value]
    change q + 1 + 0 = _
    simp only [Nat.add_zero]
    symm
    apply (Nat.ceil_eq_iff (by omega : q + 1 ≠ 0)).mpr
    constructor
    · simp only [Nat.add_sub_cancel]
      rw [lt_div_iff₀ hdQ]
      exact_mod_cast (show q * bitWordValue divisor < bitWordValue bits by
        nlinarith only [heq, Nat.pos_of_ne_zero hr0])
    · rw [div_le_iff₀ hdQ]
      push_cast
      exact_mod_cast (show bitWordValue bits ≤ (q + 1) * bitWordValue divisor by nlinarith only [heq, hr])

theorem bitCeilDivWithWork_length (divisor bits : List Bool) :
    (bitCeilDivWithWork divisor bits).1.length ≤ bits.length + 2 := by
  have hq := (bitDivModWithWork_lengths divisor bits).1
  have ha := bitAddWithWork_length (bitDivModWithWork divisor bits).1 [true] false
  unfold bitCeilDivWithWork
  dsimp only
  split_ifs <;> dsimp only
  · omega
  · simp only [List.length_cons, List.length_nil] at ha
    omega

theorem bitCeilDivWithWork_cost (divisor bits : List Bool) :
    (bitCeilDivWithWork divisor bits).2 ≤
      100 * (bits.length + divisor.length + 1) ^ 2 := by
  have hdiv := bitDivModWithWork_cost divisor bits
  have hl := bitDivModWithWork_lengths divisor bits
  have hc := bitCompareWithWork_cost (bitDivModWithWork divisor bits).2.1 []
  have ha := bitAddWithWork_cost (bitDivModWithWork divisor bits).1 [true] false
  simp only [List.length_nil, List.length_cons, Nat.add_zero] at hc ha
  unfold bitCeilDivWithWork
  dsimp only
  split_ifs <;> dsimp only <;> nlinarith only [hdiv, hl.1, hl.2, hc, ha]

namespace BinaryFraction



theorem naturalCeilingWithWork_value (a : BinaryFraction) :
    bitWordValue (a.naturalCeilingWithWork).1 = ⌈a.value⌉₊ := by
  cases hs : a.numerator.negative
  · simpa only [naturalCeilingWithWork, hs, Bool.false_eq_true, ↓reduceIte,
      value, SignedBinary.value, signedMagnitude, Int.cast_natCast] using
      bitCeilDivWithWork_value a.denominator a.numerator.bits a.denominator_pos
  · have hn : a.value ≤ 0 := by
      simp only [value, SignedBinary.value, signedMagnitude, hs, ↓reduceIte, Int.cast_neg, Int.cast_natCast]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    simp only [naturalCeilingWithWork, hs, ↓reduceIte, bitWordValue]
    exact (Nat.ceil_eq_zero.mpr hn).symm

theorem naturalCeilingWithWork_cost (a : BinaryFraction) :
    (a.naturalCeilingWithWork).2 ≤ 500 * (a.width + 1) ^ 2 := by
  have hn : a.numerator.bits.length ≤ a.width := le_max_left _ _
  have hd : a.denominator.length ≤ a.width := le_max_right _ _
  have hc := bitCeilDivWithWork_cost a.denominator a.numerator.bits
  unfold naturalCeilingWithWork
  split_ifs <;> dsimp only
  · nlinarith only [Nat.zero_le a.width]
  · have hm := Nat.mul_self_le_mul_self (show a.numerator.bits.length + a.denominator.length + 1 ≤
        2 * a.width + 1 by omega)
    nlinarith only [hc, hm, Nat.zero_le a.width]

end BinaryFraction
end EditApproximation

end OAI
