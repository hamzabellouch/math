import OAI.Combinatorics.EditApproximation.Queries.QueryPhysicalScalarReads

namespace OAI

/-! Polynomial bit costs for the three physical source guards.  Bounds
use only the words in the request, not the size of the ambient source set. -/

namespace EditApproximation

theorem queryScalePresentWithWork_cost (N b B : ℕ)
    (hN : Nat.size N ≤ B) (hb : Nat.size b ≤ B) :
    (queryScalePresentWithWork N b).2 ≤ 40 * (B + 2) ^ 2 := by
  have hs := queryScaleDispatchWithWork_cost N b B hN hb
  have hl : (dyadicScales N).length ≤ B + 1 := by
    rw [← dyadicScalesWithWork_value N]
    simp only [dyadicScalesWithWork, arithmeticMapWithWork_value, List.length_map, List.length_range]
    rw [Nat.size_eq_bits_len]
    omega
  have hi : (queryScaleDispatchWithWork N b).1 ≤ B + 1 := by
    rw [queryScaleDispatchWithWork_value]
    exact (List.idxOf_le_length (a := b) (l := dyadicScales N)).trans hl
  have hidx : Nat.size (queryScaleDispatchWithWork N b).1 ≤ B + 1 :=
    Nat.size_le.mpr (hi.trans_lt Nat.lt_two_pow_self)
  have hc : max 1 N.bits.length ≤ B + 1 := by
    rw [Nat.size_eq_bits_len]
    omega
  have hlen : Nat.size (max 1 N.bits.length) ≤ B + 1 :=
    Nat.size_le.mpr (hc.trans_lt Nat.lt_two_pow_self)
  have ht := binaryNaturalCompareWithWork_cost (queryScaleDispatchWithWork N b).1 (max 1 N.bits.length)
  change (queryScaleDispatchWithWork N b).2 +
    (binaryNaturalCompareWithWork (queryScaleDispatchWithWork N b).1 (max 1 N.bits.length)).2 + 2 ≤ _
  nlinarith only [hs, ht, hidx, hlen, Nat.zero_le B]

theorem queryRangeValidWithWork_cost (bound range B : ℕ)
    (hb : Nat.size bound ≤ B) (hr : Nat.size range ≤ B) :
    (queryRangeValidWithWork bound range).2 ≤ 12 * B + 5 := by
  have hp := binaryNaturalCompareWithWork_cost 0 range
  have hu := wordLEWithWork_cost range.bits bound.bits
  simp only [Nat.size_zero] at hp
  simp only [Nat.size_eq_bits_len] at hu
  change _ + _ + 2 ≤ _
  omega

theorem queryCellValidWithWork_cost (n exponent B : ℕ) (cell : ℕ × ℕ)
    (hn : Nat.size n ≤ B) (he : exponent + 1 ≤ B)
    (hl : Nat.size cell.1 ≤ B) (hr : Nat.size cell.2 ≤ B) :
    (queryCellValidWithWork n exponent cell).2 ≤ 100 * (B + 1) ^ 2 := by
  have hp : Nat.size (bitWordValue (powerTwoWord exponent)) ≤ B := by
    rw [powerTwoWord_value, Nat.size_pow]
    exact he
  have hm := queryNaturalMul_cost n (bitWordValue (powerTwoWord exponent)) B hn hp
  have hlength := bitMulWithWork_length n.bits (bitWordValue (powerTwoWord exponent)).bits
  change (binaryNaturalMulWithWork n (bitWordValue (powerTwoWord exponent))).1.length ≤ _ at hlength
  simp only [Nat.size_eq_bits_len] at hlength
  have hleft := wordLEWithWork_cost cell.1.bits
    (binaryNaturalMulWithWork n (bitWordValue (powerTwoWord exponent))).1
  have hright := wordLEWithWork_cost cell.2.bits
    (binaryNaturalMulWithWork n (bitWordValue (powerTwoWord exponent))).1
  simp only [Nat.size_eq_bits_len] at hleft hright
  change (binaryNaturalMulWithWork n (bitWordValue (powerTwoWord exponent))).2 +
    (wordLEWithWork cell.1.bits (binaryNaturalMulWithWork n (bitWordValue (powerTwoWord exponent))).1).2 +
    (wordLEWithWork cell.2.bits (binaryNaturalMulWithWork n (bitWordValue (powerTwoWord exponent))).1).2 +
    exponent + 4 ≤ _
  nlinarith only [hm, hlength, hleft, hright, hn, hp, hl, hr, he, Nat.zero_le B]

end EditApproximation

end OAI
