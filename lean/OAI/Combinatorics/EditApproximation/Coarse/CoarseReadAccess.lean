import OAI.Combinatorics.EditApproximation.Coarse.CoarseDescriptorWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation

/-- A padded-source lookup tests its virtual endpoint and then reads the
original symbol array. Padding is represented by `none`. -/


theorem coarsePaddedReadWithWork_value {α : Type*} (n : ℕ) (source : List α) (offset : ℕ) :
    (coarsePaddedReadWithWork n source offset).1 = coarsePaddedRead n source offset := by
  unfold coarsePaddedReadWithWork coarsePaddedRead
  dsimp only
  simp only [binaryNaturalCompareWithWork_lt]

theorem coarsePaddedReadWithWork_cost {α : Type*} (n : ℕ) (source : List α)
    (offset A : ℕ) (hn : Nat.size n ≤ A) (ho : Nat.size offset ≤ A) :
    (coarsePaddedReadWithWork n source offset).2 ≤ 12 * (A + 1) := by
  have h := binaryNaturalCompareWithWork_cost offset n
  change (binaryNaturalCompareWithWork offset n).2 + Nat.size n + Nat.size offset + 2 ≤ _
  omega

theorem coarsePaddedRead_symbol_mem (n : ℕ) (source : List ℕ) (offset a : ℕ)
    (h : coarsePaddedRead n source offset = some (some a)) : a ∈ source := by
  unfold coarsePaddedRead at h
  split_ifs at h
  exact List.mem_of_getElem? (Option.some.inj h)

/-- Child offsets are formed by literal multiplication and addition. -/


theorem coarseChildOffsetWithWork_value (offset capacity index : ℕ) :
    bitWordValue (coarseChildOffsetWithWork offset capacity index).1 = offset + index * capacity := by
  simp only [coarseChildOffsetWithWork, binaryNaturalAddWithWork_value, binaryNaturalMulWithWork_value]

theorem coarseChildOffsetWithWork_cost (offset capacity index A : ℕ)
    (ho : Nat.size offset ≤ A) (hc : Nat.size capacity ≤ A) (hi : Nat.size index ≤ A) :
    (coarseChildOffsetWithWork offset capacity index).2 ≤ 200 * (A + 1) ^ 2 := by
  have hm := binaryNaturalMulWithWork_cost index capacity
  have ha := binaryNaturalAddWithWork_cost offset (index * capacity)
  have hp := natural_product_bit_length index capacity
  simp only [coarseChildOffsetWithWork, binaryNaturalMulWithWork_value]
  have hmax : max (Nat.size offset) (Nat.size (index * capacity)) ≤ 2 * A + 1 := by
    apply max_le <;> omega
  nlinarith only [hm, ha, hp, ho, hc, hi, hmax, Nat.zero_le A]

end EditApproximation

end OAI
