import OAI.Combinatorics.EditApproximation.Coarse.CoarseReadTree
import OAI.Combinatorics.EditApproximation.Coarse.CoarseIndexedFrameWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryPowerStorage
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation

theorem saturatingSubtractWithWork_length (a b : ℕ) :
    (saturatingSubtractWithWork a b).1.length ≤ max (Nat.size a) (Nat.size b) := by
  unfold saturatingSubtractWithWork
  dsimp only
  split_ifs
  · exact Nat.zero_le _
  · simpa only [binaryNaturalSubtractWithWork, bitSubtractWithWork_length,
      Nat.size_eq_bits_len] using (le_refl (max (Nat.size a) (Nat.size b)))

/-- Construct a descriptor's clipped length by Boolean exponentiation,
subtraction and minimum, retaining the resulting bits. -/


theorem coarseDescriptorWithWork_value (B d n start : ℕ) :
    bitWordValue (coarseDescriptorWithWork B d n start).1 = coarseDescriptorLength B d n start := by
  simp only [coarseDescriptorWithWork, wordMinWithWork_value,
    bitPowerWithWork_value, bitWordValue_bits, saturatingSubtractWithWork_value,
    coarseDescriptorLength]

theorem coarseDescriptorWithWork_cost (B d n start A : ℕ)
    (hB : Nat.size B ≤ A) (hn : Nat.size n ≤ A) (hs : Nat.size start ≤ A) :
    (coarseDescriptorWithWork B d n start).2 ≤
      bitPowerBitBudget d A + 100 * (d + 2) * (A + 1) := by
  have hp := bitPowerWithWork_cost B.bits d A (by simpa only [Nat.size_eq_bits_len] using hB)
  have hpl := bitPowerWithWork_length_le B.bits d A (by simpa only [Nat.size_eq_bits_len] using hB)
  have hr := saturatingSubtractWithWork_cost n start
  have hrl := saturatingSubtractWithWork_length n start
  have hm := wordLEWithWork_cost (bitPowerWithWork B.bits d).1
    (saturatingSubtractWithWork n start).1
  have hd : Nat.size d ≤ d := Nat.size_le.mpr (Nat.lt_pow_self (by decide : 1 < (2 : ℕ)))
  simp only [coarseDescriptorWithWork, wordMinWithWork]
  nlinarith only [hp, hpl, hr, hrl, hm, hd, hB, hn, hs,
    max_le hn hs, Nat.zero_le d, Nat.zero_le A]

end EditApproximation

end OAI
