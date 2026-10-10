import OAI.Combinatorics.EditApproximation.Coarse.CoarseIndexedExecution

namespace OAI

namespace EditApproximation
namespace BinaryFraction

attribute [local irreducible] coarseIndexedWithWork coarseReadCore

/-- Charging descriptor/read operations leaves the indexed arithmetic
result unchanged, on every draw and every pruning branch. -/
theorem coarseIndexedWithWork_value {B : ℕ} (k q L n : ℕ) (source target : List ℕ)
    (two : BinaryFraction) (d offset : ℕ) (draws : CoarseThresholdDraws B d)
    (allowance : BinaryFraction) (start : ℕ) :
    (coarseIndexedWithWork k q L n source target two d offset draws allowance start).1 =
      (coarseReadCore k q L n source target two d offset draws allowance start).1 := by
  induction d generalizing offset allowance start with
  | zero =>
    rw [coarseIndexedWithWork, coarseReadCore]
    simp only [coarseDescriptorWithWork_value, coarsePaddedReadWithWork_value]
    split_ifs
    · rfl
    · simp only [arithmeticMapWithWork_value, coarseReadShiftWithWork_value]
  | succ d ih =>
    obtain ⟨draws, below⟩ := draws
    have hloop := coarseIndexChildren_value_congr k q L two
      (fun i : Fin B => coarseDescriptorLength B d n (offset + i.val * B ^ d)) draws
      (fun i a s =>
        let childOffset := coarseChildOffsetWithWork offset (bitWordValue (bitPowerWithWork B.bits d).1) i.val
        let childSize := coarseDescriptorWithWork B d n (bitWordValue childOffset.1)
        let evaluated := coarseIndexedWithWork k q L n source target two d
          (bitWordValue childOffset.1) (below i) a s
        let next := binaryNaturalAddWithWork s (bitWordValue childSize.1)
        (evaluated.1, evaluated.2 + 3 * (childOffset.2 + childSize.2 + next.2 + 3)))
      (fun i => coarseReadCore k q L n source target two d (offset + i.val * B ^ d) (below i))
      (by
        intro i a s
        simp only [coarseChildOffsetWithWork_value, bitPowerWithWork_value, bitWordValue_bits]
        exact ih (offset + i.val * B ^ d) (below i) a s)
      allowance (List.finRange B) start
    erw [coarseIndexedWithWork, coarseReadCore]
    simp only [coarseDescriptorWithWork_value, coarseChildOffsetWithWork_value,
      bitPowerWithWork_value, bitWordValue_bits]
    split_ifs
    · rfl
    · simpa only [coarseChildOffsetWithWork_value, bitPowerWithWork_value, bitWordValue_bits,
        coarseDescriptorWithWork_value] using hloop

end BinaryFraction
end EditApproximation

end OAI
