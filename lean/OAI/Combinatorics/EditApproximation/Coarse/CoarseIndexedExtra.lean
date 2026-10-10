import OAI.Combinatorics.EditApproximation.Coarse.CoarseIndexedValue

namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- All descriptor and original-input operations alongside the core
arithmetic. Threshold decisions are exactly those of the evaluated call. -/
def coarseIndexedExtra {B : ℕ} (k q L n : ℕ) (source target : List ℕ)
    (two : BinaryFraction) : (d offset : ℕ) → CoarseThresholdDraws B d →
    BinaryFraction → ℕ → ℕ
  | 0, offset, _, allowance, start =>
    let descriptor := coarseDescriptorWithWork B 0 n offset
    if (leWithWork (nat (coarseDescriptorLength B 0 n offset)) allowance).1 then descriptor.2 else
    let letter := coarsePaddedReadWithWork n source offset
    descriptor.2 + letter.2 + ((List.finRange (2 * k + 1)).map fun shift =>
      (coarseReadShiftWithWork k n target letter.1 start shift).2).sum
  | d + 1, offset, (draws, below), allowance, start =>
    let descriptor := coarseDescriptorWithWork B (d + 1) n offset
    if (leWithWork (nat (coarseDescriptorLength B (d + 1) n offset)) allowance).1 then descriptor.2 else
    let capacity := bitPowerWithWork B.bits d
    let childOffset := fun i : Fin B => coarseChildOffsetWithWork offset (bitWordValue capacity.1) i.val
    let childSize := fun i : Fin B => coarseDescriptorWithWork B d n (bitWordValue (childOffset i).1)
    descriptor.2 + capacity.2 + coarseIndexAdditionalWork q L
      (fun i => coarseDescriptorLength B d n (offset + i.val * B ^ d)) draws
      (fun i a s => coarseIndexedExtra k q L n source target two d (offset + i.val * B ^ d) (below i) a s +
        3 * ((childOffset i).2 + (childSize i).2 +
          (binaryNaturalAddWithWork s (bitWordValue (childSize i).1)).2 + 3))
      allowance (List.finRange B) start

end BinaryFraction
end EditApproximation

end OAI
