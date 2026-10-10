import OAI.Combinatorics.EditApproximation.Numerics.ScalarAllocation
import OAI.Combinatorics.EditApproximation.Coarse.CoarseReadAccess
import OAI.Combinatorics.EditApproximation.Coarse.CoarseReadLeafWork

namespace OAI

namespace EditApproximation

/-- Comparisons and minimum reuse their input bit arrays. -/
def coarseSaturatingSubtractAllocation (a b : ℕ) : ℕ :=
  if (binaryNaturalCompareWithWork a b).1 = .lt then 0
  else bitSubtractAllocation a.bits b.bits false

theorem coarseSaturatingSubtractAllocation_le_work (a b : ℕ) :
    coarseSaturatingSubtractAllocation a b ≤ (saturatingSubtractWithWork a b).2 := by
  have hs := bitSubtractAllocation_le_work a.bits b.bits false
  unfold coarseSaturatingSubtractAllocation saturatingSubtractWithWork
  dsimp only
  split_ifs <;> simp only [binaryNaturalSubtractWithWork] <;> omega

def coarseDescriptorAllocation (B d n start : ℕ) : ℕ :=
  bitPowerAllocation B.bits d + coarseSaturatingSubtractAllocation n start +
    Nat.size B + Nat.size d + Nat.size n + Nat.size start

theorem coarseDescriptorAllocation_le_work (B d n start : ℕ) :
    coarseDescriptorAllocation B d n start ≤ (coarseDescriptorWithWork B d n start).2 := by
  have hp := bitPowerAllocation_le_work B.bits d
  have hs := coarseSaturatingSubtractAllocation_le_work n start
  unfold coarseDescriptorAllocation coarseDescriptorWithWork
  dsimp only
  omega

def coarseChildOffsetAllocation (offset capacity index : ℕ) : ℕ :=
  bitMulAllocation index.bits capacity.bits +
    bitAddAllocation offset.bits (bitWordValue (binaryNaturalMulWithWork index capacity).1).bits false +
    Nat.size index + Nat.size capacity + Nat.size offset

theorem coarseChildOffsetAllocation_le_work (offset capacity index : ℕ) :
    coarseChildOffsetAllocation offset capacity index ≤ (coarseChildOffsetWithWork offset capacity index).2 := by
  have hm := bitMulAllocation_le_work index.bits capacity.bits
  have ha := bitAddAllocation_le_work offset.bits
    (bitWordValue (binaryNaturalMulWithWork index capacity).1).bits false
  unfold coarseChildOffsetAllocation coarseChildOffsetWithWork
  simp only [binaryNaturalMulWithWork, binaryNaturalAddWithWork] at ha ⊢
  omega

def coarseFramedReadAllocation (k n i : ℕ) : ℕ :=
  Nat.size k + Nat.size n + Nat.size i +
    if (binaryNaturalCompareWithWork i k).1 = .lt then 0 else
      bitAddAllocation k.bits n.bits false +
        if (binaryNaturalCompareWithWork i (bitWordValue (binaryNaturalAddWithWork k n).1)).1 = .lt
        then coarseSaturatingSubtractAllocation i k else 0

theorem coarseFramedReadAllocation_le_work {α : Type*} (k n : ℕ) (word : List α) (i : ℕ) :
    coarseFramedReadAllocation k n i ≤ (coarseFramedReadWithWork k n word i).2 := by
  have ha := bitAddAllocation_le_work k.bits n.bits false
  have hs := coarseSaturatingSubtractAllocation_le_work i k
  unfold coarseFramedReadAllocation coarseFramedReadWithWork
  dsimp only
  split_ifs <;> simp only [binaryNaturalAddWithWork] at * <;> omega

namespace BinaryFraction

def coarseReadShiftAllocation (k n : ℕ) (letter : Option (Option ℕ))
    (start : ℕ) (shift : Fin (2 * k + 1)) : ℕ :=
  match letter with
  | none => 0
  | some _ =>
    bitAddAllocation start.bits shift.val.bits false +
      coarseFramedReadAllocation k n (bitWordValue (binaryNaturalAddWithWork start shift.val).1)

theorem coarseReadShiftAllocation_le_work (k n : ℕ) (target : List ℕ)
    (letter : Option (Option ℕ)) (start : ℕ) (shift : Fin (2 * k + 1)) :
    coarseReadShiftAllocation k n letter start shift ≤ (coarseReadShiftWithWork k n target letter start shift).2 := by
  cases letter with
  | none => exact Nat.zero_le _
  | some letter =>
    have ha := bitAddAllocation_le_work start.bits shift.val.bits false
    have hf := coarseFramedReadAllocation_le_work k n target
      (bitWordValue (binaryNaturalAddWithWork start shift.val).1)
    unfold coarseReadShiftAllocation coarseReadShiftWithWork
    simp only [binaryNaturalAddWithWork] at hf ⊢
    omega

end BinaryFraction
end EditApproximation

end OAI
