import OAI.Combinatorics.EditApproximation.Numerics.ScalarControlSpace
import OAI.Combinatorics.EditApproximation.Coarse.CoarseReadAccess
import OAI.Combinatorics.EditApproximation.Coarse.CoarseReadLeafWork

namespace OAI

namespace EditApproximation

def saturatingSubtractInvocations (a b : ℕ) : ℕ :=
  bitCompareInvocations a.bits b.bits + 1 +
    if (binaryNaturalCompareWithWork a b).1 = .lt then 0
    else bitSubtractInvocations a.bits b.bits false

theorem saturatingSubtractInvocations_le_work (a b : ℕ) :
    saturatingSubtractInvocations a b ≤ (saturatingSubtractWithWork a b).2 := by
  have hc := bitCompareInvocations_le_work a.bits b.bits
  have hs := bitSubtractInvocations_le_work a.bits b.bits false
  unfold saturatingSubtractInvocations saturatingSubtractWithWork
  dsimp only
  split_ifs <;> simp only [binaryNaturalSubtractWithWork, binaryNaturalCompareWithWork] at * <;> omega

def coarseDescriptorInvocations (B d n start : ℕ) : ℕ :=
  bitPowerInvocations B.bits d + saturatingSubtractInvocations n start +
    bitCompareInvocations (saturatingSubtractWithWork n start).1 (bitPowerWithWork B.bits d).1 + 3

theorem coarseDescriptorInvocations_le_work (B d n start : ℕ) :
    coarseDescriptorInvocations B d n start ≤ (coarseDescriptorWithWork B d n start).2 := by
  have hp := bitPowerInvocations_le_work B.bits d
  have hs := saturatingSubtractInvocations_le_work n start
  have hc := bitCompareInvocations_le_work (saturatingSubtractWithWork n start).1
    (bitPowerWithWork B.bits d).1
  unfold coarseDescriptorInvocations coarseDescriptorWithWork
  simp only [wordMinWithWork, wordLEWithWork]
  omega

def coarseChildOffsetInvocations (offset capacity index : ℕ) : ℕ :=
  bitMulInvocations index.bits capacity.bits +
    bitAddInvocations offset.bits (bitWordValue (binaryNaturalMulWithWork index capacity).1).bits false + 1

theorem coarseChildOffsetInvocations_le_work (offset capacity index : ℕ) :
    coarseChildOffsetInvocations offset capacity index ≤ (coarseChildOffsetWithWork offset capacity index).2 := by
  have hm := bitMulInvocations_le_work index.bits capacity.bits
  have ha := bitAddInvocations_le_work offset.bits
    (bitWordValue (binaryNaturalMulWithWork index capacity).1).bits false
  unfold coarseChildOffsetInvocations coarseChildOffsetWithWork
  simp only [binaryNaturalMulWithWork, binaryNaturalAddWithWork] at ha ⊢
  omega

def coarsePaddedReadInvocations (n offset : ℕ) : ℕ := bitCompareInvocations offset.bits n.bits + 1

theorem coarsePaddedReadInvocations_le_work {α : Type*} (n : ℕ) (source : List α) (offset : ℕ) :
    coarsePaddedReadInvocations n offset ≤ (coarsePaddedReadWithWork n source offset).2 := by
  have hc := bitCompareInvocations_le_work offset.bits n.bits
  unfold coarsePaddedReadInvocations coarsePaddedReadWithWork binaryNaturalCompareWithWork
  dsimp only
  omega

def coarseFramedReadInvocations (k n i : ℕ) : ℕ :=
  bitCompareInvocations i.bits k.bits + 1 +
    if (binaryNaturalCompareWithWork i k).1 = .lt then 0 else
      bitAddInvocations k.bits n.bits false +
        bitCompareInvocations i.bits (bitWordValue (binaryNaturalAddWithWork k n).1).bits +
        if (binaryNaturalCompareWithWork i (bitWordValue (binaryNaturalAddWithWork k n).1)).1 = .lt
        then saturatingSubtractInvocations i k else 0

theorem coarseFramedReadInvocations_le_work {α : Type*} (k n : ℕ) (word : List α) (i : ℕ) :
    coarseFramedReadInvocations k n i ≤ (coarseFramedReadWithWork k n word i).2 := by
  have hl := bitCompareInvocations_le_work i.bits k.bits
  have ha := bitAddInvocations_le_work k.bits n.bits false
  have hu := bitCompareInvocations_le_work i.bits (bitWordValue (binaryNaturalAddWithWork k n).1).bits
  have hs := saturatingSubtractInvocations_le_work i k
  unfold coarseFramedReadInvocations coarseFramedReadWithWork
  dsimp only
  split_ifs <;> simp only [binaryNaturalAddWithWork, binaryNaturalCompareWithWork] at * <;> omega

def coarseLetterMatchInvocations : Option (Option ℕ) → Option ℕ → ℕ
  | some (some a), some b => bitCompareInvocations a.bits b.bits + 1
  | _, _ => 1

theorem coarseLetterMatchInvocations_le_work (actual : Option (Option ℕ)) (wanted : Option ℕ) :
    coarseLetterMatchInvocations actual wanted ≤ (coarseLetterMatchWithWork actual wanted).2 := by
  cases actual with
  | none => cases wanted <;> exact Nat.le_refl 1
  | some actual =>
    cases actual with
    | none => cases wanted <;> exact Nat.le_refl 1
    | some a =>
      cases wanted with
      | none => exact Nat.le_refl 1
      | some b =>
        have h := bitCompareInvocations_le_work a.bits b.bits
        exact Nat.add_le_add_right h 1

namespace BinaryFraction

def coarseReadShiftInvocations (k n : ℕ) (target : List ℕ) (letter : Option (Option ℕ))
    (start : ℕ) (shift : Fin (2 * k + 1)) : ℕ :=
  match letter with
  | none => 1
  | some wanted =>
    let position := binaryNaturalAddWithWork start shift.val
    bitAddInvocations start.bits shift.val.bits false +
      coarseFramedReadInvocations k n (bitWordValue position.1) +
      coarseLetterMatchInvocations (coarseFramedReadWithWork k n target (bitWordValue position.1)).1 wanted + 1

theorem coarseReadShiftInvocations_le_work (k n : ℕ) (target : List ℕ)
    (letter : Option (Option ℕ)) (start : ℕ) (shift : Fin (2 * k + 1)) :
    coarseReadShiftInvocations k n target letter start shift ≤ (coarseReadShiftWithWork k n target letter start shift).2 := by
  cases letter with
  | none => exact Nat.le_refl 1
  | some letter =>
    have ha := bitAddInvocations_le_work start.bits shift.val.bits false
    have hf := coarseFramedReadInvocations_le_work k n target
      (bitWordValue (binaryNaturalAddWithWork start shift.val).1)
    have hm := coarseLetterMatchInvocations_le_work
      (coarseFramedReadWithWork k n target (bitWordValue (binaryNaturalAddWithWork start shift.val).1)).1 letter
    unfold coarseReadShiftInvocations coarseReadShiftWithWork
    simp only [binaryNaturalAddWithWork] at hf hm ⊢
    omega

end BinaryFraction
end EditApproximation

end OAI
