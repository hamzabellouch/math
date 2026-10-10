import OAI.Combinatorics.EditApproximation.Queries.QueryOrderedSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryGridSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryActionInputs
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation



theorem queryChildCodeAllocation_le_work {M n : ℕ} (input : Fin M × TargetInterval n) :
    queryChildCodeAllocation input ≤ (queryChildCodeWithWork input).2 := by
  have h1 := binaryNaturalAddAllocation_le_work n 1
  have h2 := binaryNaturalMulAllocation_le_work (bitWordValue (binaryNaturalAddWithWork n 1).1) input.2.hi
  have h3 := binaryNaturalAddAllocation_le_work input.2.lo
    (bitWordValue (binaryNaturalMulWithWork (bitWordValue (binaryNaturalAddWithWork n 1).1) input.2.hi).1)
  have h4 := binaryNaturalMulAllocation_le_work M
    (bitWordValue (binaryNaturalAddWithWork input.2.lo
      (bitWordValue (binaryNaturalMulWithWork (bitWordValue (binaryNaturalAddWithWork n 1).1) input.2.hi).1)).1)
  have h5 := binaryNaturalAddAllocation_le_work input.1.val
    (bitWordValue (binaryNaturalMulWithWork M (bitWordValue (binaryNaturalAddWithWork input.2.lo
      (bitWordValue (binaryNaturalMulWithWork (bitWordValue (binaryNaturalAddWithWork n 1).1) input.2.hi).1)).1)).1)
  unfold queryChildCodeAllocation queryChildCodeWithWork
  dsimp only
  omega



theorem queryPairAllocation_le_work (a b : ℕ) : queryPairAllocation a b ≤ (queryPairWithWork a b).2 := by
  have hc := bitCompareWithWork_input_cells a.bits b.bits
  have h1 := binaryNaturalMulAllocation_le_work b b
  have h2 := binaryNaturalAddAllocation_le_work (bitWordValue (binaryNaturalMulWithWork b b).1) a
  have h3 := binaryNaturalMulAllocation_le_work a a
  have h4 := binaryNaturalAddAllocation_le_work (bitWordValue (binaryNaturalMulWithWork a a).1) a
  have h5 := binaryNaturalAddAllocation_le_work
    (bitWordValue (binaryNaturalAddWithWork (bitWordValue (binaryNaturalMulWithWork a a).1) a).1) b
  change a.bits.length + b.bits.length ≤ (binaryNaturalCompareWithWork a b).2 at hc
  unfold queryPairAllocation queryPairWithWork
  dsimp only
  split_ifs <;> dsimp only <;> omega



theorem queryHistoryCodeAllocation_le_work {M n : ℕ} (input : Fin M × ℕ × TargetInterval n) :
    queryHistoryCodeAllocation input ≤ (queryHistoryCodeWithWork input).2 := by
  have hc := queryChildCodeAllocation_le_work (input.1, input.2.2)
  have hp := queryPairAllocation_le_work input.2.1 (queryChildCodeWithWork (input.1, input.2.2)).1
  unfold queryHistoryCodeAllocation queryHistoryCodeWithWork
  dsimp only
  omega



theorem queryEncodedLEAllocation_le_work {α : Type*} (code : α → ℕ × ℕ) (allocation : α → ℕ)
    (a b : α) (h : ∀ x, allocation x ≤ (code x).2) :
    queryEncodedLEAllocation code allocation a b ≤ (queryEncodedLEWithWork code a b).2 := by
  have ha := h a
  have hb := h b
  have hc := naturalWordLEAllocation_le_work (code a).1.bits (code b).1.bits
  unfold queryEncodedLEAllocation queryEncodedLEWithWork
  dsimp only
  omega



theorem queryOrderedChildInputsAllocation_le_work {M n : ℕ} (inputs : List (Fin M × TargetInterval n)) :
    queryOrderedChildInputsAllocation inputs ≤ (queryOrderedChildInputsWithWork inputs).2 :=
  queryOrderedInputsAllocation_le_work _ _ _ _ inputs coordinateEqualAllocation_le_work
    (fun a b => queryEncodedLEAllocation_le_work _ _ a b queryChildCodeAllocation_le_work)



theorem queryOrderedHistoryInputsAllocation_le_work {M n : ℕ} (inputs : List (Fin M × ℕ × TargetInterval n)) :
    queryOrderedHistoryInputsAllocation inputs ≤ (queryOrderedHistoryInputsWithWork inputs).2 :=
  queryOrderedInputsAllocation_le_work _ _ _ _ inputs queryHistoryEqualAllocation_le_work
    (fun a b => queryEncodedLEAllocation_le_work _ _ a b queryHistoryCodeAllocation_le_work)



theorem queryActionInputsAllocation_le_work {Parent Child : Type*} {M : ℕ}
    (actions : List (BinaryBellmanAction Parent Child M)) :
    queryActionInputsAllocation actions ≤ (queryActionInputsWithWork actions).2 := by
  have h := arithmeticFlatMapAllocation_le_work
    (fun action => arithmeticMapWithWork (fun i : Fin M => (action.childState i, 1)) (List.finRange M))
    (fun _ => arithmeticMapAllocation (fun _ : Fin M => 1) (List.finRange M) + M) actions (by
      intro action _
      simpa only [List.length_finRange] using arithmeticMapAllocation_with_spine
        (fun i : Fin M => (action.childState i, 1)) (fun _ => 1) (List.finRange M) (fun _ _ => le_rfl))
  unfold queryActionInputsAllocation queryActionInputsWithWork
  dsimp only
  omega



theorem queryNeededInputsAllocation_le_work {n M : ℕ}
    (selected online : List (BinaryBellmanAction (TargetInterval n) (Fin M × TargetInterval n) M)) :
    queryNeededInputsAllocation selected online ≤ (queryNeededInputsWithWork selected online).2 := by
  have hf := queryActionInputsAllocation_le_work selected
  have hs := queryActionInputsAllocation_le_work online
  have ho := queryOrderedChildInputsAllocation_le_work
    ((queryActionInputsWithWork selected).1 ++ (queryActionInputsWithWork online).1)
  unfold queryNeededInputsAllocation queryNeededInputsWithWork
  dsimp only
  omega

end EditApproximation

end OAI
