import OAI.Combinatorics.EditApproximation.Queries.QueryOrderedInputs
import OAI.Combinatorics.EditApproximation.Geometry.LocalRefinementQuery
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Boolean arithmetic for the existing child/history key encodings.
The sorting comparison charges both encodings and the word comparison. -/

namespace EditApproximation



@[simp] theorem queryChildCodeWithWork_value {M n : ℕ} (input : Fin M × TargetInterval n) :
    (queryChildCodeWithWork input).1 = childInputCode input := by
  simp only [queryChildCodeWithWork, binaryNaturalAddWithWork_value,
    binaryNaturalMulWithWork_value, childInputCode]



@[simp] theorem queryPairWithWork_value (a b : ℕ) :
    (queryPairWithWork a b).1 = Nat.pair a b := by
  unfold queryPairWithWork Nat.pair
  by_cases h : a < b
  · rw [ite_eq_left ((binaryNaturalCompareWithWork_lt a b).mpr h), ite_eq_left h]
    simp only [binaryNaturalAddWithWork_value, binaryNaturalMulWithWork_value]
  · rw [ite_eq_right (fun ht => h ((binaryNaturalCompareWithWork_lt a b).mp ht)), ite_eq_right h]
    simp only [binaryNaturalAddWithWork_value, binaryNaturalMulWithWork_value]



@[simp] theorem queryHistoryCodeWithWork_value {M n : ℕ} (input : Fin M × ℕ × TargetInterval n) :
    (queryHistoryCodeWithWork input).1 = historyInputCode input := by
  simp only [queryHistoryCodeWithWork, queryPairWithWork_value, queryChildCodeWithWork_value,
    historyInputCode]



theorem queryEncodedLEWithWork_value {α : Type*} (code : α → ℕ × ℕ) (a b : α) :
    (queryEncodedLEWithWork code a b).1 = decide ((code a).1 ≤ (code b).1) := by
  apply Bool.eq_iff_iff.mpr
  simp only [queryEncodedLEWithWork, wordLEWithWork_value, bitWordValue_bits, decide_eq_true_eq]



@[simp] theorem queryOrderedChildInputsWithWork_value {M n : ℕ}
    (inputs : List (Fin M × TargetInterval n)) :
    (queryOrderedChildInputsWithWork inputs).1 =
      orderedInputs childInputCode (childInputCode_injective M n) inputs.toFinset := by
  apply queryOrderedInputsWithWork_value childInputCode (childInputCode_injective M n)
    _ _ coordinateEqualWithWork_value
  intro a b
  simp only [queryEncodedLEWithWork_value, queryChildCodeWithWork_value]



@[simp] theorem queryHistoryEqualWithWork_value {M n : ℕ} (a b : Fin M × ℕ × TargetInterval n) :
    (queryHistoryEqualWithWork a b).1 = true ↔ a = b := by
  simp only [queryHistoryEqualWithWork, Bool.and_eq_true, coordinateEqualWithWork_value,
    naturalEqualWithWork_value, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hi, hq⟩, ht⟩
    exact Prod.ext hi (Prod.ext ht hq)
  · intro h
    subst b
    exact ⟨⟨rfl, rfl⟩, rfl⟩



@[simp] theorem queryOrderedHistoryInputsWithWork_value {M n : ℕ}
    (inputs : List (Fin M × ℕ × TargetInterval n)) :
    (queryOrderedHistoryInputsWithWork inputs).1 =
      orderedInputs historyInputCode (historyInputCode_injective M n) inputs.toFinset := by
  apply queryOrderedInputsWithWork_value historyInputCode (historyInputCode_injective M n)
    _ _ queryHistoryEqualWithWork_value
  intro a b
  simp only [queryEncodedLEWithWork_value, queryHistoryCodeWithWork_value]

end EditApproximation

end OAI
