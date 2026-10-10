import Mathlib
import OAI.Analysis.LaughlinFock.Certificate10Data
import OAI.Analysis.LaughlinFock.GramCache
import OAI.Analysis.LaughlinFock.TraceSymmetry

namespace OAI

/-! Certificate10. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourYLower_10 (r s : CopyLabel 10) (hrs : s.val.val ≤ r.val.val) :
    integerRowsFourTrace 10 r s = fourYData_10 r s := by
  rw [integerRowsFourTrace_parts (by decide) collectedFourData_10 collectedFourChecked_10]
  fin_cases r <;> fin_cases s
  · exact fourYNumber_10_1_1
  · have h : (3:ℕ) ≤ 1 := hrs
    omega
  · have h : (5:ℕ) ≤ 1 := hrs
    omega
  · have h : (7:ℕ) ≤ 1 := hrs
    omega
  · have h : (9:ℕ) ≤ 1 := hrs
    omega
  · exact fourYNumber_10_3_1
  · exact fourYNumber_10_3_3
  · have h : (5:ℕ) ≤ 3 := hrs
    omega
  · have h : (7:ℕ) ≤ 3 := hrs
    omega
  · have h : (9:ℕ) ≤ 3 := hrs
    omega
  · exact fourYNumber_10_5_1
  · exact fourYNumber_10_5_3
  · exact fourYNumber_10_5_5
  · have h : (7:ℕ) ≤ 5 := hrs
    omega
  · have h : (9:ℕ) ≤ 5 := hrs
    omega
  · exact fourYNumber_10_7_1
  · exact fourYNumber_10_7_3
  · exact fourYNumber_10_7_5
  · exact fourYNumber_10_7_7
  · have h : (9:ℕ) ≤ 7 := hrs
    omega
  · exact fourYNumber_10_9_1
  · exact fourYNumber_10_9_3
  · exact fourYNumber_10_9_5
  · exact fourYNumber_10_9_7
  · exact fourYNumber_10_9_9

theorem fourYChecked_10 (r s : CopyLabel 10) :
    integerRowsFourTrace 10 r s = fourYData_10 r s := by
  have hh : ∀ r s : CopyLabel 10, fourYData_10 r s = fourYData_10 s r := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  by_cases h : s.val.val ≤ r.val.val
  · exact fourYLower_10 r s h
  · rw [integerRowsFourTrace_symm, fourYLower_10 s r (by omega), hh]

def fourHighestCache_10_0 : List (Occupation 24 × List ℚ) := [
  ({0,1,2,8}, [0, -3870720, 0, 725760, -1451520]),
  ({0,1,3,7}, [0, 3870720, 0, -725760, 1451520]),
  ({0,1,4,6}, [0, -1935360, 0, 362880, -725760]),
  ({0,2,3,6}, [0, -1935360, 0, 362880, -725760])
]

def fourHighestCache_10_1 : List (Occupation 24 × List ℚ) := [
  ({0,2,4,5}, [0, 1935360, 0, -362880, 725760]),
  ({1,2,3,5}, [0, 0, 0, 0, 0])
]

def fourHighestCache_10 : List (Occupation 24 × List ℚ) := fourHighestCache_10_0 ++ fourHighestCache_10_1

theorem fourHighestNumber_10_1 : ∀ A∈highestFourOccupations 10,
    kernelHighestEntry 10 ⟨⟨1,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_10 1 A := by
  rw [fourOccupations_10]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_10_3 : ∀ A∈highestFourOccupations 10,
    kernelHighestEntry 10 ⟨⟨3,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_10 3 A := by
  rw [fourOccupations_10]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_10_5 : ∀ A∈highestFourOccupations 10,
    kernelHighestEntry 10 ⟨⟨5,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_10 5 A := by
  rw [fourOccupations_10]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_10_7 : ∀ A∈highestFourOccupations 10,
    kernelHighestEntry 10 ⟨⟨7,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_10 7 A := by
  rw [fourOccupations_10]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_10_9 : ∀ A∈highestFourOccupations 10,
    kernelHighestEntry 10 ⟨⟨9,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_10 9 A := by
  rw [fourOccupations_10]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestChecked_10 : ∀ r : CopyLabel 10, ∀ A∈highestFourOccupations 10,
    kernelHighestEntry 10 r A = highestLookup fourHighestCache_10 r.val.val A := by
  intro r
  fin_cases r
  · exact fourHighestNumber_10_1
  · exact fourHighestNumber_10_3
  · exact fourHighestNumber_10_5
  · exact fourHighestNumber_10_7
  · exact fourHighestNumber_10_9

theorem fourZChecked_10 (r s : CopyLabel 10) :
    integerFourGram 10 r s = fourZData_10 r s := by
  rw [integerFourGram_cached 10 fourHighestCache_10 fourHighestChecked_10]
  have h : ∀ r s : CopyLabel 10, cachedFourGram 10 fourHighestCache_10 r s = fourZData_10 r s := by
    simp only [cachedFourGram, fourOccupations_10]
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact h r s

theorem fourLDLChecked_10 :
    fourZData_10 * (Matrix.diagonal (fun r : CopyLabel 10 =>
      ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 10 r.val.val) -
      Matrix.diagonal (fun r : CopyLabel 10 => rationalCopyDiagonal 10 r.val.val) *
        fourYData_10 * Matrix.diagonal (fun r : CopyLabel 10 => rationalCopyDiagonal 10 r.val.val)) *
      fourZData_10 = fourLData_10 * Matrix.diagonal fourPivotData_10 * (fourLData_10)ᵀ := by
  have h : ∀ r s : CopyLabel 10,
      (fourZData_10 * (Matrix.diagonal (fun r : CopyLabel 10 =>
        ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 10 r.val.val) -
        Matrix.diagonal (fun r : CopyLabel 10 => rationalCopyDiagonal 10 r.val.val) *
          fourYData_10 * Matrix.diagonal (fun r : CopyLabel 10 => rationalCopyDiagonal 10 r.val.val)) *
        fourZData_10 : Matrix (CopyLabel 10) (CopyLabel 10) ℚ) r s =
      (fourLData_10 * Matrix.diagonal fourPivotData_10 * (fourLData_10)ᵀ : Matrix (CopyLabel 10) (CopyLabel 10) ℚ) r s := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact Matrix.ext h

theorem fourPivotChecked_10 : ∀ r, 0 ≤ fourPivotData_10 r := by
  intro r
  fin_cases r <;> norm_num [fourPivotData_10, copyDiagonalData]

theorem integer_certificate_10 :
    ((integerCompression 10).map (algebraMap ℚ ℂ)).PosSemidef := by
  apply rational_ldl_posSemidef _ (fourLData_10) (fourPivotData_10) _ fourPivotChecked_10
  unfold integerCompression integerFourMiddle
  rw [show integerRowsFourTrace 10 = fourYData_10 from Matrix.ext fourYChecked_10,
    show integerFourGram 10 = fourZData_10 from Matrix.ext fourZChecked_10]
  exact fourLDLChecked_10

end LaughlinFock
end

end OAI
