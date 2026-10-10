import Mathlib
import OAI.Analysis.LaughlinFock.Certificate11Data
import OAI.Analysis.LaughlinFock.GramCache
import OAI.Analysis.LaughlinFock.TraceSymmetry

namespace OAI

/-! Certificate11. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourYLower_11 (r s : CopyLabel 11) (hrs : s.val.val ≤ r.val.val) :
    integerRowsFourTrace 11 r s = fourYData_11 r s := by
  rw [integerRowsFourTrace_parts (by decide) collectedFourData_11 collectedFourChecked_11]
  fin_cases r <;> fin_cases s
  · exact fourYNumber_11_1_1
  · have h : (3:ℕ) ≤ 1 := hrs
    omega
  · have h : (5:ℕ) ≤ 1 := hrs
    omega
  · have h : (7:ℕ) ≤ 1 := hrs
    omega
  · have h : (9:ℕ) ≤ 1 := hrs
    omega
  · have h : (11:ℕ) ≤ 1 := hrs
    omega
  · exact fourYNumber_11_3_1
  · exact fourYNumber_11_3_3
  · have h : (5:ℕ) ≤ 3 := hrs
    omega
  · have h : (7:ℕ) ≤ 3 := hrs
    omega
  · have h : (9:ℕ) ≤ 3 := hrs
    omega
  · have h : (11:ℕ) ≤ 3 := hrs
    omega
  · exact fourYNumber_11_5_1
  · exact fourYNumber_11_5_3
  · exact fourYNumber_11_5_5
  · have h : (7:ℕ) ≤ 5 := hrs
    omega
  · have h : (9:ℕ) ≤ 5 := hrs
    omega
  · have h : (11:ℕ) ≤ 5 := hrs
    omega
  · exact fourYNumber_11_7_1
  · exact fourYNumber_11_7_3
  · exact fourYNumber_11_7_5
  · exact fourYNumber_11_7_7
  · have h : (9:ℕ) ≤ 7 := hrs
    omega
  · have h : (11:ℕ) ≤ 7 := hrs
    omega
  · exact fourYNumber_11_9_1
  · exact fourYNumber_11_9_3
  · exact fourYNumber_11_9_5
  · exact fourYNumber_11_9_7
  · exact fourYNumber_11_9_9
  · have h : (11:ℕ) ≤ 9 := hrs
    omega
  · exact fourYNumber_11_11_1
  · exact fourYNumber_11_11_3
  · exact fourYNumber_11_11_5
  · exact fourYNumber_11_11_7
  · exact fourYNumber_11_11_9
  · exact fourYNumber_11_11_11

theorem fourYChecked_11 (r s : CopyLabel 11) :
    integerRowsFourTrace 11 r s = fourYData_11 r s := by
  have hh : ∀ r s : CopyLabel 11, fourYData_11 r s = fourYData_11 s r := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  by_cases h : s.val.val ≤ r.val.val
  · exact fourYLower_11 r s h
  · rw [integerRowsFourTrace_symm, fourYLower_11 s r (by omega), hh]

def fourHighestCache_11_0 : List (Occupation 24 × List ℚ) := [
  ({0,1,2,9}, [232243200, 46448640, 7257600, -7983360, 2903040, 39916800]),
  ({0,1,3,8}, [-232243200, -46448640, -7257600, 7983360, -2903040, -39916800]),
  ({0,1,4,7}, [348364800, 38707200, 1209600, -3265920, -725760, 39916800]),
  ({0,1,5,6}, [-348364800, -38707200, 4320000, -604800, 3628800, -39916800])
]

def fourHighestCache_11_1 : List (Occupation 24 × List ℚ) := [
  ({0,2,3,7}, [-116121600, 7741440, 6048000, -4717440, 3628800, 0]),
  ({0,2,4,6}, [0, 0, -5529600, 3870720, -2903040, 0]),
  ({0,3,4,5}, [116121600, -7741440, 5011200, -3024000, 2177280, 0]),
  ({1,2,3,6}, [116121600, -7741440, -518400, 846720, -725760, 0])
]

def fourHighestCache_11_2 : List (Occupation 24 × List ℚ) := [
  ({1,2,4,5}, [-116121600, 7741440, 518400, -846720, 725760, 0])
]

def fourHighestCache_11 : List (Occupation 24 × List ℚ) := fourHighestCache_11_0 ++ fourHighestCache_11_1 ++ fourHighestCache_11_2

theorem fourHighestNumber_11_1 : ∀ A∈highestFourOccupations 11,
    kernelHighestEntry 11 ⟨⟨1,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_11 1 A := by
  rw [fourOccupations_11]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_11_3 : ∀ A∈highestFourOccupations 11,
    kernelHighestEntry 11 ⟨⟨3,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_11 3 A := by
  rw [fourOccupations_11]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_11_5 : ∀ A∈highestFourOccupations 11,
    kernelHighestEntry 11 ⟨⟨5,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_11 5 A := by
  rw [fourOccupations_11]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_11_7 : ∀ A∈highestFourOccupations 11,
    kernelHighestEntry 11 ⟨⟨7,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_11 7 A := by
  rw [fourOccupations_11]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_11_9 : ∀ A∈highestFourOccupations 11,
    kernelHighestEntry 11 ⟨⟨9,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_11 9 A := by
  rw [fourOccupations_11]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_11_11 : ∀ A∈highestFourOccupations 11,
    kernelHighestEntry 11 ⟨⟨11,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_11 11 A := by
  rw [fourOccupations_11]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestChecked_11 : ∀ r : CopyLabel 11, ∀ A∈highestFourOccupations 11,
    kernelHighestEntry 11 r A = highestLookup fourHighestCache_11 r.val.val A := by
  intro r
  fin_cases r
  · exact fourHighestNumber_11_1
  · exact fourHighestNumber_11_3
  · exact fourHighestNumber_11_5
  · exact fourHighestNumber_11_7
  · exact fourHighestNumber_11_9
  · exact fourHighestNumber_11_11

theorem fourZChecked_11 (r s : CopyLabel 11) :
    integerFourGram 11 r s = fourZData_11 r s := by
  rw [integerFourGram_cached 11 fourHighestCache_11 fourHighestChecked_11]
  have h : ∀ r s : CopyLabel 11, cachedFourGram 11 fourHighestCache_11 r s = fourZData_11 r s := by
    simp only [cachedFourGram, fourOccupations_11]
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact h r s

theorem fourLDLChecked_11 :
    fourZData_11 * (Matrix.diagonal (fun r : CopyLabel 11 =>
      ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 11 r.val.val) -
      Matrix.diagonal (fun r : CopyLabel 11 => rationalCopyDiagonal 11 r.val.val) *
        fourYData_11 * Matrix.diagonal (fun r : CopyLabel 11 => rationalCopyDiagonal 11 r.val.val)) *
      fourZData_11 = fourLData_11 * Matrix.diagonal fourPivotData_11 * (fourLData_11)ᵀ := by
  have h : ∀ r s : CopyLabel 11,
      (fourZData_11 * (Matrix.diagonal (fun r : CopyLabel 11 =>
        ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 11 r.val.val) -
        Matrix.diagonal (fun r : CopyLabel 11 => rationalCopyDiagonal 11 r.val.val) *
          fourYData_11 * Matrix.diagonal (fun r : CopyLabel 11 => rationalCopyDiagonal 11 r.val.val)) *
        fourZData_11 : Matrix (CopyLabel 11) (CopyLabel 11) ℚ) r s =
      (fourLData_11 * Matrix.diagonal fourPivotData_11 * (fourLData_11)ᵀ : Matrix (CopyLabel 11) (CopyLabel 11) ℚ) r s := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact Matrix.ext h

theorem fourPivotChecked_11 : ∀ r, 0 ≤ fourPivotData_11 r := by
  intro r
  fin_cases r <;> norm_num [fourPivotData_11, copyDiagonalData]

theorem integer_certificate_11 :
    ((integerCompression 11).map (algebraMap ℚ ℂ)).PosSemidef := by
  apply rational_ldl_posSemidef _ (fourLData_11) (fourPivotData_11) _ fourPivotChecked_11
  unfold integerCompression integerFourMiddle
  rw [show integerRowsFourTrace 11 = fourYData_11 from Matrix.ext fourYChecked_11,
    show integerFourGram 11 = fourZData_11 from Matrix.ext fourZChecked_11]
  exact fourLDLChecked_11

end LaughlinFock
end

end OAI
