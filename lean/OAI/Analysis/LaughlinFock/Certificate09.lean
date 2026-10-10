import Mathlib
import OAI.Analysis.LaughlinFock.Certificate09Data
import OAI.Analysis.LaughlinFock.GramCache
import OAI.Analysis.LaughlinFock.TraceSymmetry

namespace OAI

/-! Certificate09. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourYLower_9 (r s : CopyLabel 9) (hrs : s.val.val ≤ r.val.val) :
    integerRowsFourTrace 9 r s = fourYData_9 r s := by
  rw [integerRowsFourTrace_parts (by decide) collectedFourData_9 collectedFourChecked_9]
  fin_cases r <;> fin_cases s
  · exact fourYNumber_9_1_1
  · have h : (3:ℕ) ≤ 1 := hrs
    omega
  · have h : (5:ℕ) ≤ 1 := hrs
    omega
  · have h : (7:ℕ) ≤ 1 := hrs
    omega
  · have h : (9:ℕ) ≤ 1 := hrs
    omega
  · exact fourYNumber_9_3_1
  · exact fourYNumber_9_3_3
  · have h : (5:ℕ) ≤ 3 := hrs
    omega
  · have h : (7:ℕ) ≤ 3 := hrs
    omega
  · have h : (9:ℕ) ≤ 3 := hrs
    omega
  · exact fourYNumber_9_5_1
  · exact fourYNumber_9_5_3
  · exact fourYNumber_9_5_5
  · have h : (7:ℕ) ≤ 5 := hrs
    omega
  · have h : (9:ℕ) ≤ 5 := hrs
    omega
  · exact fourYNumber_9_7_1
  · exact fourYNumber_9_7_3
  · exact fourYNumber_9_7_5
  · exact fourYNumber_9_7_7
  · have h : (9:ℕ) ≤ 7 := hrs
    omega
  · exact fourYNumber_9_9_1
  · exact fourYNumber_9_9_3
  · exact fourYNumber_9_9_5
  · exact fourYNumber_9_9_7
  · exact fourYNumber_9_9_9

theorem fourYChecked_9 (r s : CopyLabel 9) :
    integerRowsFourTrace 9 r s = fourYData_9 r s := by
  have hh : ∀ r s : CopyLabel 9, fourYData_9 r s = fourYData_9 s r := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  by_cases h : s.val.val ≤ r.val.val
  · exact fourYLower_9 r s h
  · rw [integerRowsFourTrace_symm, fourYLower_9 s r (by omega), hh]

def fourHighestCache_9_0 : List (Occupation 24 × List ℚ) := [
  ({0,1,2,7}, [1935360, 241920, -60480, -30240, 362880]),
  ({0,1,3,6}, [-1935360, -241920, 60480, 30240, -362880]),
  ({0,1,4,5}, [2580480, 138240, -34560, -40320, 362880]),
  ({0,2,3,5}, [-645120, 103680, -25920, 10080, 0])
]

def fourHighestCache_9_1 : List (Occupation 24 × List ℚ) := [
  ({1,2,3,4}, [645120, -103680, 25920, -10080, 0])
]

def fourHighestCache_9 : List (Occupation 24 × List ℚ) := fourHighestCache_9_0 ++ fourHighestCache_9_1

theorem fourHighestNumber_9_1 : ∀ A∈highestFourOccupations 9,
    kernelHighestEntry 9 ⟨⟨1,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_9 1 A := by
  rw [fourOccupations_9]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_9_3 : ∀ A∈highestFourOccupations 9,
    kernelHighestEntry 9 ⟨⟨3,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_9 3 A := by
  rw [fourOccupations_9]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_9_5 : ∀ A∈highestFourOccupations 9,
    kernelHighestEntry 9 ⟨⟨5,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_9 5 A := by
  rw [fourOccupations_9]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_9_7 : ∀ A∈highestFourOccupations 9,
    kernelHighestEntry 9 ⟨⟨7,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_9 7 A := by
  rw [fourOccupations_9]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_9_9 : ∀ A∈highestFourOccupations 9,
    kernelHighestEntry 9 ⟨⟨9,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_9 9 A := by
  rw [fourOccupations_9]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestChecked_9 : ∀ r : CopyLabel 9, ∀ A∈highestFourOccupations 9,
    kernelHighestEntry 9 r A = highestLookup fourHighestCache_9 r.val.val A := by
  intro r
  fin_cases r
  · exact fourHighestNumber_9_1
  · exact fourHighestNumber_9_3
  · exact fourHighestNumber_9_5
  · exact fourHighestNumber_9_7
  · exact fourHighestNumber_9_9

theorem fourZChecked_9 (r s : CopyLabel 9) :
    integerFourGram 9 r s = fourZData_9 r s := by
  rw [integerFourGram_cached 9 fourHighestCache_9 fourHighestChecked_9]
  have h : ∀ r s : CopyLabel 9, cachedFourGram 9 fourHighestCache_9 r s = fourZData_9 r s := by
    simp only [cachedFourGram, fourOccupations_9]
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact h r s

theorem fourLDLChecked_9 :
    fourZData_9 * (Matrix.diagonal (fun r : CopyLabel 9 =>
      ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 9 r.val.val) -
      Matrix.diagonal (fun r : CopyLabel 9 => rationalCopyDiagonal 9 r.val.val) *
        fourYData_9 * Matrix.diagonal (fun r : CopyLabel 9 => rationalCopyDiagonal 9 r.val.val)) *
      fourZData_9 = fourLData_9 * Matrix.diagonal fourPivotData_9 * (fourLData_9)ᵀ := by
  have h : ∀ r s : CopyLabel 9,
      (fourZData_9 * (Matrix.diagonal (fun r : CopyLabel 9 =>
        ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 9 r.val.val) -
        Matrix.diagonal (fun r : CopyLabel 9 => rationalCopyDiagonal 9 r.val.val) *
          fourYData_9 * Matrix.diagonal (fun r : CopyLabel 9 => rationalCopyDiagonal 9 r.val.val)) *
        fourZData_9 : Matrix (CopyLabel 9) (CopyLabel 9) ℚ) r s =
      (fourLData_9 * Matrix.diagonal fourPivotData_9 * (fourLData_9)ᵀ : Matrix (CopyLabel 9) (CopyLabel 9) ℚ) r s := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact Matrix.ext h

theorem fourPivotChecked_9 : ∀ r, 0 ≤ fourPivotData_9 r := by
  intro r
  fin_cases r <;> norm_num [fourPivotData_9, copyDiagonalData]

theorem integer_certificate_9 :
    ((integerCompression 9).map (algebraMap ℚ ℂ)).PosSemidef := by
  apply rational_ldl_posSemidef _ (fourLData_9) (fourPivotData_9) _ fourPivotChecked_9
  unfold integerCompression integerFourMiddle
  rw [show integerRowsFourTrace 9 = fourYData_9 from Matrix.ext fourYChecked_9,
    show integerFourGram 9 = fourZData_9 from Matrix.ext fourZChecked_9]
  exact fourLDLChecked_9

end LaughlinFock
end

end OAI
