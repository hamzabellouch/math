import Mathlib
import OAI.Analysis.LaughlinFock.Certificate08Data
import OAI.Analysis.LaughlinFock.GramCache
import OAI.Analysis.LaughlinFock.TraceSymmetry

namespace OAI

/-! Certificate08. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourYLower_8 (r s : CopyLabel 8) (hrs : s.val.val ≤ r.val.val) :
    integerRowsFourTrace 8 r s = fourYData_8 r s := by
  rw [integerRowsFourTrace_parts (by decide) collectedFourData_8 collectedFourChecked_8]
  fin_cases r <;> fin_cases s
  · exact fourYNumber_8_1_1
  · have h : (3:ℕ) ≤ 1 := hrs
    omega
  · have h : (5:ℕ) ≤ 1 := hrs
    omega
  · have h : (7:ℕ) ≤ 1 := hrs
    omega
  · exact fourYNumber_8_3_1
  · exact fourYNumber_8_3_3
  · have h : (5:ℕ) ≤ 3 := hrs
    omega
  · have h : (7:ℕ) ≤ 3 := hrs
    omega
  · exact fourYNumber_8_5_1
  · exact fourYNumber_8_5_3
  · exact fourYNumber_8_5_5
  · have h : (7:ℕ) ≤ 5 := hrs
    omega
  · exact fourYNumber_8_7_1
  · exact fourYNumber_8_7_3
  · exact fourYNumber_8_7_5
  · exact fourYNumber_8_7_7

theorem fourYChecked_8 (r s : CopyLabel 8) :
    integerRowsFourTrace 8 r s = fourYData_8 r s := by
  have hh : ∀ r s : CopyLabel 8, fourYData_8 r s = fourYData_8 s r := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  by_cases h : s.val.val ≤ r.val.val
  · exact fourYLower_8 r s h
  · rw [integerRowsFourTrace_symm, fourYLower_8 s r (by omega), hh]

def fourHighestCache_8_0 : List (Occupation 24 × List ℚ) := [
  ({0,1,2,6}, [0, -23040, 11520, -10080]),
  ({0,1,3,5}, [0, 23040, -11520, 10080]),
  ({0,2,3,4}, [0, -23040, 11520, -10080])
]

def fourHighestCache_8 : List (Occupation 24 × List ℚ) := fourHighestCache_8_0

theorem fourHighestNumber_8_1 : ∀ A∈highestFourOccupations 8,
    kernelHighestEntry 8 ⟨⟨1,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_8 1 A := by
  rw [fourOccupations_8]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_8_3 : ∀ A∈highestFourOccupations 8,
    kernelHighestEntry 8 ⟨⟨3,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_8 3 A := by
  rw [fourOccupations_8]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_8_5 : ∀ A∈highestFourOccupations 8,
    kernelHighestEntry 8 ⟨⟨5,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_8 5 A := by
  rw [fourOccupations_8]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_8_7 : ∀ A∈highestFourOccupations 8,
    kernelHighestEntry 8 ⟨⟨7,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_8 7 A := by
  rw [fourOccupations_8]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestChecked_8 : ∀ r : CopyLabel 8, ∀ A∈highestFourOccupations 8,
    kernelHighestEntry 8 r A = highestLookup fourHighestCache_8 r.val.val A := by
  intro r
  fin_cases r
  · exact fourHighestNumber_8_1
  · exact fourHighestNumber_8_3
  · exact fourHighestNumber_8_5
  · exact fourHighestNumber_8_7

theorem fourZChecked_8 (r s : CopyLabel 8) :
    integerFourGram 8 r s = fourZData_8 r s := by
  rw [integerFourGram_cached 8 fourHighestCache_8 fourHighestChecked_8]
  have h : ∀ r s : CopyLabel 8, cachedFourGram 8 fourHighestCache_8 r s = fourZData_8 r s := by
    simp only [cachedFourGram, fourOccupations_8]
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact h r s

theorem fourLDLChecked_8 :
    fourZData_8 * (Matrix.diagonal (fun r : CopyLabel 8 =>
      ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 8 r.val.val) -
      Matrix.diagonal (fun r : CopyLabel 8 => rationalCopyDiagonal 8 r.val.val) *
        fourYData_8 * Matrix.diagonal (fun r : CopyLabel 8 => rationalCopyDiagonal 8 r.val.val)) *
      fourZData_8 = fourLData_8 * Matrix.diagonal fourPivotData_8 * (fourLData_8)ᵀ := by
  have h : ∀ r s : CopyLabel 8,
      (fourZData_8 * (Matrix.diagonal (fun r : CopyLabel 8 =>
        ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 8 r.val.val) -
        Matrix.diagonal (fun r : CopyLabel 8 => rationalCopyDiagonal 8 r.val.val) *
          fourYData_8 * Matrix.diagonal (fun r : CopyLabel 8 => rationalCopyDiagonal 8 r.val.val)) *
        fourZData_8 : Matrix (CopyLabel 8) (CopyLabel 8) ℚ) r s =
      (fourLData_8 * Matrix.diagonal fourPivotData_8 * (fourLData_8)ᵀ : Matrix (CopyLabel 8) (CopyLabel 8) ℚ) r s := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact Matrix.ext h

theorem fourPivotChecked_8 : ∀ r, 0 ≤ fourPivotData_8 r := by
  intro r
  fin_cases r <;> norm_num [fourPivotData_8, copyDiagonalData]

theorem integer_certificate_8 :
    ((integerCompression 8).map (algebraMap ℚ ℂ)).PosSemidef := by
  apply rational_ldl_posSemidef _ (fourLData_8) (fourPivotData_8) _ fourPivotChecked_8
  unfold integerCompression integerFourMiddle
  rw [show integerRowsFourTrace 8 = fourYData_8 from Matrix.ext fourYChecked_8,
    show integerFourGram 8 = fourZData_8 from Matrix.ext fourZChecked_8]
  exact fourLDLChecked_8

end LaughlinFock
end

end OAI
