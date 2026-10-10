import Mathlib
import OAI.Analysis.LaughlinFock.Certificate05Data
import OAI.Analysis.LaughlinFock.GramCache
import OAI.Analysis.LaughlinFock.TraceSymmetry

namespace OAI

/-! Certificate05. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourYLower_5 (r s : CopyLabel 5) (hrs : s.val.val ≤ r.val.val) :
    integerRowsFourTrace 5 r s = fourYData_5 r s := by
  rw [integerRowsFourTrace_short (by decide)]
  fin_cases r <;> fin_cases s
  · exact fourYNumber_5_1_1
  · have h : (3:ℕ) ≤ 1 := hrs
    omega
  · have h : (5:ℕ) ≤ 1 := hrs
    omega
  · exact fourYNumber_5_3_1
  · exact fourYNumber_5_3_3
  · have h : (5:ℕ) ≤ 3 := hrs
    omega
  · exact fourYNumber_5_5_1
  · exact fourYNumber_5_5_3
  · exact fourYNumber_5_5_5

theorem fourYChecked_5 (r s : CopyLabel 5) :
    integerRowsFourTrace 5 r s = fourYData_5 r s := by
  have hh : ∀ r s : CopyLabel 5, fourYData_5 r s = fourYData_5 s r := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  by_cases h : s.val.val ≤ r.val.val
  · exact fourYLower_5 r s h
  · rw [integerRowsFourTrace_symm, fourYLower_5 s r (by omega), hh]

def fourHighestCache_5_0 : List (Occupation 24 × List ℚ) := [
  ({0,1,2,3}, [384, -96, 120])
]

def fourHighestCache_5 : List (Occupation 24 × List ℚ) := fourHighestCache_5_0

theorem fourHighestChecked_5 : ∀ r : CopyLabel 5, ∀ A∈highestFourOccupations 5,
    kernelHighestEntry 5 r A = highestLookup fourHighestCache_5 r.val.val A := by
  rw [fourOccupations_5]
  apply @of_decide_eq_true _ (boundedMatrixEntriesDecidable _ _ _)
  decide +kernel

theorem fourZChecked_5 (r s : CopyLabel 5) :
    integerFourGram 5 r s = fourZData_5 r s := by
  rw [integerFourGram_cached 5 fourHighestCache_5 fourHighestChecked_5]
  have h : ∀ r s : CopyLabel 5, cachedFourGram 5 fourHighestCache_5 r s = fourZData_5 r s := by
    simp only [cachedFourGram, fourOccupations_5]
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact h r s

theorem fourLDLChecked_5 :
    fourZData_5 * (Matrix.diagonal (fun r : CopyLabel 5 =>
      ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 5 r.val.val) -
      Matrix.diagonal (fun r : CopyLabel 5 => rationalCopyDiagonal 5 r.val.val) *
        fourYData_5 * Matrix.diagonal (fun r : CopyLabel 5 => rationalCopyDiagonal 5 r.val.val)) *
      fourZData_5 = fourLData_5 * Matrix.diagonal fourPivotData_5 * (fourLData_5)ᵀ := by
  have h : ∀ r s : CopyLabel 5,
      (fourZData_5 * (Matrix.diagonal (fun r : CopyLabel 5 =>
        ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 5 r.val.val) -
        Matrix.diagonal (fun r : CopyLabel 5 => rationalCopyDiagonal 5 r.val.val) *
          fourYData_5 * Matrix.diagonal (fun r : CopyLabel 5 => rationalCopyDiagonal 5 r.val.val)) *
        fourZData_5 : Matrix (CopyLabel 5) (CopyLabel 5) ℚ) r s =
      (fourLData_5 * Matrix.diagonal fourPivotData_5 * (fourLData_5)ᵀ : Matrix (CopyLabel 5) (CopyLabel 5) ℚ) r s := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact Matrix.ext h

theorem fourPivotChecked_5 : ∀ r, 0 ≤ fourPivotData_5 r := by
  intro r
  fin_cases r <;> norm_num [fourPivotData_5, copyDiagonalData]

theorem integer_certificate_5 :
    ((integerCompression 5).map (algebraMap ℚ ℂ)).PosSemidef := by
  apply rational_ldl_posSemidef _ (fourLData_5) (fourPivotData_5) _ fourPivotChecked_5
  unfold integerCompression integerFourMiddle
  rw [show integerRowsFourTrace 5 = fourYData_5 from Matrix.ext fourYChecked_5,
    show integerFourGram 5 = fourZData_5 from Matrix.ext fourZChecked_5]
  exact fourLDLChecked_5

end LaughlinFock
end

end OAI
