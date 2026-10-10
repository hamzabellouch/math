import Mathlib
import OAI.Analysis.LaughlinFock.Certificate07Data
import OAI.Analysis.LaughlinFock.GramCache
import OAI.Analysis.LaughlinFock.TraceSymmetry

namespace OAI

/-! Certificate07. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourYLower_7 (r s : CopyLabel 7) (hrs : s.val.val ≤ r.val.val) :
    integerRowsFourTrace 7 r s = fourYData_7 r s := by
  rw [integerRowsFourTrace_short (by decide)]
  fin_cases r <;> fin_cases s
  · exact fourYNumber_7_1_1
  · have h : (3:ℕ) ≤ 1 := hrs
    omega
  · have h : (5:ℕ) ≤ 1 := hrs
    omega
  · have h : (7:ℕ) ≤ 1 := hrs
    omega
  · exact fourYNumber_7_3_1
  · exact fourYNumber_7_3_3
  · have h : (5:ℕ) ≤ 3 := hrs
    omega
  · have h : (7:ℕ) ≤ 3 := hrs
    omega
  · exact fourYNumber_7_5_1
  · exact fourYNumber_7_5_3
  · exact fourYNumber_7_5_5
  · have h : (7:ℕ) ≤ 5 := hrs
    omega
  · exact fourYNumber_7_7_1
  · exact fourYNumber_7_7_3
  · exact fourYNumber_7_7_5
  · exact fourYNumber_7_7_7

theorem fourYChecked_7 (r s : CopyLabel 7) :
    integerRowsFourTrace 7 r s = fourYData_7 r s := by
  have hh : ∀ r s : CopyLabel 7, fourYData_7 r s = fourYData_7 s r := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  by_cases h : s.val.val ≤ r.val.val
  · exact fourYLower_7 r s h
  · rw [integerRowsFourTrace_symm, fourYLower_7 s r (by omega), hh]

def fourHighestCache_7_0 : List (Occupation 24 × List ℚ) := [
  ({0,1,2,5}, [23040, 0, -1440, 5040]),
  ({0,1,3,4}, [-23040, 0, 1440, -5040])
]

def fourHighestCache_7 : List (Occupation 24 × List ℚ) := fourHighestCache_7_0

theorem fourHighestChecked_7 : ∀ r : CopyLabel 7, ∀ A∈highestFourOccupations 7,
    kernelHighestEntry 7 r A = highestLookup fourHighestCache_7 r.val.val A := by
  rw [fourOccupations_7]
  apply @of_decide_eq_true _ (boundedMatrixEntriesDecidable _ _ _)
  decide +kernel

theorem fourZChecked_7 (r s : CopyLabel 7) :
    integerFourGram 7 r s = fourZData_7 r s := by
  rw [integerFourGram_cached 7 fourHighestCache_7 fourHighestChecked_7]
  have h : ∀ r s : CopyLabel 7, cachedFourGram 7 fourHighestCache_7 r s = fourZData_7 r s := by
    simp only [cachedFourGram, fourOccupations_7]
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact h r s

theorem fourLDLChecked_7 :
    fourZData_7 * (Matrix.diagonal (fun r : CopyLabel 7 =>
      ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 7 r.val.val) -
      Matrix.diagonal (fun r : CopyLabel 7 => rationalCopyDiagonal 7 r.val.val) *
        fourYData_7 * Matrix.diagonal (fun r : CopyLabel 7 => rationalCopyDiagonal 7 r.val.val)) *
      fourZData_7 = fourLData_7 * Matrix.diagonal fourPivotData_7 * (fourLData_7)ᵀ := by
  have h : ∀ r s : CopyLabel 7,
      (fourZData_7 * (Matrix.diagonal (fun r : CopyLabel 7 =>
        ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 7 r.val.val) -
        Matrix.diagonal (fun r : CopyLabel 7 => rationalCopyDiagonal 7 r.val.val) *
          fourYData_7 * Matrix.diagonal (fun r : CopyLabel 7 => rationalCopyDiagonal 7 r.val.val)) *
        fourZData_7 : Matrix (CopyLabel 7) (CopyLabel 7) ℚ) r s =
      (fourLData_7 * Matrix.diagonal fourPivotData_7 * (fourLData_7)ᵀ : Matrix (CopyLabel 7) (CopyLabel 7) ℚ) r s := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact Matrix.ext h

theorem fourPivotChecked_7 : ∀ r, 0 ≤ fourPivotData_7 r := by
  intro r
  fin_cases r <;> norm_num [fourPivotData_7, copyDiagonalData]

theorem integer_certificate_7 :
    ((integerCompression 7).map (algebraMap ℚ ℂ)).PosSemidef := by
  apply rational_ldl_posSemidef _ (fourLData_7) (fourPivotData_7) _ fourPivotChecked_7
  unfold integerCompression integerFourMiddle
  rw [show integerRowsFourTrace 7 = fourYData_7 from Matrix.ext fourYChecked_7,
    show integerFourGram 7 = fourZData_7 from Matrix.ext fourZChecked_7]
  exact fourLDLChecked_7

end LaughlinFock
end

end OAI
