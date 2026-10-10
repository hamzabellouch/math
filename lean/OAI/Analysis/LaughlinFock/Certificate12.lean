import Mathlib
import OAI.Analysis.LaughlinFock.Certificate12Data
import OAI.Analysis.LaughlinFock.GramCache
import OAI.Analysis.LaughlinFock.TraceSymmetry

namespace OAI

/-! Certificate12. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourYLower_12 (r s : CopyLabel 12) (hrs : s.val.val ≤ r.val.val) :
    integerRowsFourTrace 12 r s = fourYData_12 r s := by
  rw [integerRowsFourTrace_short (by decide)]
  fin_cases r <;> fin_cases s
  · exact fourYNumber_12_1_1
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
  · exact fourYNumber_12_3_1
  · exact fourYNumber_12_3_3
  · have h : (5:ℕ) ≤ 3 := hrs
    omega
  · have h : (7:ℕ) ≤ 3 := hrs
    omega
  · have h : (9:ℕ) ≤ 3 := hrs
    omega
  · have h : (11:ℕ) ≤ 3 := hrs
    omega
  · exact fourYNumber_12_5_1
  · exact fourYNumber_12_5_3
  · exact fourYNumber_12_5_5
  · have h : (7:ℕ) ≤ 5 := hrs
    omega
  · have h : (9:ℕ) ≤ 5 := hrs
    omega
  · have h : (11:ℕ) ≤ 5 := hrs
    omega
  · exact fourYNumber_12_7_1
  · exact fourYNumber_12_7_3
  · exact fourYNumber_12_7_5
  · exact fourYNumber_12_7_7
  · have h : (9:ℕ) ≤ 7 := hrs
    omega
  · have h : (11:ℕ) ≤ 7 := hrs
    omega
  · exact fourYNumber_12_9_1
  · exact fourYNumber_12_9_3
  · exact fourYNumber_12_9_5
  · exact fourYNumber_12_9_7
  · exact fourYNumber_12_9_9
  · have h : (11:ℕ) ≤ 9 := hrs
    omega
  · exact fourYNumber_12_11_1
  · exact fourYNumber_12_11_3
  · exact fourYNumber_12_11_5
  · exact fourYNumber_12_11_7
  · exact fourYNumber_12_11_9
  · exact fourYNumber_12_11_11

theorem fourYChecked_12 (r s : CopyLabel 12) :
    integerRowsFourTrace 12 r s = fourYData_12 r s := by
  have hh : ∀ r s : CopyLabel 12, fourYData_12 r s = fourYData_12 s r := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  by_cases h : s.val.val ≤ r.val.val
  · exact fourYLower_12 r s h
  · rw [integerRowsFourTrace_symm, fourYLower_12 s r (by omega), hh]

def fourHighestCache_12_0 : List (Occupation 24 × List ℚ) := [
  ({0,1,2,10}, [0, -696729600, -174182400, 65318400, 43545600, -239500800]),
  ({0,1,3,9}, [0, 696729600, 174182400, -65318400, -43545600, 239500800]),
  ({0,1,4,8}, [0, -557383680, -77414400, 29030400, 34836480, -159667200]),
  ({0,1,5,7}, [0, 348364800, 9676800, -3628800, -21772800, 79833600])
]

def fourHighestCache_12_1 : List (Occupation 24 × List ℚ) := [
  ({0,2,3,8}, [0, -139345920, -96768000, 36288000, 8709120, -79833600]),
  ({0,2,4,7}, [0, 209018880, 67737600, -25401600, -13063680, 79833600]),
  ({0,2,5,6}, [0, -348364800, -9676800, 3628800, 21772800, -79833600]),
  ({0,3,4,6}, [0, 69672960, -29030400, 10886400, -4354560, 0])
]

def fourHighestCache_12_2 : List (Occupation 24 × List ℚ) := [
  ({1,2,3,7}, [0, -69672960, 29030400, -10886400, 4354560, 0]),
  ({1,2,4,6}, [0, 69672960, -29030400, 10886400, -4354560, 0]),
  ({1,3,4,5}, [0, -69672960, 29030400, -10886400, 4354560, 0])
]

def fourHighestCache_12 : List (Occupation 24 × List ℚ) := fourHighestCache_12_0 ++ fourHighestCache_12_1 ++ fourHighestCache_12_2

theorem fourHighestChecked_12 : ∀ r : CopyLabel 12, ∀ A∈highestFourOccupations 12,
    kernelHighestEntry 12 r A = highestLookup fourHighestCache_12 r.val.val A := by
  rw [fourOccupations_12]
  apply @of_decide_eq_true _ (boundedMatrixEntriesDecidable _ _ _)
  decide +kernel

theorem fourZChecked_12 (r s : CopyLabel 12) :
    integerFourGram 12 r s = fourZData_12 r s := by
  rw [integerFourGram_cached 12 fourHighestCache_12 fourHighestChecked_12]
  have h : ∀ r s : CopyLabel 12, cachedFourGram 12 fourHighestCache_12 r s = fourZData_12 r s := by
    simp only [cachedFourGram, fourOccupations_12]
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact h r s

theorem fourLDLChecked_12 :
    fourZData_12 * (Matrix.diagonal (fun r : CopyLabel 12 =>
      ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 12 r.val.val) -
      Matrix.diagonal (fun r : CopyLabel 12 => rationalCopyDiagonal 12 r.val.val) *
        fourYData_12 * Matrix.diagonal (fun r : CopyLabel 12 => rationalCopyDiagonal 12 r.val.val)) *
      fourZData_12 = fourLData_12 * Matrix.diagonal fourPivotData_12 * (fourLData_12)ᵀ := by
  have h : ∀ r s : CopyLabel 12,
      (fourZData_12 * (Matrix.diagonal (fun r : CopyLabel 12 =>
        ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 12 r.val.val) -
        Matrix.diagonal (fun r : CopyLabel 12 => rationalCopyDiagonal 12 r.val.val) *
          fourYData_12 * Matrix.diagonal (fun r : CopyLabel 12 => rationalCopyDiagonal 12 r.val.val)) *
        fourZData_12 : Matrix (CopyLabel 12) (CopyLabel 12) ℚ) r s =
      (fourLData_12 * Matrix.diagonal fourPivotData_12 * (fourLData_12)ᵀ : Matrix (CopyLabel 12) (CopyLabel 12) ℚ) r s := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact Matrix.ext h

theorem fourPivotChecked_12 : ∀ r, 0 ≤ fourPivotData_12 r := by
  intro r
  fin_cases r <;> norm_num [fourPivotData_12, copyDiagonalData]

theorem integer_certificate_12 :
    ((integerCompression 12).map (algebraMap ℚ ℂ)).PosSemidef := by
  apply rational_ldl_posSemidef _ (fourLData_12) (fourPivotData_12) _ fourPivotChecked_12
  unfold integerCompression integerFourMiddle
  rw [show integerRowsFourTrace 12 = fourYData_12 from Matrix.ext fourYChecked_12,
    show integerFourGram 12 = fourZData_12 from Matrix.ext fourZChecked_12]
  exact fourLDLChecked_12

end LaughlinFock
end

end OAI
