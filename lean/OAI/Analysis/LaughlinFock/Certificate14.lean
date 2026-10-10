import Mathlib
import OAI.Analysis.LaughlinFock.Certificate14Data
import OAI.Analysis.LaughlinFock.GramCache
import OAI.Analysis.LaughlinFock.TraceSymmetry

namespace OAI

/-! Certificate14. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourYLower_14 (r s : CopyLabel 14) (hrs : s.val.val ≤ r.val.val) :
    integerRowsFourTrace 14 r s = fourYData_14 r s := by
  rw [integerRowsFourTrace_parts (by decide) collectedFourData_14 collectedFourChecked_14]
  fin_cases r <;> fin_cases s
  · exact fourYNumber_14_1_1
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
  · have h : (13:ℕ) ≤ 1 := hrs
    omega
  · exact fourYNumber_14_3_1
  · exact fourYNumber_14_3_3
  · have h : (5:ℕ) ≤ 3 := hrs
    omega
  · have h : (7:ℕ) ≤ 3 := hrs
    omega
  · have h : (9:ℕ) ≤ 3 := hrs
    omega
  · have h : (11:ℕ) ≤ 3 := hrs
    omega
  · have h : (13:ℕ) ≤ 3 := hrs
    omega
  · exact fourYNumber_14_5_1
  · exact fourYNumber_14_5_3
  · exact fourYNumber_14_5_5
  · have h : (7:ℕ) ≤ 5 := hrs
    omega
  · have h : (9:ℕ) ≤ 5 := hrs
    omega
  · have h : (11:ℕ) ≤ 5 := hrs
    omega
  · have h : (13:ℕ) ≤ 5 := hrs
    omega
  · exact fourYNumber_14_7_1
  · exact fourYNumber_14_7_3
  · exact fourYNumber_14_7_5
  · exact fourYNumber_14_7_7
  · have h : (9:ℕ) ≤ 7 := hrs
    omega
  · have h : (11:ℕ) ≤ 7 := hrs
    omega
  · have h : (13:ℕ) ≤ 7 := hrs
    omega
  · exact fourYNumber_14_9_1
  · exact fourYNumber_14_9_3
  · exact fourYNumber_14_9_5
  · exact fourYNumber_14_9_7
  · exact fourYNumber_14_9_9
  · have h : (11:ℕ) ≤ 9 := hrs
    omega
  · have h : (13:ℕ) ≤ 9 := hrs
    omega
  · exact fourYNumber_14_11_1
  · exact fourYNumber_14_11_3
  · exact fourYNumber_14_11_5
  · exact fourYNumber_14_11_7
  · exact fourYNumber_14_11_9
  · exact fourYNumber_14_11_11
  · have h : (13:ℕ) ≤ 11 := hrs
    omega
  · exact fourYNumber_14_13_1
  · exact fourYNumber_14_13_3
  · exact fourYNumber_14_13_5
  · exact fourYNumber_14_13_7
  · exact fourYNumber_14_13_9
  · exact fourYNumber_14_13_11
  · exact fourYNumber_14_13_13

theorem fourYChecked_14 (r s : CopyLabel 14) :
    integerRowsFourTrace 14 r s = fourYData_14 r s := by
  have hh : ∀ r s : CopyLabel 14, fourYData_14 r s = fourYData_14 s r := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  by_cases h : s.val.val ≤ r.val.val
  · exact fourYLower_14 r s h
  · rw [integerRowsFourTrace_symm, fourYLower_14 s r (by omega), hh]

def fourHighestCache_14_0 : List (Occupation 24 × List ℚ) := [
  ({0,1,2,12}, [0, -153280512000, -61312204800, -6706022400, 13412044800, -958003200, -49816166400]),
  ({0,1,3,11}, [0, 153280512000, 61312204800, 6706022400, -13412044800, 958003200, 49816166400]),
  ({0,1,4,10}, [0, -153280512000, -39016857600, -1828915200, 6444748800, 1916006400, -37362124800]),
  ({0,1,5,9}, [0, 122624409600, 22295347200, -2438553600, -696729600, -3832012800, 24908083200])
]

def fourHighestCache_14_1 : List (Occupation 24 × List ℚ) := [
  ({0,1,6,8}, [0, -61312204800, -11147673600, 2844979200, -1045094400, 2874009600, -12454041600]),
  ({0,2,3,10}, [0, 0, -22295347200, -4877107200, 6967296000, -2874009600, -12454041600]),
  ({0,2,4,9}, [0, 30656102400, 16721510400, 4267468800, -5748019200, 1916006400, 12454041600]),
  ({0,2,5,8}, [0, -61312204800, -11147673600, -406425600, 1741824000, 958003200, -12454041600])
]

def fourHighestCache_14_2 : List (Occupation 24 × List ℚ) := [
  ({0,2,6,7}, [0, 61312204800, 11147673600, -2844979200, 1045094400, -2874009600, 12454041600]),
  ({0,3,4,8}, [0, 0, 0, -3251404800, 2786918400, -1916006400, 0]),
  ({0,3,5,7}, [0, 15328051200, -2786918400, 2946585600, -2177280000, 1437004800, 0]),
  ({0,4,5,6}, [0, -30656102400, 5573836800, -2641766400, 1567641600, -958003200, 0])
]

def fourHighestCache_14_3 : List (Occupation 24 × List ℚ) := [
  ({1,2,3,9}, [0, -30656102400, 5573836800, 609638400, -1219276800, 958003200, 0]),
  ({1,2,4,8}, [0, 30656102400, -5573836800, -609638400, 1219276800, -958003200, 0]),
  ({1,2,5,7}, [0, -15328051200, 2786918400, 304819200, -609638400, 479001600, 0]),
  ({1,3,4,7}, [0, -15328051200, 2786918400, 304819200, -609638400, 479001600, 0])
]

def fourHighestCache_14_4 : List (Occupation 24 × List ℚ) := [
  ({1,3,5,6}, [0, 15328051200, -2786918400, -304819200, 609638400, -479001600, 0]),
  ({2,3,4,6}, [0, 0, 0, 0, 0, 0, 0])
]

def fourHighestCache_14 : List (Occupation 24 × List ℚ) := fourHighestCache_14_0 ++ fourHighestCache_14_1 ++ fourHighestCache_14_2 ++ fourHighestCache_14_3 ++ fourHighestCache_14_4

theorem fourHighestNumber_14_1 : ∀ A∈highestFourOccupations 14,
    kernelHighestEntry 14 ⟨⟨1,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_14 1 A := by
  rw [fourOccupations_14]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_14_3 : ∀ A∈highestFourOccupations 14,
    kernelHighestEntry 14 ⟨⟨3,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_14 3 A := by
  rw [fourOccupations_14]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_14_5 : ∀ A∈highestFourOccupations 14,
    kernelHighestEntry 14 ⟨⟨5,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_14 5 A := by
  rw [fourOccupations_14]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_14_7 : ∀ A∈highestFourOccupations 14,
    kernelHighestEntry 14 ⟨⟨7,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_14 7 A := by
  rw [fourOccupations_14]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_14_9 : ∀ A∈highestFourOccupations 14,
    kernelHighestEntry 14 ⟨⟨9,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_14 9 A := by
  rw [fourOccupations_14]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_14_11 : ∀ A∈highestFourOccupations 14,
    kernelHighestEntry 14 ⟨⟨11,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_14 11 A := by
  rw [fourOccupations_14]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_14_13 : ∀ A∈highestFourOccupations 14,
    kernelHighestEntry 14 ⟨⟨13,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_14 13 A := by
  rw [fourOccupations_14]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestChecked_14 : ∀ r : CopyLabel 14, ∀ A∈highestFourOccupations 14,
    kernelHighestEntry 14 r A = highestLookup fourHighestCache_14 r.val.val A := by
  intro r
  fin_cases r
  · exact fourHighestNumber_14_1
  · exact fourHighestNumber_14_3
  · exact fourHighestNumber_14_5
  · exact fourHighestNumber_14_7
  · exact fourHighestNumber_14_9
  · exact fourHighestNumber_14_11
  · exact fourHighestNumber_14_13

theorem fourZChecked_14 (r s : CopyLabel 14) :
    integerFourGram 14 r s = fourZData_14 r s := by
  rw [integerFourGram_cached 14 fourHighestCache_14 fourHighestChecked_14]
  have h : ∀ r s : CopyLabel 14, cachedFourGram 14 fourHighestCache_14 r s = fourZData_14 r s := by
    simp only [cachedFourGram, fourOccupations_14]
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact h r s

theorem fourLDLChecked_14 :
    fourZData_14 * (Matrix.diagonal (fun r : CopyLabel 14 =>
      ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 14 r.val.val) -
      Matrix.diagonal (fun r : CopyLabel 14 => rationalCopyDiagonal 14 r.val.val) *
        fourYData_14 * Matrix.diagonal (fun r : CopyLabel 14 => rationalCopyDiagonal 14 r.val.val)) *
      fourZData_14 = fourLData_14 * Matrix.diagonal fourPivotData_14 * (fourLData_14)ᵀ := by
  have h : ∀ r s : CopyLabel 14,
      (fourZData_14 * (Matrix.diagonal (fun r : CopyLabel 14 =>
        ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 14 r.val.val) -
        Matrix.diagonal (fun r : CopyLabel 14 => rationalCopyDiagonal 14 r.val.val) *
          fourYData_14 * Matrix.diagonal (fun r : CopyLabel 14 => rationalCopyDiagonal 14 r.val.val)) *
        fourZData_14 : Matrix (CopyLabel 14) (CopyLabel 14) ℚ) r s =
      (fourLData_14 * Matrix.diagonal fourPivotData_14 * (fourLData_14)ᵀ : Matrix (CopyLabel 14) (CopyLabel 14) ℚ) r s := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact Matrix.ext h

theorem fourPivotChecked_14 : ∀ r, 0 ≤ fourPivotData_14 r := by
  intro r
  fin_cases r <;> norm_num [fourPivotData_14, copyDiagonalData]

theorem integer_certificate_14 :
    ((integerCompression 14).map (algebraMap ℚ ℂ)).PosSemidef := by
  apply rational_ldl_posSemidef _ (fourLData_14) (fourPivotData_14) _ fourPivotChecked_14
  unfold integerCompression integerFourMiddle
  rw [show integerRowsFourTrace 14 = fourYData_14 from Matrix.ext fourYChecked_14,
    show integerFourGram 14 = fourZData_14 from Matrix.ext fourZChecked_14]
  exact fourLDLChecked_14

end LaughlinFock
end

end OAI
