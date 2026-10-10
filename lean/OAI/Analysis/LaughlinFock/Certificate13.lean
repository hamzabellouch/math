import Mathlib
import OAI.Analysis.LaughlinFock.Certificate13Data
import OAI.Analysis.LaughlinFock.GramCache
import OAI.Analysis.LaughlinFock.TraceSymmetry

namespace OAI

/-! Certificate13. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourYLower_13 (r s : CopyLabel 13) (hrs : s.val.val ≤ r.val.val) :
    integerRowsFourTrace 13 r s = fourYData_13 r s := by
  rw [integerRowsFourTrace_parts (by decide) collectedFourData_13 collectedFourChecked_13]
  fin_cases r <;> fin_cases s
  · exact fourYNumber_13_1_1
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
  · exact fourYNumber_13_3_1
  · exact fourYNumber_13_3_3
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
  · exact fourYNumber_13_5_1
  · exact fourYNumber_13_5_3
  · exact fourYNumber_13_5_5
  · have h : (7:ℕ) ≤ 5 := hrs
    omega
  · have h : (9:ℕ) ≤ 5 := hrs
    omega
  · have h : (11:ℕ) ≤ 5 := hrs
    omega
  · have h : (13:ℕ) ≤ 5 := hrs
    omega
  · exact fourYNumber_13_7_1
  · exact fourYNumber_13_7_3
  · exact fourYNumber_13_7_5
  · exact fourYNumber_13_7_7
  · have h : (9:ℕ) ≤ 7 := hrs
    omega
  · have h : (11:ℕ) ≤ 7 := hrs
    omega
  · have h : (13:ℕ) ≤ 7 := hrs
    omega
  · exact fourYNumber_13_9_1
  · exact fourYNumber_13_9_3
  · exact fourYNumber_13_9_5
  · exact fourYNumber_13_9_7
  · exact fourYNumber_13_9_9
  · have h : (11:ℕ) ≤ 9 := hrs
    omega
  · have h : (13:ℕ) ≤ 9 := hrs
    omega
  · exact fourYNumber_13_11_1
  · exact fourYNumber_13_11_3
  · exact fourYNumber_13_11_5
  · exact fourYNumber_13_11_7
  · exact fourYNumber_13_11_9
  · exact fourYNumber_13_11_11
  · have h : (13:ℕ) ≤ 11 := hrs
    omega
  · exact fourYNumber_13_13_1
  · exact fourYNumber_13_13_3
  · exact fourYNumber_13_13_5
  · exact fourYNumber_13_13_7
  · exact fourYNumber_13_13_9
  · exact fourYNumber_13_13_11
  · exact fourYNumber_13_13_13

theorem fourYChecked_13 (r s : CopyLabel 13) :
    integerRowsFourTrace 13 r s = fourYData_13 r s := by
  have hh : ∀ r s : CopyLabel 13, fourYData_13 r s = fourYData_13 s r := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  by_cases h : s.val.val ≤ r.val.val
  · exact fourYLower_13 r s h
  · rw [integerRowsFourTrace_symm, fourYLower_13 s r (by omega), hh]

def fourHighestCache_13_0 : List (Occupation 24 × List ℚ) := [
  ({0,1,2,11}, [38320128000, 9580032000, 3353011200, -239500800, -958003200, 1197504000, 6227020800]),
  ({0,1,3,10}, [-38320128000, -9580032000, -3353011200, 239500800, 958003200, -1197504000, -6227020800]),
  ({0,1,4,9}, [61312204800, 9754214400, 1741824000, -174182400, -505128960, 479001600, 6227020800]),
  ({0,1,5,8}, [-61312204800, -9754214400, -503193600, 174182400, 87091200, 159667200, -6227020800])
]

def fourHighestCache_13_1 : List (Occupation 24 × List ℚ) := [
  ({0,1,6,7}, [68976230400, 8883302400, 43545600, -210470400, 130636800, -479001600, 6227020800]),
  ({0,2,3,9}, [-22992076800, -174182400, 1611187200, -65318400, -452874240, 718502400, 0]),
  ({0,2,4,8}, [0, 0, -1238630400, 0, 418037760, -638668800, 0]),
  ({0,2,5,7}, [-7664025600, 870912000, 459648000, 36288000, -217728000, 319334400, 0])
]

def fourHighestCache_13_2 : List (Occupation 24 × List ℚ) := [
  ({0,3,4,7}, [30656102400, -696729600, 406425600, 29030400, -165473280, 239500800, 0]),
  ({0,3,5,6}, [-22992076800, -174182400, -246758400, -65318400, 174182400, -239500800, 0]),
  ({1,2,3,8}, [22992076800, 174182400, -372556800, 65318400, 34836480, -79833600, 0]),
  ({1,2,4,7}, [-22992076800, -174182400, 372556800, -65318400, -34836480, 79833600, 0])
]

def fourHighestCache_13_3 : List (Occupation 24 × List ℚ) := [
  ({1,2,5,6}, [30656102400, -696729600, -212889600, 29030400, 43545600, -79833600, 0]),
  ({1,3,4,6}, [-7664025600, 870912000, -159667200, 36288000, -8709120, 0, 0]),
  ({2,3,4,5}, [7664025600, -870912000, 159667200, -36288000, 8709120, 0, 0])
]

def fourHighestCache_13 : List (Occupation 24 × List ℚ) := fourHighestCache_13_0 ++ fourHighestCache_13_1 ++ fourHighestCache_13_2 ++ fourHighestCache_13_3

theorem fourHighestNumber_13_1 : ∀ A∈highestFourOccupations 13,
    kernelHighestEntry 13 ⟨⟨1,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_13 1 A := by
  rw [fourOccupations_13]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_13_3 : ∀ A∈highestFourOccupations 13,
    kernelHighestEntry 13 ⟨⟨3,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_13 3 A := by
  rw [fourOccupations_13]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_13_5 : ∀ A∈highestFourOccupations 13,
    kernelHighestEntry 13 ⟨⟨5,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_13 5 A := by
  rw [fourOccupations_13]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_13_7 : ∀ A∈highestFourOccupations 13,
    kernelHighestEntry 13 ⟨⟨7,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_13 7 A := by
  rw [fourOccupations_13]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_13_9 : ∀ A∈highestFourOccupations 13,
    kernelHighestEntry 13 ⟨⟨9,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_13 9 A := by
  rw [fourOccupations_13]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_13_11 : ∀ A∈highestFourOccupations 13,
    kernelHighestEntry 13 ⟨⟨11,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_13 11 A := by
  rw [fourOccupations_13]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_13_13 : ∀ A∈highestFourOccupations 13,
    kernelHighestEntry 13 ⟨⟨13,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_13 13 A := by
  rw [fourOccupations_13]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestChecked_13 : ∀ r : CopyLabel 13, ∀ A∈highestFourOccupations 13,
    kernelHighestEntry 13 r A = highestLookup fourHighestCache_13 r.val.val A := by
  intro r
  fin_cases r
  · exact fourHighestNumber_13_1
  · exact fourHighestNumber_13_3
  · exact fourHighestNumber_13_5
  · exact fourHighestNumber_13_7
  · exact fourHighestNumber_13_9
  · exact fourHighestNumber_13_11
  · exact fourHighestNumber_13_13

theorem fourZChecked_13 (r s : CopyLabel 13) :
    integerFourGram 13 r s = fourZData_13 r s := by
  rw [integerFourGram_cached 13 fourHighestCache_13 fourHighestChecked_13]
  have h : ∀ r s : CopyLabel 13, cachedFourGram 13 fourHighestCache_13 r s = fourZData_13 r s := by
    simp only [cachedFourGram, fourOccupations_13]
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact h r s

theorem fourLDLChecked_13 :
    fourZData_13 * (Matrix.diagonal (fun r : CopyLabel 13 =>
      ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 13 r.val.val) -
      Matrix.diagonal (fun r : CopyLabel 13 => rationalCopyDiagonal 13 r.val.val) *
        fourYData_13 * Matrix.diagonal (fun r : CopyLabel 13 => rationalCopyDiagonal 13 r.val.val)) *
      fourZData_13 = fourLData_13 * Matrix.diagonal fourPivotData_13 * (fourLData_13)ᵀ := by
  have h : ∀ r s : CopyLabel 13,
      (fourZData_13 * (Matrix.diagonal (fun r : CopyLabel 13 =>
        ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 13 r.val.val) -
        Matrix.diagonal (fun r : CopyLabel 13 => rationalCopyDiagonal 13 r.val.val) *
          fourYData_13 * Matrix.diagonal (fun r : CopyLabel 13 => rationalCopyDiagonal 13 r.val.val)) *
        fourZData_13 : Matrix (CopyLabel 13) (CopyLabel 13) ℚ) r s =
      (fourLData_13 * Matrix.diagonal fourPivotData_13 * (fourLData_13)ᵀ : Matrix (CopyLabel 13) (CopyLabel 13) ℚ) r s := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact Matrix.ext h

theorem fourPivotChecked_13 : ∀ r, 0 ≤ fourPivotData_13 r := by
  intro r
  fin_cases r <;> norm_num [fourPivotData_13, copyDiagonalData]

theorem integer_certificate_13 :
    ((integerCompression 13).map (algebraMap ℚ ℂ)).PosSemidef := by
  apply rational_ldl_posSemidef _ (fourLData_13) (fourPivotData_13) _ fourPivotChecked_13
  unfold integerCompression integerFourMiddle
  rw [show integerRowsFourTrace 13 = fourYData_13 from Matrix.ext fourYChecked_13,
    show integerFourGram 13 = fourZData_13 from Matrix.ext fourZChecked_13]
  exact fourLDLChecked_13

end LaughlinFock
end

end OAI
