import Mathlib
import OAI.Analysis.LaughlinFock.Certificate15Data
import OAI.Analysis.LaughlinFock.GramCache
import OAI.Analysis.LaughlinFock.TraceSymmetry

namespace OAI

/-! Certificate15. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourYLower_15 (r s : CopyLabel 15) (hrs : s.val.val ≤ r.val.val) :
    integerRowsFourTrace 15 r s = fourYData_15 r s := by
  rw [integerRowsFourTrace_collected (by decide) collectedFourData_15 collectedFourChecked_15]
  fin_cases r <;> fin_cases s
  · exact fourYNumber_15_1_1
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
  · have h : (15:ℕ) ≤ 1 := hrs
    omega
  · exact fourYNumber_15_3_1
  · exact fourYNumber_15_3_3
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
  · have h : (15:ℕ) ≤ 3 := hrs
    omega
  · exact fourYNumber_15_5_1
  · exact fourYNumber_15_5_3
  · exact fourYNumber_15_5_5
  · have h : (7:ℕ) ≤ 5 := hrs
    omega
  · have h : (9:ℕ) ≤ 5 := hrs
    omega
  · have h : (11:ℕ) ≤ 5 := hrs
    omega
  · have h : (13:ℕ) ≤ 5 := hrs
    omega
  · have h : (15:ℕ) ≤ 5 := hrs
    omega
  · exact fourYNumber_15_7_1
  · exact fourYNumber_15_7_3
  · exact fourYNumber_15_7_5
  · exact fourYNumber_15_7_7
  · have h : (9:ℕ) ≤ 7 := hrs
    omega
  · have h : (11:ℕ) ≤ 7 := hrs
    omega
  · have h : (13:ℕ) ≤ 7 := hrs
    omega
  · have h : (15:ℕ) ≤ 7 := hrs
    omega
  · exact fourYNumber_15_9_1
  · exact fourYNumber_15_9_3
  · exact fourYNumber_15_9_5
  · exact fourYNumber_15_9_7
  · exact fourYNumber_15_9_9
  · have h : (11:ℕ) ≤ 9 := hrs
    omega
  · have h : (13:ℕ) ≤ 9 := hrs
    omega
  · have h : (15:ℕ) ≤ 9 := hrs
    omega
  · exact fourYNumber_15_11_1
  · exact fourYNumber_15_11_3
  · exact fourYNumber_15_11_5
  · exact fourYNumber_15_11_7
  · exact fourYNumber_15_11_9
  · exact fourYNumber_15_11_11
  · have h : (13:ℕ) ≤ 11 := hrs
    omega
  · have h : (15:ℕ) ≤ 11 := hrs
    omega
  · exact fourYNumber_15_13_1
  · exact fourYNumber_15_13_3
  · exact fourYNumber_15_13_5
  · exact fourYNumber_15_13_7
  · exact fourYNumber_15_13_9
  · exact fourYNumber_15_13_11
  · exact fourYNumber_15_13_13
  · have h : (15:ℕ) ≤ 13 := hrs
    omega
  · exact fourYNumber_15_15_1
  · exact fourYNumber_15_15_3
  · exact fourYNumber_15_15_5
  · exact fourYNumber_15_15_7
  · exact fourYNumber_15_15_9
  · exact fourYNumber_15_15_11
  · exact fourYNumber_15_15_13
  · exact fourYNumber_15_15_15

theorem fourYChecked_15 (r s : CopyLabel 15) :
    integerRowsFourTrace 15 r s = fourYData_15 r s := by
  have hh : ∀ r s : CopyLabel 15, fourYData_15 r s = fourYData_15 s r := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  by_cases h : s.val.val ≤ r.val.val
  · exact fourYLower_15 r s h
  · rw [integerRowsFourTrace_symm, fourYLower_15 s r (by omega), hh]

def fourHighestCache_15_0 : List (Occupation 24 × List ℚ) := [
  ({0,1,2,13}, [8369115955200, 2391175987200, 1120863744000, 261534873600, -149448499200, -112086374400, 373621248000, 1307674368000]),
  ({0,1,3,12}, [-8369115955200, -2391175987200, -1120863744000, -261534873600, 149448499200, 112086374400, -373621248000, -1307674368000]),
  ({0,1,4,11}, [13948526592000, 2759049216000, 795142656000, 114002380800, -74724249600, -76640256000, 211718707200, 1307674368000]),
  ({0,1,5,10}, [-13948526592000, -2759049216000, -516450816000, 3048192000, 18289152000, 38320128000, -62270208000, -1307674368000])
]

def fourHighestCache_15_1 : List (Occupation 24 × List ℚ) := [
  ({0,1,6,9}, [16738231910400, 2575112601600, 276950016000, -32920473600, -4702924800, -2874009600, -37362124800, 1307674368000]),
  ({0,1,7,8}, [-16738231910400, -2575112601600, -109734912000, 19914854400, 10973491200, -20118067200, 87178291200, -1307674368000]),
  ({0,2,3,11}, [-5579410636800, -367873228800, 325721088000, 147532492800, -74724249600, -35446118400, 161902540800, 0]),
  ({0,2,4,10}, [0, 0, -278691840000, -117050572800, 56435097600, 38320128000, -149448499200, 0])
]

def fourHighestCache_15_2 : List (Occupation 24 × List ℚ) := [
  ({0,2,5,9}, [-2789705318400, 183936614400, 239500800000, 29872281600, -13586227200, -35446118400, 99632332800, 0]),
  ({0,2,6,8}, [0, 0, -167215104000, 13005619200, -6270566400, 22992076800, -49816166400, 0]),
  ({0,3,4,9}, [8369115955200, 183936614400, -7838208000, 56696371200, -24559718400, -5748019200, 37362124800, 0]),
  ({0,3,5,8}, [-5579410636800, -367873228800, -8709120000, -34546176000, 13063680000, 10538035200, -37362124800, 0])
]

def fourHighestCache_15_3 : List (Occupation 24 × List ℚ) := [
  ({0,3,6,7}, [8369115955200, 183936614400, 75769344000, -1828915200, 3657830400, -17244057600, 37362124800, 0]),
  ({0,4,5,7}, [-2789705318400, 183936614400, -39191040000, 16866662400, -7315660800, 2874009600, 0, 0]),
  ({1,2,3,10}, [5579410636800, 367873228800, -47029248000, -30481920000, 18289152000, -2874009600, -12454041600, 0]),
  ({1,2,4,9}, [-5579410636800, -367873228800, 47029248000, 30481920000, -18289152000, 2874009600, 12454041600, 0])
]

def fourHighestCache_15_4 : List (Occupation 24 × List ℚ) := [
  ({1,2,5,8}, [8369115955200, 183936614400, -63576576000, -8331724800, 6793113600, 1916006400, -12454041600, 0]),
  ({1,2,6,7}, [-8369115955200, -183936614400, 91445760000, -11176704000, 2612736000, -5748019200, 12454041600, 0]),
  ({1,3,4,8}, [-2789705318400, 183936614400, 16547328000, -22150195200, 11496038400, -4790016000, 0, 0]),
  ({1,3,5,7}, [0, 0, -27869184000, 19508428800, -9405849600, 3832012800, 0, 0])
]

def fourHighestCache_15_5 : List (Occupation 24 × List ℚ) := [
  ({1,4,5,6}, [2789705318400, -183936614400, 39191040000, -16866662400, 7315660800, -2874009600, 0, 0]),
  ({2,3,4,7}, [2789705318400, -183936614400, 11321856000, 2641766400, -2090188800, 958003200, 0, 0]),
  ({2,3,5,6}, [-2789705318400, 183936614400, -11321856000, -2641766400, 2090188800, -958003200, 0, 0])
]

def fourHighestCache_15 : List (Occupation 24 × List ℚ) := fourHighestCache_15_0 ++ fourHighestCache_15_1 ++ fourHighestCache_15_2 ++ fourHighestCache_15_3 ++ fourHighestCache_15_4 ++ fourHighestCache_15_5

theorem fourHighestNumber_15_1 : ∀ A∈highestFourOccupations 15,
    kernelHighestEntry 15 ⟨⟨1,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_15 1 A := by
  rw [fourOccupations_15]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_15_3 : ∀ A∈highestFourOccupations 15,
    kernelHighestEntry 15 ⟨⟨3,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_15 3 A := by
  rw [fourOccupations_15]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_15_5 : ∀ A∈highestFourOccupations 15,
    kernelHighestEntry 15 ⟨⟨5,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_15 5 A := by
  rw [fourOccupations_15]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_15_7 : ∀ A∈highestFourOccupations 15,
    kernelHighestEntry 15 ⟨⟨7,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_15 7 A := by
  rw [fourOccupations_15]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_15_9 : ∀ A∈highestFourOccupations 15,
    kernelHighestEntry 15 ⟨⟨9,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_15 9 A := by
  rw [fourOccupations_15]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_15_11 : ∀ A∈highestFourOccupations 15,
    kernelHighestEntry 15 ⟨⟨11,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_15 11 A := by
  rw [fourOccupations_15]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_15_13 : ∀ A∈highestFourOccupations 15,
    kernelHighestEntry 15 ⟨⟨13,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_15 13 A := by
  rw [fourOccupations_15]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_15_15 : ∀ A∈highestFourOccupations 15,
    kernelHighestEntry 15 ⟨⟨15,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_15 15 A := by
  rw [fourOccupations_15]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestChecked_15 : ∀ r : CopyLabel 15, ∀ A∈highestFourOccupations 15,
    kernelHighestEntry 15 r A = highestLookup fourHighestCache_15 r.val.val A := by
  intro r
  fin_cases r
  · exact fourHighestNumber_15_1
  · exact fourHighestNumber_15_3
  · exact fourHighestNumber_15_5
  · exact fourHighestNumber_15_7
  · exact fourHighestNumber_15_9
  · exact fourHighestNumber_15_11
  · exact fourHighestNumber_15_13
  · exact fourHighestNumber_15_15

theorem fourZChecked_15 (r s : CopyLabel 15) :
    integerFourGram 15 r s = fourZData_15 r s := by
  rw [integerFourGram_cached 15 fourHighestCache_15 fourHighestChecked_15]
  have h : ∀ r s : CopyLabel 15, cachedFourGram 15 fourHighestCache_15 r s = fourZData_15 r s := by
    simp only [cachedFourGram, fourOccupations_15]
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact h r s

theorem fourLDLChecked_15 :
    fourZData_15 * (Matrix.diagonal (fun r : CopyLabel 15 =>
      ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 15 r.val.val) -
      Matrix.diagonal (fun r : CopyLabel 15 => rationalCopyDiagonal 15 r.val.val) *
        fourYData_15 * Matrix.diagonal (fun r : CopyLabel 15 => rationalCopyDiagonal 15 r.val.val)) *
      fourZData_15 = fourLData_15 * Matrix.diagonal fourPivotData_15 * (fourLData_15)ᵀ := by
  have h : ∀ r s : CopyLabel 15,
      (fourZData_15 * (Matrix.diagonal (fun r : CopyLabel 15 =>
        ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 15 r.val.val) -
        Matrix.diagonal (fun r : CopyLabel 15 => rationalCopyDiagonal 15 r.val.val) *
          fourYData_15 * Matrix.diagonal (fun r : CopyLabel 15 => rationalCopyDiagonal 15 r.val.val)) *
        fourZData_15 : Matrix (CopyLabel 15) (CopyLabel 15) ℚ) r s =
      (fourLData_15 * Matrix.diagonal fourPivotData_15 * (fourLData_15)ᵀ : Matrix (CopyLabel 15) (CopyLabel 15) ℚ) r s := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact Matrix.ext h

theorem fourPivotChecked_15 : ∀ r, 0 ≤ fourPivotData_15 r := by
  intro r
  fin_cases r <;> norm_num [fourPivotData_15, copyDiagonalData]

theorem integer_certificate_15 :
    ((integerCompression 15).map (algebraMap ℚ ℂ)).PosSemidef := by
  apply rational_ldl_posSemidef _ (fourLData_15) (fourPivotData_15) _ fourPivotChecked_15
  unfold integerCompression integerFourMiddle
  rw [show integerRowsFourTrace 15 = fourYData_15 from Matrix.ext fourYChecked_15,
    show integerFourGram 15 = fourZData_15 from Matrix.ext fourZChecked_15]
  exact fourLDLChecked_15

end LaughlinFock
end

end OAI
