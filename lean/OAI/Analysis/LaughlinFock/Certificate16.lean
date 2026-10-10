import Mathlib
import OAI.Analysis.LaughlinFock.Certificate16Data
import OAI.Analysis.LaughlinFock.GramCache
import OAI.Analysis.LaughlinFock.TraceSymmetry

namespace OAI

/-! Certificate16. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourYLower_16 (r s : CopyLabel 16) (hrs : s.val.val ≤ r.val.val) :
    integerRowsFourTrace 16 r s = fourYData_16 r s := by
  rw [integerRowsFourTrace_collected (by decide) collectedFourData_16 collectedFourChecked_16]
  fin_cases r <;> fin_cases s
  · exact fourYNumber_16_1_1
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
  · exact fourYNumber_16_3_1
  · exact fourYNumber_16_3_3
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
  · exact fourYNumber_16_5_1
  · exact fourYNumber_16_5_3
  · exact fourYNumber_16_5_5
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
  · exact fourYNumber_16_7_1
  · exact fourYNumber_16_7_3
  · exact fourYNumber_16_7_5
  · exact fourYNumber_16_7_7
  · have h : (9:ℕ) ≤ 7 := hrs
    omega
  · have h : (11:ℕ) ≤ 7 := hrs
    omega
  · have h : (13:ℕ) ≤ 7 := hrs
    omega
  · have h : (15:ℕ) ≤ 7 := hrs
    omega
  · exact fourYNumber_16_9_1
  · exact fourYNumber_16_9_3
  · exact fourYNumber_16_9_5
  · exact fourYNumber_16_9_7
  · exact fourYNumber_16_9_9
  · have h : (11:ℕ) ≤ 9 := hrs
    omega
  · have h : (13:ℕ) ≤ 9 := hrs
    omega
  · have h : (15:ℕ) ≤ 9 := hrs
    omega
  · exact fourYNumber_16_11_1
  · exact fourYNumber_16_11_3
  · exact fourYNumber_16_11_5
  · exact fourYNumber_16_11_7
  · exact fourYNumber_16_11_9
  · exact fourYNumber_16_11_11
  · have h : (13:ℕ) ≤ 11 := hrs
    omega
  · have h : (15:ℕ) ≤ 11 := hrs
    omega
  · exact fourYNumber_16_13_1
  · exact fourYNumber_16_13_3
  · exact fourYNumber_16_13_5
  · exact fourYNumber_16_13_7
  · exact fourYNumber_16_13_9
  · exact fourYNumber_16_13_11
  · exact fourYNumber_16_13_13
  · have h : (15:ℕ) ≤ 13 := hrs
    omega
  · exact fourYNumber_16_15_1
  · exact fourYNumber_16_15_3
  · exact fourYNumber_16_15_5
  · exact fourYNumber_16_15_7
  · exact fourYNumber_16_15_9
  · exact fourYNumber_16_15_11
  · exact fourYNumber_16_15_13
  · exact fourYNumber_16_15_15

theorem fourYChecked_16 (r s : CopyLabel 16) :
    integerRowsFourTrace 16 r s = fourYData_16 r s := by
  have hh : ∀ r s : CopyLabel 16, fourYData_16 r s = fourYData_16 s r := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  by_cases h : s.val.val ≤ r.val.val
  · exact fourYLower_16 r s h
  · rw [integerRowsFourTrace_symm, fourYLower_16 s r (by omega), hh]

def fourHighestCache_16_0 : List (Occupation 24 × List ℚ) := [
  ({0,1,2,14}, [0, -41845579776000, -20922789888000, -6799906713600, 1046139494400, 2615348736000, -2092278988800, -13076743680000]),
  ({0,1,3,13}, [0, 41845579776000, 20922789888000, 6799906713600, -1046139494400, -2615348736000, 2092278988800, 13076743680000]),
  ({0,1,4,12}, [0, -47823519744000, -16554295296000, -3540779827200, 643778150400, 1437004800000, -747242496000, -10461394944000]),
  ({0,1,5,11}, [0, 41845579776000, 12339081216000, 1005903360000, -402361344000, -383201280000, -373621248000, 7846046208000])
]

def fourHighestCache_16_1 : List (Occupation 24 × List ℚ) := [
  ({0,1,6,10}, [0, -29889699840000, -7587385344000, -91445760000, 329204736000, -143700480000, 747242496000, -5230697472000]),
  ({0,1,7,9}, [0, 16738231910400, 3218890752000, -7315660800, -219469824000, 201180672000, -523069747200, 2615348736000]),
  ({0,2,3,12}, [0, 5977939968000, -4368494592000, -3259126886400, 402361344000, 1178343936000, -1345036492800, -2615348736000]),
  ({0,2,4,11}, [0, 5977939968000, 4215214080000, 2534876467200, -241416806400, -1053803520000, 1120863744000, 2615348736000])
]

def fourHighestCache_16_2 : List (Occupation 24 × List ℚ) := [
  ({0,2,5,10}, [0, -11955879936000, -4751695872000, -914457600000, 73156608000, 526901760000, -373621248000, -2615348736000]),
  ({0,2,6,9}, [0, 13151467929600, 4368494592000, 98761420800, -109734912000, -57480192000, -224172748800, 2615348736000]),
  ({0,2,7,8}, [0, -16738231910400, -3218890752000, 7315660800, 219469824000, -201180672000, 523069747200, -2615348736000]),
  ({0,3,4,10}, [0, -5977939968000, 689762304000, -896168448000, 7315660800, 402361344000, -523069747200, 0])
]

def fourHighestCache_16_3 : List (Occupation 24 × List ℚ) := [
  ({0,3,5,9}, [0, 8369115955200, -229920768000, 493807104000, 95103590400, -373621248000, 448345497600, 0]),
  ({0,3,6,8}, [0, -2391175987200, -459841536000, -65840947200, -102419251200, 201180672000, -224172748800, 0]),
  ({0,4,5,8}, [0, -9564703948800, 613122048000, -146313216000, -58525286400, 134120448000, -149448499200, 0]),
  ({0,4,6,7}, [0, 8369115955200, -229920768000, 25604812800, 95103590400, -143700480000, 149448499200, 0])
]

def fourHighestCache_16_4 : List (Occupation 24 × List ℚ) := [
  ({1,2,3,11}, [0, -11955879936000, 153280512000, 724250419200, -160944537600, -124540416000, 224172748800, 0]),
  ({1,2,4,10}, [0, 11955879936000, -153280512000, -724250419200, 160944537600, 124540416000, -224172748800, 0]),
  ({1,2,5,9}, [0, -9564703948800, 613122048000, 321889075200, -58525286400, -95800320000, 149448499200, 0]),
  ({1,2,6,8}, [0, 5977939968000, -689762304000, -40236134400, -7315660800, 57480192000, -74724249600, 0])
]

def fourHighestCache_16_5 : List (Occupation 24 × List ℚ) := [
  ({1,3,4,9}, [0, -2391175987200, -459841536000, 402361344000, -102419251200, -28740096000, 74724249600, 0]),
  ({1,3,5,8}, [0, 3586763980800, 76640256000, -281652940800, 65840947200, 38320128000, -74724249600, 0]),
  ({1,3,6,7}, [0, -5977939968000, 689762304000, 40236134400, 7315660800, -57480192000, 74724249600, 0]),
  ({1,4,5,7}, [0, 1195587993600, -383201280000, 120708403200, -36578304000, 9580032000, 0, 0])
]

def fourHighestCache_16_6 : List (Occupation 24 × List ℚ) := [
  ({2,3,4,8}, [0, -1195587993600, 383201280000, -120708403200, 36578304000, -9580032000, 0, 0]),
  ({2,3,5,7}, [0, 1195587993600, -383201280000, 120708403200, -36578304000, 9580032000, 0, 0]),
  ({2,4,5,6}, [0, -1195587993600, 383201280000, -120708403200, 36578304000, -9580032000, 0, 0])
]

def fourHighestCache_16 : List (Occupation 24 × List ℚ) := fourHighestCache_16_0 ++ fourHighestCache_16_1 ++ fourHighestCache_16_2 ++ fourHighestCache_16_3 ++ fourHighestCache_16_4 ++ fourHighestCache_16_5 ++ fourHighestCache_16_6

theorem fourHighestNumber_16_1 : ∀ A∈highestFourOccupations 16,
    kernelHighestEntry 16 ⟨⟨1,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_16 1 A := by
  rw [fourOccupations_16]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_16_3 : ∀ A∈highestFourOccupations 16,
    kernelHighestEntry 16 ⟨⟨3,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_16 3 A := by
  rw [fourOccupations_16]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_16_5 : ∀ A∈highestFourOccupations 16,
    kernelHighestEntry 16 ⟨⟨5,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_16 5 A := by
  rw [fourOccupations_16]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_16_7 : ∀ A∈highestFourOccupations 16,
    kernelHighestEntry 16 ⟨⟨7,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_16 7 A := by
  rw [fourOccupations_16]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_16_9 : ∀ A∈highestFourOccupations 16,
    kernelHighestEntry 16 ⟨⟨9,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_16 9 A := by
  rw [fourOccupations_16]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_16_11 : ∀ A∈highestFourOccupations 16,
    kernelHighestEntry 16 ⟨⟨11,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_16 11 A := by
  rw [fourOccupations_16]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_16_13 : ∀ A∈highestFourOccupations 16,
    kernelHighestEntry 16 ⟨⟨13,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_16 13 A := by
  rw [fourOccupations_16]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_16_15 : ∀ A∈highestFourOccupations 16,
    kernelHighestEntry 16 ⟨⟨15,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_16 15 A := by
  rw [fourOccupations_16]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestChecked_16 : ∀ r : CopyLabel 16, ∀ A∈highestFourOccupations 16,
    kernelHighestEntry 16 r A = highestLookup fourHighestCache_16 r.val.val A := by
  intro r
  fin_cases r
  · exact fourHighestNumber_16_1
  · exact fourHighestNumber_16_3
  · exact fourHighestNumber_16_5
  · exact fourHighestNumber_16_7
  · exact fourHighestNumber_16_9
  · exact fourHighestNumber_16_11
  · exact fourHighestNumber_16_13
  · exact fourHighestNumber_16_15

theorem fourZChecked_16 (r s : CopyLabel 16) :
    integerFourGram 16 r s = fourZData_16 r s := by
  rw [integerFourGram_cached 16 fourHighestCache_16 fourHighestChecked_16]
  have h : ∀ r s : CopyLabel 16, cachedFourGram 16 fourHighestCache_16 r s = fourZData_16 r s := by
    simp only [cachedFourGram, fourOccupations_16]
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact h r s

theorem fourLDLChecked_16 :
    fourZData_16 * (Matrix.diagonal (fun r : CopyLabel 16 =>
      ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 16 r.val.val) -
      Matrix.diagonal (fun r : CopyLabel 16 => rationalCopyDiagonal 16 r.val.val) *
        fourYData_16 * Matrix.diagonal (fun r : CopyLabel 16 => rationalCopyDiagonal 16 r.val.val)) *
      fourZData_16 = fourLData_16 * Matrix.diagonal fourPivotData_16 * (fourLData_16)ᵀ := by
  have h : ∀ r s : CopyLabel 16,
      (fourZData_16 * (Matrix.diagonal (fun r : CopyLabel 16 =>
        ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 16 r.val.val) -
        Matrix.diagonal (fun r : CopyLabel 16 => rationalCopyDiagonal 16 r.val.val) *
          fourYData_16 * Matrix.diagonal (fun r : CopyLabel 16 => rationalCopyDiagonal 16 r.val.val)) *
        fourZData_16 : Matrix (CopyLabel 16) (CopyLabel 16) ℚ) r s =
      (fourLData_16 * Matrix.diagonal fourPivotData_16 * (fourLData_16)ᵀ : Matrix (CopyLabel 16) (CopyLabel 16) ℚ) r s := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact Matrix.ext h

theorem fourPivotChecked_16 : ∀ r, 0 ≤ fourPivotData_16 r := by
  intro r
  fin_cases r <;> norm_num [fourPivotData_16, copyDiagonalData]

theorem integer_certificate_16 :
    ((integerCompression 16).map (algebraMap ℚ ℂ)).PosSemidef := by
  apply rational_ldl_posSemidef _ (fourLData_16) (fourPivotData_16) _ fourPivotChecked_16
  unfold integerCompression integerFourMiddle
  rw [show integerRowsFourTrace 16 = fourYData_16 from Matrix.ext fourYChecked_16,
    show integerFourGram 16 = fourZData_16 from Matrix.ext fourZChecked_16]
  exact fourLDLChecked_16

end LaughlinFock
end

end OAI
