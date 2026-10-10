import Mathlib
import OAI.Analysis.LaughlinFock.Certificate17Data
import OAI.Analysis.LaughlinFock.GramCache
import OAI.Analysis.LaughlinFock.TraceSymmetry

namespace OAI

/-! Certificate17. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourYLower_17 (r s : CopyLabel 17) (hrs : s.val.val ≤ r.val.val) :
    integerRowsFourTrace 17 r s = fourYData_17 r s := by
  rw [integerRowsFourTrace_collected (by decide) collectedFourData_17 collectedFourChecked_17]
  fin_cases r <;> fin_cases s
  · exact fourYNumber_17_1_1
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
  · have h : (17:ℕ) ≤ 1 := hrs
    omega
  · exact fourYNumber_17_3_1
  · exact fourYNumber_17_3_3
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
  · have h : (17:ℕ) ≤ 3 := hrs
    omega
  · exact fourYNumber_17_5_1
  · exact fourYNumber_17_5_3
  · exact fourYNumber_17_5_5
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
  · have h : (17:ℕ) ≤ 5 := hrs
    omega
  · exact fourYNumber_17_7_1
  · exact fourYNumber_17_7_3
  · exact fourYNumber_17_7_5
  · exact fourYNumber_17_7_7
  · have h : (9:ℕ) ≤ 7 := hrs
    omega
  · have h : (11:ℕ) ≤ 7 := hrs
    omega
  · have h : (13:ℕ) ≤ 7 := hrs
    omega
  · have h : (15:ℕ) ≤ 7 := hrs
    omega
  · have h : (17:ℕ) ≤ 7 := hrs
    omega
  · exact fourYNumber_17_9_1
  · exact fourYNumber_17_9_3
  · exact fourYNumber_17_9_5
  · exact fourYNumber_17_9_7
  · exact fourYNumber_17_9_9
  · have h : (11:ℕ) ≤ 9 := hrs
    omega
  · have h : (13:ℕ) ≤ 9 := hrs
    omega
  · have h : (15:ℕ) ≤ 9 := hrs
    omega
  · have h : (17:ℕ) ≤ 9 := hrs
    omega
  · exact fourYNumber_17_11_1
  · exact fourYNumber_17_11_3
  · exact fourYNumber_17_11_5
  · exact fourYNumber_17_11_7
  · exact fourYNumber_17_11_9
  · exact fourYNumber_17_11_11
  · have h : (13:ℕ) ≤ 11 := hrs
    omega
  · have h : (15:ℕ) ≤ 11 := hrs
    omega
  · have h : (17:ℕ) ≤ 11 := hrs
    omega
  · exact fourYNumber_17_13_1
  · exact fourYNumber_17_13_3
  · exact fourYNumber_17_13_5
  · exact fourYNumber_17_13_7
  · exact fourYNumber_17_13_9
  · exact fourYNumber_17_13_11
  · exact fourYNumber_17_13_13
  · have h : (15:ℕ) ≤ 13 := hrs
    omega
  · have h : (17:ℕ) ≤ 13 := hrs
    omega
  · exact fourYNumber_17_15_1
  · exact fourYNumber_17_15_3
  · exact fourYNumber_17_15_5
  · exact fourYNumber_17_15_7
  · exact fourYNumber_17_15_9
  · exact fourYNumber_17_15_11
  · exact fourYNumber_17_15_13
  · exact fourYNumber_17_15_15
  · have h : (17:ℕ) ≤ 15 := hrs
    omega
  · exact fourYNumber_17_17_1
  · exact fourYNumber_17_17_3
  · exact fourYNumber_17_17_5
  · exact fourYNumber_17_17_7
  · exact fourYNumber_17_17_9
  · exact fourYNumber_17_17_11
  · exact fourYNumber_17_17_13
  · exact fourYNumber_17_17_15
  · exact fourYNumber_17_17_17

theorem fourYChecked_17 (r s : CopyLabel 17) :
    integerRowsFourTrace 17 r s = fourYData_17 r s := by
  have hh : ∀ r s : CopyLabel 17, fourYData_17 r s = fourYData_17 s r := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  by_cases h : s.val.val ≤ r.val.val
  · exact fourYLower_17 r s h
  · rw [integerRowsFourTrace_symm, fourYLower_17 s r (by omega), hh]

def fourHighestCache_17_0 : List (Occupation 24 × List ℚ) := [
  ({0,1,2,15}, [2343352467456000, 732297646080000, 402763705344000, 159536272896000, 10461394944000, -44460928512000, -5230697472000, 128152088064000, 355687428096000]),
  ({0,1,3,14}, [-2343352467456000, -732297646080000, -402763705344000, -159536272896000, -10461394944000, 44460928512000, 5230697472000, -128152088064000, -355687428096000]),
  ({0,1,4,13}, [4017175658496000, 920602755072000, 343731548160000, 94152554496000, 2092278988800, -23164517376000, -8518564454400, 83691159552000, 355687428096000]),
  ({0,1,5,12}, [-4017175658496000, -920602755072000, -270156902400000, -42650302464000, 5633058816000, 5460618240000, 9714152448000, -41845579776000, -355687428096000])
]

def fourHighestCache_17_1 : List (Occupation 24 × List ℚ) := [
  ({0,1,6,11}, [5021469573120000, 899679965184000, 176981511168000, 16295634432000, -7242504192000, 1293304320000, -5977939968000, 10461394944000, 355687428096000]),
  ({0,1,7,10}, [-5021469573120000, -899679965184000, -103406865408000, -2249565696000, 3730987008000, -603542016000, 0, 10461394944000, -355687428096000]),
  ({0,1,8,9}, [5356234211328000, 870388059340800, 70815596544000, -5559902208000, 58525286400, -1609445376000, 4184557977600, -20922789888000, 355687428096000]),
  ({0,2,3,13}, [-1673823191040000, -188305108992000, 59032157184000, 65383718400000, 8369115955200, -21296411136000, 3287866982400, 44460928512000, 0])
]

def fourHighestCache_17_2 : List (Occupation 24 × List ℚ) := [
  ({0,2,4,12}, [0, 0, -73574645760000, -51502252032000, -7725337804800, 17703899136000, -1195587993600, -41845579776000, 0]),
  ({0,2,5,11}, [-1004293914624000, 20922789888000, 93175391232000, 26354668032000, 1609445376000, -6753922560000, -3736212480000, 31384184832000, 0]),
  ({0,2,6,10}, [0, 0, -73574645760000, -14046068736000, 3511517184000, -689762304000, 5977939968000, -20922789888000, 0]),
  ({0,2,7,9}, [-334764638208000, 29291905843200, 32591268864000, 7809467904000, -3789512294400, 2212987392000, -4184557977600, 10461394944000, 0])
]

def fourHighestCache_17_3 : List (Occupation 24 × List ℚ) := [
  ({0,3,4,11}, [2678117105664000, 167382319104000, -5058256896000, 11266117632000, 5472114278400, -7357464576000, 2839521484800, 7846046208000, 0]),
  ({0,3,5,10}, [-1673823191040000, -188305108992000, -14542488576000, -4846625280000, -4974649344000, 5604318720000, -1494484992000, -7846046208000, 0]),
  ({0,3,6,9}, [3012881743872000, 138090413260800, 21210190848000, 3456649728000, 833985331200, -1293304320000, -1345036492800, 7846046208000, 0]),
  ({0,3,7,8}, [-2678117105664000, -167382319104000, -9656672256000, -6584094720000, 2721425817600, -1609445376000, 3138418483200, -7846046208000, 0])
]

def fourHighestCache_17_4 : List (Occupation 24 × List ℚ) := [
  ({0,4,5,9}, [-1339058552832000, 50214695731200, 8047226880000, -3292047360000, 3438360576000, -2701569024000, 1643933491200, 0, 0]),
  ({0,4,6,8}, [0, 0, -14714929152000, 4682022912000, -3043314892800, 2069286912000, -1195587993600, 0, 0]),
  ({0,5,6,7}, [1004293914624000, -20922789888000, 17186577408000, -5285564928000, 2487324672000, -1408264704000, 747242496000, 0, 0]),
  ({1,2,3,12}, [1673823191040000, 188305108992000, 14542488576000, -13881466368000, -643778150400, 3592512000000, -2092278988800, -2615348736000, 0])
]

def fourHighestCache_17_5 : List (Occupation 24 × List ℚ) := [
  ({1,2,4,11}, [-1673823191040000, -188305108992000, -14542488576000, 13881466368000, 643778150400, -3592512000000, 2092278988800, 2615348736000, 0]),
  ({1,2,5,10}, [2678117105664000, 167382319104000, -5058256896000, -7461974016000, -146313216000, 1839366144000, -747242496000, -2615348736000, 0]),
  ({1,2,6,9}, [-2678117105664000, -167382319104000, 19773186048000, 2779951104000, -555990220800, -229920768000, -448345497600, 2615348736000, 0]),
  ({1,2,7,8}, [3012881743872000, 138090413260800, -22934596608000, -1225373184000, 1068086476800, -603542016000, 1046139494400, -2615348736000, 0])
]

def fourHighestCache_17_6 : List (Occupation 24 × List ℚ) := [
  ({1,3,4,10}, [-1004293914624000, 20922789888000, 19600745472000, -6419492352000, -497464934400, 1753145856000, -1345036492800, 0, 0]),
  ({1,3,5,9}, [0, 0, -14714929152000, 4682022912000, 702303436800, -1609445376000, 1195587993600, 0, 0]),
  ({1,3,6,8}, [-334764638208000, 29291905843200, 3161410560000, -1554577920000, -512096256000, 833462784000, -597793996800, 0, 0]),
  ({1,4,5,8}, [1339058552832000, -50214695731200, 6667702272000, -1389975552000, -395045683200, 632282112000, -448345497600, 0, 0])
]

def fourHighestCache_17_7 : List (Occupation 24 × List ℚ) := [
  ({1,4,6,7}, [-1004293914624000, 20922789888000, -2471648256000, 603542016000, 555990220800, -661022208000, 448345497600, 0, 0]),
  ({2,3,4,9}, [1004293914624000, -20922789888000, -4885816320000, 1737469440000, -204838502400, -143700480000, 149448499200, 0, 0]),
  ({2,3,5,8}, [-1004293914624000, 20922789888000, 4885816320000, -1737469440000, 204838502400, 143700480000, -149448499200, 0, 0]),
  ({2,3,6,7}, [1339058552832000, -50214695731200, -689762304000, 951035904000, -43893964800, -172440576000, 149448499200, 0, 0])
]

def fourHighestCache_17_8 : List (Occupation 24 × List ℚ) := [
  ({2,4,5,7}, [-334764638208000, 29291905843200, -4196054016000, 786433536000, -160944537600, 28740096000, 0, 0, 0]),
  ({3,4,5,6}, [334764638208000, -29291905843200, 4196054016000, -786433536000, 160944537600, -28740096000, 0, 0, 0])
]

def fourHighestCache_17 : List (Occupation 24 × List ℚ) := fourHighestCache_17_0 ++ fourHighestCache_17_1 ++ fourHighestCache_17_2 ++ fourHighestCache_17_3 ++ fourHighestCache_17_4 ++ fourHighestCache_17_5 ++ fourHighestCache_17_6 ++ fourHighestCache_17_7 ++ fourHighestCache_17_8

theorem fourHighestNumber_17_1 : ∀ A∈highestFourOccupations 17,
    kernelHighestEntry 17 ⟨⟨1,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_17 1 A := by
  rw [fourOccupations_17]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_17_3 : ∀ A∈highestFourOccupations 17,
    kernelHighestEntry 17 ⟨⟨3,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_17 3 A := by
  rw [fourOccupations_17]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_17_5 : ∀ A∈highestFourOccupations 17,
    kernelHighestEntry 17 ⟨⟨5,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_17 5 A := by
  rw [fourOccupations_17]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_17_7 : ∀ A∈highestFourOccupations 17,
    kernelHighestEntry 17 ⟨⟨7,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_17 7 A := by
  rw [fourOccupations_17]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_17_9 : ∀ A∈highestFourOccupations 17,
    kernelHighestEntry 17 ⟨⟨9,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_17 9 A := by
  rw [fourOccupations_17]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_17_11 : ∀ A∈highestFourOccupations 17,
    kernelHighestEntry 17 ⟨⟨11,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_17 11 A := by
  rw [fourOccupations_17]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_17_13 : ∀ A∈highestFourOccupations 17,
    kernelHighestEntry 17 ⟨⟨13,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_17 13 A := by
  rw [fourOccupations_17]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_17_15 : ∀ A∈highestFourOccupations 17,
    kernelHighestEntry 17 ⟨⟨15,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_17 15 A := by
  rw [fourOccupations_17]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_17_17 : ∀ A∈highestFourOccupations 17,
    kernelHighestEntry 17 ⟨⟨17,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_17 17 A := by
  rw [fourOccupations_17]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestChecked_17 : ∀ r : CopyLabel 17, ∀ A∈highestFourOccupations 17,
    kernelHighestEntry 17 r A = highestLookup fourHighestCache_17 r.val.val A := by
  intro r
  fin_cases r
  · exact fourHighestNumber_17_1
  · exact fourHighestNumber_17_3
  · exact fourHighestNumber_17_5
  · exact fourHighestNumber_17_7
  · exact fourHighestNumber_17_9
  · exact fourHighestNumber_17_11
  · exact fourHighestNumber_17_13
  · exact fourHighestNumber_17_15
  · exact fourHighestNumber_17_17

theorem fourZChecked_17 (r s : CopyLabel 17) :
    integerFourGram 17 r s = fourZData_17 r s := by
  rw [integerFourGram_cached 17 fourHighestCache_17 fourHighestChecked_17]
  have h : ∀ r s : CopyLabel 17, cachedFourGram 17 fourHighestCache_17 r s = fourZData_17 r s := by
    simp only [cachedFourGram, fourOccupations_17]
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact h r s

theorem fourLDLChecked_17 :
    fourZData_17 * (Matrix.diagonal (fun r : CopyLabel 17 =>
      ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 17 r.val.val) -
      Matrix.diagonal (fun r : CopyLabel 17 => rationalCopyDiagonal 17 r.val.val) *
        fourYData_17 * Matrix.diagonal (fun r : CopyLabel 17 => rationalCopyDiagonal 17 r.val.val)) *
      fourZData_17 = fourLData_17 * Matrix.diagonal fourPivotData_17 * (fourLData_17)ᵀ := by
  have h : ∀ r s : CopyLabel 17,
      (fourZData_17 * (Matrix.diagonal (fun r : CopyLabel 17 =>
        ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 17 r.val.val) -
        Matrix.diagonal (fun r : CopyLabel 17 => rationalCopyDiagonal 17 r.val.val) *
          fourYData_17 * Matrix.diagonal (fun r : CopyLabel 17 => rationalCopyDiagonal 17 r.val.val)) *
        fourZData_17 : Matrix (CopyLabel 17) (CopyLabel 17) ℚ) r s =
      (fourLData_17 * Matrix.diagonal fourPivotData_17 * (fourLData_17)ᵀ : Matrix (CopyLabel 17) (CopyLabel 17) ℚ) r s := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact Matrix.ext h

theorem fourPivotChecked_17 : ∀ r, 0 ≤ fourPivotData_17 r := by
  intro r
  fin_cases r <;> norm_num [fourPivotData_17, copyDiagonalData]

theorem integer_certificate_17 :
    ((integerCompression 17).map (algebraMap ℚ ℂ)).PosSemidef := by
  apply rational_ldl_posSemidef _ (fourLData_17) (fourPivotData_17) _ fourPivotChecked_17
  unfold integerCompression integerFourMiddle
  rw [show integerRowsFourTrace 17 = fourYData_17 from Matrix.ext fourYChecked_17,
    show integerFourGram 17 = fourZData_17 from Matrix.ext fourZChecked_17]
  exact fourLDLChecked_17

end LaughlinFock
end

end OAI
