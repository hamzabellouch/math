import Mathlib
import OAI.Analysis.LaughlinFock.Certificate18Data
import OAI.Analysis.LaughlinFock.GramCache
import OAI.Analysis.LaughlinFock.TraceSymmetry

namespace OAI

/-! Certificate18. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourYLower_18 (r s : CopyLabel 18) (hrs : s.val.val ≤ r.val.val) :
    integerRowsFourTrace 18 r s = fourYData_18 r s := by
  rw [integerRowsFourTrace_collected (by decide) collectedFourData_18 collectedFourChecked_18]
  fin_cases r <;> fin_cases s
  · exact fourYNumber_18_1_1
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
  · exact fourYNumber_18_3_1
  · exact fourYNumber_18_3_3
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
  · exact fourYNumber_18_5_1
  · exact fourYNumber_18_5_3
  · exact fourYNumber_18_5_5
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
  · exact fourYNumber_18_7_1
  · exact fourYNumber_18_7_3
  · exact fourYNumber_18_7_5
  · exact fourYNumber_18_7_7
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
  · exact fourYNumber_18_9_1
  · exact fourYNumber_18_9_3
  · exact fourYNumber_18_9_5
  · exact fourYNumber_18_9_7
  · exact fourYNumber_18_9_9
  · have h : (11:ℕ) ≤ 9 := hrs
    omega
  · have h : (13:ℕ) ≤ 9 := hrs
    omega
  · have h : (15:ℕ) ≤ 9 := hrs
    omega
  · have h : (17:ℕ) ≤ 9 := hrs
    omega
  · exact fourYNumber_18_11_1
  · exact fourYNumber_18_11_3
  · exact fourYNumber_18_11_5
  · exact fourYNumber_18_11_7
  · exact fourYNumber_18_11_9
  · exact fourYNumber_18_11_11
  · have h : (13:ℕ) ≤ 11 := hrs
    omega
  · have h : (15:ℕ) ≤ 11 := hrs
    omega
  · have h : (17:ℕ) ≤ 11 := hrs
    omega
  · exact fourYNumber_18_13_1
  · exact fourYNumber_18_13_3
  · exact fourYNumber_18_13_5
  · exact fourYNumber_18_13_7
  · exact fourYNumber_18_13_9
  · exact fourYNumber_18_13_11
  · exact fourYNumber_18_13_13
  · have h : (15:ℕ) ≤ 13 := hrs
    omega
  · have h : (17:ℕ) ≤ 13 := hrs
    omega
  · exact fourYNumber_18_15_1
  · exact fourYNumber_18_15_3
  · exact fourYNumber_18_15_5
  · exact fourYNumber_18_15_7
  · exact fourYNumber_18_15_9
  · exact fourYNumber_18_15_11
  · exact fourYNumber_18_15_13
  · exact fourYNumber_18_15_15
  · have h : (17:ℕ) ≤ 15 := hrs
    omega
  · exact fourYNumber_18_17_1
  · exact fourYNumber_18_17_3
  · exact fourYNumber_18_17_5
  · exact fourYNumber_18_17_7
  · exact fourYNumber_18_17_9
  · exact fourYNumber_18_17_11
  · exact fourYNumber_18_17_13
  · exact fourYNumber_18_17_15
  · exact fourYNumber_18_17_17

theorem fourYChecked_18 (r s : CopyLabel 18) :
    integerRowsFourTrace 18 r s = fourYData_18 r s := by
  have hh : ∀ r s : CopyLabel 18, fourYData_18 r s = fourYData_18 s r := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  by_cases h : s.val.val ≤ r.val.val
  · exact fourYLower_18 r s h
  · rw [integerRowsFourTrace_symm, fourYLower_18 s r (by omega), hh]

def fourHighestCache_18_0 : List (Occupation 24 × List ℚ) := [
  ({0,1,2,16}, [0, -14060114804736000, -8034351316992000, -3640565440512000, -753220435968000, 627683696640000, 502146957312000, -1129830653952000, -4268249137152000]),
  ({0,1,3,15}, [0, 14060114804736000, 8034351316992000, 3640565440512000, 753220435968000, -627683696640000, -502146957312000, 1129830653952000, 4268249137152000]),
  ({0,1,4,14}, [0, -17575143505920000, -7364822040576000, -2374736652288000, -338949196185600, 334764638208000, 324303243264000, -596299511808000, -3556874280960000]),
  ({0,1,5,13}, [0, 16068702633984000, 6121410527232000, 1339058552832000, 0, -104613949440000, -149448499200000, 125536739328000, 2845499424768000])
]

def fourHighestCache_18_1 : List (Occupation 24 × List ℚ) := [
  ({0,1,6,12}, [0, -13557967847424000, -4304116776960000, -668724553728000, 101395058688000, 24141680640000, 22417274880000, 125536739328000, -2134124568576000]),
  ({0,1,7,11}, [0, 10042939146240000, 2678117105664000, 234979024896000, -57940033536000, -24141680640000, 41845579776000, -188305108992000, 1422749712384000]),
  ({0,1,8,10}, [0, -5021469573120000, -1339058552832000, -27360571392000, 7900913664000, 24141680640000, -41845579776000, 125536739328000, -711374856192000]),
  ({0,2,3,14}, [0, 3515028701184000, -669529276416000, -1265828788224000, -414271239782400, 292919058432000, 177843714048000, -533531142144000, -711374856192000])
]

def fourHighestCache_18_2 : List (Occupation 24 × List ℚ) := [
  ({0,2,4,13}, [0, 1506440871936000, 1243411513344000, 1035678099456000, 338949196185600, -230150688768000, -174854744064000, 470762772480000, 711374856192000]),
  ({0,2,5,12}, [0, -2510734786560000, -1817293750272000, -670333999104000, -101395058688000, 80472268800000, 127031224320000, -251073478656000, -711374856192000]),
  ({0,2,6,11}, [0, 3515028701184000, 1625999671296000, 433745528832000, -43455025152000, 0, -64262854656000, 62768369664000, 711374856192000]),
  ({0,2,7,10}, [0, -5021469573120000, -1339058552832000, -207618453504000, 50039119872000, 0, 0, 62768369664000, -711374856192000])
]

def fourHighestCache_18_3 : List (Occupation 24 × List ℚ) := [
  ({0,2,8,9}, [0, 5021469573120000, 1339058552832000, 27360571392000, -7900913664000, -24141680640000, 41845579776000, -125536739328000, 711374856192000]),
  ({0,3,4,12}, [0, -4017175658496000, 0, -135193411584000, -162232093900800, 86910050304000, 44834549760000, -156920924160000, 0]),
  ({0,3,5,11}, [0, 4017175658496000, 382588157952000, 70815596544000, 115880067072000, -52306974720000, -52306974720000, 141228831744000, 0]),
  ({0,3,6,10}, [0, -2510734786560000, -286941118464000, -103809226752000, -17118646272000, 0, 49318004736000, -94152554496000, 0])
]

def fourHighestCache_18_4 : List (Occupation 24 × List ℚ) := [
  ({0,3,7,9}, [0, 2008587829248000, 0, 106223394816000, -24229468569600, 16899176448000, -31384184832000, 47076277248000, 0]),
  ({0,4,5,10}, [0, -2510734786560000, -286941118464000, 76448655360000, -59256852480000, 24141680640000, 7472424960000, -31384184832000, 0]),
  ({0,4,6,9}, [0, 2510734786560000, 286941118464000, -50697529344000, 33973928755200, -9656672256000, -13450364928000, 31384184832000, 0]),
  ({0,4,7,8}, [0, -4017175658496000, 0, -32188907520000, 6320730931200, -9656672256000, 20922789888000, -31384184832000, 0])
]

def fourHighestCache_18_5 : List (Occupation 24 × List ℚ) := [
  ({0,5,6,8}, [0, 1004293914624000, -191294078976000, 46673915904000, -18435465216000, 8047226880000, -2988969984000, 0, 0]),
  ({1,2,3,13}, [0, -5021469573120000, -573882236928000, 230150688768000, 75322043596800, -62768369664000, -2988969984000, 62768369664000, 0]),
  ({1,2,4,12}, [0, 5021469573120000, 573882236928000, -230150688768000, -75322043596800, 62768369664000, 2988969984000, -62768369664000, 0]),
  ({1,2,5,11}, [0, -5021469573120000, -191294078976000, 165772873728000, 28970016768000, -28165294080000, -10461394944000, 47076277248000, 0])
]

def fourHighestCache_18_6 : List (Occupation 24 × List ℚ) := [
  ({1,2,6,10}, [0, 4017175658496000, 0, -122317848576000, 10534551552000, 0, 14944849920000, -31384184832000, 0]),
  ({1,2,7,9}, [0, -2008587829248000, 0, 74034487296000, -17908737638400, 7242504192000, -10461394944000, 15692092416000, 0]),
  ({1,3,4,11}, [0, 0, -382588157952000, 64377815040000, 46352026828800, -34603075584000, 7472424960000, 15692092416000, 0]),
  ({1,3,5,10}, [0, 1004293914624000, 191294078976000, -43455025152000, -39504568320000, 28165294080000, -4483454976000, -15692092416000, 0])
]

def fourHighestCache_18_7 : List (Occupation 24 × List ℚ) := [
  ({1,3,6,9}, [0, -2008587829248000, 0, 48283361280000, 7374186086400, -7242504192000, -4483454976000, 15692092416000, 0]),
  ({1,3,7,8}, [0, 2008587829248000, 0, -74034487296000, 17908737638400, -7242504192000, 10461394944000, -15692092416000, 0]),
  ({1,4,5,9}, [0, 0, 0, -25751126016000, 25282923724800, -14485008384000, 5977939968000, 0, 0]),
  ({1,4,6,8}, [0, 502146957312000, -95647039488000, 36212520960000, -21859194470400, 11266117632000, -4483454976000, 0, 0])
]

def fourHighestCache_18_8 : List (Occupation 24 × List ℚ) := [
  ({1,5,6,7}, [0, -1004293914624000, 191294078976000, -46673915904000, 18435465216000, -8047226880000, 2988969984000, 0, 0]),
  ({2,3,4,10}, [0, -1004293914624000, 191294078976000, -20922789888000, -6847458508800, 6437781504000, -2988969984000, 0, 0]),
  ({2,3,5,9}, [0, 1004293914624000, -191294078976000, 20922789888000, 6847458508800, -6437781504000, 2988969984000, 0, 0]),
  ({2,3,6,8}, [0, -502146957312000, 95647039488000, -10461394944000, -3423729254400, 3218890752000, -1494484992000, 0, 0])
]

def fourHighestCache_18_9 : List (Occupation 24 × List ℚ) := [
  ({2,4,5,8}, [0, -502146957312000, 95647039488000, -10461394944000, -3423729254400, 3218890752000, -1494484992000, 0, 0]),
  ({2,4,6,7}, [0, 502146957312000, -95647039488000, 10461394944000, 3423729254400, -3218890752000, 1494484992000, 0, 0]),
  ({3,4,5,7}, [0, 0, 0, 0, 0, 0, 0, 0, 0])
]

def fourHighestCache_18 : List (Occupation 24 × List ℚ) := fourHighestCache_18_0 ++ fourHighestCache_18_1 ++ fourHighestCache_18_2 ++ fourHighestCache_18_3 ++ fourHighestCache_18_4 ++ fourHighestCache_18_5 ++ fourHighestCache_18_6 ++ fourHighestCache_18_7 ++ fourHighestCache_18_8 ++ fourHighestCache_18_9

theorem fourHighestNumber_18_1 : ∀ A∈highestFourOccupations 18,
    kernelHighestEntry 18 ⟨⟨1,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_18 1 A := by
  rw [fourOccupations_18]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_18_3 : ∀ A∈highestFourOccupations 18,
    kernelHighestEntry 18 ⟨⟨3,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_18 3 A := by
  rw [fourOccupations_18]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_18_5 : ∀ A∈highestFourOccupations 18,
    kernelHighestEntry 18 ⟨⟨5,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_18 5 A := by
  rw [fourOccupations_18]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_18_7 : ∀ A∈highestFourOccupations 18,
    kernelHighestEntry 18 ⟨⟨7,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_18 7 A := by
  rw [fourOccupations_18]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_18_9 : ∀ A∈highestFourOccupations 18,
    kernelHighestEntry 18 ⟨⟨9,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_18 9 A := by
  rw [fourOccupations_18]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_18_11 : ∀ A∈highestFourOccupations 18,
    kernelHighestEntry 18 ⟨⟨11,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_18 11 A := by
  rw [fourOccupations_18]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_18_13 : ∀ A∈highestFourOccupations 18,
    kernelHighestEntry 18 ⟨⟨13,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_18 13 A := by
  rw [fourOccupations_18]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_18_15 : ∀ A∈highestFourOccupations 18,
    kernelHighestEntry 18 ⟨⟨15,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_18 15 A := by
  rw [fourOccupations_18]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_18_17 : ∀ A∈highestFourOccupations 18,
    kernelHighestEntry 18 ⟨⟨17,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_18 17 A := by
  rw [fourOccupations_18]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestChecked_18 : ∀ r : CopyLabel 18, ∀ A∈highestFourOccupations 18,
    kernelHighestEntry 18 r A = highestLookup fourHighestCache_18 r.val.val A := by
  intro r
  fin_cases r
  · exact fourHighestNumber_18_1
  · exact fourHighestNumber_18_3
  · exact fourHighestNumber_18_5
  · exact fourHighestNumber_18_7
  · exact fourHighestNumber_18_9
  · exact fourHighestNumber_18_11
  · exact fourHighestNumber_18_13
  · exact fourHighestNumber_18_15
  · exact fourHighestNumber_18_17

theorem fourZChecked_18 (r s : CopyLabel 18) :
    integerFourGram 18 r s = fourZData_18 r s := by
  rw [integerFourGram_cached 18 fourHighestCache_18 fourHighestChecked_18]
  have h : ∀ r s : CopyLabel 18, cachedFourGram 18 fourHighestCache_18 r s = fourZData_18 r s := by
    simp only [cachedFourGram, fourOccupations_18]
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact h r s

theorem fourLDLChecked_18 :
    fourZData_18 * (Matrix.diagonal (fun r : CopyLabel 18 =>
      ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 18 r.val.val) -
      Matrix.diagonal (fun r : CopyLabel 18 => rationalCopyDiagonal 18 r.val.val) *
        fourYData_18 * Matrix.diagonal (fun r : CopyLabel 18 => rationalCopyDiagonal 18 r.val.val)) *
      fourZData_18 = fourLData_18 * Matrix.diagonal fourPivotData_18 * (fourLData_18)ᵀ := by
  have h : ∀ r s : CopyLabel 18,
      (fourZData_18 * (Matrix.diagonal (fun r : CopyLabel 18 =>
        ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 18 r.val.val) -
        Matrix.diagonal (fun r : CopyLabel 18 => rationalCopyDiagonal 18 r.val.val) *
          fourYData_18 * Matrix.diagonal (fun r : CopyLabel 18 => rationalCopyDiagonal 18 r.val.val)) *
        fourZData_18 : Matrix (CopyLabel 18) (CopyLabel 18) ℚ) r s =
      (fourLData_18 * Matrix.diagonal fourPivotData_18 * (fourLData_18)ᵀ : Matrix (CopyLabel 18) (CopyLabel 18) ℚ) r s := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact Matrix.ext h

theorem fourPivotChecked_18 : ∀ r, 0 ≤ fourPivotData_18 r := by
  intro r
  fin_cases r <;> norm_num [fourPivotData_18, copyDiagonalData]

theorem integer_certificate_18 :
    ((integerCompression 18).map (algebraMap ℚ ℂ)).PosSemidef := by
  apply rational_ldl_posSemidef _ (fourLData_18) (fourPivotData_18) _ fourPivotChecked_18
  unfold integerCompression integerFourMiddle
  rw [show integerRowsFourTrace 18 = fourYData_18 from Matrix.ext fourYChecked_18,
    show integerFourGram 18 = fourZData_18 from Matrix.ext fourZChecked_18]
  exact fourLDLChecked_18

end LaughlinFock
end

end OAI
