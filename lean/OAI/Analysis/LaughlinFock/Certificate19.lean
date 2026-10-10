import Mathlib
import OAI.Analysis.LaughlinFock.Certificate19Data
import OAI.Analysis.LaughlinFock.GramCache
import OAI.Analysis.LaughlinFock.TraceSymmetry

namespace OAI

/-! Certificate19. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourYLower_19 (r s : CopyLabel 19) (hrs : s.val.val ≤ r.val.val) :
    integerRowsFourTrace 19 r s = fourYData_19 r s := by
  rw [integerRowsFourTrace_collected (by decide) collectedFourData_19 collectedFourChecked_19]
  fin_cases r <;> fin_cases s
  · exact fourYNumber_19_1_1
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
  · have h : (19:ℕ) ≤ 1 := hrs
    omega
  · exact fourYNumber_19_3_1
  · exact fourYNumber_19_3_3
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
  · have h : (19:ℕ) ≤ 3 := hrs
    omega
  · exact fourYNumber_19_5_1
  · exact fourYNumber_19_5_3
  · exact fourYNumber_19_5_5
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
  · have h : (19:ℕ) ≤ 5 := hrs
    omega
  · exact fourYNumber_19_7_1
  · exact fourYNumber_19_7_3
  · exact fourYNumber_19_7_5
  · exact fourYNumber_19_7_7
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
  · have h : (19:ℕ) ≤ 7 := hrs
    omega
  · exact fourYNumber_19_9_1
  · exact fourYNumber_19_9_3
  · exact fourYNumber_19_9_5
  · exact fourYNumber_19_9_7
  · exact fourYNumber_19_9_9
  · have h : (11:ℕ) ≤ 9 := hrs
    omega
  · have h : (13:ℕ) ≤ 9 := hrs
    omega
  · have h : (15:ℕ) ≤ 9 := hrs
    omega
  · have h : (17:ℕ) ≤ 9 := hrs
    omega
  · have h : (19:ℕ) ≤ 9 := hrs
    omega
  · exact fourYNumber_19_11_1
  · exact fourYNumber_19_11_3
  · exact fourYNumber_19_11_5
  · exact fourYNumber_19_11_7
  · exact fourYNumber_19_11_9
  · exact fourYNumber_19_11_11
  · have h : (13:ℕ) ≤ 11 := hrs
    omega
  · have h : (15:ℕ) ≤ 11 := hrs
    omega
  · have h : (17:ℕ) ≤ 11 := hrs
    omega
  · have h : (19:ℕ) ≤ 11 := hrs
    omega
  · exact fourYNumber_19_13_1
  · exact fourYNumber_19_13_3
  · exact fourYNumber_19_13_5
  · exact fourYNumber_19_13_7
  · exact fourYNumber_19_13_9
  · exact fourYNumber_19_13_11
  · exact fourYNumber_19_13_13
  · have h : (15:ℕ) ≤ 13 := hrs
    omega
  · have h : (17:ℕ) ≤ 13 := hrs
    omega
  · have h : (19:ℕ) ≤ 13 := hrs
    omega
  · exact fourYNumber_19_15_1
  · exact fourYNumber_19_15_3
  · exact fourYNumber_19_15_5
  · exact fourYNumber_19_15_7
  · exact fourYNumber_19_15_9
  · exact fourYNumber_19_15_11
  · exact fourYNumber_19_15_13
  · exact fourYNumber_19_15_15
  · have h : (17:ℕ) ≤ 15 := hrs
    omega
  · have h : (19:ℕ) ≤ 15 := hrs
    omega
  · exact fourYNumber_19_17_1
  · exact fourYNumber_19_17_3
  · exact fourYNumber_19_17_5
  · exact fourYNumber_19_17_7
  · exact fourYNumber_19_17_9
  · exact fourYNumber_19_17_11
  · exact fourYNumber_19_17_13
  · exact fourYNumber_19_17_15
  · exact fourYNumber_19_17_17
  · have h : (19:ℕ) ≤ 17 := hrs
    omega
  · exact fourYNumber_19_19_1
  · exact fourYNumber_19_19_3
  · exact fourYNumber_19_19_5
  · exact fourYNumber_19_19_7
  · exact fourYNumber_19_19_9
  · exact fourYNumber_19_19_11
  · exact fourYNumber_19_19_13
  · exact fourYNumber_19_19_15
  · exact fourYNumber_19_19_17
  · exact fourYNumber_19_19_19

theorem fourYChecked_19 (r s : CopyLabel 19) :
    integerRowsFourTrace 19 r s = fourYData_19 r s := by
  have hh : ∀ r s : CopyLabel 19, fourYData_19 r s = fourYData_19 s r := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  by_cases h : s.val.val ≤ r.val.val
  · exact fourYLower_19 r s h
  · rw [integerRowsFourTrace_symm, fourYLower_19 s r (by omega), hh]

def fourHighestCache_19_0 : List (Occupation 24 × List ℚ) := [
  ({0,1,2,17}, [819503834333184000, 273167944777728000, 166461716348928000, 83230858174464000, 25609494822912000, -6402373705728000, -12804747411456000, 6402373705728000, 51218989645824000, 121645100408832000]),
  ({0,1,3,16}, [-819503834333184000, -273167944777728000, -166461716348928000, -83230858174464000, -25609494822912000, 6402373705728000, 12804747411456000, -6402373705728000, -51218989645824000, -121645100408832000]),
  ({0,1,4,15}, [1434131710083072000, 365562984923136000, 161251941666816000, 59033651668992000, 13369662738432000, -3828870549504000, -7249746696192000, 1977203644416000, 36280117665792000, 121645100408832000]),
  ({0,1,5,14}, [-1434131710083072000, -365562984923136000, -137818416992256000, -37943479461888000, -3577797070848000, 1987665039360000, 2353813862400000, 1537825056768000, -22052620541952000, -121645100408832000])
]

def fourHighestCache_19_1 : List (Occupation 24 × List ℚ) := [
  ({0,1,6,13}, [1843883627249664000, 373597336240128000, 101873063964672000, 21309861500928000, -188305108992000, -1255367393280000, 112086374400000, -2385198047232000, 10670622842880000, 121645100408832000]),
  ({0,1,7,12}, [-1843883627249664000, -373597336240128000, -71744246525952000, -9026574391296000, 593885343744000, 830473814016000, -596299511808000, 1380904132608000, -2134124568576000, -121645100408832000]),
  ({0,1,8,11}, [2048759585832960000, 361545809264640000, 49921776672768000, 2351399694336000, -463520268288000, -275215159296000, 125536739328000, 125536739328000, -3556874280960000, 121645100408832000]),
  ({0,1,9,10}, [-2048759585832960000, -361545809264640000, -36531191144448000, -188305108992000, 568865783808000, -188305108992000, 376610217984000, -1129830653952000, 6402373705728000, -121645100408832000])
]

def fourHighestCache_19_2 : List (Occupation 24 × List ℚ) := [
  ({0,2,3,15}, [-614627875749888000, -92395040145408000, 5209774682112000, 24197206505472000, 12239832084480000, -2573503156224000, -5555000715264000, 4425170061312000, 14938871980032000, 0]),
  ({0,2,4,14}, [0, 0, -23433524674560000, -21090172207104000, -9791865667584000, 1841205510144000, 4895932833792000, -3515028701184000, -14227497123840000, 0]),
  ({0,2,5,13}, [-409751917166592000, -8034351316992000, 35945353027584000, 16633617960960000, 3766102179840000, -732297646080000, -2465900236800000, 847372990464000, 11381997699072000, 0]),
  ({0,2,6,12}, [0, 0, -30128817438720000, -12283287109632000, -405580234752000, 424893579264000, 484213137408000, 1004293914624000, -8536498274304000, 0])
]

def fourHighestCache_19_3 : List (Occupation 24 × List ℚ) := [
  ({0,2,7,11}, [-204875958583296000, 12051526975488000, 21822469853184000, 6675174696960000, -130365075456000, -555258654720000, 470762772480000, -1506440871936000, 5690998849536000, 0]),
  ({0,2,8,10}, [0, 0, -13390585528320000, -2163094585344000, -105345515520000, 463520268288000, -502146957312000, 1004293914624000, -2845499424768000, 0]),
  ({0,3,4,13}, [1024379792916480000, 100429391462400000, 5711921639424000, 1349519947776000, 3577797070848000, -376610217984000, -1770964715520000, 1757514350592000, 2134124568576000, 0]),
  ({0,3,5,12}, [-614627875749888000, -92395040145408000, -14876103610368000, -1296408250368000, -2245176299520000, -24141680640000, 1546791966720000, -1349519947776000, -2134124568576000, 0])
]

def fourHighestCache_19_4 : List (Occupation 24 × List ℚ) := [
  ({0,3,6,11}, [1229255751499776000, 88377864486912000, 10670622842880000, 2708696567808000, 463520268288000, 178648436736000, -753220435968000, 376610217984000, 2134124568576000, 0]),
  ({0,3,7,10}, [-1024379792916480000, -100429391462400000, -5711921639424000, -2585573996544000, 46088663040000, 67596705792000, 31384184832000, 376610217984000, -2134124568576000, 0]),
  ({0,3,8,9}, [1229255751499776000, 88377864486912000, 6653447184384000, 1318135762944000, 179087376384000, -362125209600000, 376610217984000, -753220435968000, 2134124568576000, 0]),
  ({0,4,5,11}, [-614627875749888000, 4017175658496000, 10900773531648000, -1566795073536000, 738735427584000, 128755630080000, -560431872000000, 596299511808000, 0, 0])
]

def fourHighestCache_19_5 : List (Occupation 24 × List ℚ) := [
  ({0,4,6,10}, [0, 0, -10042939146240000, 849787158528000, -247561961472000, -270386823168000, 520080777216000, -502146957312000, 0, 0]),
  ({0,4,7,9}, [-204875958583296000, 12051526975488000, 3075650113536000, 185890940928000, -109295972352000, 217275125760000, -282457663488000, 251073478656000, 0, 0]),
  ({0,5,6,9}, [614627875749888000, -4017175658496000, 5837458378752000, -673552889856000, 67157766144000, 115880067072000, -174854744064000, 156920924160000, 0, 0]),
  ({0,5,7,8}, [-409751917166592000, -8034351316992000, -4226403557376000, 255901814784000, 79009136640000, -165772873728000, 188305108992000, -156920924160000, 0, 0])
]

def fourHighestCache_19_6 : List (Occupation 24 × List ℚ) := [
  ({1,2,3,14}, [614627875749888000, 92395040145408000, 18223749992448000, -3107034298368000, -2447966416896000, 732297646080000, 659067881472000, -910141360128000, -711374856192000, 0]),
  ({1,2,4,13}, [-614627875749888000, -92395040145408000, -18223749992448000, 3107034298368000, 2447966416896000, -732297646080000, -659067881472000, 910141360128000, 711374856192000, 0]),
  ({1,2,5,12}, [1024379792916480000, 100429391462400000, 9059568021504000, -3053922600960000, -1115345645568000, 331545747456000, 434895132672000, -502146957312000, -711374856192000, 0]),
  ({1,2,6,11}, [-1024379792916480000, -100429391462400000, -2364275257344000, 2899415844864000, 72425041920000, -48283361280000, -201755473920000, 125536739328000, 711374856192000, 0])
]

def fourHighestCache_19_7 : List (Occupation 24 × List ℚ) := [
  ({1,2,7,10}, [1229255751499776000, 88377864486912000, -2719962685440000, -1926506115072000, 189621927936000, 24141680640000, 0, 125536739328000, -711374856192000, 0]),
  ({1,2,8,9}, [-1229255751499776000, -88377864486912000, 6737138343936000, 844958822400000, -73741860864000, -101395058688000, 125536739328000, -251073478656000, 711374856192000, 0]),
  ({1,3,4,12}, [-409751917166592000, -8034351316992000, 9164181970944000, -53111697408000, -1332620771328000, 400751898624000, 224172748800000, -407994402816000, 0, 0]),
  ({1,3,5,11}, [0, 0, -6695292764160000, 154506756096000, 1042920603648000, -283262386176000, -233139658752000, 376610217984000, 0, 0])
]

def fourHighestCache_19_8 : List (Occupation 24 × List ℚ) := [
  ({1,3,6,10}, [-204875958583296000, 12051526975488000, 5084237942784000, -972909729792000, -262046969856000, 24141680640000, 201755473920000, -251073478656000, 0, 0]),
  ({1,3,7,9}, [0, 0, -4017175658496000, 1081547292672000, -115880067072000, 77253378048000, -125536739328000, 125536739328000, 0, 0]),
  ({1,4,5,10}, [614627875749888000, -4017175658496000, -857834385408000, 717007915008000, -491173466112000, 141631193088000, 40351094784000, -94152554496000, 0, 0]),
  ({1,4,6,9}, [-409751917166592000, -8034351316992000, 1129830653952000, -362125209600000, 289700167680000, -62768369664000, -62768369664000, 94152554496000, 0, 0])
]

def fourHighestCache_19_9 : List (Occupation 24 × List ℚ) := [
  ({1,4,7,8}, [614627875749888000, -4017175658496000, 1150753443840000, -441792755712000, 30286835712000, -51502252032000, 94152554496000, -94152554496000, 0, 0]),
  ({1,5,6,8}, [-204875958583296000, 12051526975488000, -1611054821376000, 417651075072000, -146166902784000, 49892806656000, -13450364928000, 0, 0, 0]),
  ({2,3,4,11}, [409751917166592000, 8034351316992000, -2468889206784000, -101395058688000, 289700167680000, -117489512448000, 8966909952000, 31384184832000, 0, 0]),
  ({2,3,5,10}, [-409751917166592000, -8034351316992000, 2468889206784000, 101395058688000, -289700167680000, 117489512448000, -8966909952000, -31384184832000, 0, 0])
]

def fourHighestCache_19_10 : List (Occupation 24 × List ℚ) := [
  ({2,3,6,9}, [614627875749888000, -4017175658496000, -2196892938240000, 253487646720000, 88226869248000, -38626689024000, -13450364928000, 31384184832000, 0, 0]),
  ({2,3,7,8}, [-614627875749888000, 4017175658496000, 2866422214656000, -639754536960000, 85593231360000, -25751126016000, 31384184832000, -31384184832000, 0, 0]),
  ({2,4,5,9}, [-204875958583296000, 12051526975488000, -271996268544000, -354882705408000, 201473298432000, -78862823424000, 22417274880000, 0, 0, 0]),
  ({2,4,6,8}, [0, 0, -669529276416000, 386266890240000, -173820100608000, 64377815040000, -17933819904000, 0, 0, 0])
]

def fourHighestCache_19_11 : List (Occupation 24 × List ℚ) := [
  ({2,5,6,7}, [204875958583296000, -12051526975488000, 1611054821376000, -417651075072000, 146166902784000, -49892806656000, 13450364928000, 0, 0, 0]),
  ({3,4,5,8}, [204875958583296000, -12051526975488000, 941525544960000, -31384184832000, -27653197824000, 14485008384000, -4483454976000, 0, 0, 0]),
  ({3,4,6,7}, [-204875958583296000, 12051526975488000, -941525544960000, 31384184832000, 27653197824000, -14485008384000, 4483454976000, 0, 0, 0])
]

def fourHighestCache_19 : List (Occupation 24 × List ℚ) := fourHighestCache_19_0 ++ fourHighestCache_19_1 ++ fourHighestCache_19_2 ++ fourHighestCache_19_3 ++ fourHighestCache_19_4 ++ fourHighestCache_19_5 ++ fourHighestCache_19_6 ++ fourHighestCache_19_7 ++ fourHighestCache_19_8 ++ fourHighestCache_19_9 ++ fourHighestCache_19_10 ++ fourHighestCache_19_11

theorem fourHighestNumber_19_1 : ∀ A∈highestFourOccupations 19,
    kernelHighestEntry 19 ⟨⟨1,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_19 1 A := by
  rw [fourOccupations_19]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_19_3 : ∀ A∈highestFourOccupations 19,
    kernelHighestEntry 19 ⟨⟨3,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_19 3 A := by
  rw [fourOccupations_19]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_19_5 : ∀ A∈highestFourOccupations 19,
    kernelHighestEntry 19 ⟨⟨5,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_19 5 A := by
  rw [fourOccupations_19]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_19_7 : ∀ A∈highestFourOccupations 19,
    kernelHighestEntry 19 ⟨⟨7,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_19 7 A := by
  rw [fourOccupations_19]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_19_9 : ∀ A∈highestFourOccupations 19,
    kernelHighestEntry 19 ⟨⟨9,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_19 9 A := by
  rw [fourOccupations_19]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_19_11 : ∀ A∈highestFourOccupations 19,
    kernelHighestEntry 19 ⟨⟨11,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_19 11 A := by
  rw [fourOccupations_19]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_19_13 : ∀ A∈highestFourOccupations 19,
    kernelHighestEntry 19 ⟨⟨13,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_19 13 A := by
  rw [fourOccupations_19]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_19_15 : ∀ A∈highestFourOccupations 19,
    kernelHighestEntry 19 ⟨⟨15,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_19 15 A := by
  rw [fourOccupations_19]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_19_17 : ∀ A∈highestFourOccupations 19,
    kernelHighestEntry 19 ⟨⟨17,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_19 17 A := by
  rw [fourOccupations_19]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_19_19 : ∀ A∈highestFourOccupations 19,
    kernelHighestEntry 19 ⟨⟨19,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_19 19 A := by
  rw [fourOccupations_19]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestChecked_19 : ∀ r : CopyLabel 19, ∀ A∈highestFourOccupations 19,
    kernelHighestEntry 19 r A = highestLookup fourHighestCache_19 r.val.val A := by
  intro r
  fin_cases r
  · exact fourHighestNumber_19_1
  · exact fourHighestNumber_19_3
  · exact fourHighestNumber_19_5
  · exact fourHighestNumber_19_7
  · exact fourHighestNumber_19_9
  · exact fourHighestNumber_19_11
  · exact fourHighestNumber_19_13
  · exact fourHighestNumber_19_15
  · exact fourHighestNumber_19_17
  · exact fourHighestNumber_19_19

theorem fourZChecked_19 (r s : CopyLabel 19) :
    integerFourGram 19 r s = fourZData_19 r s := by
  rw [integerFourGram_cached 19 fourHighestCache_19 fourHighestChecked_19]
  have h : ∀ r s : CopyLabel 19, cachedFourGram 19 fourHighestCache_19 r s = fourZData_19 r s := by
    simp only [cachedFourGram, fourOccupations_19]
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact h r s

theorem fourLDLChecked_19 :
    fourZData_19 * (Matrix.diagonal (fun r : CopyLabel 19 =>
      ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 19 r.val.val) -
      Matrix.diagonal (fun r : CopyLabel 19 => rationalCopyDiagonal 19 r.val.val) *
        fourYData_19 * Matrix.diagonal (fun r : CopyLabel 19 => rationalCopyDiagonal 19 r.val.val)) *
      fourZData_19 = fourLData_19 * Matrix.diagonal fourPivotData_19 * (fourLData_19)ᵀ := by
  have h : ∀ r s : CopyLabel 19,
      (fourZData_19 * (Matrix.diagonal (fun r : CopyLabel 19 =>
        ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 19 r.val.val) -
        Matrix.diagonal (fun r : CopyLabel 19 => rationalCopyDiagonal 19 r.val.val) *
          fourYData_19 * Matrix.diagonal (fun r : CopyLabel 19 => rationalCopyDiagonal 19 r.val.val)) *
        fourZData_19 : Matrix (CopyLabel 19) (CopyLabel 19) ℚ) r s =
      (fourLData_19 * Matrix.diagonal fourPivotData_19 * (fourLData_19)ᵀ : Matrix (CopyLabel 19) (CopyLabel 19) ℚ) r s := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact Matrix.ext h

theorem fourPivotChecked_19 : ∀ r, 0 ≤ fourPivotData_19 r := by
  intro r
  fin_cases r <;> norm_num [fourPivotData_19, copyDiagonalData]

theorem integer_certificate_19 :
    ((integerCompression 19).map (algebraMap ℚ ℂ)).PosSemidef := by
  apply rational_ldl_posSemidef _ (fourLData_19) (fourPivotData_19) _ fourPivotChecked_19
  unfold integerCompression integerFourMiddle
  rw [show integerRowsFourTrace 19 = fourYData_19 from Matrix.ext fourYChecked_19,
    show integerFourGram 19 = fourZData_19 from Matrix.ext fourZChecked_19]
  exact fourLDLChecked_19

end LaughlinFock
end

end OAI
