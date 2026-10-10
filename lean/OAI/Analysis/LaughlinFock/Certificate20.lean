import Mathlib
import OAI.Analysis.LaughlinFock.Certificate20Data
import OAI.Analysis.LaughlinFock.GramCache
import OAI.Analysis.LaughlinFock.TraceSymmetry

namespace OAI

/-! Certificate20. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourYLower_20 (r s : CopyLabel 20) (hrs : s.val.val ≤ r.val.val) :
    integerRowsFourTrace 20 r s = fourYData_20 r s := by
  rw [integerRowsFourTrace_collected (by decide) collectedFourData_20 collectedFourChecked_20]
  fin_cases r <;> fin_cases s
  · exact fourYNumber_20_1_1
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
  · exact fourYNumber_20_3_1
  · exact fourYNumber_20_3_3
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
  · exact fourYNumber_20_5_1
  · exact fourYNumber_20_5_3
  · exact fourYNumber_20_5_5
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
  · exact fourYNumber_20_7_1
  · exact fourYNumber_20_7_3
  · exact fourYNumber_20_7_5
  · exact fourYNumber_20_7_7
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
  · exact fourYNumber_20_9_1
  · exact fourYNumber_20_9_3
  · exact fourYNumber_20_9_5
  · exact fourYNumber_20_9_7
  · exact fourYNumber_20_9_9
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
  · exact fourYNumber_20_11_1
  · exact fourYNumber_20_11_3
  · exact fourYNumber_20_11_5
  · exact fourYNumber_20_11_7
  · exact fourYNumber_20_11_9
  · exact fourYNumber_20_11_11
  · have h : (13:ℕ) ≤ 11 := hrs
    omega
  · have h : (15:ℕ) ≤ 11 := hrs
    omega
  · have h : (17:ℕ) ≤ 11 := hrs
    omega
  · have h : (19:ℕ) ≤ 11 := hrs
    omega
  · exact fourYNumber_20_13_1
  · exact fourYNumber_20_13_3
  · exact fourYNumber_20_13_5
  · exact fourYNumber_20_13_7
  · exact fourYNumber_20_13_9
  · exact fourYNumber_20_13_11
  · exact fourYNumber_20_13_13
  · have h : (15:ℕ) ≤ 13 := hrs
    omega
  · have h : (17:ℕ) ≤ 13 := hrs
    omega
  · have h : (19:ℕ) ≤ 13 := hrs
    omega
  · exact fourYNumber_20_15_1
  · exact fourYNumber_20_15_3
  · exact fourYNumber_20_15_5
  · exact fourYNumber_20_15_7
  · exact fourYNumber_20_15_9
  · exact fourYNumber_20_15_11
  · exact fourYNumber_20_15_13
  · exact fourYNumber_20_15_15
  · have h : (17:ℕ) ≤ 15 := hrs
    omega
  · have h : (19:ℕ) ≤ 15 := hrs
    omega
  · exact fourYNumber_20_17_1
  · exact fourYNumber_20_17_3
  · exact fourYNumber_20_17_5
  · exact fourYNumber_20_17_7
  · exact fourYNumber_20_17_9
  · exact fourYNumber_20_17_11
  · exact fourYNumber_20_17_13
  · exact fourYNumber_20_17_15
  · exact fourYNumber_20_17_17
  · have h : (19:ℕ) ≤ 17 := hrs
    omega
  · exact fourYNumber_20_19_1
  · exact fourYNumber_20_19_3
  · exact fourYNumber_20_19_5
  · exact fourYNumber_20_19_7
  · exact fourYNumber_20_19_9
  · exact fourYNumber_20_19_11
  · exact fourYNumber_20_19_13
  · exact fourYNumber_20_19_15
  · exact fourYNumber_20_19_17
  · exact fourYNumber_20_19_19

theorem fourYChecked_20 (r s : CopyLabel 20) :
    integerRowsFourTrace 20 r s = fourYData_20 r s := by
  have hh : ∀ r s : CopyLabel 20, fourYData_20 r s = fourYData_20 s r := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  by_cases h : s.val.val ≤ r.val.val
  · exact fourYLower_20 r s h
  · rw [integerRowsFourTrace_symm, fourYLower_20 s r (by omega), hh]

def fourHighestCache_20_0 : List (Occupation 24 × List ℚ) := [
  ({0,1,2,18}, [0, -5736526840332288000, -3585329275207680000, -1933516859129856000, -742675349864448000, -12804747411456000, 256094948229120000, 64023737057280000, -589018380926976000, -1703031405723648000]),
  ({0,1,3,17}, [0, 5736526840332288000, 3585329275207680000, 1933516859129856000, 742675349864448000, 12804747411456000, -256094948229120000, -64023737057280000, 589018380926976000, 1703031405723648000]),
  ({0,1,4,16}, [0, -7648702453776384000, -3655629849231360000, -1473299172753408000, -427829207629824000, 7532204359680000, 140099001090048000, 60257634877440000, -358532927520768000, -1459741204905984000]),
  ({0,1,5,15}, [0, 7170658550415360000, 3216251261583360000, 1033481206517760000, 175123751362560000, -28245766348800000, -42996333219840000, -49273170186240000, 149388719800320000, 1216451004088320000])
]

def fourHighestCache_20_1 : List (Occupation 24 × List ℚ) := [
  ({0,1,6,14}, [0, -6692614647054336000, -2495670377840640000, -630822115123200000, -54985091825664000, 32011868528640000, 1255367393280000, 26048873410560000, -17072996548608000, -973160803270656000]),
  ({0,1,7,13}, [0, 5531650881748992000, 1830325659402240000, 319930380177408000, 9415255449600000, -19583731335168000, 2824576634880000, -1255367393280000, -46950740508672000, 729870602452992000]),
  ({0,1,8,12}, [0, -3824351226888192000, -1185066819256320000, -142107588919296000, 8575124963328000, 4229622448128000, 3766102179840000, -12553673932800000, 59755487920128000, -486580401635328000]),
  ({0,1,9,11}, [0, 2048759585832960000, 557383122616320000, 56114922479616000, -10487146070016000, 2462451425280000, -5272543051776000, 11298306539520000, -38414242234368000, 243290200817664000])
]

def fourHighestCache_20_2 : List (Occupation 24 × List ℚ) := [
  ({0,2,3,16}, [0, 1912175613444096000, 70300574023680000, -460217686376448000, -314846142234624000, -20336951771136000, 115995947139072000, 3766102179840000, -230485453406208000, -243290200817664000]),
  ({0,2,4,15}, [0, 478043903361024000, 439378587648000000, 439817966235648000, 252705456267264000, 20713561989120000, -97102667870208000, -10984464691200000, 209144207720448000, 243290200817664000]),
  ({0,2,5,14}, [0, -478043903361024000, -720580883742720000, -402659091394560000, -120138659536896000, -3766102179840000, 41740965826560000, 23224296775680000, -132315723251712000, -243290200817664000]),
  ({0,2,6,13}, [0, 1160963765305344000, 665344718438400000, 310891734945792000, 45569836376064000, -12428137193472000, -4079944028160000, -24793506017280000, 64023737057280000, 243290200817664000])
]

def fourHighestCache_20_3 : List (Occupation 24 × List ℚ) := [
  ({0,2,7,12}, [0, -1707299654860800000, -645258840145920000, -177822791258112000, -17990380412928000, 15354108887040000, -6590678814720000, 13809041326080000, -12804747411456000, -243290200817664000]),
  ({0,2,8,11}, [0, 1775591641055232000, 627683696640000000, 85992666439680000, 1912021106688000, -6692073873408000, 1506440871936000, 1255367393280000, -21341245685760000, 243290200817664000]),
  ({0,2,9,10}, [0, -2048759585832960000, -557383122616320000, -56114922479616000, 10487146070016000, -2462451425280000, 5272543051776000, -11298306539520000, 38414242234368000, -243290200817664000]),
  ({0,3,4,14}, [0, -2390219516805120000, -228476865576960000, -16759154700288000, -70426110763008000, -17324070027264000, 36468422774784000, -5021469573120000, -55487238782976000, 0])
]

def fourHighestCache_20_4 : List (Occupation 24 × List ℚ) := [
  ({0,3,5,13}, [0, 2048759585832960000, 396696096276480000, 44063395504128000, 41427123978240000, 16947459809280000, -27618082652160000, -313841848320000, 51218989645824000, 0]),
  ({0,3,6,12}, [0, -1843883627249664000, -248562743869440000, -69484585218048000, -16425999507456000, -4953872867328000, 8473729904640000, 8473729904640000, -38414242234368000, 0]),
  ({0,3,7,11}, [0, 1639007668666368000, 140601148047360000, 43686785286144000, 12746807377920000, -5620183252992000, 3515028701184000, -11298306539520000, 25609494822912000, 0]),
  ({0,3,8,10}, [0, -682919861944320000, -105450861035520000, -8662035013632000, -10718906204160000, 6807953940480000, -5021469573120000, 7532204359680000, -12804747411456000, 0])
]

def fourHighestCache_20_5 : List (Occupation 24 × List ℚ) := [
  ({0,4,5,12}, [0, -546335889555456000, -261116417802240000, 9540792188928000, -3012881743872000, -10718906204160000, 11298306539520000, -3766102179840000, -8536498274304000, 0]),
  ({0,4,6,11}, [0, 887795820527616000, 213412456857600000, 10356780994560000, -4142712397824000, 9560105533440000, -8222656425984000, 1569209241600000, 8536498274304000, 0]),
  ({0,4,7,10}, [0, -1707299654860800000, -123026004541440000, -8097119686656000, -376610217984000, -1883051089920000, 1318135762944000, 2510734786560000, -8536498274304000, 0]),
  ({0,4,8,9}, [0, 1639007668666368000, 140601148047360000, -12553673932800000, 9038645231616000, -4461382582272000, 3263955222528000, -5021469573120000, 8536498274304000, 0])
]

def fourHighestCache_20_6 : List (Occupation 24 × List ℚ) := [
  ({0,5,6,10}, [0, 341459930972160000, -47703960944640000, -12239832084480000, 7677054443520000, -5794003353600000, 4079944028160000, -2196892938240000, 0, 0]),
  ({0,5,7,9}, [0, 204875958583296000, -12553673932800000, 18767742529536000, -8372334845952000, 4924902850560000, -3075650113536000, 1569209241600000, 0, 0]),
  ({0,6,7,8}, [0, -682919861944320000, 55236165304320000, -20713561989120000, 7821904527360000, -3737132163072000, 2008587829248000, -941525544960000, 0, 0]),
  ({1,2,3,15}, [0, -2390219516805120000, -509679161671680000, 20399720140800000, 62140685967360000, -376610217984000, -18893279268864000, 7218362511360000, 21341245685760000, 0])
]

def fourHighestCache_20_7 : List (Occupation 24 × List ℚ) := [
  ({1,2,4,14}, [0, 2390219516805120000, 509679161671680000, -20399720140800000, -62140685967360000, 376610217984000, 18893279268864000, -7218362511360000, -21341245685760000, 0]),
  ({1,2,5,13}, [0, -2731679447777280000, -341459930972160000, 47703960944640000, 33141699182592000, -753220435968000, -10042939146240000, 1883051089920000, 17072996548608000, 0]),
  ({1,2,6,12}, [0, 2390219516805120000, 228476865576960000, -63584358469632000, -11153456455680000, 2027901173760000, 2196892938240000, 2510734786560000, -12804747411456000, 0]),
  ({1,2,7,11}, [0, -1707299654860800000, -123026004541440000, 48143339532288000, 3331551928320000, -3041851760640000, 1569209241600000, -3766102179840000, 8536498274304000, 0])
]

def fourHighestCache_20_8 : List (Occupation 24 × List ℚ) := [
  ({1,2,8,10}, [0, 956087806722048000, 35150287011840000, -21215708946432000, -1680260972544000, 2346571358208000, -1757514350592000, 2510734786560000, -4268249137152000, 0]),
  ({1,3,4,13}, [0, 341459930972160000, -168219230699520000, -27304240803840000, 28998986784768000, 376610217984000, -8850340122624000, 5335311421440000, 4268249137152000, 0]),
  ({1,3,5,12}, [0, 341459930972160000, 112983065395200000, 15880397524992000, -21988242726912000, -1274680737792000, 7846046208000000, -4393785876480000, -4268249137152000, 0]),
  ({1,3,6,11}, [0, -682919861944320000, -105450861035520000, 15441018937344000, 7821904527360000, 1013950586880000, -3766102179840000, 1255367393280000, 4268249137152000, 0])
]

def fourHighestCache_20_9 : List (Occupation 24 × List ℚ) := [
  ({1,3,7,10}, [0, 751211848138752000, 87875717529600000, -26927630585856000, -1651290955776000, 695280402432000, 188305108992000, 1255367393280000, -4268249137152000, 0]),
  ({1,3,8,9}, [0, -956087806722048000, -35150287011840000, 21215708946432000, 1680260972544000, -2346571358208000, 1757514350592000, -2510734786560000, 4268249137152000, 0]),
  ({1,4,5,11}, [0, -341459930972160000, 47703960944640000, -19897573183488000, 7155594141696000, 1158800670720000, -3075650113536000, 2196892938240000, 0, 0]),
  ({1,4,6,10}, [0, 478043903361024000, -42682491371520000, 9980170776576000, -3157731827712000, -1883051089920000, 2824576634880000, -1883051089920000, 0, 0])
]

def fourHighestCache_20_10 : List (Occupation 24 × List ℚ) := [
  ({1,4,7,9}, [0, -136583972388864000, -5021469573120000, 1883051089920000, -289700167680000, 1419530821632000, -1506440871936000, 941525544960000, 0, 0]),
  ({1,5,6,9}, [0, -546335889555456000, 60257634877440000, -6527910445056000, 695280402432000, 869100503040000, -1004293914624000, 627683696640000, 0, 0]),
  ({1,5,7,8}, [0, 478043903361024000, -42682491371520000, 1945819459584000, 550430318592000, -1187770687488000, 1067062284288000, -627683696640000, 0, 0]),
  ({2,3,4,12}, [0, -682919861944320000, 55236165304320000, 11423843278848000, -7010744057856000, 898070519808000, 1004293914624000, -941525544960000, 0, 0])
]

def fourHighestCache_20_11 : List (Occupation 24 × List ℚ) := [
  ({2,3,5,11}, [0, 682919861944320000, -55236165304320000, -11423843278848000, 7010744057856000, -898070519808000, -1004293914624000, 941525544960000, 0, 0]),
  ({2,3,6,10}, [0, -546335889555456000, 60257634877440000, 1506440871936000, -3012881743872000, 173820100608000, 753220435968000, -627683696640000, 0, 0]),
  ({2,3,7,9}, [0, 341459930972160000, -47703960944640000, 3828870549504000, 260730150912000, 231760134144000, -439378587648000, 313841848320000, 0, 0]),
  ({2,4,5,10}, [0, -136583972388864000, -5021469573120000, 9917402406912000, -3997862313984000, 724250419200000, 251073478656000, -313841848320000, 0, 0])
]

def fourHighestCache_20_12 : List (Occupation 24 × List ℚ) := [
  ({2,4,6,9}, [0, 204875958583296000, -12553673932800000, -5335311421440000, 2752151592960000, -405580234752000, -313841848320000, 313841848320000, 0, 0]),
  ({2,4,7,8}, [0, -341459930972160000, 47703960944640000, -3828870549504000, -260730150912000, -231760134144000, 439378587648000, -313841848320000, 0, 0]),
  ({2,5,6,8}, [0, 68291986194432000, -17575143505920000, 4582090985472000, -1245710721024000, 318670184448000, -62768369664000, 0, 0, 0]),
  ({3,4,5,9}, [0, -68291986194432000, 17575143505920000, -4582090985472000, 1245710721024000, -318670184448000, 62768369664000, 0, 0, 0])
]

def fourHighestCache_20_13 : List (Occupation 24 × List ℚ) := [
  ({3,4,6,8}, [0, 68291986194432000, -17575143505920000, 4582090985472000, -1245710721024000, 318670184448000, -62768369664000, 0, 0, 0]),
  ({3,5,6,7}, [0, -68291986194432000, 17575143505920000, -4582090985472000, 1245710721024000, -318670184448000, 62768369664000, 0, 0, 0])
]

def fourHighestCache_20 : List (Occupation 24 × List ℚ) := fourHighestCache_20_0 ++ fourHighestCache_20_1 ++ fourHighestCache_20_2 ++ fourHighestCache_20_3 ++ fourHighestCache_20_4 ++ fourHighestCache_20_5 ++ fourHighestCache_20_6 ++ fourHighestCache_20_7 ++ fourHighestCache_20_8 ++ fourHighestCache_20_9 ++ fourHighestCache_20_10 ++ fourHighestCache_20_11 ++ fourHighestCache_20_12 ++ fourHighestCache_20_13

theorem fourHighestNumber_20_1 : ∀ A∈highestFourOccupations 20,
    kernelHighestEntry 20 ⟨⟨1,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_20 1 A := by
  rw [fourOccupations_20]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_20_3 : ∀ A∈highestFourOccupations 20,
    kernelHighestEntry 20 ⟨⟨3,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_20 3 A := by
  rw [fourOccupations_20]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_20_5 : ∀ A∈highestFourOccupations 20,
    kernelHighestEntry 20 ⟨⟨5,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_20 5 A := by
  rw [fourOccupations_20]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_20_7 : ∀ A∈highestFourOccupations 20,
    kernelHighestEntry 20 ⟨⟨7,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_20 7 A := by
  rw [fourOccupations_20]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_20_9 : ∀ A∈highestFourOccupations 20,
    kernelHighestEntry 20 ⟨⟨9,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_20 9 A := by
  rw [fourOccupations_20]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_20_11 : ∀ A∈highestFourOccupations 20,
    kernelHighestEntry 20 ⟨⟨11,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_20 11 A := by
  rw [fourOccupations_20]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_20_13 : ∀ A∈highestFourOccupations 20,
    kernelHighestEntry 20 ⟨⟨13,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_20 13 A := by
  rw [fourOccupations_20]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_20_15 : ∀ A∈highestFourOccupations 20,
    kernelHighestEntry 20 ⟨⟨15,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_20 15 A := by
  rw [fourOccupations_20]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_20_17 : ∀ A∈highestFourOccupations 20,
    kernelHighestEntry 20 ⟨⟨17,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_20 17 A := by
  rw [fourOccupations_20]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestNumber_20_19 : ∀ A∈highestFourOccupations 20,
    kernelHighestEntry 20 ⟨⟨19,by decide⟩,by decide⟩ A = highestLookup fourHighestCache_20 19 A := by
  rw [fourOccupations_20]
  apply @of_decide_eq_true _ (boundedEntriesDecidable _ _ _)
  decide +kernel

theorem fourHighestChecked_20 : ∀ r : CopyLabel 20, ∀ A∈highestFourOccupations 20,
    kernelHighestEntry 20 r A = highestLookup fourHighestCache_20 r.val.val A := by
  intro r
  fin_cases r
  · exact fourHighestNumber_20_1
  · exact fourHighestNumber_20_3
  · exact fourHighestNumber_20_5
  · exact fourHighestNumber_20_7
  · exact fourHighestNumber_20_9
  · exact fourHighestNumber_20_11
  · exact fourHighestNumber_20_13
  · exact fourHighestNumber_20_15
  · exact fourHighestNumber_20_17
  · exact fourHighestNumber_20_19

theorem fourZChecked_20 (r s : CopyLabel 20) :
    integerFourGram 20 r s = fourZData_20 r s := by
  rw [integerFourGram_cached 20 fourHighestCache_20 fourHighestChecked_20]
  have h : ∀ r s : CopyLabel 20, cachedFourGram 20 fourHighestCache_20 r s = fourZData_20 r s := by
    simp only [cachedFourGram, fourOccupations_20]
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact h r s

theorem fourLDLChecked_20 :
    fourZData_20 * (Matrix.diagonal (fun r : CopyLabel 20 =>
      ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 20 r.val.val) -
      Matrix.diagonal (fun r : CopyLabel 20 => rationalCopyDiagonal 20 r.val.val) *
        fourYData_20 * Matrix.diagonal (fun r : CopyLabel 20 => rationalCopyDiagonal 20 r.val.val)) *
      fourZData_20 = fourLData_20 * Matrix.diagonal fourPivotData_20 * (fourLData_20)ᵀ := by
  have h : ∀ r s : CopyLabel 20,
      (fourZData_20 * (Matrix.diagonal (fun r : CopyLabel 20 =>
        ((if r.val.val=1 then 2 else 0)+3/10^6) * rationalCopyDiagonal 20 r.val.val) -
        Matrix.diagonal (fun r : CopyLabel 20 => rationalCopyDiagonal 20 r.val.val) *
          fourYData_20 * Matrix.diagonal (fun r : CopyLabel 20 => rationalCopyDiagonal 20 r.val.val)) *
        fourZData_20 : Matrix (CopyLabel 20) (CopyLabel 20) ℚ) r s =
      (fourLData_20 * Matrix.diagonal fourPivotData_20 * (fourLData_20)ᵀ : Matrix (CopyLabel 20) (CopyLabel 20) ℚ) r s := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact Matrix.ext h

theorem fourPivotChecked_20 : ∀ r, 0 ≤ fourPivotData_20 r := by
  intro r
  fin_cases r <;> norm_num [fourPivotData_20, copyDiagonalData]

theorem integer_certificate_20 :
    ((integerCompression 20).map (algebraMap ℚ ℂ)).PosSemidef := by
  apply rational_ldl_posSemidef _ (fourLData_20) (fourPivotData_20) _ fourPivotChecked_20
  unfold integerCompression integerFourMiddle
  rw [show integerRowsFourTrace 20 = fourYData_20 from Matrix.ext fourYChecked_20,
    show integerFourGram 20 = fourZData_20 from Matrix.ext fourZChecked_20]
  exact fourLDLChecked_20

end LaughlinFock
end

end OAI
