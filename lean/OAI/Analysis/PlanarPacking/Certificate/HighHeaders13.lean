import OAI.Analysis.PlanarPacking.Certificate.KernelValues20
import OAI.Analysis.PlanarPacking.Certificate.Powers20
import OAI.Analysis.PlanarPacking.HighRuleBridge
import OAI.Analysis.PlanarPacking.Certificate.MomentPowers30

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
noncomputable def hk13_0_0 (j : Fin 6) (i k : Fin 16) : CBox := (power13 j i k).conj.mul (mpower0_0 j i k)
lemma hk13_0_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_0_0 j i k).Contains (fullFactor false 13 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_0_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power13 j i k) (mpower0_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 0 (power13_contains j i k) (mpower0_0_contains j i k)
noncomputable def ha13_0_0 : Fin 7 → CBox := ![⟨⟨999999999999999999999999999845,1000000000000000000000000000207⟩,⟨(-207),207⟩⟩,⟨⟨866025403784438646742693794068,866025403784438646779646544579⟩,⟨499999999999999999985439611613,500000000000000000023404244797⟩⟩,⟨⟨499999999999999999940165171904,500000000000000000042147115238⟩,⟨866025403784438646717467884184,866025403784438646820190463112⟩⟩,⟨⟨(-57784783185),27148765851⟩,⟨999999999999999999957533225495,1000000000000000000042466774518⟩⟩,⟨⟨(-500000000000000000157773117513),(-499999999999999999877602308226)⟩,⟨866025403784438646613696481328,866025403784438646893325848570⟩⟩,⟨⟨(-866025403784438646952765054648),(-866025403784438646600211301278)⟩,⟨499999999999999999801882176790,500000000000000000153898541039⟩⟩,⟨⟨(-1000000000000000000085191571217),(-999999999999999999914808428835)⟩,⟨(-115827588577),54555553805⟩⟩]
lemma ha13_0_0_eq (j : Fin 7) : ha13_0_0 j = ((atomPoints j).direct.powBin 7 13).conj := by fin_cases j <;> decide +kernel
lemma ha13_0_0_contains (j : Fin 7) : (ha13_0_0 j).Contains (fullFactor false 13 0 ((j.val:ℝ)/6)) := by
  rw [ha13_0_0_eq]
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @direct_factor_zero_full ((atomPoints j).direct.powBin 7 13) ((j.val:ℝ)/6) 13 (@direct_power_bin_contains (atomPoints j) ((j.val:ℝ)/6) (atomPoints_contains j) 13 (by norm_num))
noncomputable def hk13_0_1 (j : Fin 6) (i k : Fin 16) : CBox := (power13 j i k).conj.mul (mpower0_1 j i k)
lemma hk13_0_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_0_1 j i k).Contains (fullFactor false 13 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_0_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power13 j i k) (mpower0_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 1 (power13_contains j i k) (mpower0_1_contains j i k)
noncomputable def ha13_0_1 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-261799387799149436551421100588),(-261799387799149436530709531800)⟩,⟨453449841058554462637127069012,453449841058554462657918859612⟩⟩,⟨⟨(-906899682117108925358295211427),(-906899682117108925247837626971)⟩,⟨523598775598298873014007781207,523598775598298873122469689202⟩⟩,⟨⟨(-1570796326794896619301706653424),(-1570796326794896619163293346596)⟩,⟨(-90768125172),42645181676⟩⟩,⟨⟨(-1813799364234217850869764815965),(-1813799364234217850278336936032)⟩,⟨(-1047197551196597746487105911277),(-1047197551196597745896984207136)⟩⟩,⟨⟨(-1308996938995747183098738771607),(-1308996938995747182172995418381)⟩,⟨(-2267249205292772313742817497581),(-2267249205292772312812617051227)⟩⟩,⟨⟨(-171391327047),363883101357⟩,⟨(-3141592653589793238737637214284),(-3141592653589793238192362785880)⟩⟩]
lemma ha13_0_1_eq (j : Fin 7) : ha13_0_1 j = ((ha13_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha13_0_1_contains (j : Fin 7) : (ha13_0_1 j).Contains (fullFactor false 13 1 ((j.val:ℝ)/6)) := by
  rw [ha13_0_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_0_0 j) false 13 0 j (ha13_0_0_contains j)
noncomputable def hk13_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power13 j i k).conj.mul (mpower0_2 j i k)
lemma hk13_0_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_0_2 j i k).Contains (fullFactor false 13 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_0_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power13 j i k) (mpower0_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 2 (power13_contains j i k) (mpower0_2_contains j i k)
noncomputable def ha13_0_2 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-118712890786751174410676029255),(-118712890786751174404854876336)⟩,⟨(-68538919452009434856546494868),(-68538919452009434850906052681)⟩⟩,⟨⟨(-274155677808037739436462908170),(-274155677808037739378799721317)⟩,⟨(-474851563147004697664934807952),(-474851563147004697605587852503)⟩⟩,⟨⟨(-33493447367),71289118806⟩,⟨(-1233700550136169827412480531332),(-1233700550136169827299843983541)⟩⟩,⟨⟨1096622711232150957377983170892,1096622711232150957999447832884⟩,⟨(-1899406252588018790820143081177),(-1899406252588018790194755255716)⟩⟩,⟨⟨2967822269668779359633092103599,2967822269668779360860168512223⟩,⟨(-1713472986300235871860859274637),(-1713472986300235870643609905053)⟩⟩,⟨⟨4934802200544679308988537513593,4934802200544679309860760546094⟩,⟨(-269220866970),571586238995⟩⟩]
lemma ha13_0_2_eq (j : Fin 7) : ha13_0_2 j = ((ha13_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha13_0_2_contains (j : Fin 7) : (ha13_0_2 j).Contains (fullFactor false 13 2 ((j.val:ℝ)/6)) := by
  rw [ha13_0_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_0_1 j) false 13 1 j (ha13_0_1_contains j)
noncomputable def hk13_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power13 j i k).conj.mul (mpower0_3 j i k)
lemma hk13_0_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_0_3 j i k).Contains (fullFactor false 13 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_0_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power13 j i k) (mpower0_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 3 (power13_contains j i k) (mpower0_3_contains j i k)
noncomputable def ha13_0_3 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨11962298101967523215468796590,11962298101967523216491316643⟩,⟨(-20719308087892496642941934423),(-20719308087892496641859999968)⟩⟩,⟨⟨165754464703139973130051842090,165754464703139973151295450412⟩,⟨(-95698384815740185735517857995),(-95698384815740185715084991219)⟩⟩,⟨⟨645964097506246253626693980527,645964097506246253687726506622⟩,⟨(-17537128032),37326895321⟩⟩,⟨⟨1326035717625119784881522646432,1326035717625119785322346615467⟩,⟨765587078525921485624885289700,765587078525921486061186410523⟩⟩,⟨⟨1495287262745940401384657385310,1495287262745940402451667498351⟩,⟨2589913510986562079806395482890,2589913510986562080885465608846⟩⟩,⟨⟨(-598563709774),281927432623⟩,⟨5167712780049970028792762366496,5167712780049970029722601530898⟩⟩]
lemma ha13_0_3_eq (j : Fin 7) : ha13_0_3 j = ((ha13_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha13_0_3_contains (j : Fin 7) : (ha13_0_3 j).Contains (fullFactor false 13 3 ((j.val:ℝ)/6)) := by
  rw [ha13_0_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_0_2 j) false 13 2 j (ha13_0_2_contains j)
noncomputable def hk13_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power13 j i k).conj.mul (mpower0_4 j i k)
lemma hk13_0_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_0_4 j i k).Contains (fullFactor false 13 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_0_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power13 j i k) (mpower0_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 4 (power13_contains j i k) (mpower0_4_contains j i k)
noncomputable def ha13_0_4 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2712151086516110563320963919,2712151086516110563471221854⟩,⟨1565861159883012429804460172,1565861159883012429943292026⟩⟩,⟨⟨25053778558128198874602771183,25053778558128198880031831851⟩,⟨43394417384257769011871413991,43394417384257769017571106366⟩⟩,⟨⟨(-14658237516),6886814074⟩,⟨253669507901048013624937075238,253669507901048013649711947312⟩⟩,⟨⟨(-400860456930051182173209093812),(-400860456930051181943486382691)⟩,⟨694310678148124304106746919941,694310678148124304339771869914⟩⟩,⟨⟨(-1695094429072569102508363096996),(-1695094429072569101796717697926)⟩,⟨978663224926882768268505785450,978663224926882768969977453173⟩⟩,⟨⟨(-4058712126416768218568798807444),(-4058712126416768217825585553516)⟩,⟨(-470110838333),221425287794⟩⟩]
lemma ha13_0_4_eq (j : Fin 7) : ha13_0_4 j = ((ha13_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha13_0_4_contains (j : Fin 7) : (ha13_0_4 j).Contains (fullFactor false 13 4 ((j.val:ℝ)/6)) := by
  rw [ha13_0_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_0_3 j) false 13 3 j (ha13_0_3_contains j)
noncomputable def hk13_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power13 j i k).conj.mul (mpower0_5 j i k)
lemma hk13_0_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_0_5 j i k).Contains (fullFactor false 13 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_0_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power13 j i k) (mpower0_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 5 (power13_contains j i k) (mpower0_5_contains j i k)
noncomputable def ha13_0_5 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-163976597214335483796643860),(-163976597214335483781583467)⟩,⟨284015797627486289479132533,284015797627486289495771559⟩⟩,⟨⟨(-9088505524079561264290178111),(-9088505524079561263067507718)⟩,⟨5247251110858735480535538267,5247251110858735481689300594⟩⟩,⟨⟨(-79692626246167045124822912952),(-79692626246167045116785987833)⟩,⟨(-4605021130),2163556451⟩⟩,⟨⟨(-290832176770545960481846322405),(-290832176770545960383311312041)⟩,⟨(-167912035547479535452887613807),(-167912035547479535356127108981)⟩⟩,⟨⟨(-512426866294798386998249626957),(-512426866294798386629328815244)⟩,⟨(-887549367585894654851707271033),(-887549367585894654476265454036)⟩⟩,⟨⟨(-139125611491),295379351216⟩,⟨(-2550164039877345444103288454609),(-2550164039877345443628196370637)⟩⟩]
lemma ha13_0_5_eq (j : Fin 7) : ha13_0_5 j = ((ha13_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha13_0_5_contains (j : Fin 7) : (ha13_0_5 j).Contains (fullFactor false 13 5 ((j.val:ℝ)/6)) := by
  rw [ha13_0_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_0_4 j) false 13 4 j (ha13_0_4_contains j)
noncomputable def hk13_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power13 j i k).conj.mul (mpower0_6 j i k)
lemma hk13_0_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_0_6 j i k).Contains (fullFactor false 13 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_0_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power13 j i k) (mpower0_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 6 (power13_contains j i k) (mpower0_6_contains j i k)
noncomputable def ha13_0_6 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-24785053981387676527708397),(-24785053981387676526177474)⟩,⟨(-14309657588033580846585295),(-14309657588033580845225478)⟩⟩,⟨⟨(-915818085634149174215788965),(-915818085634149174011504310)⟩,⟨(-1586243454808811297847599101),(-1586243454808811297629153690)⟩⟩,⟨⟨(-566417755),1205591713⟩,⟨(-20863480763352960874230776019),(-20863480763352960872060303420)⟩⟩,⟨⟨58612357480585547129402362039,58612357480585547163364718871⟩,⟨(-101519581107763923070819617166),(-101519581107763923036101263115)⟩⟩,⟨⟨387266468459182445657808176910,387266468459182445822858280773⟩,⟨(-223588399813024700786249247541),(-223588399813024700624565472471)⟩⟩,⟨⟨1335262768854589495754810588670,1335262768854589496007818495534⟩,⟨(-72845999832),154660266634⟩⟩]
lemma ha13_0_6_eq (j : Fin 7) : ha13_0_6 j = ((ha13_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha13_0_6_contains (j : Fin 7) : (ha13_0_6 j).Contains (fullFactor false 13 6 ((j.val:ℝ)/6)) := by
  rw [ha13_0_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_0_5 j) false 13 5 j (ha13_0_5_contains j)
noncomputable def hk13_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power13 j i k).conj.mul (mpower0_7 j i k)
lemma hk13_0_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_0_7 j i k).Contains (fullFactor false 13 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_0_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power13 j i k) (mpower0_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 7 (power13_contains j i k) (mpower0_7_contains j i k)
noncomputable def ha13_0_7 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1070359884617898514065284,1070359884617898514170406⟩,⟨(-1853917702541761442322040),(-1853917702541761442201625)⟩⟩,⟨⟨237301465925345464594895858,237301465925345464628330570⟩,⟨(-137006065231091009818947633),(-137006065231091009787950615)⟩⟩,⟨⟨4681754135318688100459069848,4681754135318688100961025247⟩,⟨(-127103847),270534148⟩⟩,⟨⟨30374587638444219464507038131,30374587638444219474991430689⟩,⟨17536776349579649250663376883,17536776349579649260880711579⟩⟩,⟨⟨83621865985773321380651487654,83621865985773321441387254794⟩,⟨144837320511075112648172688287,144837320511075112710362314294⟩⟩,⟨⟨(-69411365352),32693208274⟩,⟨599264529320792076833157485472,599264529320792076948614686786⟩⟩]
lemma ha13_0_7_eq (j : Fin 7) : ha13_0_7 j = ((ha13_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha13_0_7_contains (j : Fin 7) : (ha13_0_7 j).Contains (fullFactor false 13 7 ((j.val:ℝ)/6)) := by
  rw [ha13_0_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_0_6 j) false 13 6 j (ha13_0_6_contains j)
noncomputable def hk13_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power13 j i k).conj.mul (mpower0_8 j i k)
lemma hk13_0_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_0_8 j i k).Contains (fullFactor false 13 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_0_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power13 j i k) (mpower0_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 8 (power13_contains j i k) (mpower0_8_contains j i k)
noncomputable def ha13_0_8 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨121338629888859693710827,121338629888859693719096⟩,⟨70054890629433514724032,70054890629433514731137⟩⟩,⟨⟨17934052001134979767728496,17934052001134979771843083⟩,⟨31062689251548081589067137,31062689251548081593542607⟩⟩,⟨⟨(-53119256),24956782⟩,⟨919260274839426580196490367,919260274839426580297975176⟩⟩,⟨⟨(-4591117312290554822653534164),(-4591117312290554819964028215)⟩,⟨7952048448396308885848333754,7952048448396308888618453464⟩⟩,⟨⟨(-47397902300335817868496407269),(-47397902300335817847994027539)⟩,⟨27365191652122466679029155986,27365191652122466698991995416⟩⟩,⟨⟨(-235330630358893204566336098388),(-235330630358893204520247080794)⟩,⟨(-27257779434),12838592867⟩⟩]
lemma ha13_0_8_eq (j : Fin 7) : ha13_0_8 j = ((ha13_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha13_0_8_contains (j : Fin 7) : (ha13_0_8 j).Contains (fullFactor false 13 8 ((j.val:ℝ)/6)) := by
  rw [ha13_0_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_0_7 j) false 13 7 j (ha13_0_7_contains j)
noncomputable def hk13_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power13 j i k).conj.mul (mpower0_9 j i k)
lemma hk13_0_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_0_9 j i k).Contains (fullFactor false 13 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_0_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power13 j i k) (mpower0_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 9 (power13_contains j i k) (mpower0_9_contains j i k)
noncomputable def ha13_0_9 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-4075628328693792152710),(-4075628328693792152282)⟩,⟨7059195338064676366337,7059195338064676366841⟩⟩,⟨⟨(-3614308013089114299991696),(-3614308013089114299459446)⟩,⟨2086721704291221581779960,2086721704291221582265357⟩⟩,⟨⟨(-160441184787359821882855613),(-160441184787359821864632471)⟩,⟨(-9271060),4355781⟩⟩,⟨⟨(-1850525702701626521752024180),(-1850525702701626521101497644)⟩,⟨(-1068401512597105450366932560),(-1068401512597105449737655277)⟩⟩,⟨⟨(-7960211579480062800337771722),(-7960211579480062794505478979)⟩,⟨(-13787490894657571031742051651),(-13787490894657571025734264190)⟩⟩,⟨⟨(-4481514338),9514759959⟩,⟨(-82145886611128228807531739924),(-82145886611128228791182159324)⟩⟩]
lemma ha13_0_9_eq (j : Fin 7) : ha13_0_9 j = ((ha13_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha13_0_9_contains (j : Fin 7) : (ha13_0_9 j).Contains (fullFactor false 13 9 ((j.val:ℝ)/6)) := by
  rw [ha13_0_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_0_8 j) false 13 8 j (ha13_0_8_contains j)
noncomputable def hk13_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power13 j i k).conj.mul (mpower0_10 j i k)
lemma hk13_0_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_0_10 j i k).Contains (fullFactor false 13 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_0_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power13 j i k) (mpower0_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 10 (power13_contains j i k) (mpower0_10_contains j i k)
noncomputable def ha13_0_10 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-369618603571988403206),(-369618603571988403177)⟩,⟨(-213399400269781075741),(-213399400269781075717)⟩⟩,⟨⟨(-218520985876255821566648),(-218520985876255821515121)⟩,⟨(-378489450057716124899969),(-378489450057716124843026)⟩⟩,⟨⟨(-684205),1456295⟩,⟨(-25202042373060605482713424),(-25202042373060605479770718)⟩⟩,⟨⟨223765489537285961203485860,223765489537285961335993654⟩,⟨(-387573196859101311930297906),(-387573196859101311792818262)⟩⟩,⟨⟨3609556675507699249189190819,3609556675507699250773515475⟩,⟨(-2083978518259580818323974134),(-2083978518259580816790449953)⟩⟩,⟨⟨25806891390014060010182621565,25806891390014060015401139682⟩,⟨(-1407909253),2989149999⟩⟩]
lemma ha13_0_10_eq (j : Fin 7) : ha13_0_10 j = ((ha13_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha13_0_10_contains (j : Fin 7) : (ha13_0_10 j).Contains (fullFactor false 13 10 ((j.val:ℝ)/6)) := by
  rw [ha13_0_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_0_9 j) false 13 9 j (ha13_0_9_contains j)
noncomputable def hk13_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power13 j i k).conj.mul (mpower0_11 j i k)
lemma hk13_0_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_0_11 j i k).Contains (fullFactor false 13 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_0_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power13 j i k) (mpower0_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 11 (power13_contains j i k) (mpower0_11_contains j i k)
noncomputable def ha13_0_11 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨10157787699515332860,10157787699515332862⟩,⟨(-17593804388058740566),(-17593804388058740563)⟩⟩,⟨⟨36032111386744300673908,36032111386744300679444⟩,⟨(-20803149208607401700482),(-20803149208607401695509)⟩⟩,⟨⟨3598843235212085340272399,3598843235212085340704073⟩,⟨(-97705),207959⟩⟩,⟨⟨73793764120052327771321489,73793764120052327797732446⟩,⟨42604849579227958667072566,42604849579227958692437608⟩⟩,⟨⟨495985727515397112125303562,495985727515397112491860236⟩,⟨859072479885680691457498135,859072479885680691837301035⟩⟩,⟨⟨(-853699244),402097943⟩,⟨7370430945714350776562973859,7370430945714350778076839959⟩⟩]
lemma ha13_0_11_eq (j : Fin 7) : ha13_0_11 j = ((ha13_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha13_0_11_contains (j : Fin 7) : (ha13_0_11 j).Contains (fullFactor false 13 11 ((j.val:ℝ)/6)) := by
  rw [ha13_0_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_0_10 j) false 13 10 j (ha13_0_10_contains j)
noncomputable def hk13_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power13 j i k).conj.mul (mpower0_12 j i k)
lemma hk13_0_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_0_12 j i k).Contains (fullFactor false 13 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_0_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power13 j i k) (mpower0_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 12 (power13_contains j i k) (mpower0_12_contains j i k)
noncomputable def ha13_0_12 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨767674536308627877,767674536308627878⟩,⟨443217100187807442,443217100187807443⟩⟩,⟨⟨1815417242369259285276,1815417242369259285716⟩,⟨3144394900720139784725,3144394900720139785219⟩⟩,⟨⟨(-27222),12790⟩,⟨471087477881817150342265,471087477881817150400272⟩⟩,⟨⟨(-7435949024744486036011642),(-7435949024744486031560937)⟩,⟨12879441513349692556691692,12879441513349692561342271⟩⟩,⟨⟨(-187420541090973602873073025),(-187420541090973602789616307)⟩,⟨108207299850538926409133060,108207299850538926489447757⟩⟩,⟨⟨(-1929574309403923048121950467),(-1929574309403923047719479222)⟩,⟨(-223497940),105268996⟩⟩]
lemma ha13_0_12_eq (j : Fin 7) : ha13_0_12 j = ((ha13_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha13_0_12_contains (j : Fin 7) : (ha13_0_12 j).Contains (fullFactor false 13 12 ((j.val:ℝ)/6)) := by
  rw [ha13_0_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_0_11 j) false 13 11 j (ha13_0_11_contains j)
noncomputable def hk13_0_13 (j : Fin 6) (i k : Fin 16) : CBox := (power13 j i k).conj.mul (mpower0_13 j i k)
lemma hk13_0_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_0_13 j i k).Contains (fullFactor false 13 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_0_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power13 j i k) (mpower0_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 13 (power13_contains j i k) (mpower0_13_contains j i k)
noncomputable def ha13_0_13 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-17851379306351119),(-17851379306351118)⟩,⟨30919495943783799,30919495943783800⟩⟩,⟨⟨(-253292510771476882306),(-253292510771476882264)⟩,⟨146238499277628361492,146238499277628361529⟩⟩,⟨⟨(-56921729219679268121903),(-56921729219679268114712)⟩,⟨(-3290),1546⟩⟩,⟨⟨(-2074972248239938620018724),(-2074972248239938619262876)⟩,⟨(-1197985786082331537917803),(-1197985786082331537196948)⟩⟩,⟨⟨(-21791234504823142522737171),(-21791234504823142506493700)⟩,⟨(-37743525322001707903130189),(-37743525322001707886203187)⟩⟩,⟨⟨(-25439409),54010730⟩,⟨(-466302805767612564474549122),(-466302805767612564375803241)⟩⟩]
lemma ha13_0_13_eq (j : Fin 7) : ha13_0_13 j = ((ha13_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha13_0_13_contains (j : Fin 7) : (ha13_0_13 j).Contains (fullFactor false 13 13 ((j.val:ℝ)/6)) := by
  rw [ha13_0_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_0_12 j) false 13 12 j (ha13_0_12_contains j)
noncomputable def hk13_0_14 (j : Fin 6) (i k : Fin 16) : CBox := (power13 j i k).conj.mul (mpower0_14 j i k)
lemma hk13_0_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_0_14 j i k).Contains (fullFactor false 13 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_0_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power13 j i k) (mpower0_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 14 (power13_contains j i k) (mpower0_14_contains j i k)
noncomputable def ha13_0_14 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1156386444162984),(-1156386444162983)⟩,⟨(-667640024824733),(-667640024824732)⟩⟩,⟨⟨(-10938614166728417761),(-10938614166728417757)⟩,⟨(-18946235501166317753),(-18946235501166317749)⟩⟩,⟨⟨(-174),370⟩,⟨(-6386603083791852241571),(-6386603083791852240743)⟩⟩,⟨⟨179218254507678396512889,179218254507678396621300⟩,⟨(-310415122451108950087933),(-310415122451108949973870)⟩⟩,⟨⟨7058022730486958379720743,7058022730486958382908553⟩,⟨(-4074951323393142879920348),(-4074951323393142876869854)⟩⟩,⟨⟨104638104924845707107869826,104638104924845707130361424⟩,⟨(-5708591),12119980⟩⟩]
lemma ha13_0_14_eq (j : Fin 7) : ha13_0_14 j = ((ha13_0_13 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha13_0_14_contains (j : Fin 7) : (ha13_0_14 j).Contains (fullFactor false 13 14 ((j.val:ℝ)/6)) := by
  rw [ha13_0_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_0_13 j) false 13 13 j (ha13_0_13_contains j)
noncomputable def hk13_0_15 (j : Fin 6) (i k : Fin 16) : CBox := (power13 j i k).conj.mul (mpower0_15 j i k)
lemma hk13_0_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_0_15 j i k).Contains (fullFactor false 13 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_0_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power13 j i k) (mpower0_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 15 (power13_contains j i k) (mpower0_15_contains j i k)
noncomputable def ha13_0_15 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨23305033302576,23305033302577⟩,⟨(-40365501752148),(-40365501752147)⟩⟩,⟨⟨1322696761414360852,1322696761414360853⟩,⟨(-763659331258827444),(-763659331258827443)⟩⟩,⟨⟨668803510981146723210,668803510981146723300⟩,⟨(-19),39⟩⟩,⟨⟨43342127478025776412348,43342127478025776428414⟩,⟨25023588966689257657286,25023588966689257672504⟩⟩,⟨⟨711213174517105746119140,711213174517105746653816⟩,⟨1231857353275977868965870,1231857353275977869526170⟩⟩,⟨⟨(-2538403),1195605⟩,⟨21915353447830215825241049,21915353447830215830021438⟩⟩]
lemma ha13_0_15_eq (j : Fin 7) : ha13_0_15 j = ((ha13_0_14 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha13_0_15_contains (j : Fin 7) : (ha13_0_15 j).Contains (fullFactor false 13 15 ((j.val:ℝ)/6)) := by
  rw [ha13_0_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_0_14 j) false 13 14 j (ha13_0_14_contains j)
noncomputable def hk13_0_16 (j : Fin 6) (i k : Fin 16) : CBox := (power13 j i k).conj.mul (mpower0_16 j i k)
lemma hk13_0_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_0_16 j i k).Contains (fullFactor false 13 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_0_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power13 j i k) (mpower0_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 16 (power13_contains j i k) (mpower0_16_contains j i k)
noncomputable def ha13_0_16 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1320957955864,1320957955865⟩,⟨762655431406,762655431407⟩⟩,⟨⟨49981386352667221,49981386352667222⟩,⟨86570300595549323,86570300595549324⟩⟩,⟨⟨(-4),2⟩,⟨65659631149794723618,65659631149794723628⟩⟩,⟨⟨(-3275580136008399050533),(-3275580136008399048529)⟩,⟨5673471219829920493694,5673471219829920495816⟩⟩,⟨⟨(-201562188089707223646653),(-201562188089707223554332)⟩,⟨116371983552042445638845,116371983552042445726703⟩⟩,⟨⟨(-4303069587032947007825632),(-4303069587032947006873307)⟩,⟨(-498415),234757⟩⟩]
lemma ha13_0_16_eq (j : Fin 7) : ha13_0_16 j = ((ha13_0_15 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha13_0_16_contains (j : Fin 7) : (ha13_0_16 j).Contains (fullFactor false 13 16 ((j.val:ℝ)/6)) := by
  rw [ha13_0_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_0_15 j) false 13 15 j (ha13_0_15_contains j)
noncomputable def hk13_0_17 (j : Fin 6) (i k : Fin 16) : CBox := (power13 j i k).conj.mul (mpower0_17 j i k)
lemma hk13_0_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_0_17 j i k).Contains (fullFactor false 13 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_0_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power13 j i k) (mpower0_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 17 (power13_contains j i k) (mpower0_17_contains j i k)
noncomputable def ha13_0_17 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-23489732359),(-23489732358)⟩,⟨40685409900,40685409901⟩⟩,⟨⟨(-5332718046471331),(-5332718046471330)⟩,⟨3078846199642597,3078846199642598⟩⟩,⟨⟨(-6066935731106195668),(-6066935731106195666)⟩,⟨(-1),1⟩⟩,⟨⟨(-698970019787090239347),(-698970019787090239082)⟩,⟨(-403550529079554596853),(-403550529079554596604)⟩⟩,⟨⟨(-17921243559351411749290),(-17921243559351411735701)⟩,⟨(-31040504379613153646857),(-31040504379613153632540)⟩⟩,⟨⟨(-43383),92107⟩,⟨(-795205400147551278577722),(-795205400147551278399201)⟩⟩]
lemma ha13_0_17_eq (j : Fin 7) : ha13_0_17 j = ((ha13_0_16 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha13_0_17_contains (j : Fin 7) : (ha13_0_17 j).Contains (fullFactor false 13 17 ((j.val:ℝ)/6)) := by
  rw [ha13_0_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_0_16 j) false 13 16 j (ha13_0_16_contains j)
noncomputable def hk13_0_18 (j : Fin 6) (i k : Fin 16) : CBox := (power13 j i k).conj.mul (mpower0_18 j i k)
lemma hk13_0_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_0_18 j i k).Contains (fullFactor false 13 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_0_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power13 j i k) (mpower0_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 18 (power13_contains j i k) (mpower0_18_contains j i k)
noncomputable def ha13_0_18 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1183490601),(-1183490600)⟩,⟨(-683288617),(-683288616)⟩⟩,⟨⟨(-179120011154260),(-179120011154259)⟩,⟨(-310244959971483),(-310244959971482)⟩⟩,⟨⟨(-1),1⟩,⟨(-529440020073462377),(-529440020073462376)⟩⟩,⟨⟨46955236204022331356,46955236204022331386⟩,⟨(-81328854786764263398),(-81328854786764263366)⟩⟩,⟨⟨4514658357533078057205,4514658357533078059302⟩,⟨(-2606539218020916336715),(-2606539218020916334729)⟩⟩,⟨⟨138789524622137721130755,138789524622137721162355⟩,⟨(-7572),16076⟩⟩]
lemma ha13_0_18_eq (j : Fin 7) : ha13_0_18 j = ((ha13_0_17 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha13_0_18_contains (j : Fin 7) : (ha13_0_18 j).Contains (fullFactor false 13 18 ((j.val:ℝ)/6)) := by
  rw [ha13_0_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_0_17 j) false 13 17 j (ha13_0_17_contains j)
noncomputable def hk13_0_19 (j : Fin 6) (i k : Fin 16) : CBox := (power13 j i k).conj.mul (mpower0_19 j i k)
lemma hk13_0_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_0_19 j i k).Contains (fullFactor false 13 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_0_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power13 j i k) (mpower0_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 19 (power13_contains j i k) (mpower0_19_contains j i k)
noncomputable def ha13_0_19 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨18829951,18829952⟩,⟨(-32614434),(-32614433)⟩⟩,⟨⟨17099355913327,17099355913328⟩,⟨(-9872317739529),(-9872317739528)⟩⟩,⟨⟨43770654673137422,43770654673137423⟩,⟨(-1),1⟩⟩,⟨⟨8964987113086656143,8964987113086656147⟩,⟨5175937723022106879,5175937723022106883⟩⟩,⟨⟨359152827132815577372,359152827132815577647⟩,⟨622070944276038605360,622070944276038605652⟩⟩,⟨⟨(-2659),1253⟩,⟨22948428997269873107881,22948428997269873113180⟩⟩]
lemma ha13_0_19_eq (j : Fin 7) : ha13_0_19 j = ((ha13_0_18 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha13_0_19_contains (j : Fin 7) : (ha13_0_19 j).Contains (fullFactor false 13 19 ((j.val:ℝ)/6)) := by
  rw [ha13_0_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_0_18 j) false 13 18 j (ha13_0_18_contains j)
noncomputable def hk13_0_20 (j : Fin 6) (i k : Fin 16) : CBox := (power13 j i k).conj.mul (mpower0_20 j i k)
lemma hk13_0_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_0_20 j i k).Contains (fullFactor false 13 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_0_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power13 j i k) (mpower0_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 20 (power13_contains j i k) (mpower0_20_contains j i k)
noncomputable def ha13_0_20 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨853843,853844⟩,⟨492966,492967⟩⟩,⟨⟨516913348073,516913348074⟩,⟨895320181973,895320181974⟩⟩,⟨⟨(-1),1⟩,⟨3437739179098606,3437739179098608⟩⟩,⟨⟨(-542022930869484434),(-542022930869484433)⟩,⟨938811255133340262,938811255133340263⟩⟩,⟨⟨(-81428896189552855177),(-81428896189552855138)⟩,⟨47012995134852432587,47012995134852432624⟩⟩,⟨⟨(-3604730797462500934336),(-3604730797462500933491)⟩,⟨(-418),197⟩⟩]
lemma ha13_0_20_eq (j : Fin 7) : ha13_0_20 j = ((ha13_0_19 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha13_0_20_contains (j : Fin 7) : (ha13_0_20 j).Contains (fullFactor false 13 20 ((j.val:ℝ)/6)) := by
  rw [ha13_0_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_0_19 j) false 13 19 j (ha13_0_19_contains j)
noncomputable def hk13_0_21 (j : Fin 6) (i k : Fin 16) : CBox := (power13 j i k).conj.mul (mpower0_21 j i k)
lemma hk13_0_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_0_21 j i k).Contains (fullFactor false 13 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_0_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power13 j i k) (mpower0_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 21 (power13_contains j i k) (mpower0_21_contains j i k)
noncomputable def ha13_0_21 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-12292),(-12291)⟩,⟨21289,21290⟩⟩,⟨⟨(-44646528672),(-44646528671)⟩,⟨25776685346,25776685347⟩⟩,⟨⟨(-257142289286048),(-257142289286047)⟩,⟨(-1),1⟩⟩,⟨⟨(-93630556896327456),(-93630556896327455)⟩,⟨(-54057627228469228),(-54057627228469227)⟩⟩,⟨⟨(-5860939688051789414),(-5860939688051789408)⟩,⟨(-10151445319802585618),(-10151445319802585612)⟩⟩,⟨⟨(-30),63⟩,⟨(-539266466260812849008),(-539266466260812848879)⟩⟩]
lemma ha13_0_21_eq (j : Fin 7) : ha13_0_21 j = ((ha13_0_20 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha13_0_21_contains (j : Fin 7) : (ha13_0_21 j).Contains (fullFactor false 13 21 ((j.val:ℝ)/6)) := by
  rw [ha13_0_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_0_20 j) false 13 20 j (ha13_0_20_contains j)
noncomputable def hk13_0_22 (j : Fin 6) (i k : Fin 16) : CBox := (power13 j i k).conj.mul (mpower0_22 j i k)
lemma hk13_0_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_0_22 j i k).Contains (fullFactor false 13 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_0_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power13 j i k) (mpower0_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 22 (power13_contains j i k) (mpower0_22_contains j i k)
noncomputable def ha13_0_22 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-507),(-506)⟩,⟨(-293),(-292)⟩⟩,⟨⟨(-1226967354),(-1226967353)⟩,⟨(-2125169796),(-2125169795)⟩⟩,⟨⟨(-1),1⟩,⟨(-18359916521553),(-18359916521552)⟩⟩,⟨⟨5146274077922863,5146274077922864⟩,⟨(-8913608172637076),(-8913608172637075)⟩⟩,⟨⟨1208019168182208037,1208019168182208038⟩,⟨(-697450191936225611),(-697450191936225609)⟩⟩,⟨⟨77007071306013533789,77007071306013533809⟩,⟨(-5),9⟩⟩]
lemma ha13_0_22_eq (j : Fin 7) : ha13_0_22 j = ((ha13_0_21 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha13_0_22_contains (j : Fin 7) : (ha13_0_22 j).Contains (fullFactor false 13 22 ((j.val:ℝ)/6)) := by
  rw [ha13_0_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_0_21 j) false 13 21 j (ha13_0_21_contains j)
noncomputable def hk13_0_23 (j : Fin 6) (i k : Fin 16) : CBox := (power13 j i k).conj.mul (mpower0_23 j i k)
lemma hk13_0_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_0_23 j i k).Contains (fullFactor false 13 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_0_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power13 j i k) (mpower0_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 23 (power13_contains j i k) (mpower0_23_contains j i k)
noncomputable def ha13_0_23 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨6,7⟩,⟨(-12),(-11)⟩⟩,⟨⟨96759678,96759679⟩,⟨(-55864227),(-55864226)⟩⟩,⟨⟨1253899540535,1253899540536⟩,⟨(-1),1⟩⟩,⟨⟨811679013105350,811679013105351⟩,⟨468623096711943,468623096711944⟩⟩,⟨⟨79387840551870928,79387840551870929⟩,⟨137503773339017306,137503773339017308⟩⟩,⟨⟨(-2),1⟩,⟨10518471716932064453,10518471716932064457⟩⟩]
lemma ha13_0_23_eq (j : Fin 7) : ha13_0_23 j = ((ha13_0_22 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha13_0_23_contains (j : Fin 7) : (ha13_0_23 j).Contains (fullFactor false 13 23 ((j.val:ℝ)/6)) := by
  rw [ha13_0_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_0_22 j) false 13 22 j (ha13_0_22_contains j)
noncomputable def hk13_0_24 (j : Fin 6) (i k : Fin 16) : CBox := (power13 j i k).conj.mul (mpower0_24 j i k)
lemma hk13_0_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_0_24 j i k).Contains (fullFactor false 13 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_0_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power13 j i k) (mpower0_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 24 (power13_contains j i k) (mpower0_24_contains j i k)
noncomputable def ha13_0_24 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨0,1⟩⟩,⟨⟨2437536,2437537⟩,⟨4221937,4221938⟩⟩,⟨⟨(-1),1⟩,⟨82067533018,82067533019⟩⟩,⟨⟨(-40895079942577),(-40895079942576)⟩,⟨70832356240132,70832356240133⟩⟩,⟨⟨(-14999334866761558),(-14999334866761557)⟩,⟨8659870022990124,8659870022990125⟩⟩,⟨⟨(-1376864728037741371),(-1376864728037741370)⟩,⟨(-1),1⟩⟩]
lemma ha13_0_24_eq (j : Fin 7) : ha13_0_24 j = ((ha13_0_23 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha13_0_24_contains (j : Fin 7) : (ha13_0_24 j).Contains (fullFactor false 13 24 ((j.val:ℝ)/6)) := by
  rw [ha13_0_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_0_23 j) false 13 23 j (ha13_0_23_contains j)
noncomputable def hk13_0_25 (j : Fin 6) (i k : Fin 16) : CBox := (power13 j i k).conj.mul (mpower0_25 j i k)
lemma hk13_0_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_0_25 j i k).Contains (fullFactor false 13 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_0_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power13 j i k) (mpower0_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 25 (power13_contains j i k) (mpower0_25_contains j i k)
noncomputable def ha13_0_25 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨0,1⟩⟩,⟨⟨(-176849),(-176848)⟩,⟨102103,102104⟩⟩,⟨⟨(-5156455177),(-5156455176)⟩,⟨(-1),1⟩⟩,⟨⟨(-5934037600013),(-5934037600012)⟩,⟨(-3426018205749),(-3426018205748)⟩⟩,⟨⟨(-906859468175609),(-906859468175608)⟩,⟨(-1570726674205046),(-1570726674205044)⟩⟩,⟨⟨(-1),1⟩,⟨(-173021924583611077),(-173021924583611076)⟩⟩]
lemma ha13_0_25_eq (j : Fin 7) : ha13_0_25 j = ((ha13_0_24 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha13_0_25_contains (j : Fin 7) : (ha13_0_25 j).Contains (fullFactor false 13 25 ((j.val:ℝ)/6)) := by
  rw [ha13_0_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_0_24 j) false 13 24 j (ha13_0_24_contains j)
noncomputable def hk13_0_26 (j : Fin 6) (i k : Fin 16) : CBox := (power13 j i k).conj.mul (mpower0_26 j i k)
lemma hk13_0_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_0_26 j i k).Contains (fullFactor false 13 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_0_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power13 j i k) (mpower0_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 26 (power13_contains j i k) (mpower0_26_contains j i k)
noncomputable def ha13_0_26 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),0⟩⟩,⟨⟨(-4113),(-4112)⟩,⟨(-7123),(-7122)⟩⟩,⟨⟨(-1),1⟩,⟨(-311528495),(-311528494)⟩⟩,⟨⟨275978298108,275978298109⟩,⟨(-478008434111),(-478008434110)⟩⟩,⟨⟨158159723733336,158159723733337⟩,⟨(-91313559072399),(-91313559072398)⟩⟩,⟨⟨20906323353147684,20906323353147685⟩,⟨(-1),1⟩⟩]
lemma ha13_0_26_eq (j : Fin 7) : ha13_0_26 j = ((ha13_0_25 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha13_0_26_contains (j : Fin 7) : (ha13_0_26 j).Contains (fullFactor false 13 26 ((j.val:ℝ)/6)) := by
  rw [ha13_0_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_0_25 j) false 13 25 j (ha13_0_25_contains j)
noncomputable def hk13_0_27 (j : Fin 6) (i k : Fin 16) : CBox := (power13 j i k).conj.mul (mpower0_27 j i k)
lemma hk13_0_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_0_27 j i k).Contains (fullFactor false 13 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_0_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power13 j i k) (mpower0_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 27 (power13_contains j i k) (mpower0_27_contains j i k)
noncomputable def ha13_0_27 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨(-1),0⟩⟩,⟨⟨276,277⟩,⟨(-160),(-159)⟩⟩,⟨⟨18123993,18123994⟩,⟨(-1),1⟩⟩,⟨⟨37079204566,37079204567⟩,⟨21407688737,21407688739⟩⟩,⟨⟨8854012541820,8854012541821⟩,⟨15335599573285,15335599573286⟩⟩,⟨⟨(-1),1⟩,⟨2432561179993388,2432561179993389⟩⟩]
lemma ha13_0_27_eq (j : Fin 7) : ha13_0_27 j = ((ha13_0_26 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha13_0_27_contains (j : Fin 7) : (ha13_0_27 j).Contains (fullFactor false 13 27 ((j.val:ℝ)/6)) := by
  rw [ha13_0_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_0_26 j) false 13 26 j (ha13_0_26_contains j)
noncomputable def hk13_0_28 (j : Fin 6) (i k : Fin 16) : CBox := (power13 j i k).conj.mul (mpower0_28 j i k)
lemma hk13_0_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_0_28 j i k).Contains (fullFactor false 13 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_0_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power13 j i k) (mpower0_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 28 (power13_contains j i k) (mpower0_28_contains j i k)
noncomputable def ha13_0_28 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨0,1⟩⟩,⟨⟨5,6⟩,⟨10,11⟩⟩,⟨⟨(-1),1⟩,⟨1016753,1016754⟩⟩,⟨⟨(-1601291374),(-1601291373)⟩,⟨2773518015,2773518016⟩⟩,⟨⟨(-1433875207079),(-1433875207078)⟩,⟨827848236790,827848236791⟩⟩,⟨⟨(-272932726159820),(-272932726159819)⟩,⟨(-1),1⟩⟩]
lemma ha13_0_28_eq (j : Fin 7) : ha13_0_28 j = ((ha13_0_27 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha13_0_28_contains (j : Fin 7) : (ha13_0_28 j).Contains (fullFactor false 13 28 ((j.val:ℝ)/6)) := by
  rw [ha13_0_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_0_27 j) false 13 27 j (ha13_0_27_contains j)
noncomputable def hk13_0_29 (j : Fin 6) (i k : Fin 16) : CBox := (power13 j i k).conj.mul (mpower0_29 j i k)
lemma hk13_0_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_0_29 j i k).Contains (fullFactor false 13 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_0_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power13 j i k) (mpower0_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 29 (power13_contains j i k) (mpower0_29_contains j i k)
noncomputable def ha13_0_29 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨0,1⟩⟩,⟨⟨(-1),0⟩,⟨0,1⟩⟩,⟨⟨(-55073),(-55072)⟩,⟨(-1),1⟩⟩,⟨⟨(-200304916),(-200304915)⟩,⟨(-115646097),(-115646096)⟩⟩,⟨⟨(-74734538477),(-74734538476)⟩,⟨(-129444017722),(-129444017721)⟩⟩,⟨⟨(-1),1⟩,⟨(-29567015428550),(-29567015428549)⟩⟩]
lemma ha13_0_29_eq (j : Fin 7) : ha13_0_29 j = ((ha13_0_28 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha13_0_29_contains (j : Fin 7) : (ha13_0_29 j).Contains (fullFactor false 13 29 ((j.val:ℝ)/6)) := by
  rw [ha13_0_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_0_28 j) false 13 28 j (ha13_0_28_contains j)
noncomputable def hk13_0_30 (j : Fin 6) (i k : Fin 16) : CBox := (power13 j i k).conj.mul (mpower0_30 j i k)
lemma hk13_0_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_0_30 j i k).Contains (fullFactor false 13 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_0_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power13 j i k) (mpower0_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 30 (power13_contains j i k) (mpower0_30_contains j i k)
noncomputable def ha13_0_30 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),0⟩⟩,⟨⟨(-1),1⟩,⟨(-2884),(-2883)⟩⟩,⟨⟨8073620,8073621⟩,⟨(-13983922),(-13983921)⟩⟩,⟨⟨11296121531,11296121532⟩,⟨(-6521818807),(-6521818806)⟩⟩,⟨⟨3096250615296,3096250615297⟩,⟨(-1),1⟩⟩]
lemma ha13_0_30_eq (j : Fin 7) : ha13_0_30 j = ((ha13_0_29 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha13_0_30_contains (j : Fin 7) : (ha13_0_30 j).Contains (fullFactor false 13 30 ((j.val:ℝ)/6)) := by
  rw [ha13_0_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_0_29 j) false 13 29 j (ha13_0_29_contains j)
noncomputable def hk13_1_0 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_0 j i k)
lemma hk13_1_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_1_0 j i k).Contains (fullFactor true 13 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_1_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel13_0 j i k) (mpower1_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 0 (kernel13_0_contains j i k) (mpower1_0_contains j i k)
noncomputable def ha13_1_0 : Fin 7 → CBox := ![⟨⟨0,3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),0⟩,⟨(-2),3⟩⟩,⟨⟨(-341),(-337)⟩,⟨98,102⟩⟩,⟨⟨(-169976153021903),(-169976153021900)⟩,⟨(-84606803526621),(-84606803526617)⟩⟩,⟨⟨(-3263693326028840015143),(-3263693326028840004989)⟩,⟨(-2537037848528971869479),(-2537037848528971859297)⟩⟩,⟨⟨(-19618607417581830024810844),(-19618607417581829855857605)⟩,⟨(-130432011910631655003953346),(-130432011910631654833571214)⟩⟩,⟨⟨(-18541242464926204931798182214),(-18541242464926204806447611936)⟩,⟨(-91487929281433214680992385330),(-91487929281433214554185512444)⟩⟩]
lemma ha13_1_0_eq (j : Fin 7) : ha13_1_0 j = atomKernel13_0 j := by fin_cases j <;> decide +kernel
lemma ha13_1_0_contains (j : Fin 7) : (ha13_1_0 j).Contains (fullFactor true 13 0 ((j.val:ℝ)/6)) := by
  rw [ha13_1_0_eq]
  simpa only [fullFactor,ite_true] using atomKernel13_0_contains j
noncomputable def hk13_1_1 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_1 j i k)
lemma hk13_1_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_1_1 j i k).Contains (fullFactor true 13 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_1_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel13_0 j i k) (mpower1_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 1 (kernel13_0_contains j i k) (mpower1_1_contains j i k)
noncomputable def ha13_1_1 : Fin 7 → CBox := ![⟨⟨(-28),0⟩,⟨(-28),28⟩⟩,⟨⟨(-8),42⟩,⟨(-23),31⟩⟩,⟨⟨2163,2205⟩,⟨1233,1274⟩⟩,⟨⟨48835088491071,48835088491101⟩,⟨1107722107138669,1107722107138696⟩⟩,⟨⟨(-6775428697773202029332),(-6775428697773201966850)⟩,⟨18922744590791917501633,18922744590791917564035⟩⟩,⟨⟨(-519035897525465939974967179),(-519035897525465939158171005)⟩,⟨172011742142599044405582776,172011742142599045216355299⟩⟩,⟨⟨(-326883743568561696968067370144),(-326883743568561696485564285752)⟩,⟨84131904661401513556648150900,84131904661401514033371076133⟩⟩]
lemma ha13_1_1_eq (j : Fin 7) : ha13_1_1 j = ((ha13_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha13_1_1_contains (j : Fin 7) : (ha13_1_1 j).Contains (fullFactor true 13 1 ((j.val:ℝ)/6)) := by
  rw [ha13_1_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_1_0 j) true 13 0 j (ha13_1_0_contains j)
noncomputable def hk13_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_2 j i k)
lemma hk13_1_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_1_2 j i k).Contains (fullFactor true 13 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_1_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel13_0 j i k) (mpower1_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 2 (kernel13_0_contains j i k) (mpower1_2_contains j i k)
noncomputable def ha13_1_2 : Fin 7 → CBox := ![⟨⟨0,130⟩,⟨(-130),130⟩⟩,⟨⟨(-204),89⟩,⟨(-197),104⟩⟩,⟨⟨(-2254),(-2044)⟩,⟨(-8815),(-8605)⟩⟩,⟨⟨2760176405530330,2760176405530442⟩,⟨(-1692151545105966),(-1692151545105850)⟩⟩,⟨⟨48845032599524479814526,48845032599524480006172⟩,⟨1313852097947150019291,1313852097947150211002⟩⟩,⟨⟨534139242887687895050152966,534139242887687896995612902⟩,⟨999633279784417540395057059,999633279784417542352567292⟩⟩,⟨⟨182591277655268899504498524374,182591277655268900411109789811⟩,⟨582293989853362588239181519142,582293989853362589157008836243⟩⟩]
lemma ha13_1_2_eq (j : Fin 7) : ha13_1_2 j = ((ha13_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha13_1_2_contains (j : Fin 7) : (ha13_1_2 j).Contains (fullFactor true 13 2 ((j.val:ℝ)/6)) := by
  rw [ha13_1_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_1_1 j) true 13 1 j (ha13_1_1_contains j)
noncomputable def hk13_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_3 j i k)
lemma hk13_1_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_1_3 j i k).Contains (fullFactor true 13 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_1_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel13_0 j i k) (mpower1_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 3 (kernel13_0_contains j i k) (mpower1_3_contains j i k)
noncomputable def ha13_1_3 : Fin 7 → CBox := ![⟨⟨(-400),0⟩,⟨(-400),400⟩⟩,⟨⟨(-472),651⟩,⟨(-377),757⟩⟩,⟨⟨(-11779),(-11073)⟩,⟨17631,18337⟩⟩,⟨⟨(-5485083315752250),(-5485083315751946)⟩,⟨(-3103662731815189),(-3103662731814887)⟩⟩,⟨⟨(-22649217672109940303763),(-22649217672109939911639)⟩,⟨(-75884825723250568401803),(-75884825723250568009590)⟩⟩,⟨⟨1235866972863728180200608917,1235866972863728183327743131⟩,⟨(-962054562367831363678094400),(-962054562367831360566210722)⟩⟩,⟨⟨689464327622705912420089806480,689464327622705913583869122641⟩,⟨(-256227051176441857486368010911),(-256227051176441856336838948166)⟩⟩]
lemma ha13_1_3_eq (j : Fin 7) : ha13_1_3 j = ((ha13_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha13_1_3_contains (j : Fin 7) : (ha13_1_3 j).Contains (fullFactor true 13 3 ((j.val:ℝ)/6)) := by
  rw [ha13_1_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_1_2 j) true 13 2 j (ha13_1_2_contains j)
noncomputable def hk13_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_4 j i k)
lemma hk13_1_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_1_4 j i k).Contains (fullFactor true 13 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_1_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel13_0 j i k) (mpower1_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 4 (kernel13_0_contains j i k) (mpower1_4_contains j i k)
noncomputable def ha13_1_4 : Fin 7 → CBox := ![⟨⟨0,922⟩,⟨(-922),922⟩⟩,⟨⟨(-1599),1609⟩,⟨(-2056),1162⟩⟩,⟨⟨36330,38109⟩,⟨(-8314),(-6535)⟩⟩,⟨⟨(-82915792964556),(-82915792963955)⟩,⟨9200668067424293,9200668067424895⟩⟩,⟨⟨(-79066359195910865669898),(-79066359195910865068034)⟩,⟨54907925389668894341541,54907925389668894943204⟩⟩,⟨⟨(-1200176256633177587039657055),(-1200176256633177583306981164)⟩,⟨(-1092825643537363590870776926),(-1092825643537363587124473860)⟩⟩,⟨⟨(-263676395715119290114324209685),(-263676395715119289021108370840)⟩,⟨(-610390256737678504310629280639),(-610390256737678503204037689130)⟩⟩]
lemma ha13_1_4_eq (j : Fin 7) : ha13_1_4 j = ((ha13_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha13_1_4_contains (j : Fin 7) : (ha13_1_4 j).Contains (fullFactor true 13 4 ((j.val:ℝ)/6)) := by
  rw [ha13_1_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_1_3 j) true 13 3 j (ha13_1_3_contains j)
noncomputable def hk13_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_5 j i k)
lemma hk13_1_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_1_5 j i k).Contains (fullFactor true 13 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_1_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel13_0 j i k) (mpower1_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 5 (kernel13_0_contains j i k) (mpower1_5_contains j i k)
noncomputable def ha13_1_5 : Fin 7 → CBox := ![⟨⟨(-1700),0⟩,⟨(-1700),1700⟩⟩,⟨⟨(-3996),3316⟩,⟨(-2979),4342⟩⟩,⟨⟨(-46090),(-42505)⟩,⟨(-32819),(-29234)⟩⟩,⟨⟨9446849224275024,9446849224275980⟩,⟨(-5122843747512184),(-5122843747511229)⟩⟩,⟨⟨74697547998916742219019,74697547998916742957601⟩,⟨56416129207872985797256,56416129207872986536010⟩⟩,⟨⟨(-723845217883143919567514799),(-723845217883143915977394569)⟩,⟨1134551582408423153079996947,1134551582408423156661133567⟩⟩,⟨⟨(-430924741919376684124963183671),(-430924741919376683283286896587)⟩,⟨213351471291017857680766176774,213351471291017858512529150510⟩⟩]
lemma ha13_1_5_eq (j : Fin 7) : ha13_1_5 j = ((ha13_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha13_1_5_contains (j : Fin 7) : (ha13_1_5 j).Contains (fullFactor true 13 5 ((j.val:ℝ)/6)) := by
  rw [ha13_1_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_1_4 j) true 13 4 j (ha13_1_4_contains j)
noncomputable def hk13_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_6 j i k)
lemma hk13_1_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_1_6 j i k).Contains (fullFactor true 13 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_1_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel13_0 j i k) (mpower1_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 6 (kernel13_0_contains j i k) (mpower1_6_contains j i k)
noncomputable def ha13_1_6 : Fin 7 → CBox := ![⟨⟨0,2612⟩,⟨(-2612),2612⟩⟩,⟨⟨(-6083),7797⟩,⟨(-7603),6283⟩⟩,⟨⟨6708,12728⟩,⟨60473,66493⟩⟩,⟨⟨(-8817231587687975),(-8817231587686710)⟩,⟨(-5626595667738985),(-5626595667737719)⟩⟩,⟨⟨24574749301001984059298,24574749301001984814873⟩,⟨(-71765401733179323166362),(-71765401733179322410847)⟩⟩,⟨⟨857464486341701723623671140,857464486341701726486157703⟩,⟨359675267804115930754305571,359675267804115933621117712⟩⟩,⟨⟨141888983720414355336479928680,141888983720414355863858597932⟩,⟨252669790400821602609904231353,252669790400821603143333996427⟩⟩]
lemma ha13_1_6_eq (j : Fin 7) : ha13_1_6 j = ((ha13_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha13_1_6_contains (j : Fin 7) : (ha13_1_6 j).Contains (fullFactor true 13 6 ((j.val:ℝ)/6)) := by
  rw [ha13_1_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_1_5 j) true 13 5 j (ha13_1_5_contains j)
noncomputable def hk13_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_7 j i k)
lemma hk13_1_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_1_7 j i k).Contains (fullFactor true 13 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_1_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel13_0 j i k) (mpower1_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 7 (kernel13_0_contains j i k) (mpower1_7_contains j i k)
noncomputable def ha13_1_7 : Fin 7 → CBox := ![⟨⟨(-3439),0⟩,⟨(-3439),3439⟩⟩,⟨⟨(-12578),9999⟩,⟨(-11023),11558⟩⟩,⟨⟨35539,44204⟩,⟨(-56134),(-47469)⟩⟩,⟨⟨(-541367833933428),(-541367833931992)⟩,⟨8709155692288295,8709155692289731⟩⟩,⟨⟨(-52684983672169639510038),(-52684983672169638847664)⟩,⟨(-683558773004893116034),(-683558773004892453700)⟩⟩,⟨⟨123637627127261647650643986,123637627127261649612706772⟩,⟨(-536616767428347176290016710),(-536616767428347174329277856)⟩⟩,⟨⟨126536317419616170666598825001,126536317419616170956348180815⟩,⟨(-79972781258022134335226993193),(-79972781258022134048609288638)⟩⟩]
lemma ha13_1_7_eq (j : Fin 7) : ha13_1_7 j = ((ha13_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha13_1_7_contains (j : Fin 7) : (ha13_1_7 j).Contains (fullFactor true 13 7 ((j.val:ℝ)/6)) := by
  rw [ha13_1_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_1_6 j) true 13 6 j (ha13_1_6_contains j)
noncomputable def hk13_1_8 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_8 j i k)
lemma hk13_1_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_1_8 j i k).Contains (fullFactor true 13 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_1_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel13_0 j i k) (mpower1_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 8 (kernel13_0_contains j i k) (mpower1_8_contains j i k)
noncomputable def ha13_1_8 : Fin 7 → CBox := ![⟨⟨0,3962⟩,⟨(-3962),3962⟩⟩,⟨⟨(-14705),17425⟩,⟨(-15723),16409⟩⟩,⟨⟨(-63343),(-52431)⟩,⟨757,11669⟩⟩,⟨⟨5752609560200473,5752609560201899⟩,⟨(-2735167889476390),(-2735167889474964)⟩⟩,⟨⟨9584812002312223512470,9584812002312224020468⟩,⟨30554986322611210427193,30554986322611210935270⟩⟩,⟨⟨(-284914619713582947122491795),(-284914619713582945947573711)⟩,⟨(-15894302006669254500263098),(-15894302006669253325341050)⟩⟩,⟨⟨(-39067993028544540536854133596),(-39067993028544540400555875981)⟩,⟨(-55238647458222753096063561489),(-55238647458222752958361826929)⟩⟩]
lemma ha13_1_8_eq (j : Fin 7) : ha13_1_8 j = ((ha13_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha13_1_8_contains (j : Fin 7) : (ha13_1_8 j).Contains (fullFactor true 13 8 ((j.val:ℝ)/6)) := by
  rw [ha13_1_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_1_7 j) true 13 7 j (ha13_1_7_contains j)
noncomputable def hk13_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_9 j i k)
lemma hk13_1_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_1_9 j i k).Contains (fullFactor true 13 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_1_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel13_0 j i k) (mpower1_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 9 (kernel13_0_contains j i k) (mpower1_9_contains j i k)
noncomputable def ha13_1_9 : Fin 7 → CBox := ![⟨⟨(-4057),0⟩,⟨(-4057),4057⟩⟩,⟨⟨(-21338),19305⟩,⟨(-21176),19468⟩⟩,⟨⟨29116,41330⟩,⟨23619,35834⟩⟩,⟨⟨(-3361313195115143),(-3361313195113884)⟩,⟨(-2405050399016979),(-2405050399015720)⟩⟩,⟨⟨14071033328540994924106,14071033328540995270507⟩,⟨(-10064824855674054380362),(-10064824855674054034011)⟩⟩,⟨⟨15081541418509049339926184,15081541418509049965287356⟩,⟨130572778242652870485762055,130572778242652871111443428⟩⟩,⟨⟨(-21348029580429440803236481140),(-21348029580429440745070258028)⟩,⟨16827542911816119928619651535,16827542911816119986232467915⟩⟩]
lemma ha13_1_9_eq (j : Fin 7) : ha13_1_9 j = ((ha13_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha13_1_9_contains (j : Fin 7) : (ha13_1_9 j).Contains (fullFactor true 13 9 ((j.val:ℝ)/6)) := by
  rw [ha13_1_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_1_8 j) true 13 8 j (ha13_1_8_contains j)
noncomputable def hk13_1_10 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_10 j i k)
lemma hk13_1_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_1_10 j i k).Contains (fullFactor true 13 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_1_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel13_0 j i k) (mpower1_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 10 (kernel13_0_contains j i k) (mpower1_10_contains j i k)
noncomputable def ha13_1_10 : Fin 7 → CBox := ![⟨⟨0,3739⟩,⟨(-3739),3739⟩⟩,⟨⟨(-22673),23597⟩,⟨(-22102),24168⟩⟩,⟨⟨(-8185),4120⟩,⟨(-38929),(-26624)⟩⟩,⟨⟨(-277319820423234),(-277319820422234)⟩,⟨2397679408232195,2397679408233195⟩⟩,⟨⟨(-6782201330058256009673),(-6782201330058255797144)⟩,⟨(-4975622463286817479620),(-4975622463286817267072)⟩⟩,⟨⟨52280644810052441823982991,52280644810052442123810035⟩,⟨(-15357562682695983564426029),(-15357562682695983264831537)⟩⟩,⟨⟨6477328673614970815493547274,6477328673614970837410509943⟩,⟨7392852651566533800736117655,7392852651566533822847451204⟩⟩]
lemma ha13_1_10_eq (j : Fin 7) : ha13_1_10 j = ((ha13_1_9 j).mul (piI.mul (atomPoints j).z)).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha13_1_10_contains (j : Fin 7) : (ha13_1_10 j).Contains (fullFactor true 13 10 ((j.val:ℝ)/6)) := by
  rw [ha13_1_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_1_9 j) true 13 9 j (ha13_1_9_contains j)
noncomputable def hk13_1_11 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_11 j i k)
lemma hk13_1_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_1_11 j i k).Contains (fullFactor true 13 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_1_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel13_0 j i k) (mpower1_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 11 (kernel13_0_contains j i k) (mpower1_11_contains j i k)
noncomputable def ha13_1_11 : Fin 7 → CBox := ![⟨⟨(-3133),0⟩,⟨(-3133),3133⟩⟩,⟨⟨(-23916),23970⟩,⟨(-24819),23067⟩⟩,⟨⟨(-20071),(-8801)⟩,⟨9987,21257⟩⟩,⟨⟨1184802833555247,1184802833555970⟩,⟨(-488070484188893),(-488070484188170)⟩⟩,⟨⟨(-1155442677424044368538),(-1155442677424044249980)⟩,⟨3533958045235689272388,3533958045235689390943⟩⟩,⟨⟨(-9051064678853364685811396),(-9051064678853364555318777)⟩,⟨(-18433227488874013452298251),(-18433227488874013321698030)⟩⟩,⟨⟨2316319426759211056685814532,2316319426759211064326620861⟩,⟨(-2252543930829199664174145176),(-2252543930829199656594734910)⟩⟩]
lemma ha13_1_11_eq (j : Fin 7) : ha13_1_11 j = ((ha13_1_10 j).mul (piI.mul (atomPoints j).z)).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha13_1_11_contains (j : Fin 7) : (ha13_1_11 j).Contains (fullFactor true 13 11 ((j.val:ℝ)/6)) := by
  rw [ha13_1_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_1_10 j) true 13 10 j (ha13_1_10_contains j)
noncomputable def hk13_1_12 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_12 j i k)
lemma hk13_1_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_1_12 j i k).Contains (fullFactor true 13 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_1_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel13_0 j i k) (mpower1_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 12 (kernel13_0_contains j i k) (mpower1_12_contains j i k)
noncomputable def ha13_1_12 : Fin 7 → CBox := ![⟨⟨0,2406⟩,⟨(-2406),2406⟩⟩,⟨⟨(-23003),22426⟩,⟨(-22163),23266⟩⟩,⟨⟨7897,17359⟩,⟨(-4945),4517⟩⟩,⟨⟨(-487181524646578),(-487181524646098)⟩,⟨(-389256009092657),(-389256009092178)⟩⟩,⟨⟨1506479625916169508828,1506479625916169569449⟩,⟨(-1422787817008995771),(-1422787817008935151)⟩⟩,⟨⟨(-5744206732736001736064142),(-5744206732736001683921877)⟩,⟨4163241137144289910132698,4163241137144289962236232⟩⟩,⟨⟨(-714078154587542154274049133),(-714078154587542151871427179)⟩,⟨(-661776836235156282263248585),(-661776836235156279843054201)⟩⟩]
lemma ha13_1_12_eq (j : Fin 7) : ha13_1_12 j = ((ha13_1_11 j).mul (piI.mul (atomPoints j).z)).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha13_1_12_contains (j : Fin 7) : (ha13_1_12 j).Contains (fullFactor true 13 12 ((j.val:ℝ)/6)) := by
  rw [ha13_1_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_1_11 j) true 13 11 j (ha13_1_11_contains j)
noncomputable def hk13_1_13 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_13 j i k)
lemma hk13_1_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_1_13 j i k).Contains (fullFactor true 13 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_1_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel13_0 j i k) (mpower1_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 13 (kernel13_0_contains j i k) (mpower1_13_contains j i k)
noncomputable def ha13_1_13 : Fin 7 → CBox := ![⟨⟨(-1706),0⟩,⟨(-1706),1706⟩⟩,⟨⟨(-19564),20219⟩,⟨(-20134),19649⟩⟩,⟨⟨(-8534),(-1201)⟩,⟨(-8588),(-1255)⟩⟩,⟨⟨(-46900871869911),(-46900871869617)⟩,⟨276173049938498,276173049938792⟩⟩,⟨⟨(-176109760920533965299),(-176109760920533936688)⟩,⟨(-535212581977576878551),(-535212581977576849938)⟩⟩,⟨⟨1619518943110304045264022,1619518943110304064467826⟩,⟨1579584100474629079635979,1579584100474629098851164⟩⟩,⟨⟨(-173508349021761392124750608),(-173508349021761391417168548)⟩,⟨207909143535531104764087803,207909143535531105467086404⟩⟩]
lemma ha13_1_13_eq (j : Fin 7) : ha13_1_13 j = ((ha13_1_12 j).mul (piI.mul (atomPoints j).z)).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha13_1_13_contains (j : Fin 7) : (ha13_1_13 j).Contains (fullFactor true 13 13 ((j.val:ℝ)/6)) := by
  rw [ha13_1_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_1_12 j) true 13 12 j (ha13_1_12_contains j)
noncomputable def hk13_1_14 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_14 j i k)
lemma hk13_1_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_1_14 j i k).Contains (fullFactor true 13 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_1_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel13_0 j i k) (mpower1_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 14 (kernel13_0_contains j i k) (mpower1_14_contains j i k)
noncomputable def ha13_1_14 : Fin 7 → CBox := ![⟨⟨0,1123⟩,⟨(-1123),1123⟩⟩,⟨⟨(-16419),15932⟩,⟨(-16129),16221⟩⟩,⟨⟨(-2737),2540⟩,⟨883,6160⟩⟩,⟨⟨110249882407226,110249882407394⟩,⟨(-38713104765464),(-38713104765296)⟩⟩,⟨⟨(-157557663092208391915),(-157557663092208379374)⟩,⟨116047359607822127229,116047359607822139769⟩⟩,⟨⟨379459522779161671899565,379459522779161678474511⟩,⟨(-552051668636543077432771),(-552051668636543070860543)⟩⟩,⟨⟨55953255401131351213075368,55953255401131351404068567⟩,⟨41964526358793112980017863,41964526358793113172105026⟩⟩]
lemma ha13_1_14_eq (j : Fin 7) : ha13_1_14 j = ((ha13_1_13 j).mul (piI.mul (atomPoints j).z)).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha13_1_14_contains (j : Fin 7) : (ha13_1_14 j).Contains (fullFactor true 13 14 ((j.val:ℝ)/6)) := by
  rw [ha13_1_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_1_13 j) true 13 13 j (ha13_1_13_contains j)
noncomputable def hk13_1_15 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_15 j i k)
lemma hk13_1_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_1_15 j i k).Contains (fullFactor true 13 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_1_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel13_0 j i k) (mpower1_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 15 (kernel13_0_contains j i k) (mpower1_15_contains j i k)
noncomputable def ha13_1_15 : Fin 7 → CBox := ![⟨⟨(-690),0⟩,⟨(-690),690⟩⟩,⟨⟨(-12141),12412⟩,⟨(-12240),12313⟩⟩,⟨⟨(-531),3014⟩,⟨(-2895),650⟩⟩,⟨⟨(-33984213307097),(-33984213307007)⟩,⟨(-30241983129272),(-30241983129182)⟩⟩,⟨⟨51659571312886998122,51659571312887003252⟩,⟨36804105711370736570,36804105711370741701⟩⟩,⟨⟨(-168169983210662732612274),(-168169983210662730513053)⟩,⟨(-77426114283267638611231),(-77426114283267636511522)⟩⟩,⟨⟨9401897796345060580999080,9401897796345060629666479⟩,⟨(-13995232137477086324510427),(-13995232137477086276082526)⟩⟩]
lemma ha13_1_15_eq (j : Fin 7) : ha13_1_15 j = ((ha13_1_14 j).mul (piI.mul (atomPoints j).z)).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha13_1_15_contains (j : Fin 7) : (ha13_1_15 j).Contains (fullFactor true 13 15 ((j.val:ℝ)/6)) := by
  rw [ha13_1_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_1_14 j) true 13 14 j (ha13_1_14_contains j)
noncomputable def hk13_1_16 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_16 j i k)
lemma hk13_1_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_1_16 j i k).Contains (fullFactor true 13 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_1_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel13_0 j i k) (mpower1_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 16 (kernel13_0_contains j i k) (mpower1_16_contains j i k)
noncomputable def ha13_1_16 : Fin 7 → CBox := ![⟨⟨0,398⟩,⟨(-398),398⟩⟩,⟨⟨(-8792),8679⟩,⟨(-8784),8686⟩⟩,⟨⟨(-1860),373⟩,⟨(-1171),1062⟩⟩,⟨⟨(-3644352503520),(-3644352503474)⟩,⟨16199083582030,16199083582076⟩⟩,⟨⟨5734494115373043925,5734494115373045893⟩,⟨(-18402375035762237755),(-18402375035762235787)⟩⟩,⟨⟨(-12366601981441535326053),(-12366601981441534697439)⟩,⟨46347235530570450131219,46347235530570450759791⟩⟩,⟨⟨(-3268910846753978339022012),(-3268910846753978327510803)⟩,⟨(-1957660379773265460832635),(-1957660379773265449273312)⟩⟩]
lemma ha13_1_16_eq (j : Fin 7) : ha13_1_16 j = ((ha13_1_15 j).mul (piI.mul (atomPoints j).z)).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha13_1_16_contains (j : Fin 7) : (ha13_1_16 j).Contains (fullFactor true 13 16 ((j.val:ℝ)/6)) := by
  rw [ha13_1_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_1_15 j) true 13 15 j (ha13_1_15_contains j)
noncomputable def hk13_1_17 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_17 j i k)
lemma hk13_1_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_1_17 j i k).Contains (fullFactor true 13 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_1_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel13_0 j i k) (mpower1_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 17 (kernel13_0_contains j i k) (mpower1_17_contains j i k)
noncomputable def ha13_1_17 : Fin 7 → CBox := ![⟨⟨(-216),0⟩,⟨(-216),216⟩⟩,⟨⟨(-5835),5865⟩,⟨(-5816),5884⟩⟩,⟨⟨(-463),861⟩,⟨(-421),903⟩⟩,⟨⟨5474290515447,5474290515469⟩,⟨(-1601578165748),(-1601578165725)⟩⟩,⟨⟨(-5512269208028139207),(-5512269208028138495)⟩,⟨81932762591983489,81932762591984201⟩⟩,⟨⟨11650119869057567266912,11650119869057567444047⟩,⟨1051684626320867785569,1051684626320867962690⟩⟩,⟨⟨(-379726367792195836307583),(-379726367792195833723642)⟩,⟨715983449472812879471836,715983449472812882046928⟩⟩]
lemma ha13_1_17_eq (j : Fin 7) : ha13_1_17 j = ((ha13_1_16 j).mul (piI.mul (atomPoints j).z)).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha13_1_17_contains (j : Fin 7) : (ha13_1_17 j).Contains (fullFactor true 13 17 ((j.val:ℝ)/6)) := by
  rw [ha13_1_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_1_16 j) true 13 16 j (ha13_1_16_contains j)
noncomputable def hk13_1_18 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_18 j i k)
lemma hk13_1_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_1_18 j i k).Contains (fullFactor true 13 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_1_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel13_0 j i k) (mpower1_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 18 (kernel13_0_contains j i k) (mpower1_18_contains j i k)
noncomputable def ha13_1_18 : Fin 7 → CBox := ![⟨⟨0,111⟩,⟨(-111),111⟩⟩,⟨⟨(-3700),3701⟩,⟨(-3718),3683⟩⟩,⟨⟨(-356),386⟩,⟨(-494),248⟩⟩,⟨⟨(-1315193598916),(-1315193598905)⟩,⟨(-1301764808712),(-1301764808701)⟩⟩,⟨⟨485087845112077795,485087845112078039⟩,⟨1407914824903179340,1407914824903179584⟩⟩,⟨⟨(-217155281565886610801),(-217155281565886563668)⟩,⟨(-2685271962697031146368),(-2685271962697031099225)⟩⟩,⟨⟨147596520719159857896599,147596520719159858440620⟩,⟨68708843773474047054191,68708843773474047599693⟩⟩]
lemma ha13_1_18_eq (j : Fin 7) : ha13_1_18 j = ((ha13_1_17 j).mul (piI.mul (atomPoints j).z)).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha13_1_18_contains (j : Fin 7) : (ha13_1_18 j).Contains (fullFactor true 13 18 ((j.val:ℝ)/6)) := by
  rw [ha13_1_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_1_17 j) true 13 17 j (ha13_1_17_contains j)
noncomputable def hk13_1_19 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_19 j i k)
lemma hk13_1_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_1_19 j i k).Contains (fullFactor true 13 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_1_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel13_0 j i k) (mpower1_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 19 (kernel13_0_contains j i k) (mpower1_19_contains j i k)
noncomputable def ha13_1_19 : Fin 7 → CBox := ![⟨⟨(-54),0⟩,⟨(-54),54⟩⟩,⟨⟨(-2221),2214⟩,⟨(-2211),2225⟩⟩,⟨⟨(-234),160⟩,⟨(-169),225⟩⟩,⟨⟨(-154094663925),(-154094663919)⟩,⟨547492436906,547492436912⟩⟩,⟨⟨303656330660654126,303656330660654206⟩,⟨(-230241759146353892),(-230241759146353812)⟩⟩,⟨⟨(-569325650148297228405),(-569325650148297216518)⟩,⟨146231272665711444020,146231272665711455903⟩⟩,⟨⟨11599722642812166090680,11599722642812166199778⟩,⟨(-28730345766858248704667),(-28730345766858248595791)⟩⟩]
lemma ha13_1_19_eq (j : Fin 7) : ha13_1_19 j = ((ha13_1_18 j).mul (piI.mul (atomPoints j).z)).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha13_1_19_contains (j : Fin 7) : (ha13_1_19 j).Contains (fullFactor true 13 19 ((j.val:ℝ)/6)) := by
  rw [ha13_1_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_1_18 j) true 13 18 j (ha13_1_18_contains j)
noncomputable def hk13_1_20 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_20 j i k)
lemma hk13_1_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_1_20 j i k).Contains (fullFactor true 13 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_1_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel13_0 j i k) (mpower1_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 20 (kernel13_0_contains j i k) (mpower1_20_contains j i k)
noncomputable def ha13_1_20 : Fin 7 → CBox := ![⟨⟨0,25⟩,⟨(-25),25⟩⟩,⟨⟨(-1260),1265⟩,⟨(-1265),1261⟩⟩,⟨⟨(-83),116⟩,⟨(-97),102⟩⟩,⟨⟨161641552325,161641552329⟩,⟨(-38111898251),(-38111898248)⟩⟩,⟨⟨(-76193101051690185),(-76193101051690160)⟩,⟨(-52699531541181317),(-52699531541181291)⟩⟩,⟨⟨49918848101738665337,49918848101738668184⟩,⟨111143620062230221850,111143620062230224698⟩⟩,⟨⟨(-5296207274428164286732),(-5296207274428164266032)⟩,⟨(-1824605355869686504641),(-1824605355869686483913)⟩⟩]
lemma ha13_1_20_eq (j : Fin 7) : ha13_1_20 j = ((ha13_1_19 j).mul (piI.mul (atomPoints j).z)).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha13_1_20_contains (j : Fin 7) : (ha13_1_20 j).Contains (fullFactor true 13 20 ((j.val:ℝ)/6)) := by
  rw [ha13_1_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_1_19 j) true 13 19 j (ha13_1_19_contains j)
noncomputable def hk13_1_21 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_21 j i k)
lemma hk13_1_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_1_21 j i k).Contains (fullFactor true 13 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_1_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel13_0 j i k) (mpower1_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 21 (kernel13_0_contains j i k) (mpower1_21_contains j i k)
noncomputable def ha13_1_21 : Fin 7 → CBox := ![⟨⟨(-11),0⟩,⟨(-11),11⟩⟩,⟨⟨(-686),684⟩,⟨(-685),685⟩⟩,⟨⟨(-51),45⟩,⟨(-53),44⟩⟩,⟨⟨(-31053802520),(-31053802517)⟩,⟨(-34183534830),(-34183534827)⟩⟩,⟨⟨(-6095788512564738),(-6095788512564729)⟩,⟨20565232336924463,20565232336924472⟩⟩,⟨⟨19947452122923390013,19947452122923390664⟩,⟨(-13438680182829295894),(-13438680182829295244)⟩⟩,⟨⟨(-266390992704363197630),(-266390992704363193879)⟩,⟨927016887678203849940,927016887678203853688⟩⟩]
lemma ha13_1_21_eq (j : Fin 7) : ha13_1_21 j = ((ha13_1_20 j).mul (piI.mul (atomPoints j).z)).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha13_1_21_contains (j : Fin 7) : (ha13_1_21 j).Contains (fullFactor true 13 21 ((j.val:ℝ)/6)) := by
  rw [ha13_1_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_1_20 j) true 13 20 j (ha13_1_20_contains j)
noncomputable def hk13_1_22 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_22 j i k)
lemma hk13_1_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_1_22 j i k).Contains (fullFactor true 13 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_1_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel13_0 j i k) (mpower1_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 22 (kernel13_0_contains j i k) (mpower1_22_contains j i k)
noncomputable def ha13_1_22 : Fin 7 → CBox := ![⟨⟨0,5⟩,⟨(-5),5⟩⟩,⟨⟨(-355),355⟩,⟨(-355),355⟩⟩,⟨⟨(-23),22⟩,⟨(-21),24⟩⟩,⟨⟨(-3942600849),(-3942600847)⟩,⟨11607750839,11607750841⟩⟩,⟨⟨4738565622671909,4738565622671912⟩,⟨(-136417296725784),(-136417296725781)⟩⟩,⟨⟨(-3134094450884164939),(-3134094450884164797)⟩,⟨(-3273923499621043274),(-3273923499621043131)⟩⟩,⟨⟨154431965900625431326,154431965900625431975⟩,⟨35812533676602747667,35812533676602748316⟩⟩]
lemma ha13_1_22_eq (j : Fin 7) : ha13_1_22 j = ((ha13_1_21 j).mul (piI.mul (atomPoints j).z)).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha13_1_22_contains (j : Fin 7) : (ha13_1_22 j).Contains (fullFactor true 13 22 ((j.val:ℝ)/6)) := by
  rw [ha13_1_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_1_21 j) true 13 21 j (ha13_1_21_contains j)
noncomputable def hk13_1_23 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_23 j i k)
lemma hk13_1_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_1_23 j i k).Contains (fullFactor true 13 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_1_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel13_0 j i k) (mpower1_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 23 (kernel13_0_contains j i k) (mpower1_23_contains j i k)
noncomputable def ha13_1_23 : Fin 7 → CBox := ![⟨⟨(-3),0⟩,⟨(-3),3⟩⟩,⟨⟨(-176),176⟩,⟨(-176),176⟩⟩,⟨⟨(-10),11⟩,⟨(-11),10⟩⟩,⟨⟨3063180923,3063180925⟩,⟨(-552603398),(-552603397)⟩⟩,⟨⟨(-339602715115267),(-339602715115265)⟩,⟨(-942843528351169),(-942843528351167)⟩⟩,⟨⟨(-485547312825471062),(-485547312825471031)⟩,⟨656936715480859687,656936715480859718⟩⟩,⟨⟨4361816670070208692,4361816670070208800⟩,⟨(-24538369114117272971),(-24538369114117272862)⟩⟩]
lemma ha13_1_23_eq (j : Fin 7) : ha13_1_23 j = ((ha13_1_22 j).mul (piI.mul (atomPoints j).z)).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha13_1_23_contains (j : Fin 7) : (ha13_1_23 j).Contains (fullFactor true 13 23 ((j.val:ℝ)/6)) := by
  rw [ha13_1_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_1_22 j) true 13 22 j (ha13_1_22_contains j)
noncomputable def hk13_1_24 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_24 j i k)
lemma hk13_1_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_1_24 j i k).Contains (fullFactor true 13 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_1_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel13_0 j i k) (mpower1_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 24 (kernel13_0_contains j i k) (mpower1_24_contains j i k)
noncomputable def ha13_1_24 : Fin 7 → CBox := ![⟨⟨0,2⟩,⟨(-2),2⟩⟩,⟨⟨(-84),84⟩,⟨(-84),84⟩⟩,⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨(-478817380),(-478817379)⟩,⟨(-586821975),(-586821974)⟩⟩,⟨⟨(-160054489498203),(-160054489498202)⟩,⟨124904370959028,124904370959030⟩⟩,⟨⟨126073099142750849,126073099142750856⟩,⟨63371694827256420,63371694827256427⟩⟩,⟨⟨(-3726155115074205307),(-3726155115074205289)⟩,⟨(-464290904201092748),(-464290904201092730)⟩⟩]
lemma ha13_1_24_eq (j : Fin 7) : ha13_1_24 j = ((ha13_1_23 j).mul (piI.mul (atomPoints j).z)).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha13_1_24_contains (j : Fin 7) : (ha13_1_24 j).Contains (fullFactor true 13 24 ((j.val:ℝ)/6)) := by
  rw [ha13_1_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_1_23 j) true 13 23 j (ha13_1_23_contains j)
noncomputable def hk13_1_25 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_25 j i k)
lemma hk13_1_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_1_25 j i k).Contains (fullFactor true 13 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_1_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel13_0 j i k) (mpower1_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 25 (kernel13_0_contains j i k) (mpower1_25_contains j i k)
noncomputable def ha13_1_25 : Fin 7 → CBox := ![⟨⟨(-1),0⟩,⟨(-1),1⟩⟩,⟨⟨(-39),39⟩,⟨(-39),39⟩⟩,⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-65704168),(-65704166)⟩,⟨164265298,164265299⟩⟩,⟨⟨32783857938547,32783857938548⟩,⟨22007014694235,22007014694236⟩⟩,⟨⟨6803928602750483,6803928602750485⟩,⟨(-22387157454350206),(-22387157454350204)⟩⟩,⟨⟨(-39075756041965584),(-39075756041965580)⟩,⟨541696984189840146,541696984189840149⟩⟩]
lemma ha13_1_25_eq (j : Fin 7) : ha13_1_25 j = ((ha13_1_24 j).mul (piI.mul (atomPoints j).z)).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha13_1_25_contains (j : Fin 7) : (ha13_1_25 j).Contains (fullFactor true 13 25 ((j.val:ℝ)/6)) := by
  rw [ha13_1_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_1_24 j) true 13 24 j (ha13_1_24_contains j)
noncomputable def hk13_1_26 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_26 j i k)
lemma hk13_1_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_1_26 j i k).Contains (fullFactor true 13 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_1_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel13_0 j i k) (mpower1_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 26 (kernel13_0_contains j i k) (mpower1_26_contains j i k)
noncomputable def ha13_1_26 : Fin 7 → CBox := ![⟨⟨0,1⟩,⟨(-1),1⟩⟩,⟨⟨(-18),18⟩,⟨(-18),18⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨39425201,39425202⟩,⟨(-4970517),(-4970515)⟩⟩,⟨⟨1999728436134,1999728436135⟩,⟨(-7108059280695),(-7108059280693)⟩⟩,⟨⟨(-3701931032599262),(-3701931032599260)⟩,⟨(-462641338728508),(-462641338728507)⟩⟩,⟨⟨75516126950686264,75516126950686265⟩,⟨1514896652642508,1514896652642509⟩⟩]
lemma ha13_1_26_eq (j : Fin 7) : ha13_1_26 j = ((ha13_1_25 j).mul (piI.mul (atomPoints j).z)).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha13_1_26_contains (j : Fin 7) : (ha13_1_26 j).Contains (fullFactor true 13 26 ((j.val:ℝ)/6)) := by
  rw [ha13_1_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_1_25 j) true 13 25 j (ha13_1_25_contains j)
noncomputable def hk13_1_27 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_27 j i k)
lemma hk13_1_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_1_27 j i k).Contains (fullFactor true 13 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_1_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel13_0 j i k) (mpower1_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 27 (kernel13_0_contains j i k) (mpower1_27_contains j i k)
noncomputable def ha13_1_27 : Fin 7 → CBox := ![⟨⟨(-1),0⟩,⟨(-1),1⟩⟩,⟨⟨(-8),8⟩,⟨(-8),8⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-5072727),(-5072726)⟩,⟨(-6938093),(-6938092)⟩⟩,⟨⟨(-1328498462274),(-1328498462273)⟩,⟨56759990849,56759990851⟩⟩,⟨⟨26565253506185,26565253506186⟩,⟨572197215089038,572197215089039⟩⟩,⟨⟨(-322577228915015),(-322577228915014)⟩,⟨(-10110191036269239),(-10110191036269238)⟩⟩]
lemma ha13_1_27_eq (j : Fin 7) : ha13_1_27 j = ((ha13_1_26 j).mul (piI.mul (atomPoints j).z)).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha13_1_27_contains (j : Fin 7) : (ha13_1_27 j).Contains (fullFactor true 13 27 ((j.val:ℝ)/6)) := by
  rw [ha13_1_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_1_26 j) true 13 26 j (ha13_1_26_contains j)
noncomputable def hk13_1_28 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_28 j i k)
lemma hk13_1_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_1_28 j i k).Contains (fullFactor true 13 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_1_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel13_0 j i k) (mpower1_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 28 (kernel13_0_contains j i k) (mpower1_28_contains j i k)
noncomputable def ha13_1_28 : Fin 7 → CBox := ![⟨⟨0,1⟩,⟨(-1),1⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-753071),(-753070)⟩,⟨1626700,1626702⟩⟩,⟨⟨81263545238,81263545240⟩,⟨216129890164,216129890165⟩⟩,⟨⟨82817320506323,82817320506324⟩,⟨(-18268868059780),(-18268868059779)⟩⟩,⟨⟨(-1301699702824259),(-1301699702824258)⟩,⟨109402116200462,109402116200463⟩⟩]
lemma ha13_1_28_eq (j : Fin 7) : ha13_1_28 j = ((ha13_1_27 j).mul (piI.mul (atomPoints j).z)).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha13_1_28_contains (j : Fin 7) : (ha13_1_28 j).Contains (fullFactor true 13 28 ((j.val:ℝ)/6)) := by
  rw [ha13_1_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_1_27 j) true 13 27 j (ha13_1_27_contains j)
noncomputable def hk13_1_29 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_29 j i k)
lemma hk13_1_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_1_29 j i k).Contains (fullFactor true 13 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_1_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel13_0 j i k) (mpower1_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 29 (kernel13_0_contains j i k) (mpower1_29_contains j i k)
noncomputable def ha13_1_29 : Fin 7 → CBox := ![⟨⟨(-1),0⟩,⟨(-1),1⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨360028,360029⟩,⟨(-26092),(-26091)⟩⟩,⟨⟨30185328263,30185328264⟩,⟨(-24239673296),(-24239673294)⟩⟩,⟨⟨(-4584910010288),(-4584910010287)⟩,⟨(-11222979847810),(-11222979847808)⟩⟩,⟨⟨22050979634099,22050979634100⟩,⟨161376852381153,161376852381154⟩⟩]
lemma ha13_1_29_eq (j : Fin 7) : ha13_1_29 j = ((ha13_1_28 j).mul (piI.mul (atomPoints j).z)).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha13_1_29_contains (j : Fin 7) : (ha13_1_29 j).Contains (fullFactor true 13 29 ((j.val:ℝ)/6)) := by
  rw [ha13_1_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_1_28 j) true 13 28 j (ha13_1_28_contains j)
noncomputable def hk13_1_30 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_30 j i k)
lemma hk13_1_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk13_1_30 j i k).Contains (fullFactor true 13 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk13_1_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel13_0 j i k) (mpower1_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 13 30 (kernel13_0_contains j i k) (mpower1_30_contains j i k)
noncomputable def ha13_1_30 : Fin 7 → CBox := ![⟨⟨0,1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-38406),(-38405)⟩,⟨(-58844),(-58842)⟩⟩,⟨⟨(-5257618695),(-5257618693)⟩,⟨(-3424138169),(-3424138167)⟩⟩,⟨⟨(-1420667329920),(-1420667329919)⟩,⟨887837197971,887837197972⟩⟩,⟨⟨19286514319068,19286514319069⟩,⟨(-3664297815547),(-3664297815545)⟩⟩]
lemma ha13_1_30_eq (j : Fin 7) : ha13_1_30 j = ((ha13_1_29 j).mul (piI.mul (atomPoints j).z)).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha13_1_30_contains (j : Fin 7) : (ha13_1_30 j).Contains (fullFactor true 13 30 ((j.val:ℝ)/6)) := by
  rw [ha13_1_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha13_1_29 j) true 13 29 j (ha13_1_29_contains j)
end SharpPlanar.CachedData

end OAI
