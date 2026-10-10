import OAI.Analysis.PlanarPacking.Certificate.Powers10
import OAI.Analysis.PlanarPacking.Certificate.KernelValues10
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
noncomputable def hk7_0_0 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_0 j i k)
lemma hk7_0_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_0_0 j i k).Contains (fullFactor false 7 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_0_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power7 j i k) (mpower0_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 0 (power7_contains j i k) (mpower0_0_contains j i k)
noncomputable def ha7_0_0 : Fin 7 → CBox := ![⟨⟨999999999999999999999999999917,1000000000000000000000000000111⟩,⟨(-111),111⟩⟩,⟨⟨(-866025403784438646771800588553),(-866025403784438646752896366797)⟩,⟨(-500000000000000000012307326611),(-499999999999999999992454749917)⟩⟩,⟨⟨499999999999999999968936654721,500000000000000000021539192201⟩,⟨866025403784438646739824219579,866025403784438646793120894275⟩⟩,⟨⟨(-14618566227),31114883253⟩,⟨(-1000000000000000000022866724740),(-999999999999999999977133275267)⟩⟩,⟨⟨(-500000000000000000082050976378),(-499999999999999999936997329789)⟩,⟨866025403784438646685951299793,866025403784438646830497497000⟩⟩,⟨⟨866025403784438646679347406341,866025403784438646861845866006⟩,⟨(-500000000000000000079092213025),(-499999999999999999897097404267)⟩⟩,⟨⟨(-1000000000000000000045872384501),(-999999999999999999954127615527)⟩,⟨(-62368701541),29376067433⟩⟩]
lemma ha7_0_0_eq (j : Fin 7) : ha7_0_0 j = ((atomPoints j).direct.powBin 7 7).conj := by fin_cases j <;> decide +kernel
lemma ha7_0_0_contains (j : Fin 7) : (ha7_0_0 j).Contains (fullFactor false 7 0 ((j.val:ℝ)/6)) := by
  rw [ha7_0_0_eq]
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @direct_factor_zero_full ((atomPoints j).direct.powBin 7 7) ((j.val:ℝ)/6) 7 (@direct_power_bin_contains (atomPoints j) ((j.val:ℝ)/6) (atomPoints_contains j) 7 (by norm_num))
noncomputable def hk7_0_1 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_1 j i k)
lemma hk7_0_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_0_1 j i k).Contains (fullFactor false 7 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_0_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power7 j i k) (mpower0_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 1 (power7_contains j i k) (mpower0_1_contains j i k)
noncomputable def ha7_0_1 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨261799387799149436534382649626,261799387799149436545610767812⟩,⟨(-453449841058554462653810726644),(-453449841058554462642469123601)⟩⟩,⟨⟨(-906899682117108925329948025229),(-906899682117108925271249126650)⟩,⟨523598775598298873044137207557,523598775598298873100889122663⟩⟩,⟨⟨1570796326794896619194081032783,1570796326794896619270918967228⟩,⟨(-22962790133),48875144323⟩⟩,⟨⟨(-1813799364234217850738177424145),(-1813799364234217850429667073949)⟩,⟨(-1047197551196597746328513829741),(-1047197551196597746021380849404)⟩⟩,⟨⟨1308996938995747182422268301007,1308996938995747182902896262831⟩,⟨2267249205292772313019794889810,2267249205292772313504791618325⟩⟩,⟨⟨(-92287637639),195937054576⟩,⟨(-3141592653589793238614112346151),(-3141592653589793238315887653936)⟩⟩]
lemma ha7_0_1_eq (j : Fin 7) : ha7_0_1 j = ((ha7_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha7_0_1_contains (j : Fin 7) : (ha7_0_1 j).Contains (fullFactor false 7 1 ((j.val:ℝ)/6)) := by
  rw [ha7_0_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_0_0 j) false 7 0 j (ha7_0_0_contains j)
noncomputable def hk7_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_2 j i k)
lemma hk7_0_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_0_2 j i k).Contains (fullFactor false 7 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_0_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power7 j i k) (mpower0_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 2 (power7_contains j i k) (mpower0_2_contains j i k)
noncomputable def ha7_0_2 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨118712890786751174406253422957,118712890786751174409600522559⟩,⟨68538919452009434851867672679,68538919452009434855025353305⟩⟩,⟨⟨(-274155677808037739425163349954),(-274155677808037739394575452063)⟩,⟨(-474851563147004697650092255967),(-474851563147004697617846085070)⟩⟩,⟨⟨(-38386448588),18034933197⟩,⟨1233700550136169827324024575728,1233700550136169827388299939138⟩⟩,⟨⟨1096622711232150957508251030052,1096622711232150957833370593460⟩,⟨(-1899406252588018790682345086695),(-1899406252588018790353227805565)⟩⟩,⟨⟨(-2967822269668779360548593364875),(-2967822269668779359904287260132)⟩,⟨1713472986300235870969907345385,1713472986300235871604502030124⟩⟩,⟨⟨4934802200544679309182569922603,4934802200544679309666728136963⟩,⟨(-144965082212),307777205611⟩⟩]
lemma ha7_0_2_eq (j : Fin 7) : ha7_0_2 j = ((ha7_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha7_0_2_contains (j : Fin 7) : (ha7_0_2 j).Contains (fullFactor false 7 2 ((j.val:ℝ)/6)) := by
  rw [ha7_0_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_0_1 j) false 7 1 j (ha7_0_1_contains j)
noncomputable def hk7_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_3 j i k)
lemma hk7_0_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_0_3 j i k).Contains (fullFactor false 7 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_0_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power7 j i k) (mpower0_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 3 (power7_contains j i k) (mpower0_3_contains j i k)
noncomputable def ha7_0_3 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-11962298101967523216225827356),(-11962298101967523215636630941)⟩,⟨20719308087892496642104092401,20719308087892496642754223093⟩⟩,⟨⟨165754464703139973134330772466,165754464703139973146114422381⟩,⟨(-95698384815740185731573568098),(-95698384815740185720591760087)⟩⟩,⟨⟨(-645964097506246253675065578156),(-645964097506246253639354908989)⟩,⟨(-20099097481),9443068940⟩⟩,⟨⟨1326035717625119784992157357188,1326035717625119785226145467213⟩,⟨765587078525921485715829411774,765587078525921485945242624900⟩⟩,⟨⟨(-1495287262745940402227953599446),(-1495287262745940401669405619041)⟩,⟨(-2589913510986562080613564999416),(-2589913510986562080043057902739)⟩⟩,⟨⟨(-322303536030),151807079102⟩,⟨5167712780049970028995952630064,5167712780049970029519411267203⟩⟩]
lemma ha7_0_3_eq (j : Fin 7) : ha7_0_3 j = ((ha7_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha7_0_3_contains (j : Fin 7) : (ha7_0_3 j).Contains (fullFactor false 7 3 ((j.val:ℝ)/6)) := by
  rw [ha7_0_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_0_2 j) false 7 2 j (ha7_0_2_contains j)
noncomputable def hk7_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_4 j i k)
lemma hk7_0_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_0_4 j i k).Contains (fullFactor false 7 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_0_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power7 j i k) (mpower0_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 4 (power7_contains j i k) (mpower0_4_contains j i k)
noncomputable def ha7_0_4 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-2712151086516110563446650498),(-2712151086516110563352915544)⟩,⟨(-1565861159883012429908539559),(-1565861159883012429826429637)⟩⟩,⟨⟨25053778558128198876044439901,25053778558128198878999219170⟩,⟨43394417384257769012991635344,43394417384257769016214716400⟩⟩,⟨⟨(-3708284502),7892897124⟩,⟨(-253669507901048013644740012330),(-253669507901048013629909010218)⟩⟩,⟨⟨(-400860456930051182112501069622),(-400860456930051181991104613657)⟩,⟨694310678148124304164675119032,694310678148124304289401066477⟩⟩,⟨⟨1695094429072569101951612889505,1695094429072569102330404564269⟩,⟨(-978663224926882768823557048735),(-978663224926882768454873068619)⟩⟩,⟨⟨(-4058712126416768218409213547517),(-4058712126416768217985170813343)⟩,⟨(-253136605255),119229001118⟩⟩]
lemma ha7_0_4_eq (j : Fin 7) : ha7_0_4 j = ((ha7_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha7_0_4_contains (j : Fin 7) : (ha7_0_4 j).Contains (fullFactor false 7 4 ((j.val:ℝ)/6)) := by
  rw [ha7_0_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_0_3 j) false 7 3 j (ha7_0_3_contains j)
noncomputable def hk7_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_5 j i k)
lemma hk7_0_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_0_5 j i k).Contains (fullFactor false 7 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_0_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power7 j i k) (mpower0_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 5 (power7_contains j i k) (mpower0_5_contains j i k)
noncomputable def ha7_0_5 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨163976597214335483783884104,163976597214335483793004590⟩,⟨(-284015797627486289493198453),(-284015797627486289482478500)⟩⟩,⟨⟨(-9088505524079561264006096460),(-9088505524079561263302126330)⟩,⟨5247251110858735480837480657,5247251110858735481473030700⟩⟩,⟨⟨79692626246167045118347967274,79692626246167045123260933511⟩,⟨(-1164991935),2479626763⟩⟩,⟨⟨(-290832176770545960460747049600),(-290832176770545960407576219334)⟩,⟨(-167912035547479535427458296099),(-167912035547479535376073386925)⟩⟩,⟨⟨512426866294798386726910496523,512426866294798386921584082471⟩,⟨887549367585894654557368386693,887549367585894654758528401190⟩⟩,⟨⟨(-74913790802),159050419885⟩,⟨(-2550164039877345444003018078567),(-2550164039877345443728466746616)⟩⟩]
lemma ha7_0_5_eq (j : Fin 7) : ha7_0_5 j = ((ha7_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha7_0_5_contains (j : Fin 7) : (ha7_0_5 j).Contains (fullFactor false 7 5 ((j.val:ℝ)/6)) := by
  rw [ha7_0_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_0_4 j) false 7 4 j (ha7_0_4_contains j)
noncomputable def hk7_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_6 j i k)
lemma hk7_0_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_0_6 j i k).Contains (fullFactor false 7 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_0_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power7 j i k) (mpower0_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 6 (power7_contains j i k) (mpower0_6_contains j i k)
noncomputable def ha7_0_6 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨24785053981387676526469465,24785053981387676527483851⟩,⟨14309657588033580845426246,14309657588033580846267709⟩⟩,⟨⟨(-915818085634149174178042748),(-915818085634149174064203199)⟩,⟨(-1586243454808811297798017500),(-1586243454808811297670102363)⟩⟩,⟨⟨(-649164769),304994176⟩,⟨20863480763352960872469228682,20863480763352960873821850758⟩⟩,⟨⟨58612357480585547136364926512,58612357480585547154488212460⟩,⟨(-101519581107763923063454581561),(-101519581107763923044571313614)⟩⟩,⟨⟨(-387266468459182445782201328972),(-387266468459182445693196007107)⟩,⟨223588399813024700667143513170,223588399813024700752797593188⟩⟩,⟨⟨1335262768854589495807312034761,1335262768854589495955317049410⟩,⟨(-39224769140),83278605111⟩⟩]
lemma ha7_0_6_eq (j : Fin 7) : ha7_0_6 j = ((ha7_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha7_0_6_contains (j : Fin 7) : (ha7_0_6 j).Contains (fullFactor false 7 6 ((j.val:ℝ)/6)) := by
  rw [ha7_0_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_0_5 j) false 7 5 j (ha7_0_5_contains j)
noncomputable def hk7_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_7 j i k)
lemma hk7_0_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_0_7 j i k).Contains (fullFactor false 7 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_0_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power7 j i k) (mpower0_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 7 (power7_contains j i k) (mpower0_7_contains j i k)
noncomputable def ha7_0_7 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1070359884617898514146650),(-1070359884617898514080301)⟩,⟨1853917702541761442223466,1853917702541761442305244⟩⟩,⟨⟨237301465925345464601021765,237301465925345464620913180⟩,⟨(-137006065231091009813300812),(-137006065231091009795834350)⟩⟩,⟨⟨(-4681754135318688100869262633),(-4681754135318688100550832462)⟩,⟨(-145672234),68440534⟩⟩,⟨⟨30374587638444219467041271314,30374587638444219472787817189⟩,⟨17536776349579649252746571302,17536776349579649258224867072⟩⟩,⟨⟨(-83621865985773321428876365322),(-83621865985773321396575637638)⟩,⟨(-144837320511075112695156649878),(-144837320511075112661407705831)⟩⟩,⟨⟨(-37375350574),17604035225⟩,⟨599264529320792076856720079378,599264529320792076925052092865⟩⟩]
lemma ha7_0_7_eq (j : Fin 7) : ha7_0_7 j = ((ha7_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha7_0_7_contains (j : Fin 7) : (ha7_0_7 j).Contains (fullFactor false 7 7 ((j.val:ℝ)/6)) := by
  rw [ha7_0_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_0_6 j) false 7 6 j (ha7_0_6_contains j)
noncomputable def hk7_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_8 j i k)
lemma hk7_0_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_0_8 j i k).Contains (fullFactor false 7 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_0_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power7 j i k) (mpower0_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 8 (power7_contains j i k) (mpower0_8_contains j i k)
noncomputable def ha7_0_8 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-121338629888859693717996),(-121338629888859693712257)⟩,⟨(-70054890629433514729582),(-70054890629433514725015)⟩⟩,⟨⟨17934052001134979768760474,17934052001134979771103916⟩,⟨31062689251548081589869016,31062689251548081592571673⟩⟩,⟨⟨(-13438268),28602677⟩,⟨(-919260274839426580279957629),(-919260274839426580214507914)⟩⟩,⟨⟨(-4591117312290554821958235698),(-4591117312290554820509407238)⟩,⟨7952048448396308886511794450,7952048448396308888041548799⟩⟩,⟨⟨47397902300335817852325176903,47397902300335817863520365225⟩,⟨(-27365191652122466694897816410),(-27365191652122466684240321882)⟩⟩,⟨⟨(-235330630358893204557083089393),(-235330630358893204529500089784)⟩,⟨(-14677265849),6913088468⟩⟩]
lemma ha7_0_8_eq (j : Fin 7) : ha7_0_8 j = ((ha7_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha7_0_8_contains (j : Fin 7) : (ha7_0_8 j).Contains (fullFactor false 7 8 ((j.val:ℝ)/6)) := by
  rw [ha7_0_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_0_7 j) false 7 7 j (ha7_0_7_contains j)
noncomputable def hk7_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_9 j i k)
lemma hk7_0_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_0_9 j i k).Contains (fullFactor false 7 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_0_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power7 j i k) (mpower0_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 9 (power7_contains j i k) (mpower0_9_contains j i k)
noncomputable def ha7_0_9 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨4075628328693792152340,4075628328693792152619⟩,⟨(-7059195338064676366777),(-7059195338064676366420)⟩⟩,⟨⟨(-3614308013089114299878723),(-3614308013089114299552749)⟩,⟨2086721704291221581900036,2086721704291221582179351⟩⟩,⟨⟨160441184787359821867777126,160441184787359821879710958⟩,⟨(-2345421),4992109⟩⟩,⟨⟨(-1850525702701626521617772368),(-1850525702701626521255891959)⟩,⟨(-1068401512597105450205129260),(-1068401512597105449864570739)⟩⟩,⟨⟨7960211579480062796021345691,7960211579480062799146823325⟩,⟨13787490894657571026994144470,13787490894657571030294579694⟩⟩,⟨⟨(-2413123105),5123332286⟩,⟨(-82145886611128228804301830470),(-82145886611128228794412068776)⟩⟩]
lemma ha7_0_9_eq (j : Fin 7) : ha7_0_9 j = ((ha7_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha7_0_9_contains (j : Fin 7) : (ha7_0_9 j).Contains (fullFactor false 7 9 ((j.val:ℝ)/6)) := by
  rw [ha7_0_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_0_8 j) false 7 8 j (ha7_0_8_contains j)
noncomputable def hk7_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_10 j i k)
lemma hk7_0_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_0_10 j i k).Contains (fullFactor false 7 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_0_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power7 j i k) (mpower0_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 10 (power7_contains j i k) (mpower0_10_contains j i k)
noncomputable def ha7_0_10 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨369618603571988403182,369618603571988403202⟩,⟨213399400269781075720,213399400269781075736⟩⟩,⟨⟨(-218520985876255821557642),(-218520985876255821527696)⟩,⟨(-378489450057716124888138),(-378489450057716124852797)⟩⟩,⟨⟨(-784159),368418⟩,⟨25202042373060605480264679,25202042373060605482219463⟩⟩,⟨⟨223765489537285961230066972,223765489537285961302105650⟩,⟨(-387573196859101311902180272),(-387573196859101311825154532)⟩⟩,⟨⟨(-3609556675507699250394568203),(-3609556675507699249519026705)⟩,⟨2083978518259580817187302931,2083978518259580818012184572⟩⟩,⟨⟨25806891390014060011197327545,25806891390014060014386433701⟩,⟨(-758104982),1609542308⟩⟩]
lemma ha7_0_10_eq (j : Fin 7) : ha7_0_10 j = ((ha7_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha7_0_10_contains (j : Fin 7) : (ha7_0_10 j).Contains (fullFactor false 7 10 ((j.val:ℝ)/6)) := by
  rw [ha7_0_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_0_9 j) false 7 9 j (ha7_0_9_contains j)
noncomputable def hk7_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_11 j i k)
lemma hk7_0_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_0_11 j i k).Contains (fullFactor false 7 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_0_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power7 j i k) (mpower0_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 11 (power7_contains j i k) (mpower0_11_contains j i k)
noncomputable def ha7_0_11 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-10157787699515332861),(-10157787699515332860)⟩,⟨17593804388058740564,17593804388058740566⟩⟩,⟨⟨36032111386744300674838,36032111386744300678318⟩,⟨(-20803149208607401699624),(-20803149208607401696706)⟩⟩,⟨⟨(-3598843235212085340633535),(-3598843235212085340342936)⟩,⟨(-111978),52610⟩⟩,⟨⟨73793764120052327777478300,73793764120052327792378861⟩,⟨42604849579227958672133598,42604849579227958685985347⟩⟩,⟨⟨(-495985727515397112417654494),(-495985727515397112219754350)⟩,⟨(-859072479885680691747111795),(-859072479885680691535998892)⟩⟩,⟨⟨(-459684209),216514277⟩,⟨7370430945714350776852773209,7370430945714350777787040609⟩⟩]
lemma ha7_0_11_eq (j : Fin 7) : ha7_0_11 j = ((ha7_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha7_0_11_contains (j : Fin 7) : (ha7_0_11 j).Contains (fullFactor false 7 11 ((j.val:ℝ)/6)) := by
  rw [ha7_0_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_0_10 j) false 7 10 j (ha7_0_10_contains j)
noncomputable def hk7_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_12 j i k)
lemma hk7_0_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_0_12 j i k).Contains (fullFactor false 7 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_0_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power7 j i k) (mpower0_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 12 (power7_contains j i k) (mpower0_12_contains j i k)
noncomputable def ha7_0_12 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-767674536308627878),(-767674536308627877)⟩,⟨(-443217100187807443),(-443217100187807442)⟩⟩,⟨⟨1815417242369259285380,1815417242369259285642⟩,⟨3144394900720139784806,3144394900720139785121⟩⟩,⟨⟨(-6887),14658⟩,⟨(-471087477881817150391038),(-471087477881817150351498)⟩⟩,⟨⟨(-7435949024744486034885510),(-7435949024744486032444254)⟩,⟨12879441513349692557766258,12879441513349692560407894⟩⟩,⟨⟨187420541090973602806742515,187420541090973602853396785⟩,⟨(-108207299850538926473258575),(-108207299850538926429739026)⟩⟩,⟨⟨(-1929574309403923048046081175),(-1929574309403923047795348514)⟩,⟨(-120345045),56683306⟩⟩]
lemma ha7_0_12_eq (j : Fin 7) : ha7_0_12 j = ((ha7_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha7_0_12_contains (j : Fin 7) : (ha7_0_12 j).Contains (fullFactor false 7 12 ((j.val:ℝ)/6)) := by
  rw [ha7_0_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_0_11 j) false 7 11 j (ha7_0_11_contains j)
noncomputable def hk7_0_13 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_13 j i k)
lemma hk7_0_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_0_13 j i k).Contains (fullFactor false 7 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_0_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power7 j i k) (mpower0_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 13 (power7_contains j i k) (mpower0_13_contains j i k)
noncomputable def ha7_0_13 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨17851379306351118,17851379306351119⟩,⟨(-30919495943783800),(-30919495943783799)⟩⟩,⟨⟨(-253292510771476882298),(-253292510771476882271)⟩,⟨146238499277628361500,146238499277628361523⟩⟩,⟨⟨56921729219679268115828,56921729219679268120788⟩,⟨(-833),1772⟩⟩,⟨⟨(-2074972248239938619868189),(-2074972248239938619435996)⟩,⟨(-1197985786082331537736375),(-1197985786082331537339257)⟩⟩,⟨⟨21791234504823142510643414,21791234504823142519476926⟩,⟨37743525322001707889652133,37743525322001707899167706⟩⟩,⟨⟨(-13698143),29082701⟩,⟨(-466302805767612564456214475),(-466302805767612564394137888)⟩⟩]
lemma ha7_0_13_eq (j : Fin 7) : ha7_0_13 j = ((ha7_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha7_0_13_contains (j : Fin 7) : (ha7_0_13 j).Contains (fullFactor false 7 13 ((j.val:ℝ)/6)) := by
  rw [ha7_0_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_0_12 j) false 7 12 j (ha7_0_12_contains j)
noncomputable def hk7_0_14 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_14 j i k)
lemma hk7_0_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_0_14 j i k).Contains (fullFactor false 7 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_0_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power7 j i k) (mpower0_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 14 (power7_contains j i k) (mpower0_14_contains j i k)
noncomputable def ha7_0_14 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1156386444162983,1156386444162984⟩,⟨667640024824732,667640024824733⟩⟩,⟨⟨(-10938614166728417760),(-10938614166728417757)⟩,⟨(-18946235501166317753),(-18946235501166317750)⟩⟩,⟨⟨(-199),94⟩,⟨6386603083791852240868,6386603083791852241446⟩⟩,⟨⟨179218254507678396534178,179218254507678396594158⟩,⟨(-310415122451108950065413),(-310415122451108949999768)⟩⟩,⟨⟨(-7058022730486958382167570),(-7058022730486958380365695)⟩,⟨4074951323393142877645848,4074951323393142879310683⟩⟩,⟨⟨104638104924845707111984111,104638104924845707126247139⟩,⟨(-3073857),6526143⟩⟩]
lemma ha7_0_14_eq (j : Fin 7) : ha7_0_14 j = ((ha7_0_13 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha7_0_14_contains (j : Fin 7) : (ha7_0_14 j).Contains (fullFactor false 7 14 ((j.val:ℝ)/6)) := by
  rw [ha7_0_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_0_13 j) false 7 13 j (ha7_0_13_contains j)
noncomputable def hk7_0_15 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_15 j i k)
lemma hk7_0_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_0_15 j i k).Contains (fullFactor false 7 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_0_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power7 j i k) (mpower0_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 15 (power7_contains j i k) (mpower0_15_contains j i k)
noncomputable def ha7_0_15 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-23305033302577),(-23305033302576)⟩,⟨40365501752147,40365501752148⟩⟩,⟨⟨1322696761414360852,1322696761414360853⟩,⟨(-763659331258827444),(-763659331258827443)⟩⟩,⟨⟨(-668803510981146723287),(-668803510981146723224)⟩,⟨(-21),10⟩⟩,⟨⟨43342127478025776415965,43342127478025776425269⟩,⟨25023588966689257660258,25023588966689257668714⟩⟩,⟨⟨(-711213174517105746547409),(-711213174517105746254576)⟩,⟨(-1231857353275977869396844),(-1231857353275977869078435)⟩⟩,⟨⟨(-1366833),643788⟩,⟨21915353447830215826102743,21915353447830215829159745⟩⟩]
lemma ha7_0_15_eq (j : Fin 7) : ha7_0_15 j = ((ha7_0_14 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha7_0_15_contains (j : Fin 7) : (ha7_0_15 j).Contains (fullFactor false 7 15 ((j.val:ℝ)/6)) := by
  rw [ha7_0_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_0_14 j) false 7 14 j (ha7_0_14_contains j)
noncomputable def hk7_0_16 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_16 j i k)
lemma hk7_0_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_0_16 j i k).Contains (fullFactor false 7 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_0_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power7 j i k) (mpower0_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 16 (power7_contains j i k) (mpower0_16_contains j i k)
noncomputable def ha7_0_16 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1320957955865),(-1320957955864)⟩,⟨(-762655431407),(-762655431406)⟩⟩,⟨⟨49981386352667221,49981386352667222⟩,⟨86570300595549323,86570300595549324⟩⟩,⟨⟨(-1),3⟩,⟨(-65659631149794723627),(-65659631149794723619)⟩⟩,⟨⟨(-3275580136008399050036),(-3275580136008399048918)⟩,⟨5673471219829920494167,5673471219829920495404⟩⟩,⟨⟨201562188089707223572750,201562188089707223625492⟩,⟨(-116371983552042445709292),(-116371983552042445661006)⟩⟩,⟨⟨(-4303069587032947007656439),(-4303069587032947007042500)⟩,⟨(-268378),126408⟩⟩]
lemma ha7_0_16_eq (j : Fin 7) : ha7_0_16 j = ((ha7_0_15 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha7_0_16_contains (j : Fin 7) : (ha7_0_16 j).Contains (fullFactor false 7 16 ((j.val:ℝ)/6)) := by
  rw [ha7_0_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_0_15 j) false 7 15 j (ha7_0_15_contains j)
noncomputable def hk7_0_17 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_17 j i k)
lemma hk7_0_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_0_17 j i k).Contains (fullFactor false 7 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_0_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power7 j i k) (mpower0_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 17 (power7_contains j i k) (mpower0_17_contains j i k)
noncomputable def ha7_0_17 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨23489732358,23489732359⟩,⟨(-40685409901),(-40685409900)⟩⟩,⟨⟨(-5332718046471331),(-5332718046471330)⟩,⟨3078846199642597,3078846199642598⟩⟩,⟨⟨6066935731106195666,6066935731106195668⟩,⟨(-1),1⟩⟩,⟨⟨(-698970019787090239296),(-698970019787090239141)⟩,⟨(-403550529079554596791),(-403550529079554596651)⟩⟩,⟨⟨17921243559351411739114,17921243559351411746608⟩,⟨31040504379613153635377,31040504379613153643599⟩⟩,⟨⟨(-23361),49597⟩,⟨(-795205400147551278546455),(-795205400147551278430467)⟩⟩]
lemma ha7_0_17_eq (j : Fin 7) : ha7_0_17 j = ((ha7_0_16 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha7_0_17_contains (j : Fin 7) : (ha7_0_17 j).Contains (fullFactor false 7 17 ((j.val:ℝ)/6)) := by
  rw [ha7_0_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_0_16 j) false 7 16 j (ha7_0_16_contains j)
noncomputable def hk7_0_18 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_18 j i k)
lemma hk7_0_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_0_18 j i k).Contains (fullFactor false 7 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_0_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power7 j i k) (mpower0_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 18 (power7_contains j i k) (mpower0_18_contains j i k)
noncomputable def ha7_0_18 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1183490600,1183490601⟩,⟨683288616,683288617⟩⟩,⟨⟨(-179120011154260),(-179120011154259)⟩,⟨(-310244959971483),(-310244959971482)⟩⟩,⟨⟨(-1),1⟩,⟨529440020073462376,529440020073462377⟩⟩,⟨⟨46955236204022331362,46955236204022331379⟩,⟨(-81328854786764263392),(-81328854786764263373)⟩⟩,⟨⟨(-4514658357533078058829),(-4514658357533078057617)⟩,⟨2606539218020916335225,2606539218020916336325⟩⟩,⟨⟨138789524622137721136212,138789524622137721156898⟩,⟨(-4078),8657⟩⟩]
lemma ha7_0_18_eq (j : Fin 7) : ha7_0_18 j = ((ha7_0_17 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha7_0_18_contains (j : Fin 7) : (ha7_0_18 j).Contains (fullFactor false 7 18 ((j.val:ℝ)/6)) := by
  rw [ha7_0_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_0_17 j) false 7 17 j (ha7_0_17_contains j)
noncomputable def hk7_0_19 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_19 j i k)
lemma hk7_0_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_0_19 j i k).Contains (fullFactor false 7 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_0_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power7 j i k) (mpower0_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 19 (power7_contains j i k) (mpower0_19_contains j i k)
noncomputable def ha7_0_19 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-18829952),(-18829951)⟩,⟨32614433,32614434⟩⟩,⟨⟨17099355913327,17099355913328⟩,⟨(-9872317739529),(-9872317739528)⟩⟩,⟨⟨(-43770654673137423),(-43770654673137422)⟩,⟨(-1),1⟩⟩,⟨⟨8964987113086656143,8964987113086656147⟩,⟨5175937723022106879,5175937723022106882⟩⟩,⟨⟨(-359152827132815577594),(-359152827132815577440)⟩,⟨(-622070944276038605587),(-622070944276038605417)⟩⟩,⟨⟨(-1432),675⟩,⟨22948428997269873108784,22948428997269873112278⟩⟩]
lemma ha7_0_19_eq (j : Fin 7) : ha7_0_19 j = ((ha7_0_18 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha7_0_19_contains (j : Fin 7) : (ha7_0_19 j).Contains (fullFactor false 7 19 ((j.val:ℝ)/6)) := by
  rw [ha7_0_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_0_18 j) false 7 18 j (ha7_0_18_contains j)
noncomputable def hk7_0_20 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_20 j i k)
lemma hk7_0_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_0_20 j i k).Contains (fullFactor false 7 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_0_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power7 j i k) (mpower0_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 20 (power7_contains j i k) (mpower0_20_contains j i k)
noncomputable def ha7_0_20 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-853844),(-853843)⟩,⟨(-492967),(-492966)⟩⟩,⟨⟨516913348073,516913348074⟩,⟨895320181973,895320181974⟩⟩,⟨⟨(-1),1⟩,⟨(-3437739179098608),(-3437739179098606)⟩⟩,⟨⟨(-542022930869484434),(-542022930869484433)⟩,⟨938811255133340262,938811255133340263⟩⟩,⟨⟨81428896189552855145,81428896189552855169⟩,⟨(-47012995134852432617),(-47012995134852432596)⟩⟩,⟨⟨(-3604730797462500934194),(-3604730797462500933633)⟩,⟨(-225),107⟩⟩]
lemma ha7_0_20_eq (j : Fin 7) : ha7_0_20 j = ((ha7_0_19 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha7_0_20_contains (j : Fin 7) : (ha7_0_20 j).Contains (fullFactor false 7 20 ((j.val:ℝ)/6)) := by
  rw [ha7_0_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_0_19 j) false 7 19 j (ha7_0_19_contains j)
noncomputable def hk7_0_21 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_21 j i k)
lemma hk7_0_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_0_21 j i k).Contains (fullFactor false 7 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_0_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power7 j i k) (mpower0_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 21 (power7_contains j i k) (mpower0_21_contains j i k)
noncomputable def ha7_0_21 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨12291,12292⟩,⟨(-21290),(-21289)⟩⟩,⟨⟨(-44646528672),(-44646528671)⟩,⟨25776685346,25776685347⟩⟩,⟨⟨257142289286047,257142289286048⟩,⟨(-1),1⟩⟩,⟨⟨(-93630556896327456),(-93630556896327455)⟩,⟨(-54057627228469228),(-54057627228469227)⟩⟩,⟨⟨5860939688051789410,5860939688051789413⟩,⟨10151445319802585613,10151445319802585617⟩⟩,⟨⟨(-17),34⟩,⟨(-539266466260812848987),(-539266466260812848900)⟩⟩]
lemma ha7_0_21_eq (j : Fin 7) : ha7_0_21 j = ((ha7_0_20 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha7_0_21_contains (j : Fin 7) : (ha7_0_21 j).Contains (fullFactor false 7 21 ((j.val:ℝ)/6)) := by
  rw [ha7_0_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_0_20 j) false 7 20 j (ha7_0_20_contains j)
noncomputable def hk7_0_22 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_22 j i k)
lemma hk7_0_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_0_22 j i k).Contains (fullFactor false 7 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_0_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power7 j i k) (mpower0_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 22 (power7_contains j i k) (mpower0_22_contains j i k)
noncomputable def ha7_0_22 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨506,507⟩,⟨292,293⟩⟩,⟨⟨(-1226967354),(-1226967353)⟩,⟨(-2125169796),(-2125169795)⟩⟩,⟨⟨(-1),1⟩,⟨18359916521552,18359916521553⟩⟩,⟨⟨5146274077922863,5146274077922864⟩,⟨(-8913608172637076),(-8913608172637075)⟩⟩,⟨⟨(-1208019168182208038),(-1208019168182208037)⟩,⟨697450191936225609,697450191936225610⟩⟩,⟨⟨77007071306013533792,77007071306013533806⟩,⟨(-3),5⟩⟩]
lemma ha7_0_22_eq (j : Fin 7) : ha7_0_22 j = ((ha7_0_21 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha7_0_22_contains (j : Fin 7) : (ha7_0_22 j).Contains (fullFactor false 7 22 ((j.val:ℝ)/6)) := by
  rw [ha7_0_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_0_21 j) false 7 21 j (ha7_0_21_contains j)
noncomputable def hk7_0_23 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_23 j i k)
lemma hk7_0_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_0_23 j i k).Contains (fullFactor false 7 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_0_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power7 j i k) (mpower0_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 23 (power7_contains j i k) (mpower0_23_contains j i k)
noncomputable def ha7_0_23 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-7),(-6)⟩,⟨11,12⟩⟩,⟨⟨96759678,96759679⟩,⟨(-55864227),(-55864226)⟩⟩,⟨⟨(-1253899540536),(-1253899540535)⟩,⟨(-1),1⟩⟩,⟨⟨811679013105350,811679013105351⟩,⟨468623096711943,468623096711944⟩⟩,⟨⟨(-79387840551870929),(-79387840551870928)⟩,⟨(-137503773339017308),(-137503773339017306)⟩⟩,⟨⟨(-1),1⟩,⟨10518471716932064454,10518471716932064457⟩⟩]
lemma ha7_0_23_eq (j : Fin 7) : ha7_0_23 j = ((ha7_0_22 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha7_0_23_contains (j : Fin 7) : (ha7_0_23 j).Contains (fullFactor false 7 23 ((j.val:ℝ)/6)) := by
  rw [ha7_0_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_0_22 j) false 7 22 j (ha7_0_22_contains j)
noncomputable def hk7_0_24 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_24 j i k)
lemma hk7_0_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_0_24 j i k).Contains (fullFactor false 7 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_0_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power7 j i k) (mpower0_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 24 (power7_contains j i k) (mpower0_24_contains j i k)
noncomputable def ha7_0_24 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),0⟩⟩,⟨⟨2437536,2437537⟩,⟨4221937,4221938⟩⟩,⟨⟨(-1),1⟩,⟨(-82067533019),(-82067533018)⟩⟩,⟨⟨(-40895079942577),(-40895079942576)⟩,⟨70832356240132,70832356240133⟩⟩,⟨⟨14999334866761557,14999334866761558⟩,⟨(-8659870022990125),(-8659870022990124)⟩⟩,⟨⟨(-1376864728037741371),(-1376864728037741370)⟩,⟨(-1),1⟩⟩]
lemma ha7_0_24_eq (j : Fin 7) : ha7_0_24 j = ((ha7_0_23 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha7_0_24_contains (j : Fin 7) : (ha7_0_24 j).Contains (fullFactor false 7 24 ((j.val:ℝ)/6)) := by
  rw [ha7_0_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_0_23 j) false 7 23 j (ha7_0_23_contains j)
noncomputable def hk7_0_25 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_25 j i k)
lemma hk7_0_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_0_25 j i k).Contains (fullFactor false 7 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_0_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power7 j i k) (mpower0_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 25 (power7_contains j i k) (mpower0_25_contains j i k)
noncomputable def ha7_0_25 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨(-1),0⟩⟩,⟨⟨(-176849),(-176848)⟩,⟨102103,102104⟩⟩,⟨⟨5156455176,5156455177⟩,⟨(-1),1⟩⟩,⟨⟨(-5934037600013),(-5934037600012)⟩,⟨(-3426018205749),(-3426018205748)⟩⟩,⟨⟨906859468175608,906859468175609⟩,⟨1570726674205044,1570726674205046⟩⟩,⟨⟨(-1),1⟩,⟨(-173021924583611077),(-173021924583611076)⟩⟩]
lemma ha7_0_25_eq (j : Fin 7) : ha7_0_25 j = ((ha7_0_24 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha7_0_25_contains (j : Fin 7) : (ha7_0_25 j).Contains (fullFactor false 7 25 ((j.val:ℝ)/6)) := by
  rw [ha7_0_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_0_24 j) false 7 24 j (ha7_0_24_contains j)
noncomputable def hk7_0_26 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_26 j i k)
lemma hk7_0_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_0_26 j i k).Contains (fullFactor false 7 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_0_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power7 j i k) (mpower0_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 26 (power7_contains j i k) (mpower0_26_contains j i k)
noncomputable def ha7_0_26 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨0,1⟩⟩,⟨⟨(-4113),(-4112)⟩,⟨(-7123),(-7122)⟩⟩,⟨⟨(-1),1⟩,⟨311528494,311528495⟩⟩,⟨⟨275978298108,275978298109⟩,⟨(-478008434111),(-478008434110)⟩⟩,⟨⟨(-158159723733337),(-158159723733336)⟩,⟨91313559072398,91313559072399⟩⟩,⟨⟨20906323353147684,20906323353147685⟩,⟨(-1),1⟩⟩]
lemma ha7_0_26_eq (j : Fin 7) : ha7_0_26 j = ((ha7_0_25 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha7_0_26_contains (j : Fin 7) : (ha7_0_26 j).Contains (fullFactor false 7 26 ((j.val:ℝ)/6)) := by
  rw [ha7_0_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_0_25 j) false 7 25 j (ha7_0_25_contains j)
noncomputable def hk7_0_27 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_27 j i k)
lemma hk7_0_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_0_27 j i k).Contains (fullFactor false 7 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_0_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power7 j i k) (mpower0_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 27 (power7_contains j i k) (mpower0_27_contains j i k)
noncomputable def ha7_0_27 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨0,1⟩⟩,⟨⟨276,277⟩,⟨(-160),(-159)⟩⟩,⟨⟨(-18123994),(-18123993)⟩,⟨(-1),1⟩⟩,⟨⟨37079204566,37079204567⟩,⟨21407688737,21407688739⟩⟩,⟨⟨(-8854012541821),(-8854012541820)⟩,⟨(-15335599573286),(-15335599573285)⟩⟩,⟨⟨(-1),1⟩,⟨2432561179993388,2432561179993389⟩⟩]
lemma ha7_0_27_eq (j : Fin 7) : ha7_0_27 j = ((ha7_0_26 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha7_0_27_contains (j : Fin 7) : (ha7_0_27 j).Contains (fullFactor false 7 27 ((j.val:ℝ)/6)) := by
  rw [ha7_0_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_0_26 j) false 7 26 j (ha7_0_26_contains j)
noncomputable def hk7_0_28 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_28 j i k)
lemma hk7_0_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_0_28 j i k).Contains (fullFactor false 7 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_0_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power7 j i k) (mpower0_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 28 (power7_contains j i k) (mpower0_28_contains j i k)
noncomputable def ha7_0_28 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),0⟩⟩,⟨⟨5,6⟩,⟨10,11⟩⟩,⟨⟨(-1),1⟩,⟨(-1016754),(-1016753)⟩⟩,⟨⟨(-1601291374),(-1601291373)⟩,⟨2773518015,2773518016⟩⟩,⟨⟨1433875207078,1433875207079⟩,⟨(-827848236791),(-827848236790)⟩⟩,⟨⟨(-272932726159820),(-272932726159819)⟩,⟨(-1),1⟩⟩]
lemma ha7_0_28_eq (j : Fin 7) : ha7_0_28 j = ((ha7_0_27 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha7_0_28_contains (j : Fin 7) : (ha7_0_28 j).Contains (fullFactor false 7 28 ((j.val:ℝ)/6)) := by
  rw [ha7_0_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_0_27 j) false 7 27 j (ha7_0_27_contains j)
noncomputable def hk7_0_29 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_29 j i k)
lemma hk7_0_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_0_29 j i k).Contains (fullFactor false 7 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_0_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power7 j i k) (mpower0_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 29 (power7_contains j i k) (mpower0_29_contains j i k)
noncomputable def ha7_0_29 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨(-1),0⟩⟩,⟨⟨(-1),0⟩,⟨0,1⟩⟩,⟨⟨55072,55073⟩,⟨(-1),1⟩⟩,⟨⟨(-200304916),(-200304915)⟩,⟨(-115646097),(-115646096)⟩⟩,⟨⟨74734538476,74734538477⟩,⟨129444017721,129444017722⟩⟩,⟨⟨(-1),1⟩,⟨(-29567015428550),(-29567015428549)⟩⟩]
lemma ha7_0_29_eq (j : Fin 7) : ha7_0_29 j = ((ha7_0_28 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha7_0_29_contains (j : Fin 7) : (ha7_0_29 j).Contains (fullFactor false 7 29 ((j.val:ℝ)/6)) := by
  rw [ha7_0_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_0_28 j) false 7 28 j (ha7_0_28_contains j)
noncomputable def hk7_0_30 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_30 j i k)
lemma hk7_0_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_0_30 j i k).Contains (fullFactor false 7 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_0_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power7 j i k) (mpower0_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 30 (power7_contains j i k) (mpower0_30_contains j i k)
noncomputable def ha7_0_30 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨0,1⟩⟩,⟨⟨(-1),0⟩,⟨(-1),0⟩⟩,⟨⟨(-1),1⟩,⟨2883,2884⟩⟩,⟨⟨8073620,8073621⟩,⟨(-13983922),(-13983921)⟩⟩,⟨⟨(-11296121532),(-11296121531)⟩,⟨6521818806,6521818807⟩⟩,⟨⟨3096250615296,3096250615297⟩,⟨(-1),1⟩⟩]
lemma ha7_0_30_eq (j : Fin 7) : ha7_0_30 j = ((ha7_0_29 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha7_0_30_contains (j : Fin 7) : (ha7_0_30 j).Contains (fullFactor false 7 30 ((j.val:ℝ)/6)) := by
  rw [ha7_0_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_0_29 j) false 7 29 j (ha7_0_29_contains j)
noncomputable def hk7_1_0 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_0 j i k)
lemma hk7_1_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_1_0 j i k).Contains (fullFactor true 7 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_1_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel7_0 j i k) (mpower1_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 0 (kernel7_0_contains j i k) (mpower1_0_contains j i k)
noncomputable def ha7_1_0 : Fin 7 → CBox := ![⟨⟨277,281⟩,⟨(-3),3⟩⟩,⟨⟨11580277,11580282⟩,⟨(-6288733),(-6288728)⟩⟩,⟨⟨(-1665710323167166),(-1665710323167162)⟩,⟨1710986465904294,1710986465904298⟩⟩,⟨⟨(-4288482058811659370282),(-4288482058811659363575)⟩,⟨1347241831520230599839,1347241831520230606532⟩⟩,⟨⟨36521831631557482951131335,36521831631557482985427878⟩,⟨3899877544961305718935797,3899877544961305753146455⟩⟩,⟨⟨(-6285013554969111273878743515),(-6285013554969111268462701209)⟩,⟨(-6478261771340776764017300108),(-6478261771340776758509615976)⟩⟩,⟨⟨144338024383918188411416917775,144338024383918188519066263138⟩,⟨249223963933666164018182252952,249223963933666164130533379093⟩⟩]
lemma ha7_1_0_eq (j : Fin 7) : ha7_1_0 j = atomKernel7_0 j := by fin_cases j <;> decide +kernel
lemma ha7_1_0_contains (j : Fin 7) : (ha7_1_0 j).Contains (fullFactor true 7 0 ((j.val:ℝ)/6)) := by
  rw [ha7_1_0_eq]
  simpa only [fullFactor,ite_true] using atomKernel7_0_contains j
noncomputable def hk7_1_1 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_1 j i k)
lemma hk7_1_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_1_1 j i k).Contains (fullFactor true 7 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_1_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel7_0 j i k) (mpower1_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 1 (kernel7_0_contains j i k) (mpower1_1_contains j i k)
noncomputable def ha7_1_1 : Fin 7 → CBox := ![⟨⟨(-2590),(-2552)⟩,⟨(-28),28⟩⟩,⟨⟨(-112157738),(-112157680)⟩,⟨5156952,5157010⟩⟩,⟨⟨17013040262490527,17013040262490568⟩,⟨154541955914585,154541955914626⟩⟩,⟨⟨19018440239828876646774,19018440239828876700006⟩,⟨18094092713122343905337,18094092713122343958622⟩⟩,⟨⟨(-37326201238580442081012481),(-37326201238580441870754607)⟩,⟨(-174640172189637644844922541),(-174640172189637644634075644)⟩⟩,⟨⟨(-22039050446094185125438974516),(-22039050446094185099025575597)⟩,⟨30238813374675442746566322808,30238813374675442772667801795⟩⟩,⟨⟨872851388260399717489646974695,872851388260399717918514409563⟩,⟨(-568005984018613276009284490086),(-568005984018613275597655333954)⟩⟩]
lemma ha7_1_1_eq (j : Fin 7) : ha7_1_1 j = ((ha7_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha7_1_1_contains (j : Fin 7) : (ha7_1_1 j).Contains (fullFactor true 7 1 ((j.val:ℝ)/6)) := by
  rw [ha7_1_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_1_0 j) true 7 0 j (ha7_1_0_contains j)
noncomputable def hk7_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_2 j i k)
lemma hk7_1_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_1_2 j i k).Contains (fullFactor true 7 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_1_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel7_0 j i k) (mpower1_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 2 (kernel7_0_contains j i k) (mpower1_2_contains j i k)
noncomputable def ha7_1_2 : Fin 7 → CBox := ![⟨⟨11758,11934⟩,⟨(-130),130⟩⟩,⟨⟨439499681,439500012⟩,⟨188725927,188726259⟩⟩,⟨⟨(-41484279155020408),(-41484279155020201)⟩,⟨(-44190317894108296),(-44190317894108088)⟩⟩,⟨⟨19303878288826371350227,19303878288826371561881⟩,⟨(-74178794327358818574522),(-74178794327358818362925)⟩⟩,⟨⟨(-375136604371051098279313533),(-375136604371051097631576384)⟩,⟨218544379473940161253409543,218544379473940161899553849⟩⟩,⟨⟨69528359364234200487201722872,69528359364234200550040717819⟩,⟨34369348452773435290199474044,34369348452773435353521645191⟩⟩,⟨⟨(-1107491315550409323350028402780),(-1107491315550409322563036409571)⟩,⟨(-1522616351064340442050391577779),(-1522616351064340441232233210732)⟩⟩]
lemma ha7_1_2_eq (j : Fin 7) : ha7_1_2 j = ((ha7_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha7_1_2_contains (j : Fin 7) : (ha7_1_2 j).Contains (fullFactor true 7 2 ((j.val:ℝ)/6)) := by
  rw [ha7_1_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_1_1 j) true 7 1 j (ha7_1_1_contains j)
noncomputable def hk7_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_3 j i k)
lemma hk7_1_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_1_3 j i k).Contains (fullFactor true 7 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_1_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel7_0 j i k) (mpower1_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 3 (kernel7_0_contains j i k) (mpower1_3_contains j i k)
noncomputable def ha7_1_3 : Fin 7 → CBox := ![⟨⟨(-36659),(-36117)⟩,⟨(-400),400⟩⟩,⟨⟨(-889217078),(-889215820)⟩,⟨(-1026939618),(-1026938358)⟩⟩,⟨⟨(-7779041811418171),(-7779041811417473)⟩,⟨143741122215489835,143741122215490532⟩⟩,⟨⟨(-144518613669232090619019),(-144518613669232090058600)⟩,⟨37105144403422090830809,37105144403422091391139⟩⟩,⟨⟨526046115865125922880711395,526046115865125924204629981⟩,⟨467318140978446544546627701,467318140978446545872710517⟩⟩,⟨⟨30479929787426174545204233849,30479929787426174646387715494⟩,⟨(-102750145435817668478464673229),(-102750145435817668377699602285)⟩⟩,⟨⟨(-1763416643883276281730794609174),(-1763416643883276280690684416015)⟩,⟨1428362252364027510308178570036,1428362252364027511311217495084⟩⟩]
lemma ha7_1_3_eq (j : Fin 7) : ha7_1_3 j = ((ha7_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha7_1_3_contains (j : Fin 7) : (ha7_1_3 j).Contains (fullFactor true 7 3 ((j.val:ℝ)/6)) := by
  rw [ha7_1_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_1_2 j) true 7 2 j (ha7_1_2_contains j)
noncomputable def hk7_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_4 j i k)
lemma hk7_1_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_1_4 j i k).Contains (fullFactor true 7 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_1_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel7_0 j i k) (mpower1_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 4 (kernel7_0_contains j i k) (mpower1_4_contains j i k)
noncomputable def ha7_1_4 : Fin 7 → CBox := ![⟨⟨83207,84457⟩,⟨(-922),922⟩⟩,⟨⟨749728448,749732031⟩,⟨2794681554,2794685139⟩⟩,⟨⟨194647269111047915,194647269111049673⟩,⟨(-166913166642253874),(-166913166642252116)⟩⟩,⟨⟨149632342188558044724599,149632342188558045837152⟩,⟨158308638628646215385936,158308638628646216498734⟩⟩,⟨⟨340464346142019281650974645,340464346142019283686501293⟩,⟨(-784620233569081777198723064),(-784620233569081775164731109)⟩⟩,⟨⟨(-110307982544932220283105104068),(-110307982544932220162024187620)⟩,⟨(-13038022856820289467269434243),(-13038022856820289346029300623)⟩⟩,⟨⟨1372243985896886756732468287720,1372243985896886757691162439894⟩,⟨1524883761778648221965611354551,1524883761778648222956944320623⟩⟩]
lemma ha7_1_4_eq (j : Fin 7) : ha7_1_4 j = ((ha7_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha7_1_4_contains (j : Fin 7) : (ha7_1_4 j).Contains (fullFactor true 7 4 ((j.val:ℝ)/6)) := by
  rw [ha7_1_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_1_3 j) true 7 3 j (ha7_1_3_contains j)
noncomputable def hk7_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_5 j i k)
lemma hk7_1_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_1_5 j i k).Contains (fullFactor true 7 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_1_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel7_0 j i k) (mpower1_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 5 (kernel7_0_contains j i k) (mpower1_5_contains j i k)
noncomputable def ha7_1_5 : Fin 7 → CBox := ![⟨⟨(-155660),(-153356)⟩,⟨(-1700),1700⟩⟩,⟨⟨928523998,928532158⟩,⟨(-4842419529),(-4842411367)⟩⟩,⟨⟨(-363596557980772762),(-363596557980769219)⟩,⟨(-36131695871066267),(-36131695871062724)⟩⟩,⟨⟨77045461404964505837792,77045461404964507605177⟩,⟨(-242475096860821541124888),(-242475096860821539357627)⟩⟩,⟨⟨(-828172369504533420075376004),(-828172369504533417576425987)⟩,⟨(-76792452832817874009329675),(-76792452832817871510304588)⟩⟩,⟨⟨4885256920971816311270025270,4885256920971816427469340976⟩,⟨91964701854872144180252186875,91964701854872144296553204634⟩⟩,⟨⟨1049744822777194244616056091486,1049744822777194245371674883732⟩,⟨(-1048308260563840941893130561981),(-1048308260563840941160190600637)⟩⟩]
lemma ha7_1_5_eq (j : Fin 7) : ha7_1_5 j = ((ha7_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha7_1_5_contains (j : Fin 7) : (ha7_1_5 j).Contains (fullFactor true 7 5 ((j.val:ℝ)/6)) := by
  rw [ha7_1_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_1_4 j) true 7 4 j (ha7_1_4_contains j)
noncomputable def hk7_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_6 j i k)
lemma hk7_1_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_1_6 j i k).Contains (fullFactor true 7 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_1_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel7_0 j i k) (mpower1_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 6 (kernel7_0_contains j i k) (mpower1_6_contains j i k)
noncomputable def ha7_1_6 : Fin 7 → CBox := ![⟨⟨235537,239077⟩,⟨(-2612),2612⟩⟩,⟨⟨(-4186964016),(-4186948531)⟩,⟨5611813994,5611829480⟩⟩,⟨⟨267350061473778404,267350061473784354⟩,⟨341745589792223843,341745589792229792⟩⟩,⟨⟨(-242778093589932093607397),(-242778093589932091268400)⟩,⟨48771942283650417681477,48771942283650420020322⟩⟩,⟨⟨150032674119139377215873122,150032674119139379772105283⟩,⟨657085889853306493999368376,657085889853306496556799260⟩⟩,⟨⟨62043720185150139784281893939,62043720185150139877310344356⟩,⟨(-14121487248646576838199996656),(-14121487248646576745385047107)⟩⟩,⟨⟨(-663763755268325022031952601049),(-663763755268325021565081382038)⟩,⟨(-598968588470563277351838747229),(-598968588470563276872025691161)⟩⟩]
lemma ha7_1_6_eq (j : Fin 7) : ha7_1_6 j = ((ha7_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha7_1_6_contains (j : Fin 7) : (ha7_1_6 j).Contains (fullFactor true 7 6 ((j.val:ℝ)/6)) := by
  rw [ha7_1_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_1_5 j) true 7 5 j (ha7_1_5_contains j)
noncomputable def hk7_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_7 j i k)
lemma hk7_1_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_1_7 j i k).Contains (fullFactor true 7 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_1_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel7_0 j i k) (mpower1_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 7 (kernel7_0_contains j i k) (mpower1_7_contains j i k)
noncomputable def ha7_1_7 : Fin 7 → CBox := ![⟨⟨(-314740),(-310079)⟩,⟨(-3439),3439⟩⟩,⟨⟨7566007723,7566032908⟩,⟨(-3922154335),(-3922129150)⟩⟩,⟨⟨63390225935340755,63390225935349318⟩,⟨(-437070469377547907),(-437070469377539344)⟩⟩,⟨⟨133742821482412655429906,133742821482412658082734⟩,⟨157450667224983875645000,157450667224983878298079⟩⟩,⟨⟨401196675837523625366129355,401196675837523627608885453⟩,⟨(-241266954166986591946317479),(-241266954166986589704808877)⟩⟩,⟨⟨(-14484022936717885888904846818),(-14484022936717885825330606751)⟩,⟨(-34788732812174303747469273787),(-34788732812174303683718235869)⟩⟩,⟨⟨(-291179146097228615848248274597),(-291179146097228615587167582797)⟩,⟨358476934937305768743017939854,358476934937305768997870469575⟩⟩]
lemma ha7_1_7_eq (j : Fin 7) : ha7_1_7 j = ((ha7_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha7_1_7_contains (j : Fin 7) : (ha7_1_7 j).Contains (fullFactor true 7 7 ((j.val:ℝ)/6)) := by
  rw [ha7_1_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_1_6 j) true 7 6 j (ha7_1_6_contains j)
noncomputable def hk7_1_8 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_8 j i k)
lemma hk7_1_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_1_8 j i k).Contains (fullFactor true 7 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_1_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel7_0 j i k) (mpower1_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 8 (kernel7_0_contains j i k) (mpower1_8_contains j i k)
noncomputable def ha7_1_8 : Fin 7 → CBox := ![⟨⟨357185,362555⟩,⟨(-3962),3962⟩⟩,⟨⟨(-9073121367),(-9073085527)⟩,⟨242310390,242346229⟩⟩,⟨⟨(-320385493444403813),(-320385493444393030)⟩,⟨228183365380930082,228183365380940866⟩⟩,⟨⟨53226461707993327765929,53226461707993330398919⟩,⟨(-141097412922479145014608),(-141097412922479142381712)⟩⟩,⟨⟨(-215325836843105898887925551),(-215325836843105897167950089)⟩,⟨(-185989858912664168745506467),(-185989858912664167024849318)⟩⟩,⟨⟨(-16490137753801682392558006351),(-16490137753801682354345208757)⟩,⟨10459175159529297712199182093,10459175159529297750309945710⟩⟩,⟨⟨168643153897388135464408527846,168643153897388135586108225428⟩,⟨123017882756181088672612154228,123017882756181088796885259150⟩⟩]
lemma ha7_1_8_eq (j : Fin 7) : ha7_1_8 j = ((ha7_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha7_1_8_contains (j : Fin 7) : (ha7_1_8 j).Contains (fullFactor true 7 8 ((j.val:ℝ)/6)) := by
  rw [ha7_1_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_1_7 j) true 7 7 j (ha7_1_7_contains j)
noncomputable def hk7_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_9 j i k)
lemma hk7_1_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_1_9 j i k).Contains (fullFactor true 7 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_1_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel7_0 j i k) (mpower1_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 9 (kernel7_0_contains j i k) (mpower1_9_contains j i k)
noncomputable def ha7_1_9 : Fin 7 → CBox := ![⟨⟨(-371230),(-365731)⟩,⟨(-4057),4057⟩⟩,⟨⟨7828581515,7828626849⟩,⟨3541621127,3541666462⟩⟩,⟨⟨305845716852972509,305845716852984580⟩,⟨58506982200543103,58506982200555174⟩⟩,⟨⟨(-96821713263816682697368),(-96821713263816680374736)⟩,⟨14156467757521802447882,14156467757521804770467⟩⟩,⟨⟨(-59219526858756957466242106),(-59219526858756956292956868)⟩,⟨141849330385344226557594473,141849330385344227730676769⟩⟩,⟨⟨6038101547372975081393483072,6038101547372975101702393775⟩,⟨6666738299054809562328396232,6666738299054809582682849307⟩⟩,⟨⟨45839343023263364660937449513,45839343023263364713506357850⟩,⟨(-70230477822739578962511054968),(-70230477822739578910865731681)⟩⟩]
lemma ha7_1_9_eq (j : Fin 7) : ha7_1_9 j = ((ha7_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha7_1_9_contains (j : Fin 7) : (ha7_1_9 j).Contains (fullFactor true 7 9 ((j.val:ℝ)/6)) := by
  rw [ha7_1_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_1_8 j) true 7 8 j (ha7_1_8_contains j)
noncomputable def hk7_1_10 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_10 j i k)
lemma hk7_1_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_1_10 j i k).Contains (fullFactor true 7 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_1_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel7_0 j i k) (mpower1_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 10 (kernel7_0_contains j i k) (mpower1_10_contains j i k)
noncomputable def ha7_1_10 : Fin 7 → CBox := ![⟨⟨337033,342102⟩,⟨(-3739),3739⟩⟩,⟨⟨(-4684879573),(-4684827963)⟩,⟨(-5625697589),(-5625645978)⟩⟩,⟨⟨(-120452536855020786),(-120452536855008625)⟩,⟨(-186321366888812213),(-186321366888800052)⟩⟩,⟨⟨34631945259166303059628,34631945259166304903483⟩,⟨45452986563879102202105,45452986563879104046030⟩⟩,⟨⟨74508106627733545159539919,74508106627733545879534376⟩,⟨5864127566591063651919831,5864127566591064371895636⟩⟩,⟨⟨2298293422876451474481525882,2298293422876451484237312371⟩,⟨(-2936284969602183650368921914),(-2936284969602183640629209801)⟩⟩,⟨⟨(-26221149130684761893762896237),(-26221149130684761874043066986)⟩,⟨(-15233964887539507149728298387),(-15233964887539507129718880562)⟩⟩]
lemma ha7_1_10_eq (j : Fin 7) : ha7_1_10 j = ((ha7_1_9 j).mul (piI.mul (atomPoints j).z)).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha7_1_10_contains (j : Fin 7) : (ha7_1_10 j).Contains (fullFactor true 7 10 ((j.val:ℝ)/6)) := by
  rw [ha7_1_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_1_9 j) true 7 9 j (ha7_1_9_contains j)
noncomputable def hk7_1_11 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_11 j i k)
lemma hk7_1_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_1_11 j i k).Contains (fullFactor true 7 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_1_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel7_0 j i k) (mpower1_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 11 (kernel7_0_contains j i k) (mpower1_11_contains j i k)
noncomputable def ha7_1_11 : Fin 7 → CBox := ![⟨⟨(-286599),(-282352)⟩,⟨(-3133),3133⟩⟩,⟨⟨1363582239,1363635652⟩,⟨5504093977,5504147391⟩⟩,⟨⟨(-33320893584189246),(-33320893584178108)⟩,⟨139791866686725267,139791866686736405⟩⟩,⟨⟨12198058413958445163197,12198058413958446493964⟩,⟨(-27776462180406639934431),(-27776462180406638603685)⟩⟩,⟨⟨(-7801284948270583706723856),(-7801284948270583305108008)⟩,⟨(-32101171930717794057200283),(-32101171930717793655517501)⟩⟩,⟨⟨(-1237662998952027813606004586),(-1237662998952027809360187084)⟩,⟨(-665560792861892017989286652),(-665560792861892013739152674)⟩⟩,⟨⟨(-4553328251086897706469672325),(-4553328251086897699547112077)⟩,⟨8867798632265419853053210884,8867798632265419859896533638⟩⟩]
lemma ha7_1_11_eq (j : Fin 7) : ha7_1_11 j = ((ha7_1_10 j).mul (piI.mul (atomPoints j).z)).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha7_1_11_contains (j : Fin 7) : (ha7_1_11 j).Contains (fullFactor true 7 11 ((j.val:ℝ)/6)) := by
  rw [ha7_1_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_1_10 j) true 7 10 j (ha7_1_10_contains j)
noncomputable def hk7_1_12 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_12 j i k)
lemma hk7_1_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_1_12 j i k).Contains (fullFactor true 7 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_1_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel7_0 j i k) (mpower1_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 12 (kernel7_0_contains j i k) (mpower1_12_contains j i k)
noncomputable def ha7_1_12 : Fin 7 → CBox := ![⟨⟨216830,220093⟩,⟨(-2406),2406⟩⟩,⟨⟨834126081,834176754⟩,⟨(-3938822158),(-3938771485)⟩⟩,⟨⟨73667189375947624,73667189375956975⟩,⟨(-43055326018758034),(-43055326018748683)⟩⟩,⟨⟨(-14700859991494403187726),(-14700859991494402307355)⟩,⟨1357994560641981661355,1357994560641982541720⟩⟩,⟨⟨(-11373778333217441510141343),(-11373778333217441304735427)⟩,⟨7057214193658567375976018,7057214193658567581344606⟩⟩,⟨⟨(-153943382177754593196847554),(-153943382177754591499777909)⟩,⟨460414797121216966334844993,460414797121216968031211556⟩⟩,⟨⟨2739737123654648210043501434,2739737123654648212219829707⟩,⟨1231420882096958716568538643,1231420882096958718763553342⟩⟩]
lemma ha7_1_12_eq (j : Fin 7) : ha7_1_12 j = ((ha7_1_11 j).mul (piI.mul (atomPoints j).z)).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha7_1_12_contains (j : Fin 7) : (ha7_1_12 j).Contains (fullFactor true 7 12 ((j.val:ℝ)/6)) := by
  rw [ha7_1_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_1_11 j) true 7 11 j (ha7_1_11_contains j)
noncomputable def hk7_1_13 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_13 j i k)
lemma hk7_1_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_1_13 j i k).Contains (fullFactor true 7 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_1_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel7_0 j i k) (mpower1_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 13 (kernel7_0_contains j i k) (mpower1_13_contains j i k)
noncomputable def ha7_1_13 : Fin 7 → CBox := ![⟨⟨(-156018),(-153704)⟩,⟨(-1706),1706⟩⟩,⟨⟨(-1618383412),(-1618339037)⟩,⟨2084167184,2084211560⟩⟩,⟨⟨(-44957323534751221),(-44957323534743974)⟩,⟨(-12877874660291348),(-12877874660284101)⟩⟩,⟨⟨3733866760879634870529,3733866760879635408126⟩,⟨5481000942258830565008,5481000942258831102614⟩⟩,⟨⟨3833813981777287978766181,3833813981777288075706373⟩,⟨3219425994578671820227985,3219425994578671917180373⟩⟩,⟨⟨153027218940144285249788926,153027218940144285875307897⟩,⟨23433217586417430921087699,23433217586417431546535813⟩⟩,⟨⟨302480249302383148706622916,302480249302383149348984725⟩,⟨(-778806932437459144399584224),(-778806932437459143760878793)⟩⟩]
lemma ha7_1_13_eq (j : Fin 7) : ha7_1_13 j = ((ha7_1_12 j).mul (piI.mul (atomPoints j).z)).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha7_1_13_contains (j : Fin 7) : (ha7_1_13 j).Contains (fullFactor true 7 13 ((j.val:ℝ)/6)) := by
  rw [ha7_1_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_1_12 j) true 7 12 j (ha7_1_12_contains j)
noncomputable def hk7_1_14 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_14 j i k)
lemma hk7_1_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_1_14 j i k).Contains (fullFactor true 7 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_1_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel7_0 j i k) (mpower1_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 14 (kernel7_0_contains j i k) (mpower1_14_contains j i k)
noncomputable def ha7_1_14 : Fin 7 → CBox := ![⟨⟨101173,102698⟩,⟨(-1123),1123⟩⟩,⟨⟨1439657347,1439693432⟩,⟨(-711520333),(-711484248)⟩⟩,⟨⟨11073314593928576,11073314593933791⟩,⟨21067274492463644,21067274492468860⟩⟩,⟨⟨1245121083504391105990,1245121083504391410831⟩,⟨(-2470343140142409891908),(-2470343140142409587069)⟩⟩,⟨⟨647437038833958222495958,647437038833958264987657⟩,⟨(-1613625510281335584602570),(-1613625510281335542113142)⟩⟩,⟨⟨(-860443580586065515550567),(-860443580586065301525948)⟩,⟨(-45833258892538462191726829),(-45833258892538461977585477)⟩⟩,⟨⟨(-204934988786672549194147568),(-204934988786672549020138069)⟩,⟨(-67573204754830807099436572),(-67573204754830806924903760)⟩⟩]
lemma ha7_1_14_eq (j : Fin 7) : ha7_1_14 j = ((ha7_1_13 j).mul (piI.mul (atomPoints j).z)).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha7_1_14_contains (j : Fin 7) : (ha7_1_14 j).Contains (fullFactor true 7 14 ((j.val:ℝ)/6)) := by
  rw [ha7_1_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_1_13 j) true 7 13 j (ha7_1_13_contains j)
noncomputable def hk7_1_15 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_15 j i k)
lemma hk7_1_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_1_15 j i k).Contains (fullFactor true 7 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_1_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel7_0 j i k) (mpower1_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 15 (kernel7_0_contains j i k) (mpower1_15_contains j i k)
noncomputable def ha7_1_15 : Fin 7 → CBox := ![⟨⟨(-63094),(-62156)⟩,⟨(-690),690⟩⟩,⟨⟨(-912156951),(-912129564)⟩,⟨6788092,6815479⟩⟩,⟨⟨3598646570904566,3598646570908070⟩,⟨(-10716995364559133),(-10716995364555629)⟩⟩,⟨⟨(-1076192227721879930534),(-1076192227721879769203)⟩,⟨42040815412579300994,42040815412579462325⟩⟩,⟨⟨(-562402021437243974695334),(-562402021437243957314159)⟩,⟨(-36395619301407600146359),(-36395619301407582765350)⟩⟩,⟨⟨(-12442427749089766406831498),(-12442427749089766338420339)⟩,⟨2386384123518979546184723,2386384123518979614537304⟩⟩,⟨⟨(-13701818112263452726919974),(-13701818112263452682665569)⟩,⟨50180935201904712119062198,50180935201904712163296960⟩⟩]
lemma ha7_1_15_eq (j : Fin 7) : ha7_1_15 j = ((ha7_1_14 j).mul (piI.mul (atomPoints j).z)).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha7_1_15_contains (j : Fin 7) : (ha7_1_15 j).Contains (fullFactor true 7 15 ((j.val:ℝ)/6)) := by
  rw [ha7_1_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_1_14 j) true 7 14 j (ha7_1_14_contains j)
noncomputable def hk7_1_16 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_16 j i k)
lemma hk7_1_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_1_16 j i k).Contains (fullFactor true 7 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_1_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel7_0 j i k) (mpower1_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 16 (kernel7_0_contains j i k) (mpower1_16_contains j i k)
noncomputable def ha7_1_16 : Fin 7 → CBox := ![⟨⟨35799,36340⟩,⟨(-398),398⟩⟩,⟨⟨438614493,438633980⟩,⟨208682626,208702113⟩⟩,⟨⟨(-4557015813951268),(-4557015813949061)⟩,⟨2139502170487275,2139502170489482⟩⟩,⟨⟨203772929399466450193,203772929399466530237⟩,⟨336157315216055962143,336157315216056042189⟩⟩,⟨⟨42755760395473508208579,42755760395473514873705⟩,⟨165840224987454521349628,165840224987454528015111⟩⟩,⟨⟨1157021883919423492581753,1157021883919423513049365⟩,⟨3071891152119813664069209,3071891152119813684555964⟩⟩,⟨⟨11486093749923091518386099,11486093749923091528925328⟩,⟨2503436216847760679686219,2503436216847760690204808⟩⟩]
lemma ha7_1_16_eq (j : Fin 7) : ha7_1_16 j = ((ha7_1_15 j).mul (piI.mul (atomPoints j).z)).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha7_1_16_contains (j : Fin 7) : (ha7_1_16 j).Contains (fullFactor true 7 16 ((j.val:ℝ)/6)) := by
  rw [ha7_1_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_1_15 j) true 7 15 j (ha7_1_15_contains j)
noncomputable def hk7_1_17 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_17 j i k)
lemma hk7_1_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_1_17 j i k).Contains (fullFactor true 7 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_1_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel7_0 j i k) (mpower1_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 17 (kernel7_0_contains j i k) (mpower1_17_contains j i k)
noncomputable def ha7_1_17 : Fin 7 → CBox := ![⟨⟨(-19700),(-19405)⟩,⟨(-216),216⟩⟩,⟨⟨(-152165636),(-152152585)⟩,⟨(-190043445),(-190030394)⟩⟩,⟨⟨1967966736623697,1967966736625006⟩,⟨760905173721916,760905173723225⟩⟩,⟨⟨67088887602124617893,67088887602124655273⟩,⟨(-117191196458426122863),(-117191196458426085484)⟩⟩,⟨⟨41258225306742928710560,41258225306742931116275⟩,⟨(-26402247457947417461548),(-26402247457947415055969)⟩⟩,⟨⟨690275789034642324571523,690275789034642330345197⟩,⟨(-405313254733281895063885),(-405313254733281889295230)⟩⟩,⟨⟨404893589244965806058790,404893589244965808411587⟩,⟨(-2467450719285744467170038),(-2467450719285744464807328)⟩⟩]
lemma ha7_1_17_eq (j : Fin 7) : ha7_1_17 j = ((ha7_1_16 j).mul (piI.mul (atomPoints j).z)).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha7_1_17_contains (j : Fin 7) : (ha7_1_17 j).Contains (fullFactor true 7 17 ((j.val:ℝ)/6)) := by
  rw [ha7_1_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_1_16 j) true 7 16 j (ha7_1_16_contains j)
noncomputable def hk7_1_18 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_18 j i k)
lemma hk7_1_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_1_18 j i k).Contains (fullFactor true 7 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_1_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel7_0 j i k) (mpower1_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 18 (kernel7_0_contains j i k) (mpower1_18_contains j i k)
noncomputable def ha7_1_18 : Fin 7 → CBox := ![⟨⟨9934,10086⟩,⟨(-111),111⟩⟩,⟨⟨25548973,25557228⟩,⟨112361045,112369300⟩⟩,⟨⟨(-320588665335719),(-320588665334986)⟩,⟨(-771204368448841),(-771204368448107)⟩⟩,⟨⟨(-43805902594443855879),(-43805902594443839393)⟩,⟨(-614402655677971652),(-614402655677955166)⟩⟩,⟨⟨(-10249945339865937616028),(-10249945339865936796035)⟩,⟨(-8366874390679063830784),(-8366874390679063010760)⟩⟩,⟨⟨(-118999408281338401750395),(-118999408281338400214843)⟩,⟨(-140806487750863024077613),(-140806487750863022540949)⟩⟩,⟨⟨(-499225390199664147324569),(-499225390199664146824446)⟩,⟨(-55486655345583314930012),(-55486655345583314433023)⟩⟩]
lemma ha7_1_18_eq (j : Fin 7) : ha7_1_18 j = ((ha7_1_17 j).mul (piI.mul (atomPoints j).z)).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha7_1_18_contains (j : Fin 7) : (ha7_1_18 j).Contains (fullFactor true 7 18 ((j.val:ℝ)/6)) := by
  rw [ha7_1_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_1_17 j) true 7 17 j (ha7_1_17_contains j)
noncomputable def hk7_1_19 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_19 j i k)
lemma hk7_1_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_1_19 j i k).Contains (fullFactor true 7 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_1_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel7_0 j i k) (mpower1_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 19 (kernel7_0_contains j i k) (mpower1_19_contains j i k)
noncomputable def ha7_1_19 : Fin 7 → CBox := ![⟨⟨(-4892),(-4818)⟩,⟨(-54),54⟩⟩,⟨⟨11674483,11679430⟩,⟨(-50340373),(-50335426)⟩⟩,⟨⟨(-125967728931120),(-125967728930730)⟩,⟨286744204928975,286744204929365⟩⟩,⟨⟨6359558777380443354,6359558777380450243⟩,⟨11869031593002625851,11869031593002632740⟩⟩,⟨⟨(-1216976233902185923116),(-1216976233902185658312)⟩,⟨3159654413818806958844,3159654413818807223644⟩⟩,⟨⟨(-25864437049687863275066),(-25864437049687862887627)⟩,⟨30806238410682156261245,30806238410682156648474⟩⟩,⟨⟨(-5611712174981349323778),(-5611712174981349224331)⟩,⟨95428147290663788361678,95428147290663788461944⟩⟩]
lemma ha7_1_19_eq (j : Fin 7) : ha7_1_19 j = ((ha7_1_18 j).mul (piI.mul (atomPoints j).z)).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha7_1_19_contains (j : Fin 7) : (ha7_1_19 j).Contains (fullFactor true 7 19 ((j.val:ℝ)/6)) := by
  rw [ha7_1_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_1_18 j) true 7 18 j (ha7_1_18_contains j)
noncomputable def hk7_1_20 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_20 j i k)
lemma hk7_1_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_1_20 j i k).Contains (fullFactor true 7 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_1_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel7_0 j i k) (mpower1_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 20 (kernel7_0_contains j i k) (mpower1_20_contains j i k)
noncomputable def ha7_1_20 : Fin 7 → CBox := ![⟨⟨2219,2255⟩,⟨(-25),25⟩⟩,⟨⟨(-13834786),(-13831969)⟩,⟨17123021,17125838⟩⟩,⟨⟨104849200870767,104849200870965⟩,⟨(-38152255935253),(-38152255935056)⟩⟩,⟨⟨2131643671622914318,2131643671622917053⟩,⟨(-3303781149326288314),(-3303781149326285579)⟩⟩,⟨⟨822086102487532792311,822086102487532873547⟩,⟨41720716843997142859,41720716843997224094⟩⟩,⟨⟨7203452851685605566556,7203452851685605659321⟩,⟨4198344666592872661321,4198344666592872754119⟩⟩,⟨⟨17282362734980985230268,17282362734980985249361⟩,⟨117258775076553700322,117258775076553719226⟩⟩]
lemma ha7_1_20_eq (j : Fin 7) : ha7_1_20 j = ((ha7_1_19 j).mul (piI.mul (atomPoints j).z)).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha7_1_20_contains (j : Fin 7) : (ha7_1_20 j).Contains (fullFactor true 7 20 ((j.val:ℝ)/6)) := by
  rw [ha7_1_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_1_19 j) true 7 19 j (ha7_1_19_contains j)
noncomputable def hk7_1_21 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_21 j i k)
lemma hk7_1_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_1_21 j i k).Contains (fullFactor true 7 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_1_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel7_0 j i k) (mpower1_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 21 (kernel7_0_contains j i k) (mpower1_21_contains j i k)
noncomputable def ha7_1_21 : Fin 7 → CBox := ![⟨⟨(-990),(-973)⟩,⟨(-11),11⟩⟩,⟨⟨8080955,8082483⟩,⟨(-3803108),(-3801580)⟩⟩,⟨⟨(-33939033026593),(-33939033026497)⟩,⟨(-16768807298512),(-16768807298416)⟩⟩,⟨⟨(-1090912695822704559),(-1090912695822703524)⟩,⟨(-73303564630663250),(-73303564630662215)⟩⟩,⟨⟨(-50143058193538875695),(-50143058193538851960)⟩,⟨(-183869079508829723858),(-183869079508829700123)⟩⟩,⟨⟨575145367005792410747,575145367005792431916⟩,⟨(-1542150128297189283688),(-1542150128297189262524)⟩⟩,⟨⟨(-134368701231792829333),(-134368701231792825910)⟩,⟨(-2972813329437353085587),(-2972813329437353082125)⟩⟩]
lemma ha7_1_21_eq (j : Fin 7) : ha7_1_21 j = ((ha7_1_20 j).mul (piI.mul (atomPoints j).z)).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha7_1_21_contains (j : Fin 7) : (ha7_1_21 j).Contains (fullFactor true 7 21 ((j.val:ℝ)/6)) := by
  rw [ha7_1_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_1_20 j) true 7 20 j (ha7_1_20_contains j)
noncomputable def hk7_1_22 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_22 j i k)
lemma hk7_1_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_1_22 j i k).Contains (fullFactor true 7 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_1_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel7_0 j i k) (mpower1_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 22 (kernel7_0_contains j i k) (mpower1_22_contains j i k)
noncomputable def ha7_1_22 : Fin 7 → CBox := ![⟨⟨407,415⟩,⟨(-5),5⟩⟩,⟨⟨(-3459164),(-3458372)⟩,⟨(-41172),(-40380)⟩⟩,⟨⟨3669929945392,3669929945437⟩,⟨11697870724601,11697870724646⟩⟩,⟨⟨123309733489684010,123309733489684384⟩,⟨262733476550927036,262733476550927411⟩⟩,⟨⟨(-35158570632451282424),(-35158570632451275803)⟩,⟨23194890177468411341,23194890177468417961⟩⟩,⟨⟨(-304782617676364542090),(-304782617676364537480)⟩,⟨(-57431590279822282217),(-57431590279822277607)⟩⟩,⟨⟨(-486803430855369266820),(-486803430855369266220)⟩,⟨47428364028600870493,47428364028600871086⟩⟩]
lemma ha7_1_22_eq (j : Fin 7) : ha7_1_22 j = ((ha7_1_21 j).mul (piI.mul (atomPoints j).z)).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha7_1_22_contains (j : Fin 7) : (ha7_1_22 j).Contains (fullFactor true 7 22 ((j.val:ℝ)/6)) := by
  rw [ha7_1_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_1_21 j) true 7 21 j (ha7_1_21_contains j)
noncomputable def hk7_1_23 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_23 j i k)
lemma hk7_1_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_1_23 j i k).Contains (fullFactor true 7 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_1_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel7_0 j i k) (mpower1_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 23 (kernel7_0_contains j i k) (mpower1_23_contains j i k)
noncomputable def ha7_1_23 : Fin 7 → CBox := ![⟨⟨(-167),(-163)⟩,⟨(-3),3⟩⟩,⟨⟨1146069,1146462⟩,⟨572491,572884⟩⟩,⟨⟨1833771523401,1833771523422⟩,⟨(-3325899652088),(-3325899652068)⟩⟩,⟨⟨43180493454018387,43180493454018517⟩,⟨(-59714486883557486),(-59714486883557355)⟩⟩,⟨⟨6975561262603222506,6975561262603224273⟩,⟨5534073473824407673,5534073473824409440⟩⟩,⟨⟨(-868048496691271892),(-868048496691270931)⟩,⟨55894633865618370793,55894633865618371754⟩⟩,⟨⟨11420598714350161078,11420598714350161177⟩,⟨76041481804963775571,76041481804963775671⟩⟩]
lemma ha7_1_23_eq (j : Fin 7) : ha7_1_23 j = ((ha7_1_22 j).mul (piI.mul (atomPoints j).z)).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha7_1_23_contains (j : Fin 7) : (ha7_1_23 j).Contains (fullFactor true 7 23 ((j.val:ℝ)/6)) := by
  rw [ha7_1_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_1_22 j) true 7 22 j (ha7_1_22_contains j)
noncomputable def hk7_1_24 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_24 j i k)
lemma hk7_1_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_1_24 j i k).Contains (fullFactor true 7 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_1_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel7_0 j i k) (mpower1_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 24 (kernel7_0_contains j i k) (mpower1_24_contains j i k)
noncomputable def ha7_1_24 : Fin 7 → CBox := ![⟨⟨62,65⟩,⟨(-2),2⟩⟩,⟨⟨(-277525),(-277338)⟩,⟨(-360594),(-360407)⟩⟩,⟨⟨(-1089897724145),(-1089897724136)⟩,⟨288792308946,288792308955⟩⟩,⟨⟨(-17801609210552986),(-17801609210552942)⟩,⟨(-2149451241318045),(-2149451241318001)⟩⟩,⟨⟨624870744370813799,624870744370814252⟩,⟨(-1692212985058327630),(-1692212985058327177)⟩⟩,⟨⟨9539895718000562382,9539895718000562575⟩,⟨(-1492526545415293276),(-1492526545415293083)⟩⟩,⟨⟨11351803611948513116,11351803611948513133⟩,⟨(-2313276809010556638),(-2313276809010556622)⟩⟩]
lemma ha7_1_24_eq (j : Fin 7) : ha7_1_24 j = ((ha7_1_23 j).mul (piI.mul (atomPoints j).z)).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha7_1_24_contains (j : Fin 7) : (ha7_1_24 j).Contains (fullFactor true 7 24 ((j.val:ℝ)/6)) := by
  rw [ha7_1_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_1_23 j) true 7 23 j (ha7_1_23_contains j)
noncomputable def hk7_1_25 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_25 j i k)
lemma hk7_1_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_1_25 j i k).Contains (fullFactor true 7 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_1_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel7_0 j i k) (mpower1_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 25 (kernel7_0_contains j i k) (mpower1_25_contains j i k)
noncomputable def ha7_1_25 : Fin 7 → CBox := ![⟨⟨(-24),(-22)⟩,⟨(-1),1⟩⟩,⟨⟨31419,31506⟩,⟨151762,151848⟩⟩,⟨⟨274139398914,274139398918⟩,⟨167650273450,167650273454⟩⟩,⟨⟨1575933267302100,1575933267302115⟩,⟨3880741505352921,3880741505352936⟩⟩,⟨⟨(-350596305039699786),(-350596305039699673)⟩,⟨(-12903608623957017),(-12903608623956904)⟩⟩,⟨⟨(-512656375610894045),(-512656375610894007)⟩,⟨(-1516884168816044951),(-1516884168816044913)⟩⟩,⟨⟨(-419394761203970734),(-419394761203970731)⟩,⟨(-1622291467309809393),(-1622291467309809389)⟩⟩]
lemma ha7_1_25_eq (j : Fin 7) : ha7_1_25 j = ((ha7_1_24 j).mul (piI.mul (atomPoints j).z)).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha7_1_25_contains (j : Fin 7) : (ha7_1_25 j).Contains (fullFactor true 7 25 ((j.val:ℝ)/6)) := by
  rw [ha7_1_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_1_24 j) true 7 24 j (ha7_1_24_contains j)
noncomputable def hk7_1_26 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_26 j i k)
lemma hk7_1_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_1_26 j i k).Contains (fullFactor true 7 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_1_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel7_0 j i k) (mpower1_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 26 (kernel7_0_contains j i k) (mpower1_26_contains j i k)
noncomputable def ha7_1_26 : Fin 7 → CBox := ![⟨⟨7,9⟩,⟨(-1),1⟩⟩,⟨⟨12411,12450⟩,⟨(-49279),(-49240)⟩⟩,⟨⟨(-18704359654),(-18704359651)⟩,⟨(-86049740164),(-86049740161)⟩⟩,⟨⟨590924830262043,590924830262048⟩,⟨(-732029215957015),(-732029215957009)⟩⟩,⟨⟨18140917000270885,18140917000270912⟩,⟨63050181086165834,63050181086165862⟩⟩,⟨⟨(-224455939157093426),(-224455939157093418)⟩,⟨121642393118367865,121642393118367873⟩⟩,⟨⟨(-222284060373243878),(-222284060373243877)⟩,⟨69964173583019409,69964173583019411⟩⟩]
lemma ha7_1_26_eq (j : Fin 7) : ha7_1_26 j = ((ha7_1_25 j).mul (piI.mul (atomPoints j).z)).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha7_1_26_contains (j : Fin 7) : (ha7_1_26 j).Contains (fullFactor true 7 26 ((j.val:ℝ)/6)) := by
  rw [ha7_1_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_1_25 j) true 7 25 j (ha7_1_25_contains j)
noncomputable def hk7_1_27 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_27 j i k)
lemma hk7_1_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_1_27 j i k).Contains (fullFactor true 7 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_1_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel7_0 j i k) (mpower1_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 27 (kernel7_0_contains j i k) (mpower1_27_contains j i k)
noncomputable def ha7_1_27 : Fin 7 → CBox := ![⟨⟨(-4),(-2)⟩,⟨(-1),1⟩⟩,⟨⟨(-10321),(-10304)⟩,⟨12266,12284⟩⟩,⟨⟨(-13002869323),(-13002869321)⟩,⟨19259262186,19259262188⟩⟩,⟨⟨(-200434097895347),(-200434097895344)⟩,⟨(-35073199112424),(-35073199112421)⟩⟩,⟨⟨9770414805577701,9770414805577708⟩,⟨(-6642753316426649),(-6642753316426642)⟩⟩,⟨⟨24260393898442428,24260393898442431⟩,⟨30788726254122220,30788726254122222⟩⟩,⟨⟨10903017634695057,10903017634695058⟩,⟨29242078608942635,29242078608942636⟩⟩]
lemma ha7_1_27_eq (j : Fin 7) : ha7_1_27 j = ((ha7_1_26 j).mul (piI.mul (atomPoints j).z)).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha7_1_27_contains (j : Fin 7) : (ha7_1_27 j).Contains (fullFactor true 7 27 ((j.val:ℝ)/6)) := by
  rw [ha7_1_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_1_26 j) true 7 26 j (ha7_1_26_contains j)
noncomputable def hk7_1_28 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_28 j i k)
lemma hk7_1_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_1_28 j i k).Contains (fullFactor true 7 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_1_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel7_0 j i k) (mpower1_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 28 (kernel7_0_contains j i k) (mpower1_28_contains j i k)
noncomputable def ha7_1_28 : Fin 7 → CBox := ![⟨⟨0,2⟩,⟨(-1),1⟩⟩,⟨⟨4449,4457⟩,⟨(-1996),(-1987)⟩⟩,⟨⟨5828869303,5828869305⟩,⟨(-994896287),(-994896286)⟩⟩,⟨⟨13859366068567,13859366068568⟩,⟨40111798482218,40111798482220⟩⟩,⟨⟨(-1624825346939808),(-1624825346939806)⟩,⟨(-1252609704288943),(-1252609704288940)⟩⟩,⟨⟨3881940849023714,3881940849023716⟩,⟨(-4314126645352071),(-4314126645352070)⟩⟩,⟨⟨3698093253209658,3698093253209659⟩,⟨(-1602212991316196),(-1602212991316195)⟩⟩]
lemma ha7_1_28_eq (j : Fin 7) : ha7_1_28 j = ((ha7_1_27 j).mul (piI.mul (atomPoints j).z)).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha7_1_28_contains (j : Fin 7) : (ha7_1_28 j).Contains (fullFactor true 7 28 ((j.val:ℝ)/6)) := by
  rw [ha7_1_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_1_27 j) true 7 27 j (ha7_1_27_contains j)
noncomputable def hk7_1_29 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_29 j i k)
lemma hk7_1_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_1_29 j i k).Contains (fullFactor true 7 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_1_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel7_0 j i k) (mpower1_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 29 (kernel7_0_contains j i k) (mpower1_29_contains j i k)
noncomputable def ha7_1_29 : Fin 7 → CBox := ![⟨⟨(-1),0⟩,⟨(-1),1⟩⟩,⟨⟨(-1435),(-1430)⟩,⟨(-47),(-42)⟩⟩,⟨⟨(-1166295467),(-1166295465)⟩,⟨(-866246395),(-866246393)⟩⟩,⟨⟨5713120496780,5713120496781⟩,⟨(-6355635247484),(-6355635247483)⟩⟩,⟨⟨(-114650128314549),(-114650128314548)⟩,⟨324304336268259,324304336268260⟩⟩,⟨⟨(-702019137489121),(-702019137489120)⟩,⟨(-442083325703484),(-442083325703482)⟩⟩,⟨⟨(-223449524297539),(-223449524297538)⟩,⟨(-450105452528624),(-450105452528623)⟩⟩]
lemma ha7_1_29_eq (j : Fin 7) : ha7_1_29 j = ((ha7_1_28 j).mul (piI.mul (atomPoints j).z)).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha7_1_29_contains (j : Fin 7) : (ha7_1_29 j).Contains (fullFactor true 7 29 ((j.val:ℝ)/6)) := by
  rw [ha7_1_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_1_28 j) true 7 28 j (ha7_1_28_contains j)
noncomputable def hk7_1_30 (j : Fin 6) (i k : Fin 16) : CBox := (kernel7_0 j i k).mul (mpower1_30 j i k)
lemma hk7_1_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_1_30 j i k).Contains (fullFactor true 7 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_1_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel7_0 j i k) (mpower1_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 30 (kernel7_0_contains j i k) (mpower1_30_contains j i k)
noncomputable def ha7_1_30 : Fin 7 → CBox := ![⟨⟨0,1⟩,⟨(-1),1⟩⟩,⟨⟨359,362⟩,⟨187,190⟩⟩,⟨⟨42700264,42700266⟩,⟨342386735,342386737⟩⟩,⟨⟨(-1621147628829),(-1621147628828)⟩,⟨(-373261829943),(-373261829942)⟩⟩,⟨⟨55733944736529,55733944736530⟩,⟨1274856145689,1274856145691⟩⟩,⟨⟨(-43720188151538),(-43720188151537)⟩,⟨105977250480059,105977250480060⟩⟩,⟨⟨(-52779488085733),(-52779488085731)⟩,⟨29713328701054,29713328701055⟩⟩]
lemma ha7_1_30_eq (j : Fin 7) : ha7_1_30 j = ((ha7_1_29 j).mul (piI.mul (atomPoints j).z)).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha7_1_30_contains (j : Fin 7) : (ha7_1_30 j).Contains (fullFactor true 7 30 ((j.val:ℝ)/6)) := by
  rw [ha7_1_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha7_1_29 j) true 7 29 j (ha7_1_29_contains j)
end SharpPlanar.CachedData

end OAI
