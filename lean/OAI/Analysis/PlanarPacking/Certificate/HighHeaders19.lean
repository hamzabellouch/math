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
noncomputable def hk19_0_0 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_0 j i k)
lemma hk19_0_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_0_0 j i k).Contains (fullFactor false 19 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_0_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power19 j i k) (mpower0_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 0 (power19_contains j i k) (mpower0_0_contains j i k)
noncomputable def ha19_0_0 : Fin 7 → CBox := ![⟨⟨999999999999999999999999999773,1000000000000000000000000000303⟩,⟨(-303),303⟩⟩,⟨⟨(-866025403784438646812202266006),(-866025403784438646707781455940)⟩,⟨(-500000000000000000059187675620),(-499999999999999999953737960674)⟩⟩,⟨⟨499999999999999999843899897497,500000000000000000130248829862⟩,⟨866025403784438646627634776787,866025403784438646914736803947⟩⟩,⟨⟨(-39678965475),84454683117⟩,⟨(-1000000000000000000062066824296),(-999999999999999999937933175723)⟩⟩,⟨⟨(-500000000000000000418039296860),(-499999999999999999633663248451)⟩,⟨866025403784438646356885182472,866025403784438647140710680530⟩⟩,⟨⟨866025403784438646288804563125,866025403784438647275954876385⟩,⟨(-500000000000000000460987851192),(-499999999999999999474383967179)⟩⟩,⟨⟨(-1000000000000000000124510757933),(-999999999999999999875489242143)⟩,⟨(-169286475613),79735040177⟩⟩]
lemma ha19_0_0_eq (j : Fin 7) : ha19_0_0 j = ((atomPoints j).direct.powBin 7 19).conj := by fin_cases j <;> decide +kernel
lemma ha19_0_0_contains (j : Fin 7) : (ha19_0_0 j).Contains (fullFactor false 19 0 ((j.val:ℝ)/6)) := by
  rw [ha19_0_0_eq]
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @direct_factor_zero_full ((atomPoints j).direct.powBin 7 19) ((j.val:ℝ)/6) 19 (@direct_power_bin_contains (atomPoints j) ((j.val:ℝ)/6) (atomPoints_contains j) 19 (by norm_num))
noncomputable def hk19_0_1 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_1 j i k)
lemma hk19_0_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_0_1 j i k).Contains (fullFactor false 19 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_0_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power19 j i k) (mpower0_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 1 (power19_contains j i k) (mpower0_1_contains j i k)
noncomputable def ha19_0_1 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨261799387799149436514110586184,261799387799149436570157261153⟩,⟨(-453449841058554462674964995490),(-453449841058554462618847011515)⟩⟩,⟨⟨(-906899682117108925457303908024),(-906899682117108925153764616888)⟩,⟨523598775598298872913199021583,523598775598298873214729589013⟩⟩,⟨⟨1570796326794896619132505660409,1570796326794896619332494339620⟩,⟨(-62327573220),132661106021⟩⟩,⟨⟨(-1813799364234217851387886396428),(-1813799364234217849740472609468)⟩,⟨(-1047197551196597747032206122619),(-1047197551196597745386079435061)⟩⟩,⟨⟨1308996938995747181315607110566,1308996938995747183902696705584⟩,⟨2267249205292772311997356117177,2267249205292772314588926472318⟩⟩,⟨⟨(-250495016454),531829148138⟩,⟨(-3141592653589793238861162082416),(-3141592653589793238068837917823)⟩⟩]
lemma ha19_0_1_eq (j : Fin 7) : ha19_0_1 j = ((ha19_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha19_0_1_contains (j : Fin 7) : (ha19_0_1 j).Contains (fullFactor false 19 1 ((j.val:ℝ)/6)) := by
  rw [ha19_0_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_0_0 j) false 19 0 j (ha19_0_0_contains j)
noncomputable def hk19_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_2 j i k)
lemma hk19_0_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_0_2 j i k).Contains (fullFactor false 19 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_0_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power19 j i k) (mpower0_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 2 (power19_contains j i k) (mpower0_2_contains j i k)
noncomputable def ha19_0_2 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨118712890786751174400069168474,118712890786751174415138697193⟩,⟨68538919452009434846560458881,68538919452009434861451610234⟩⟩,⟨⟨(-274155677808037739484770078748),(-274155677808037739326016378208)⟩,⟨(-474851563147004697716775640264),(-474851563147004697556331339607)⟩⟩,⟨⟨(-104191789024),48951961537⟩,⟨1233700550136169827275663391355,1233700550136169827436661123525⟩⟩,⟨⟨1096622711232150956842964944681,1096622711232150958570275439358⟩,⟨(-1899406252588018791362718731460),(-1899406252588018789631505050062)⟩⟩,⟨⟨(-2967822269668779361967722570210),(-2967822269668779358565918036445)⟩,⟨1713472986300235869521291234592,1713472986300235872913237749294⟩⟩,⟨⟨4934802200544679308794505104581,4934802200544679310054792955223⟩,⟨(-393476651727),835395272378⟩⟩]
lemma ha19_0_2_eq (j : Fin 7) : ha19_0_2 j = ((ha19_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha19_0_2_contains (j : Fin 7) : (ha19_0_2 j).Contains (fullFactor false 19 2 ((j.val:ℝ)/6)) := by
  rw [ha19_0_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_0_1 j) false 19 1 j (ha19_0_1_contains j)
noncomputable def hk19_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_3 j i k)
lemma hk19_0_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_0_3 j i k).Contains (fullFactor false 19 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_0_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power19 j i k) (mpower0_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 3 (power19_contains j i k) (mpower0_3_contains j i k)
noncomputable def ha19_0_3 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-11962298101967523217347420776),(-11962298101967523214710347392)⟩,⟨20719308087892496641024736376,20719308087892496643720816912⟩⟩,⟨⟨165754464703139973112858075529,165754464703139973169391314629⟩,⟨(-95698384815740185752380241574),(-95698384815740185696660128669)⟩⟩,⟨⟨(-645964097506246253700387435088),(-645964097506246253614033052065)⟩,⟨(-54554693161),25631187124⟩⟩,⟨⟨1326035717625119784488299822384,1326035717625119785701135877010⟩,⟨765587078525921485251372105477,765587078525921486459699258293⟩⟩,⟨⟨(-1495287262745940403370040966345),(-1495287262745940400405249582503)⟩,⟨(-2589913510986562081851988856631),(-2589913510986562078875110424704)⟩⟩,⟨⟨(-874823883516),412047786142⟩,⟨5167712780049970028589572102926,5167712780049970029925791794590⟩⟩]
lemma ha19_0_3_eq (j : Fin 7) : ha19_0_3 j = ((ha19_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha19_0_3_contains (j : Fin 7) : (ha19_0_3 j).Contains (fullFactor false 19 3 ((j.val:ℝ)/6)) := by
  rw [ha19_0_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_0_2 j) false 19 2 j (ha19_0_2_contains j)
noncomputable def hk19_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_4 j i k)
lemma hk19_0_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_0_4 j i k).Contains (fullFactor false 19 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_0_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power19 j i k) (mpower0_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 4 (power19_contains j i k) (mpower0_4_contains j i k)
noncomputable def ha19_0_4 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-2712151086516110563573177333),(-2712151086516110563211628170)⟩,⟨(-1565861159883012430055355794),(-1565861159883012429705179404)⟩⟩,⟨⟨25053778558128198869779153447,25053778558128198884446393549⟩,⟨43394417384257769007370096432,43394417384257769022308592540⟩⟩,⟨⟨(-10065343647),21423577907⟩,⟨(-253669507901048013654683882294),(-253669507901048013619965140257)⟩⟩,⟨⟨(-400860456930051182381869932965),(-400860456930051181747915336762)⟩,⟨694310678148124303900855930732,694310678148124304538105463468⟩⟩,⟨⟨1695094429072569101187193052677,1695094429072569103140951083406⟩,⟨(-978663224926882769571051482403),(-978663224926882767627484877498)⟩⟩,⟨⟨(-4058712126416768218728384067368),(-4058712126416768217666000293688)⟩,⟨(-687085071410),323621574468⟩⟩]
lemma ha19_0_4_eq (j : Fin 7) : ha19_0_4 j = ((ha19_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha19_0_4_contains (j : Fin 7) : (ha19_0_4 j).Contains (fullFactor false 19 4 ((j.val:ℝ)/6)) := by
  rw [ha19_0_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_0_3 j) false 19 3 j (ha19_0_3_contains j)
noncomputable def hk19_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_5 j i k)
lemma hk19_0_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_0_5 j i k).Contains (fullFactor false 19 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_0_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power19 j i k) (mpower0_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 5 (power19_contains j i k) (mpower0_5_contains j i k)
noncomputable def ha19_0_5 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨163976597214335483771186810,163976597214335483808379150⟩,⟨(-284015797627486289506448312),(-284015797627486289467682921)⟩⟩,⟨⟨(-9088505524079561265282394895),(-9088505524079561262124753973)⟩,⟨5247251110858735479525282131,5247251110858735482613884234⟩⟩,⟨⟨79692626246167045115224008392,79692626246167045126384892394⟩,⟨(-3162120966),6730415497⟩⟩,⟨⟨(-290832176770545960564924103801),(-290832176770545960297067896155)⟩,⟨(-167912035547479535540291261724),(-167912035547479535274206500828)⟩⟩,⟨⟨512426866294798386293691052707,512426866294798387312971252706⟩,⟨887549367585894654157119096086,887549367585894655182929566175⟩⟩,⟨⟨(-203337432179),431708282547⟩,⟨(-2550164039877345444203558830649),(-2550164039877345443527925994658)⟩⟩]
lemma ha19_0_5_eq (j : Fin 7) : ha19_0_5 j = ((ha19_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha19_0_5_contains (j : Fin 7) : (ha19_0_5 j).Contains (fullFactor false 19 5 ((j.val:ℝ)/6)) := by
  rw [ha19_0_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_0_4 j) false 19 4 j (ha19_0_4_contains j)
noncomputable def hk19_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_6 j i k)
lemma hk19_0_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_0_6 j i k).Contains (fullFactor false 19 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_0_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power19 j i k) (mpower0_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 6 (power19_contains j i k) (mpower0_6_contains j i k)
noncomputable def ha19_0_6 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨24785053981387676525178307,24785053981387676528640120⟩,⟨14309657588033580844318198,14309657588033580847609392⟩⟩,⟨⟨(-915818085634149174377159252),(-915818085634149173835181352)⟩,⟨(-1586243454808811298020773599),(-1586243454808811297464612122)⟩⟩,⟨⟨(-1762018657),827841334⟩,⟨20863480763352960871651378159,20863480763352960874639701281⟩⟩,⟨⟨58612357480585547100806675289,58612357480585547193874347559⟩,⟨(-101519581107763923099819233578),(-101519581107763923005996631807)⟩⟩,⟨⟨(-387266468459182445967381270929),(-387266468459182445518554308361)⟩,⟨223588399813024700478115871213,223588399813024700923572462455⟩⟩,⟨⟨1335262768854589495702309142578,1335262768854589496060319941658⟩,⟨(-106467230523),226041928158⟩⟩]
lemma ha19_0_6_eq (j : Fin 7) : ha19_0_6 j = ((ha19_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha19_0_6_contains (j : Fin 7) : (ha19_0_6 j).Contains (fullFactor false 19 6 ((j.val:ℝ)/6)) := by
  rw [ha19_0_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_0_5 j) false 19 5 j (ha19_0_5_contains j)
noncomputable def hk19_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_7 j i k)
lemma hk19_0_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_0_7 j i k).Contains (fullFactor false 19 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_0_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power19 j i k) (mpower0_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 7 (power19_contains j i k) (mpower0_7_contains j i k)
noncomputable def ha19_0_7 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1070359884617898514247008),(-1070359884617898513997419)⟩,⟨1853917702541761442126887,1853917702541761442391733⟩⟩,⟨⟨237301465925345464570280497,237301465925345464654237414⟩,⟨(-137006065231091009843088571),(-137006065231091009761572762)⟩⟩,⟨⟨(-4681754135318688101052787862),(-4681754135318688100367307234)⟩,⟨(-395396063),185767161⟩⟩,⟨⟨30374587638444219455499753507,30374587638444219483668095629⟩,⟨17536776349579649242107567415,17536776349579649270009171137⟩⟩,⟨⟨(-83621865985773321492746017073),(-83621865985773321325879464865)⟩,⟨(-144837320511075112764413786217),(-144837320511075112596091863237)⟩⟩,⟨⟨(-101447380130),47782381323⟩,⟨599264529320792076809594891565,599264529320792076972177280707⟩⟩]
lemma ha19_0_7_eq (j : Fin 7) : ha19_0_7 j = ((ha19_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha19_0_7_contains (j : Fin 7) : (ha19_0_7 j).Contains (fullFactor false 19 7 ((j.val:ℝ)/6)) := by
  rw [ha19_0_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_0_6 j) false 19 6 j (ha19_0_6_contains j)
noncomputable def hk19_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_8 j i k)
lemma hk19_0_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_0_8 j i k).Contains (fullFactor false 19 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_0_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power19 j i k) (mpower0_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 8 (power19_contains j i k) (mpower0_8_contains j i k)
noncomputable def ha19_0_8 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-121338629888859693723657),(-121338629888859693705936)⟩,⟨(-70054890629433514736150),(-70054890629433514719591)⟩⟩,⟨⟨17934052001134979764275643,17934052001134979775003124⟩,⟨31062689251548081585844993,31062689251548081596933805⟩⟩,⟨⟨(-36475297),77635836⟩,⟨(-919260274839426580315992724),(-919260274839426580178472820)⟩⟩,⟨⟨(-4591117312290554825043359288),(-4591117312290554817724122534)⟩,⟨7952048448396308883490232154,7952048448396308890889999034⟩⟩,⟨⟨47397902300335817830950617397,47397902300335817886184710093⟩,⟨(-27365191652122466715799111069),(-27365191652122466661105053443)⟩⟩,⟨⟨(-235330630358893204575589107384),(-235330630358893204510994071805)⟩,⟨(-39838293018),18764097267⟩⟩]
lemma ha19_0_8_eq (j : Fin 7) : ha19_0_8 j = ((ha19_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha19_0_8_contains (j : Fin 7) : (ha19_0_8 j).Contains (fullFactor false 19 8 ((j.val:ℝ)/6)) := by
  rw [ha19_0_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_0_7 j) false 19 7 j (ha19_0_7_contains j)
noncomputable def hk19_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_9 j i k)
lemma hk19_0_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_0_9 j i k).Contains (fullFactor false 19 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_0_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power19 j i k) (mpower0_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 9 (power19_contains j i k) (mpower0_9_contains j i k)
noncomputable def ha19_0_9 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨4075628328693792152024,4075628328693792153001⟩,⟨(-7059195338064676367107),(-7059195338064676366052)⟩⟩,⟨⟨(-3614308013089114300386280),(-3614308013089114299084533)⟩,⟨2086721704291221581378202,2086721704291221582633045⟩⟩,⟨⟨160441184787359821861487816,160441184787359821886000268⟩,⟨(-6366141),13550010⟩⟩,⟨⟨(-1850525702701626522280636837),(-1850525702701626520552742484)⟩,⟨(-1068401512597105450923070120),(-1068401512597105449216405557)⟩⟩,⟨⟨7960211579480062789291568898,7960211579480062805226763487⟩,⟨13787490894657571020776537144,13787490894657571036887370374⟩⟩,⟨⟨(-6549905570),13906187631⟩,⟨(-82145886611128228810761649378),(-82145886611128228787952249873)⟩⟩]
lemma ha19_0_9_eq (j : Fin 7) : ha19_0_9 j = ((ha19_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha19_0_9_contains (j : Fin 7) : (ha19_0_9 j).Contains (fullFactor false 19 9 ((j.val:ℝ)/6)) := by
  rw [ha19_0_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_0_8 j) false 19 8 j (ha19_0_8_contains j)
noncomputable def hk19_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_10 j i k)
lemma hk19_0_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_0_10 j i k).Contains (fullFactor false 19 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_0_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power19 j i k) (mpower0_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 10 (power19_contains j i k) (mpower0_10_contains j i k)
noncomputable def ha19_0_10 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨369618603571988403162,369618603571988403220⟩,⟨213399400269781075704,213399400269781075756⟩⟩,⟨⟨(-218520985876255821605153),(-218520985876255821473049)⟩,⟨(-378489450057716124941290),(-378489450057716124803765)⟩⟩,⟨⟨(-2128431),999992⟩,⟨25202042373060605479276757,25202042373060605483207385⟩⟩,⟨⟨223765489537285961094315574,223765489537285961452470833⟩,⟨(-387573196859101312041010282),(-387573196859101311677887250)⟩⟩,⟨⟨(-3609556675507699252120556767),(-3609556675507699247891260914)⟩,⟨2083978518259580815425451486,2083978518259580819603909185⟩⟩,⟨⟨25806891390014060009167915584,25806891390014060016415845664⟩,⟨(-2057713523),4368757691⟩⟩]
lemma ha19_0_10_eq (j : Fin 7) : ha19_0_10 j = ((ha19_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha19_0_10_contains (j : Fin 7) : (ha19_0_10 j).Contains (fullFactor false 19 10 ((j.val:ℝ)/6)) := by
  rw [ha19_0_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_0_9 j) false 19 9 j (ha19_0_9_contains j)
noncomputable def hk19_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_11 j i k)
lemma hk19_0_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_0_11 j i k).Contains (fullFactor false 19 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_0_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power19 j i k) (mpower0_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 11 (power19_contains j i k) (mpower0_11_contains j i k)
noncomputable def ha19_0_11 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-10157787699515332862),(-10157787699515332859)⟩,⟨17593804388058740563,17593804388058740567⟩⟩,⟨⟨36032111386744300670170,36032111386744300683378⟩,⟨(-20803149208607401704147),(-20803149208607401691504)⟩⟩,⟨⟨(-3598843235212085340774610),(-3598843235212085340201861)⟩,⟨(-303940),142799⟩⟩,⟨⟨73793764120052327749438675,73793764120052327818812033⟩,⟨42604849579227958646286592,42604849579227958714614811⟩⟩,⟨⟨(-495985727515397112796484066),(-495985727515397111800434687)⟩,⟨(-859072479885680692157896113),(-859072479885680691148591540)⟩⟩,⟨⟨(-1247714279),587681608⟩,⟨7370430945714350776273174509,7370430945714350778366639310⟩⟩]
lemma ha19_0_11_eq (j : Fin 7) : ha19_0_11 j = ((ha19_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha19_0_11_contains (j : Fin 7) : (ha19_0_11 j).Contains (fullFactor false 19 11 ((j.val:ℝ)/6)) := by
  rw [ha19_0_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_0_10 j) false 19 10 j (ha19_0_10_contains j)
noncomputable def hk19_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_12 j i k)
lemma hk19_0_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_0_12 j i k).Contains (fullFactor false 19 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_0_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power19 j i k) (mpower0_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 12 (power19_contains j i k) (mpower0_12_contains j i k)
noncomputable def ha19_0_12 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-767674536308627878),(-767674536308627877)⟩,⟨(-443217100187807443),(-443217100187807442)⟩⟩,⟨⟨1815417242369259284926,1815417242369259286036⟩,⟨3144394900720139784399,3144394900720139785562⟩⟩,⟨⟨(-18693),39786⟩,⟨(-471087477881817150409505),(-471087477881817150333032)⟩⟩,⟨⟨(-7435949024744486039882294),(-7435949024744486027933100)⟩,⟨12879441513349692552872421,12879441513349692565021353⟩⟩,⟨⟨187420541090973602722223342,187420541090973602943016021⟩,⟨(-108207299850538926555906367),(-108207299850538926338257667)⟩⟩,⟨⟨(-1929574309403923048197819760),(-1929574309403923047643609930)⟩,⟨(-326650835),153854686⟩⟩]
lemma ha19_0_12_eq (j : Fin 7) : ha19_0_12 j = ((ha19_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha19_0_12_contains (j : Fin 7) : (ha19_0_12 j).Contains (fullFactor false 19 12 ((j.val:ℝ)/6)) := by
  rw [ha19_0_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_0_11 j) false 19 11 j (ha19_0_11_contains j)
noncomputable def hk19_0_13 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_13 j i k)
lemma hk19_0_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_0_13 j i k).Contains (fullFactor false 19 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_0_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power19 j i k) (mpower0_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 13 (power19_contains j i k) (mpower0_13_contains j i k)
noncomputable def ha19_0_13 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨17851379306351118,17851379306351119⟩,⟨(-30919495943783800),(-30919495943783799)⟩⟩,⟨⟨(-253292510771476882333),(-253292510771476882238)⟩,⟨146238499277628361464,146238499277628361555⟩⟩,⟨⟨56921729219679268113596,56921729219679268123019⟩,⟨(-2259),4808⟩⟩,⟨⟨(-2074972248239938620611451),(-2074972248239938618647563)⟩,⟨(-1197985786082331538541394),(-1197985786082331536612477)⟩⟩,⟨⟨21791234504823142492220519,21791234504823142536120881⟩,⟨37743525322001707872631312,37743525322001707917215599⟩⟩,⟨⟨(-37180674),78938759⟩,⟨(-466302805767612564492883770),(-466302805767612564357468594)⟩⟩]
lemma ha19_0_13_eq (j : Fin 7) : ha19_0_13 j = ((ha19_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha19_0_13_contains (j : Fin 7) : (ha19_0_13 j).Contains (fullFactor false 19 13 ((j.val:ℝ)/6)) := by
  rw [ha19_0_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_0_12 j) false 19 12 j (ha19_0_12_contains j)
noncomputable def hk19_0_14 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_14 j i k)
lemma hk19_0_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_0_14 j i k).Contains (fullFactor false 19 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_0_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power19 j i k) (mpower0_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 14 (power19_contains j i k) (mpower0_14_contains j i k)
noncomputable def ha19_0_14 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1156386444162983,1156386444162984⟩,⟨667640024824732,667640024824733⟩⟩,⟨⟨(-10938614166728417762),(-10938614166728417755)⟩,⟨(-18946235501166317755),(-18946235501166317747)⟩⟩,⟨⟨(-540),254⟩,⟨6386603083791852240618,6386603083791852241696⟩⟩,⟨⟨179218254507678396425452,179218254507678396714589⟩,⟨(-310415122451108950176605),(-310415122451108949881819)⟩⟩,⟨⟨(-7058022730486958385542518),(-7058022730486958377182808)⟩,⟨4074951323393142874200775,4074951323393142882423095⟩⟩,⟨⟨104638104924845707103755541,104638104924845707134475710⟩,⟨(-8343324),17713817⟩⟩]
lemma ha19_0_14_eq (j : Fin 7) : ha19_0_14 j = ((ha19_0_13 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha19_0_14_contains (j : Fin 7) : (ha19_0_14 j).Contains (fullFactor false 19 14 ((j.val:ℝ)/6)) := by
  rw [ha19_0_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_0_13 j) false 19 13 j (ha19_0_13_contains j)
noncomputable def hk19_0_15 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_15 j i k)
lemma hk19_0_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_0_15 j i k).Contains (fullFactor false 19 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_0_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power19 j i k) (mpower0_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 15 (power19_contains j i k) (mpower0_15_contains j i k)
noncomputable def ha19_0_15 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-23305033302577),(-23305033302576)⟩,⟨40365501752147,40365501752148⟩⟩,⟨⟨1322696761414360852,1322696761414360853⟩,⟨(-763659331258827444),(-763659331258827443)⟩⟩,⟨⟨(-668803510981146723313),(-668803510981146723197)⟩,⟨(-57),27⟩⟩,⟨⟨43342127478025776399496,43342127478025776440795⟩,⟨25023588966689257645077,25023588966689257685529⟩⟩,⟨⟨(-711213174517105747090628),(-711213174517105745653297)⟩,⟨(-1231857353275977869985883),(-1231857353275977868522917)⟩⟩,⟨⟨(-3709974),1747422⟩,⟨21915353447830215824379356,21915353447830215830883132⟩⟩]
lemma ha19_0_15_eq (j : Fin 7) : ha19_0_15 j = ((ha19_0_14 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha19_0_15_contains (j : Fin 7) : (ha19_0_15 j).Contains (fullFactor false 19 15 ((j.val:ℝ)/6)) := by
  rw [ha19_0_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_0_14 j) false 19 14 j (ha19_0_14_contains j)
noncomputable def hk19_0_16 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_16 j i k)
lemma hk19_0_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_0_16 j i k).Contains (fullFactor false 19 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_0_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power19 j i k) (mpower0_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 16 (power19_contains j i k) (mpower0_16_contains j i k)
noncomputable def ha19_0_16 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1320957955865),(-1320957955864)⟩,⟨(-762655431407),(-762655431406)⟩⟩,⟨⟨49981386352667221,49981386352667222⟩,⟨86570300595549323,86570300595549324⟩⟩,⟨⟨(-3),6⟩,⟨(-65659631149794723629),(-65659631149794723617)⟩⟩,⟨⟨(-3275580136008399052237),(-3275580136008399046931)⟩,⟨5673471219829920492012,5673471219829920497437⟩⟩,⟨⟨201562188089707223481854,201562188089707223721873⟩,⟨(-116371983552042445798176),(-116371983552042445562622)⟩⟩,⟨⟨(-4303069587032947007994826),(-4303069587032947006704114)⟩,⟨(-728452),343106⟩⟩]
lemma ha19_0_16_eq (j : Fin 7) : ha19_0_16 j = ((ha19_0_15 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha19_0_16_contains (j : Fin 7) : (ha19_0_16 j).Contains (fullFactor false 19 16 ((j.val:ℝ)/6)) := by
  rw [ha19_0_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_0_15 j) false 19 15 j (ha19_0_15_contains j)
noncomputable def hk19_0_17 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_17 j i k)
lemma hk19_0_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_0_17 j i k).Contains (fullFactor false 19 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_0_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power19 j i k) (mpower0_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 17 (power19_contains j i k) (mpower0_17_contains j i k)
noncomputable def ha19_0_17 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨23489732358,23489732359⟩,⟨(-40685409901),(-40685409900)⟩⟩,⟨⟨(-5332718046471331),(-5332718046471330)⟩,⟨3078846199642597,3078846199642598⟩⟩,⟨⟨6066935731106195666,6066935731106195668⟩,⟨(-1),1⟩⟩,⟨⟨(-698970019787090239547),(-698970019787090238875)⟩,⟨(-403550529079554597063),(-403550529079554596407)⟩⟩,⟨⟨17921243559351411723963,17921243559351411760296⟩,⟨31040504379613153621379,31040504379613153658441⟩⟩,⟨⟨(-63406),134618⟩,⟨(-795205400147551278608989),(-795205400147551278367934)⟩⟩]
lemma ha19_0_17_eq (j : Fin 7) : ha19_0_17 j = ((ha19_0_16 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha19_0_17_contains (j : Fin 7) : (ha19_0_17 j).Contains (fullFactor false 19 17 ((j.val:ℝ)/6)) := by
  rw [ha19_0_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_0_16 j) false 19 16 j (ha19_0_16_contains j)
noncomputable def hk19_0_18 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_18 j i k)
lemma hk19_0_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_0_18 j i k).Contains (fullFactor false 19 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_0_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power19 j i k) (mpower0_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 18 (power19_contains j i k) (mpower0_18_contains j i k)
noncomputable def ha19_0_18 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1183490600,1183490601⟩,⟨683288616,683288617⟩⟩,⟨⟨(-179120011154260),(-179120011154259)⟩,⟨(-310244959971483),(-310244959971482)⟩⟩,⟨⟨(-1),1⟩,⟨529440020073462376,529440020073462377⟩⟩,⟨⟨46955236204022331333,46955236204022331411⟩,⟨(-81328854786764263422),(-81328854786764263342)⟩⟩,⟨⟨(-4514658357533078060987),(-4514658357533078055581)⟩,⟨2606539218020916333022,2606539218020916338315⟩⟩,⟨⟨138789524622137721125297,138789524622137721167812⟩,⟨(-11067),23496⟩⟩]
lemma ha19_0_18_eq (j : Fin 7) : ha19_0_18 j = ((ha19_0_17 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha19_0_18_contains (j : Fin 7) : (ha19_0_18 j).Contains (fullFactor false 19 18 ((j.val:ℝ)/6)) := by
  rw [ha19_0_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_0_17 j) false 19 17 j (ha19_0_17_contains j)
noncomputable def hk19_0_19 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_19 j i k)
lemma hk19_0_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_0_19 j i k).Contains (fullFactor false 19 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_0_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power19 j i k) (mpower0_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 19 (power19_contains j i k) (mpower0_19_contains j i k)
noncomputable def ha19_0_19 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-18829952),(-18829951)⟩,⟨32614433,32614434⟩⟩,⟨⟨17099355913327,17099355913328⟩,⟨(-9872317739529),(-9872317739528)⟩⟩,⟨⟨(-43770654673137423),(-43770654673137422)⟩,⟨(-1),1⟩⟩,⟨⟨8964987113086656140,8964987113086656150⟩,⟨5175937723022106876,5175937723022106886⟩⟩,⟨⟨(-359152827132815577868),(-359152827132815577136)⟩,⟨(-622070944276038605884),(-622070944276038605136)⟩⟩,⟨⟨(-3885),1830⟩,⟨22948428997269873106979,22948428997269873114083⟩⟩]
lemma ha19_0_19_eq (j : Fin 7) : ha19_0_19 j = ((ha19_0_18 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha19_0_19_contains (j : Fin 7) : (ha19_0_19 j).Contains (fullFactor false 19 19 ((j.val:ℝ)/6)) := by
  rw [ha19_0_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_0_18 j) false 19 18 j (ha19_0_18_contains j)
noncomputable def hk19_0_20 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_20 j i k)
lemma hk19_0_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_0_20 j i k).Contains (fullFactor false 19 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_0_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power19 j i k) (mpower0_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 20 (power19_contains j i k) (mpower0_20_contains j i k)
noncomputable def ha19_0_20 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-853844),(-853843)⟩,⟨(-492967),(-492966)⟩⟩,⟨⟨516913348073,516913348074⟩,⟨895320181973,895320181974⟩⟩,⟨⟨(-1),1⟩,⟨(-3437739179098608),(-3437739179098606)⟩⟩,⟨⟨(-542022930869484435),(-542022930869484432)⟩,⟨938811255133340262,938811255133340264⟩⟩,⟨⟨81428896189552855109,81428896189552855208⟩,⟨(-47012995134852432653),(-47012995134852432556)⟩⟩,⟨⟨(-3604730797462500934478),(-3604730797462500933349)⟩,⟨(-611),288⟩⟩]
lemma ha19_0_20_eq (j : Fin 7) : ha19_0_20 j = ((ha19_0_19 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha19_0_20_contains (j : Fin 7) : (ha19_0_20 j).Contains (fullFactor false 19 20 ((j.val:ℝ)/6)) := by
  rw [ha19_0_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_0_19 j) false 19 19 j (ha19_0_19_contains j)
noncomputable def hk19_0_21 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_21 j i k)
lemma hk19_0_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_0_21 j i k).Contains (fullFactor false 19 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_0_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power19 j i k) (mpower0_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 21 (power19_contains j i k) (mpower0_21_contains j i k)
noncomputable def ha19_0_21 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨12291,12292⟩,⟨(-21290),(-21289)⟩⟩,⟨⟨(-44646528672),(-44646528671)⟩,⟨25776685346,25776685347⟩⟩,⟨⟨257142289286047,257142289286048⟩,⟨(-1),1⟩⟩,⟨⟨(-93630556896327456),(-93630556896327455)⟩,⟨(-54057627228469228),(-54057627228469227)⟩⟩,⟨⟨5860939688051789405,5860939688051789418⟩,⟨10151445319802585609,10151445319802585622⟩⟩,⟨⟨(-44),92⟩,⟨(-539266466260812849030),(-539266466260812848858)⟩⟩]
lemma ha19_0_21_eq (j : Fin 7) : ha19_0_21 j = ((ha19_0_20 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha19_0_21_contains (j : Fin 7) : (ha19_0_21 j).Contains (fullFactor false 19 21 ((j.val:ℝ)/6)) := by
  rw [ha19_0_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_0_20 j) false 19 20 j (ha19_0_20_contains j)
noncomputable def hk19_0_22 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_22 j i k)
lemma hk19_0_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_0_22 j i k).Contains (fullFactor false 19 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_0_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power19 j i k) (mpower0_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 22 (power19_contains j i k) (mpower0_22_contains j i k)
noncomputable def ha19_0_22 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨506,507⟩,⟨292,293⟩⟩,⟨⟨(-1226967354),(-1226967353)⟩,⟨(-2125169796),(-2125169795)⟩⟩,⟨⟨(-1),1⟩,⟨18359916521552,18359916521553⟩⟩,⟨⟨5146274077922863,5146274077922864⟩,⟨(-8913608172637076),(-8913608172637075)⟩⟩,⟨⟨(-1208019168182208039),(-1208019168182208036)⟩,⟨697450191936225608,697450191936225611⟩⟩,⟨⟨77007071306013533786,77007071306013533812⟩,⟨(-7),14⟩⟩]
lemma ha19_0_22_eq (j : Fin 7) : ha19_0_22 j = ((ha19_0_21 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha19_0_22_contains (j : Fin 7) : (ha19_0_22 j).Contains (fullFactor false 19 22 ((j.val:ℝ)/6)) := by
  rw [ha19_0_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_0_21 j) false 19 21 j (ha19_0_21_contains j)
noncomputable def hk19_0_23 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_23 j i k)
lemma hk19_0_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_0_23 j i k).Contains (fullFactor false 19 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_0_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power19 j i k) (mpower0_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 23 (power19_contains j i k) (mpower0_23_contains j i k)
noncomputable def ha19_0_23 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-7),(-6)⟩,⟨11,12⟩⟩,⟨⟨96759678,96759679⟩,⟨(-55864227),(-55864226)⟩⟩,⟨⟨(-1253899540536),(-1253899540535)⟩,⟨(-1),1⟩⟩,⟨⟨811679013105350,811679013105351⟩,⟨468623096711943,468623096711944⟩⟩,⟨⟨(-79387840551870929),(-79387840551870928)⟩,⟨(-137503773339017308),(-137503773339017306)⟩⟩,⟨⟨(-2),1⟩,⟨10518471716932064453,10518471716932064458⟩⟩]
lemma ha19_0_23_eq (j : Fin 7) : ha19_0_23 j = ((ha19_0_22 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha19_0_23_contains (j : Fin 7) : (ha19_0_23 j).Contains (fullFactor false 19 23 ((j.val:ℝ)/6)) := by
  rw [ha19_0_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_0_22 j) false 19 22 j (ha19_0_22_contains j)
noncomputable def hk19_0_24 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_24 j i k)
lemma hk19_0_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_0_24 j i k).Contains (fullFactor false 19 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_0_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power19 j i k) (mpower0_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 24 (power19_contains j i k) (mpower0_24_contains j i k)
noncomputable def ha19_0_24 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),0⟩⟩,⟨⟨2437536,2437537⟩,⟨4221937,4221938⟩⟩,⟨⟨(-1),1⟩,⟨(-82067533019),(-82067533018)⟩⟩,⟨⟨(-40895079942577),(-40895079942576)⟩,⟨70832356240132,70832356240133⟩⟩,⟨⟨14999334866761557,14999334866761558⟩,⟨(-8659870022990125),(-8659870022990124)⟩⟩,⟨⟨(-1376864728037741371),(-1376864728037741370)⟩,⟨(-1),1⟩⟩]
lemma ha19_0_24_eq (j : Fin 7) : ha19_0_24 j = ((ha19_0_23 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha19_0_24_contains (j : Fin 7) : (ha19_0_24 j).Contains (fullFactor false 19 24 ((j.val:ℝ)/6)) := by
  rw [ha19_0_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_0_23 j) false 19 23 j (ha19_0_23_contains j)
noncomputable def hk19_0_25 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_25 j i k)
lemma hk19_0_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_0_25 j i k).Contains (fullFactor false 19 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_0_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power19 j i k) (mpower0_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 25 (power19_contains j i k) (mpower0_25_contains j i k)
noncomputable def ha19_0_25 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨(-1),0⟩⟩,⟨⟨(-176849),(-176848)⟩,⟨102103,102104⟩⟩,⟨⟨5156455176,5156455177⟩,⟨(-1),1⟩⟩,⟨⟨(-5934037600013),(-5934037600012)⟩,⟨(-3426018205749),(-3426018205748)⟩⟩,⟨⟨906859468175608,906859468175609⟩,⟨1570726674205044,1570726674205046⟩⟩,⟨⟨(-1),1⟩,⟨(-173021924583611077),(-173021924583611076)⟩⟩]
lemma ha19_0_25_eq (j : Fin 7) : ha19_0_25 j = ((ha19_0_24 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha19_0_25_contains (j : Fin 7) : (ha19_0_25 j).Contains (fullFactor false 19 25 ((j.val:ℝ)/6)) := by
  rw [ha19_0_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_0_24 j) false 19 24 j (ha19_0_24_contains j)
noncomputable def hk19_0_26 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_26 j i k)
lemma hk19_0_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_0_26 j i k).Contains (fullFactor false 19 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_0_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power19 j i k) (mpower0_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 26 (power19_contains j i k) (mpower0_26_contains j i k)
noncomputable def ha19_0_26 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨0,1⟩⟩,⟨⟨(-4113),(-4112)⟩,⟨(-7123),(-7122)⟩⟩,⟨⟨(-1),1⟩,⟨311528494,311528495⟩⟩,⟨⟨275978298108,275978298109⟩,⟨(-478008434111),(-478008434110)⟩⟩,⟨⟨(-158159723733337),(-158159723733336)⟩,⟨91313559072398,91313559072399⟩⟩,⟨⟨20906323353147684,20906323353147685⟩,⟨(-1),1⟩⟩]
lemma ha19_0_26_eq (j : Fin 7) : ha19_0_26 j = ((ha19_0_25 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha19_0_26_contains (j : Fin 7) : (ha19_0_26 j).Contains (fullFactor false 19 26 ((j.val:ℝ)/6)) := by
  rw [ha19_0_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_0_25 j) false 19 25 j (ha19_0_25_contains j)
noncomputable def hk19_0_27 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_27 j i k)
lemma hk19_0_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_0_27 j i k).Contains (fullFactor false 19 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_0_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power19 j i k) (mpower0_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 27 (power19_contains j i k) (mpower0_27_contains j i k)
noncomputable def ha19_0_27 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨0,1⟩⟩,⟨⟨276,277⟩,⟨(-160),(-159)⟩⟩,⟨⟨(-18123994),(-18123993)⟩,⟨(-1),1⟩⟩,⟨⟨37079204566,37079204567⟩,⟨21407688737,21407688739⟩⟩,⟨⟨(-8854012541821),(-8854012541820)⟩,⟨(-15335599573286),(-15335599573285)⟩⟩,⟨⟨(-1),1⟩,⟨2432561179993388,2432561179993389⟩⟩]
lemma ha19_0_27_eq (j : Fin 7) : ha19_0_27 j = ((ha19_0_26 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha19_0_27_contains (j : Fin 7) : (ha19_0_27 j).Contains (fullFactor false 19 27 ((j.val:ℝ)/6)) := by
  rw [ha19_0_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_0_26 j) false 19 26 j (ha19_0_26_contains j)
noncomputable def hk19_0_28 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_28 j i k)
lemma hk19_0_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_0_28 j i k).Contains (fullFactor false 19 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_0_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power19 j i k) (mpower0_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 28 (power19_contains j i k) (mpower0_28_contains j i k)
noncomputable def ha19_0_28 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),0⟩⟩,⟨⟨5,6⟩,⟨10,11⟩⟩,⟨⟨(-1),1⟩,⟨(-1016754),(-1016753)⟩⟩,⟨⟨(-1601291374),(-1601291373)⟩,⟨2773518015,2773518016⟩⟩,⟨⟨1433875207078,1433875207079⟩,⟨(-827848236791),(-827848236790)⟩⟩,⟨⟨(-272932726159820),(-272932726159819)⟩,⟨(-1),1⟩⟩]
lemma ha19_0_28_eq (j : Fin 7) : ha19_0_28 j = ((ha19_0_27 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha19_0_28_contains (j : Fin 7) : (ha19_0_28 j).Contains (fullFactor false 19 28 ((j.val:ℝ)/6)) := by
  rw [ha19_0_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_0_27 j) false 19 27 j (ha19_0_27_contains j)
noncomputable def hk19_0_29 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_29 j i k)
lemma hk19_0_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_0_29 j i k).Contains (fullFactor false 19 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_0_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power19 j i k) (mpower0_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 29 (power19_contains j i k) (mpower0_29_contains j i k)
noncomputable def ha19_0_29 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨(-1),0⟩⟩,⟨⟨(-1),0⟩,⟨0,1⟩⟩,⟨⟨55072,55073⟩,⟨(-1),1⟩⟩,⟨⟨(-200304916),(-200304915)⟩,⟨(-115646097),(-115646096)⟩⟩,⟨⟨74734538476,74734538477⟩,⟨129444017721,129444017722⟩⟩,⟨⟨(-1),1⟩,⟨(-29567015428550),(-29567015428549)⟩⟩]
lemma ha19_0_29_eq (j : Fin 7) : ha19_0_29 j = ((ha19_0_28 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha19_0_29_contains (j : Fin 7) : (ha19_0_29 j).Contains (fullFactor false 19 29 ((j.val:ℝ)/6)) := by
  rw [ha19_0_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_0_28 j) false 19 28 j (ha19_0_28_contains j)
noncomputable def hk19_0_30 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_30 j i k)
lemma hk19_0_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_0_30 j i k).Contains (fullFactor false 19 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_0_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power19 j i k) (mpower0_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 30 (power19_contains j i k) (mpower0_30_contains j i k)
noncomputable def ha19_0_30 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨0,1⟩⟩,⟨⟨(-1),0⟩,⟨(-1),0⟩⟩,⟨⟨(-1),1⟩,⟨2883,2884⟩⟩,⟨⟨8073620,8073621⟩,⟨(-13983922),(-13983921)⟩⟩,⟨⟨(-11296121532),(-11296121531)⟩,⟨6521818806,6521818807⟩⟩,⟨⟨3096250615296,3096250615297⟩,⟨(-1),1⟩⟩]
lemma ha19_0_30_eq (j : Fin 7) : ha19_0_30 j = ((ha19_0_29 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha19_0_30_contains (j : Fin 7) : (ha19_0_30 j).Contains (fullFactor false 19 30 ((j.val:ℝ)/6)) := by
  rw [ha19_0_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_0_29 j) false 19 29 j (ha19_0_29_contains j)
noncomputable def hk19_1_0 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_0 j i k)
lemma hk19_1_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_1_0 j i k).Contains (fullFactor true 19 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_1_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel19_0 j i k) (mpower1_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 0 (kernel19_0_contains j i k) (mpower1_0_contains j i k)
noncomputable def ha19_1_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-3),4⟩,⟨(-4),2⟩⟩,⟨⟨(-4),0⟩,⟨(-2),2⟩⟩,⟨⟨(-2694941),(-2694938)⟩,⟨(-7553494),(-7553491)⟩⟩,⟨⟨161985630457654811,161985630457654815⟩,⟨436136473825194671,436136473825194675⟩⟩,⟨⟨875795745701851962050983,875795745701851969854345⟩,⟨(-1717008702880404811713990),(-1717008702880404803916317)⟩⟩,⟨⟨(-3773270257214874982714516262),(-3773270257214874921032772599)⟩,⟨30019734216488397017839289471,30019734216488397079757731725⟩⟩]
lemma ha19_1_0_eq (j : Fin 7) : ha19_1_0 j = atomKernel19_0 j := by fin_cases j <;> decide +kernel
lemma ha19_1_0_contains (j : Fin 7) : (ha19_1_0 j).Contains (fullFactor true 19 0 ((j.val:ℝ)/6)) := by
  rw [ha19_1_0_eq]
  simpa only [fullFactor,ite_true] using atomKernel19_0_contains j
noncomputable def hk19_1_1 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_1 j i k)
lemma hk19_1_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_1_1 j i k).Contains (fullFactor true 19 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_1_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel19_0 j i k) (mpower1_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 1 (kernel19_0_contains j i k) (mpower1_1_contains j i k)
noncomputable def ha19_1_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),31⟩,⟨(-31),42⟩⟩,⟨⟨(-11),30⟩,⟨(-10),31⟩⟩,⟨⟨(-30958727),(-30958703)⟩,⟨35142785,35142810⟩⟩,⟨⟨1769479826288535701,1769479826288535726⟩,⟨(-1409274084194273722),(-1409274084194273697)⟩⟩,⟨⟨(-7631316207020498734798912),(-7631316207020498697422870)⟩,⟨(-2368587012362611643398018),(-2368587012362611606011795)⟩⟩,⟨⟨109110561539634485129127268825,109110561539634485364645873668⟩,⟨7988470969262919066081260666,7988470969262919300503590470⟩⟩]
lemma ha19_1_1_eq (j : Fin 7) : ha19_1_1 j = ((ha19_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha19_1_1_contains (j : Fin 7) : (ha19_1_1 j).Contains (fullFactor true 19 1 ((j.val:ℝ)/6)) := by
  rw [ha19_1_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_1_0 j) true 19 0 j (ha19_1_0_contains j)
noncomputable def hk19_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_2 j i k)
lemma hk19_1_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_1_2 j i k).Contains (fullFactor true 19 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_1_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel19_0 j i k) (mpower1_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 2 (kernel19_0_contains j i k) (mpower1_2_contains j i k)
noncomputable def ha19_1_2 : Fin 7 → CBox := ![⟨⟨(-130),130⟩,⟨(-130),130⟩⟩,⟨⟨(-177),255⟩,⟨(-219),205⟩⟩,⟨⟨(-100),107⟩,⟨(-154),53⟩⟩,⟨⟨133565977,133566076⟩,⟨29346016,29346113⟩⟩,⟨⟨(-4596111861562243883),(-4596111861562243806)⟩,⟨(-3019712549212694957),(-3019712549212694879)⟩⟩,⟨⟨(-2150802347297484515006745),(-2150802347297484425453828)⟩,⟨16422196816187689448032916,16422196816187689537596942⟩⟩,⟨⟨4179260290361574195554509713,4179260290361574640997655879⟩,⟨(-197750550397078292256571304667),(-197750550397078291808700804220)⟩⟩]
lemma ha19_1_2_eq (j : Fin 7) : ha19_1_2 j = ((ha19_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha19_1_2_contains (j : Fin 7) : (ha19_1_2 j).Contains (fullFactor true 19 2 ((j.val:ℝ)/6)) := by
  rw [ha19_1_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_1_1 j) true 19 1 j (ha19_1_1_contains j)
noncomputable def hk19_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_3 j i k)
lemma hk19_1_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_1_3 j i k).Contains (fullFactor true 19 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_1_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel19_0 j i k) (mpower1_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 3 (kernel19_0_contains j i k) (mpower1_3_contains j i k)
noncomputable def ha19_1_3 : Fin 7 → CBox := ![⟨⟨(-400),400⟩,⟨(-400),400⟩⟩,⟨⟨(-924),707⟩,⟨(-840),779⟩⟩,⟨⟨(-440),256⟩,⟨(-271),425⟩⟩,⟨⟨(-76027548),(-76027288)⟩,⟨(-255114050),(-255113788)⟩⟩,⟨⟨(-2328763856612328119),(-2328763856612327959)⟩,⟨8603309351384496550,8603309351384496709⟩⟩,⟨⟨22868118841049176338572596,22868118841049176481634765⟩,⟨(-926523875944949058447102),(-926523875944948915448649)⟩⟩,⟨⟨(-238289046785031641968742893630),(-238289046785031641401012931830)⟩,⟨7346955458100419993732702775,7346955458100420557989762363⟩⟩]
lemma ha19_1_3_eq (j : Fin 7) : ha19_1_3 j = ((ha19_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha19_1_3_contains (j : Fin 7) : (ha19_1_3 j).Contains (fullFactor true 19 3 ((j.val:ℝ)/6)) := by
  rw [ha19_1_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_1_2 j) true 19 2 j (ha19_1_2_contains j)
noncomputable def hk19_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_4 j i k)
lemma hk19_1_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_1_4 j i k).Contains (fullFactor true 19 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_1_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel19_0 j i k) (mpower1_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 4 (kernel19_0_contains j i k) (mpower1_4_contains j i k)
noncomputable def ha19_1_4 : Fin 7 → CBox := ![⟨⟨(-922),922⟩,⟨(-922),922⟩⟩,⟨⟨(-2136),2495⟩,⟨(-2151),2469⟩⟩,⟨⟨(-665),1089⟩,⟨(-853),901⟩⟩,⟨⟨(-272009478),(-272008959)⟩,⟨277584392,277584910⟩⟩,⟨⟨10819025900699310642,10819025900699310888⟩,⟨(-569554128425957473),(-569554128425957227)⟩⟩,⟨⟨(-4972813901797147646372603),(-4972813901797147475119169)⟩,⟨(-23192619969007155635514257),(-23192619969007155464147933)⟩⟩,⟨⟨17818595250453951295317019165,17818595250453951831411610951⟩,⟨214772097546986240919462570370,214772097546986241459158435722⟩⟩]
lemma ha19_1_4_eq (j : Fin 7) : ha19_1_4 j = ((ha19_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha19_1_4_contains (j : Fin 7) : (ha19_1_4 j).Contains (fullFactor true 19 4 ((j.val:ℝ)/6)) := by
  rw [ha19_1_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_1_3 j) true 19 3 j (ha19_1_3_contains j)
noncomputable def hk19_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_5 j i k)
lemma hk19_1_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_1_5 j i k).Contains (fullFactor true 19 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_1_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel19_0 j i k) (mpower1_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 5 (kernel19_0_contains j i k) (mpower1_5_contains j i k)
noncomputable def ha19_1_5 : Fin 7 → CBox := ![⟨⟨(-1700),1700⟩,⟨(-1700),1700⟩⟩,⟨⟨(-5425),5111⟩,⟨(-5641),4887⟩⟩,⟨⟨(-1951),1583⟩,⟨(-2009),1525⟩⟩,⟨⟨437552192,437553016⟩,⟨120787258,120788082⟩⟩,⟨⟨(-3805202934222615043),(-3805202934222614740)⟩,⟨(-9824141050320606241),(-9824141050320605939)⟩⟩,⟨⟨(-18249268120410069345151169),(-18249268120410069180949255)⟩,⟨7330019199856127906313651,7330019199856128070400012⟩⟩,⟨⟨154440355842989514856201575260,154440355842989515266601454716⟩,⟨(-20934377704896460532232464219),(-20934377704896460124727421448)⟩⟩]
lemma ha19_1_5_eq (j : Fin 7) : ha19_1_5 j = ((ha19_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha19_1_5_contains (j : Fin 7) : (ha19_1_5 j).Contains (fullFactor true 19 5 ((j.val:ℝ)/6)) := by
  rw [ha19_1_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_1_4 j) true 19 4 j (ha19_1_4_contains j)
noncomputable def hk19_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_6 j i k)
lemma hk19_1_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_1_6 j i k).Contains (fullFactor true 19 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_1_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel19_0 j i k) (mpower1_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 6 (kernel19_0_contains j i k) (mpower1_6_contains j i k)
noncomputable def ha19_1_6 : Fin 7 → CBox := ![⟨⟨(-2612),2612⟩,⟨(-2612),2612⟩⟩,⟨⟨(-10026),9960⟩,⟨(-9412),10570⟩⟩,⟨⟨(-3024),2910⟩,⟨(-2611),3324⟩⟩,⟨⟨(-103542393),(-103541302)⟩,⟨(-429495402),(-429494311)⟩⟩,⟨⟨(-6603531113751344547),(-6603531113751344237)⟩,⟨5411178669330811427,5411178669330811737⟩⟩,⟨⟨7133058309754072907852901,7133058309754073038873873⟩,⟨11565182218904509405513681,11565182218904509536619353⟩⟩,⟨⟨(-17432394434205249749694734783),(-17432394434205249491543665387)⟩,⟨(-92292871340892753487656813024),(-92292871340892753227611658253)⟩⟩]
lemma ha19_1_6_eq (j : Fin 7) : ha19_1_6 j = ((ha19_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha19_1_6_contains (j : Fin 7) : (ha19_1_6 j).Contains (fullFactor true 19 6 ((j.val:ℝ)/6)) := by
  rw [ha19_1_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_1_5 j) true 19 5 j (ha19_1_5_contains j)
noncomputable def hk19_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_7 j i k)
lemma hk19_1_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_1_7 j i k).Contains (fullFactor true 19 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_1_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel19_0 j i k) (mpower1_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 7 (kernel19_0_contains j i k) (mpower1_7_contains j i k)
noncomputable def ha19_1_7 : Fin 7 → CBox := ![⟨⟨(-3439),3439⟩,⟨(-3439),3439⟩⟩,⟨⟨(-15907),16595⟩,⟨(-16866),15633⟩⟩,⟨⟨(-3968),4573⟩,⟨(-4479),4062⟩⟩,⟨⟨(-271566071),(-271564833)⟩,⟨249197368,249198607⟩⟩,⟨⟨5000898642986824463,5000898642986824736⟩,⟨3186911124354648273,3186911124354648545⟩⟩,⟨⟨6031906315165059307602774,6031906315165059397324289⟩,⟨(-5326581563722765197388740),(-5326581563722765107714949)⟩⟩,⟨⟨(-47142660345522125790848657697),(-47142660345522125649623661382)⟩,⟨11468424602842061990946668400,11468424602842062131128857014⟩⟩]
lemma ha19_1_7_eq (j : Fin 7) : ha19_1_7 j = ((ha19_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha19_1_7_contains (j : Fin 7) : (ha19_1_7 j).Contains (fullFactor true 19 7 ((j.val:ℝ)/6)) := by
  rw [ha19_1_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_1_6 j) true 19 6 j (ha19_1_6_contains j)
noncomputable def hk19_1_8 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_8 j i k)
lemma hk19_1_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_1_8 j i k).Contains (fullFactor true 19 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_1_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel19_0 j i k) (mpower1_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 8 (kernel19_0_contains j i k) (mpower1_8_contains j i k)
noncomputable def ha19_1_8 : Fin 7 → CBox := ![⟨⟨(-3962),3962⟩,⟨(-3962),3962⟩⟩,⟨⟨(-23741),22509⟩,⟨(-22694),23555⟩⟩,⟨⟨(-5698),5058⟩,⟨(-5444),5312⟩⟩,⟨⟨255186900,255188130⟩,⟨85250056,85251286⟩⟩,⟨⟨893168864742913692,893168864742913902⟩,⟨(-3491675506443947167),(-3491675506443946957)⟩⟩,⟨⟨(-3251120570199236038126050),(-3251120570199235984423788)⟩,⟨(-2611323093539420116235076),(-2611323093539420062511696)⟩⟩,⟨⟨6283114414076144423751820394,6283114414076144490361798227⟩,⟨21009988685514834245050623323,21009988685514834312155416209⟩⟩]
lemma ha19_1_8_eq (j : Fin 7) : ha19_1_8 j = ((ha19_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha19_1_8_contains (j : Fin 7) : (ha19_1_8 j).Contains (fullFactor true 19 8 ((j.val:ℝ)/6)) := by
  rw [ha19_1_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_1_7 j) true 19 7 j (ha19_1_7_contains j)
noncomputable def hk19_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_9 j i k)
lemma hk19_1_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_1_9 j i k).Contains (fullFactor true 19 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_1_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel19_0 j i k) (mpower1_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 9 (kernel19_0_contains j i k) (mpower1_9_contains j i k)
noncomputable def ha19_1_9 : Fin 7 → CBox := ![⟨⟨(-4057),4057⟩,⟨(-4057),4057⟩⟩,⟨⟨(-28549),29954⟩,⟨(-29363),29139⟩⟩,⟨⟨(-5883),6157⟩,⟨(-5801),6239⟩⟩,⟨⟨(-31855335),(-31854249)⟩,⟨(-171648077),(-171646991)⟩⟩,⟨⟨(-1942774702575184421),(-1942774702575184277)⟩,⟨129411390750167914,129411390750168058⟩⟩,⟨⟨(-930916366180930791912364),(-930916366180930763319038)⟩,⟨1680106443794698550931763,1680106443794698579517922⟩⟩,⟨⟨8298646083014296406207736817,8298646083014296434548846032⟩,⟨(-2959289532881161415734763283),(-2959289532881161387599692858)⟩⟩]
lemma ha19_1_9_eq (j : Fin 7) : ha19_1_9 j = ((ha19_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha19_1_9_contains (j : Fin 7) : (ha19_1_9 j).Contains (fullFactor true 19 9 ((j.val:ℝ)/6)) := by
  rw [ha19_1_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_1_8 j) true 19 8 j (ha19_1_8_contains j)
noncomputable def hk19_1_10 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_10 j i k)
lemma hk19_1_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_1_10 j i k).Contains (fullFactor true 19 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_1_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel19_0 j i k) (mpower1_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 10 (kernel19_0_contains j i k) (mpower1_10_contains j i k)
noncomputable def ha19_1_10 : Fin 7 → CBox := ![⟨⟨(-3739),3739⟩,⟨(-3739),3739⟩⟩,⟨⟨(-33881),32720⟩,⟨(-33476),33125⟩⟩,⟨⟨(-6020),6110⟩,⟨(-6243),5886⟩⟩,⟨⟨(-78667944),(-78667081)⟩,⟨64847929,64848792⟩⟩,⟨⟨354187541611467975,354187541611468064⟩,⟨877949375053473648,877949375053473737⟩⟩,⟨⟨751938128481459963597514,751938128481459977292043⟩,⟨261976151179624053574562,261976151179624067270708⟩⟩,⟨⟨(-1224433616774698596923872593),(-1224433616774698586228157395)⟩,⟨(-2941095136989598447269495618),(-2941095136989598436497430079)⟩⟩]
lemma ha19_1_10_eq (j : Fin 7) : ha19_1_10 j = ((ha19_1_9 j).mul (piI.mul (atomPoints j).z)).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha19_1_10_contains (j : Fin 7) : (ha19_1_10 j).Contains (fullFactor true 19 10 ((j.val:ℝ)/6)) := by
  rw [ha19_1_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_1_9 j) true 19 9 j (ha19_1_9_contains j)
noncomputable def hk19_1_11 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_11 j i k)
lemma hk19_1_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_1_11 j i k).Contains (fullFactor true 19 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_1_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel19_0 j i k) (mpower1_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 11 (kernel19_0_contains j i k) (mpower1_11_contains j i k)
noncomputable def ha19_1_11 : Fin 7 → CBox := ![⟨⟨(-3133),3133⟩,⟨(-3133),3133⟩⟩,⟨⟨(-34119),34809⟩,⟨(-34145),34782⟩⟩,⟨⟨(-5658),5451⟩,⟨(-5496),5613⟩⟩,⟨⟨50353480,50354104⟩,⟨19848387,19849011⟩⟩,⟨⟨319945113619212357,319945113619212408⟩,⟨(-269704442697875539),(-269704442697875489)⟩⟩,⟨⟨49150574651159287983172,49150574651159293947084⟩,⟨(-296036452756779617495888),(-296036452756779611531993)⟩⟩,⟨⟨(-944586828610372500846884240),(-944586828610372497124964511)⟩,⟨452156451913613702348161854,452156451913613706044620473⟩⟩]
lemma ha19_1_11_eq (j : Fin 7) : ha19_1_11 j = ((ha19_1_10 j).mul (piI.mul (atomPoints j).z)).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha19_1_11_contains (j : Fin 7) : (ha19_1_11 j).Contains (fullFactor true 19 11 ((j.val:ℝ)/6)) := by
  rw [ha19_1_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_1_10 j) true 19 10 j (ha19_1_10_contains j)
noncomputable def hk19_1_12 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_12 j i k)
lemma hk19_1_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_1_12 j i k).Contains (fullFactor true 19 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_1_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel19_0 j i k) (mpower1_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 12 (kernel19_0_contains j i k) (mpower1_12_contains j i k)
noncomputable def ha19_1_12 : Fin 7 → CBox := ![⟨⟨(-2406),2406⟩,⟨(-2406),2406⟩⟩,⟨⟨(-32817),32574⟩,⟨(-33006),32385⟩⟩,⟨⟨(-4596),4731⟩,⟨(-4643),4684⟩⟩,⟨⟨(-3425863),(-3425449)⟩,⟨(-26116280),(-26115866)⟩⟩,⟨⟨(-144238542094061510),(-144238542094061483)⟩,⟨(-89120383317285786),(-89120383317285759)⟩⟩,⟨⟨(-103667795416028570151103),(-103667795416028567770381)⟩,⟨642109742571968360268,642109742571970740773⟩⟩,⟨⟨150843079862060999887446983,150843079862061001058500938⟩,⟨277168725027257233618347763,277168725027257234797112186⟩⟩]
lemma ha19_1_12_eq (j : Fin 7) : ha19_1_12 j = ((ha19_1_11 j).mul (piI.mul (atomPoints j).z)).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha19_1_12_contains (j : Fin 7) : (ha19_1_12 j).Contains (fullFactor true 19 12 ((j.val:ℝ)/6)) := by
  rw [ha19_1_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_1_11 j) true 19 11 j (ha19_1_11_contains j)
noncomputable def hk19_1_13 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_13 j i k)
lemma hk19_1_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_1_13 j i k).Contains (fullFactor true 19 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_1_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel19_0 j i k) (mpower1_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 13 (kernel19_0_contains j i k) (mpower1_13_contains j i k)
noncomputable def ha19_1_13 : Fin 7 → CBox := ![⟨⟨(-1706),1706⟩,⟨(-1706),1706⟩⟩,⟨⟨(-28649),28615⟩,⟨(-28414),28850⟩⟩,⟨⟨(-3632),3597⟩,⟨(-3649),3580⟩⟩,⟨⟨(-9516563),(-9516309)⟩,⟨7031210,7031463⟩⟩,⟨⟨(-14858646313883249),(-14858646313883236)⟩,⟨61648434957468829,61648434957468843⟩⟩,⟨⟨5818227605944683973470,5818227605944684850553⟩,⟨32543184061911994640421,32543184061911995517645⟩⟩,⟨⟨74810705548225137490494895,74810705548225137835088570⟩,⟨(-45903322326943795243031332),(-45903322326943794900573918)⟩⟩]
lemma ha19_1_13_eq (j : Fin 7) : ha19_1_13 j = ((ha19_1_12 j).mul (piI.mul (atomPoints j).z)).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha19_1_13_contains (j : Fin 7) : (ha19_1_13 j).Contains (fullFactor true 19 13 ((j.val:ℝ)/6)) := by
  rw [ha19_1_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_1_12 j) true 19 12 j (ha19_1_12_contains j)
noncomputable def hk19_1_14 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_14 j i k)
lemma hk19_1_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_1_14 j i k).Contains (fullFactor true 19 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_1_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel19_0 j i k) (mpower1_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 14 (kernel19_0_contains j i k) (mpower1_14_contains j i k)
noncomputable def ha19_1_14 : Fin 7 → CBox := ![⟨⟨(-1123),1123⟩,⟨(-1123),1123⟩⟩,⟨⟨(-23215),23350⟩,⟨(-23397),23168⟩⟩,⟨⟨(-2608),2595⟩,⟨(-2583),2620⟩⟩,⟨⟨4489173,4489318⟩,⟨2050930,2051075⟩⟩,⟨⟨21952232079111683,21952232079111690⟩,⟨(-1769469178426308),(-1769469178426301)⟩⟩,⟨⟨9203623851294521228588,9203623851294521528724⟩,⟨(-3334965046103480144406),(-3334965046103479844324)⟩⟩,⟨⟨(-12843253519837436017546084),(-12843253519837435924553191)⟩,⟨(-18680284636280242088269868),(-18680284636280241994732121)⟩⟩]
lemma ha19_1_14_eq (j : Fin 7) : ha19_1_14 j = ((ha19_1_13 j).mul (piI.mul (atomPoints j).z)).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha19_1_14_contains (j : Fin 7) : (ha19_1_14 j).Contains (fullFactor true 19 14 ((j.val:ℝ)/6)) := by
  rw [ha19_1_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_1_13 j) true 19 13 j (ha19_1_13_contains j)
noncomputable def hk19_1_15 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_15 j i k)
lemma hk19_1_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_1_15 j i k).Contains (fullFactor true 19 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_1_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel19_0 j i k) (mpower1_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 15 (kernel19_0_contains j i k) (mpower1_15_contains j i k)
noncomputable def ha19_1_15 : Fin 7 → CBox := ![⟨⟨(-690),690⟩,⟨(-690),690⟩⟩,⟨⟨(-17733),17608⟩,⟨(-17629),17712⟩⟩,⟨⟨(-1739),1756⟩,⟨(-1751),1744⟩⟩,⟨⟨(-148533),(-148455)⟩,⟨(-1915815),(-1915737)⟩⟩,⟨⟨(-2762692340139029),(-2762692340139025)⟩,⟨(-6582513233305751),(-6582513233305747)⟩⟩,⟨⟨(-1340431875249325234671),(-1340431875249325138845)⟩,⟨(-2350046358602387699353),(-2350046358602387603511)⟩⟩,⟨⟨(-4336224896029612195603331),(-4336224896029612171906582)⟩,⟨3325665505370755990531695,3325665505370756014099858⟩⟩]
lemma ha19_1_15_eq (j : Fin 7) : ha19_1_15 j = ((ha19_1_14 j).mul (piI.mul (atomPoints j).z)).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha19_1_15_contains (j : Fin 7) : (ha19_1_15 j).Contains (fullFactor true 19 15 ((j.val:ℝ)/6)) := by
  rw [ha19_1_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_1_14 j) true 19 14 j (ha19_1_14_contains j)
noncomputable def hk19_1_16 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_16 j i k)
lemma hk19_1_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_1_16 j i k).Contains (fullFactor true 19 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_1_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel19_0 j i k) (mpower1_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 16 (kernel19_0_contains j i k) (mpower1_16_contains j i k)
noncomputable def ha19_1_16 : Fin 7 → CBox := ![⟨⟨(-398),398⟩,⟨(-398),398⟩⟩,⟨⟨(-12534),12613⟩,⟨(-12579),12568⟩⟩,⟨⟨(-1104),1097⟩,⟨(-1102),1099⟩⟩,⟨⟨(-585400),(-585360)⟩,⟨386241,386281⟩⟩,⟨⟨(-1639042271788660),(-1639042271788657)⟩,⟨1421153918265472,1421153918265475⟩⟩,⟨⟨(-541035134843753901112),(-541035134843753872419)⟩,⟨445700657339520783322,445700657339520812011⟩⟩,⟨⟨801455764253527543695125,801455764253527549294856⟩,⟨939609352661017771359396,939609352661017776987327⟩⟩]
lemma ha19_1_16_eq (j : Fin 7) : ha19_1_16 j = ((ha19_1_15 j).mul (piI.mul (atomPoints j).z)).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha19_1_16_contains (j : Fin 7) : (ha19_1_16 j).Contains (fullFactor true 19 16 ((j.val:ℝ)/6)) := by
  rw [ha19_1_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_1_15 j) true 19 15 j (ha19_1_15_contains j)
noncomputable def hk19_1_17 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_17 j i k)
lemma hk19_1_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_1_17 j i k).Contains (fullFactor true 19 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_1_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel19_0 j i k) (mpower1_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 17 (kernel19_0_contains j i k) (mpower1_17_contains j i k)
noncomputable def ha19_1_17 : Fin 7 → CBox := ![⟨⟨(-216),216⟩,⟨(-216),216⟩⟩,⟨⟨(-8439),8401⟩,⟨(-8427),8414⟩⟩,⟨⟨(-652),653⟩,⟨(-651),654⟩⟩,⟨⟨213505,213524⟩,⟨111588,111608⟩⟩,⟨⟨532320531636224,532320531636226⟩,⟨318753107209568,318753107209570⟩⟩,⟨⟨129521935321114445871,129521935321114453956⟩,⟨111551733828312439500,111551733828312447585⟩⟩,⟨⟨190733047155104716282367,190733047155104717540331⟩,⟨(-180618307830521253063094),(-180618307830521251810897)⟩⟩]
lemma ha19_1_17_eq (j : Fin 7) : ha19_1_17 j = ((ha19_1_16 j).mul (piI.mul (atomPoints j).z)).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha19_1_17_contains (j : Fin 7) : (ha19_1_17 j).Contains (fullFactor true 19 17 ((j.val:ℝ)/6)) := by
  rw [ha19_1_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_1_16 j) true 19 16 j (ha19_1_16_contains j)
noncomputable def hk19_1_18 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_18 j i k)
lemma hk19_1_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_1_18 j i k).Contains (fullFactor true 19 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_1_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel19_0 j i k) (mpower1_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 18 (kernel19_0_contains j i k) (mpower1_18_contains j i k)
noncomputable def ha19_1_18 : Fin 7 → CBox := ![⟨⟨(-111),111⟩,⟨(-111),111⟩⟩,⟨⟨(-5319),5333⟩,⟨(-5319),5333⟩⟩,⟨⟨(-365),366⟩,⟨(-366),365⟩⟩,⟨⟨(-1903),(-1893)⟩,⟨(-78144),(-78135)⟩⟩,⟨⟨36998919840871,36998919840873⟩,⟨(-163463315790577),(-163463315790575)⟩⟩,⟨⟨20249939157843312598,20249939157843314750⟩,⟨(-33761216516028120806),(-33761216516028118653)⟩⟩,⟨⟨(-38223999811662041465820),(-38223999811662041201368)⟩,⟨(-36379260791321516815237),(-36379260791321516549682)⟩⟩]
lemma ha19_1_18_eq (j : Fin 7) : ha19_1_18 j = ((ha19_1_17 j).mul (piI.mul (atomPoints j).z)).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha19_1_18_contains (j : Fin 7) : (ha19_1_18 j).Contains (fullFactor true 19 18 ((j.val:ℝ)/6)) := by
  rw [ha19_1_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_1_17 j) true 19 17 j (ha19_1_17_contains j)
noncomputable def hk19_1_19 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_19 j i k)
lemma hk19_1_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_1_19 j i k).Contains (fullFactor true 19 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_1_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel19_0 j i k) (mpower1_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 19 (kernel19_0_contains j i k) (mpower1_19_contains j i k)
noncomputable def ha19_1_19 : Fin 7 → CBox := ![⟨⟨(-54),54⟩,⟨(-54),54⟩⟩,⟨⟨(-3193),3190⟩,⟨(-3196),3187⟩⟩,⟨⟨(-195),194⟩,⟨(-194),194⟩⟩,⟨⟨(-20728),(-20723)⟩,⟨12146,12151⟩⟩,⟨⟨(-42698173949019),(-42698173949017)⟩,⟨4040556896239,4040556896241⟩⟩,⟨⟨(-8009826222927950960),(-8009826222927950417)⟩,⟨(-3102568493281103675),(-3102568493281103131)⟩⟩,⟨⟨(-6536263649188618255003),(-6536263649188618201895)⟩,⟨7624153391305344161621,7624153391305344214531⟩⟩]
lemma ha19_1_19_eq (j : Fin 7) : ha19_1_19 j = ((ha19_1_18 j).mul (piI.mul (atomPoints j).z)).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha19_1_19_contains (j : Fin 7) : (ha19_1_19 j).Contains (fullFactor true 19 19 ((j.val:ℝ)/6)) := by
  rw [ha19_1_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_1_18 j) true 19 18 j (ha19_1_18_contains j)
noncomputable def hk19_1_20 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_20 j i k)
lemma hk19_1_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_1_20 j i k).Contains (fullFactor true 19 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_1_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel19_0 j i k) (mpower1_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 20 (kernel19_0_contains j i k) (mpower1_20_contains j i k)
noncomputable def ha19_1_20 : Fin 7 → CBox := ![⟨⟨(-25),25⟩,⟨(-25),25⟩⟩,⟨⟨(-1817),1817⟩,⟨(-1815),1819⟩⟩,⟨⟨(-98),98⟩,⟨(-98),98⟩⟩,⟨⟨6034,6037⟩,⟨3573,3576⟩⟩,⟨⟨4168514139000,4168514139002⟩,⟨9557110918625,9557110918627⟩⟩,⟨⟨(-351677491006819747),(-351677491006819616)⟩,⟨1745383297749337746,1745383297749337877⟩⟩,⟨⟨1437917628321945988094,1437917628321945998151⟩,⟨1108550268933949104887,1108550268933949114978⟩⟩]
lemma ha19_1_20_eq (j : Fin 7) : ha19_1_20 j = ((ha19_1_19 j).mul (piI.mul (atomPoints j).z)).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha19_1_20_contains (j : Fin 7) : (ha19_1_20 j).Contains (fullFactor true 19 20 ((j.val:ℝ)/6)) := by
  rw [ha19_1_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_1_19 j) true 19 19 j (ha19_1_19_contains j)
noncomputable def hk19_1_21 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_21 j i k)
lemma hk19_1_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_1_21 j i k).Contains (fullFactor true 19 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_1_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel19_0 j i k) (mpower1_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 21 (kernel19_0_contains j i k) (mpower1_21_contains j i k)
noncomputable def ha19_1_21 : Fin 7 → CBox := ![⟨⟨(-11),11⟩,⟨(-11),11⟩⟩,⟨⟨(-985),986⟩,⟨(-986),985⟩⟩,⟨⟨(-48),48⟩,⟨(-48),48⟩⟩,⟨⟨55,57⟩,⟨(-1951),(-1949)⟩⟩,⟨⟨1801760208527,1801760208529⟩,⟨(-1606710477281),(-1606710477279)⟩⟩,⟨⟨351337890488046537,351337890488046567⟩,⟨9877352984422367,9877352984422398⟩⟩,⟨⟨177761965255747286071,177761965255747287897⟩,⟨(-257167342825200565744),(-257167342825200563923)⟩⟩]
lemma ha19_1_21_eq (j : Fin 7) : ha19_1_21 j = ((ha19_1_20 j).mul (piI.mul (atomPoints j).z)).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha19_1_21_contains (j : Fin 7) : (ha19_1_21 j).Contains (fullFactor true 19 21 ((j.val:ℝ)/6)) := by
  rw [ha19_1_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_1_20 j) true 19 20 j (ha19_1_20_contains j)
noncomputable def hk19_1_22 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_22 j i k)
lemma hk19_1_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_1_22 j i k).Contains (fullFactor true 19 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_1_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel19_0 j i k) (mpower1_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 22 (kernel19_0_contains j i k) (mpower1_22_contains j i k)
noncomputable def ha19_1_22 : Fin 7 → CBox := ![⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨(-511),510⟩,⟨(-510),511⟩⟩,⟨⟨(-22),22⟩,⟨(-22),22⟩⟩,⟨⟨(-461),(-459)⟩,⟨237,239⟩⟩,⟨⟨(-461513364174),(-461513364172)⟩,⟨(-267698800120),(-267698800119)⟩⟩,⟨⟨(-9413506134254430),(-9413506134254422)⟩,⟨(-65557998256255393),(-65557998256255386)⟩⟩,⟨⟨(-43728042347851890679),(-43728042347851890364)⟩,⟨(-26982450486785325981),(-26982450486785325665)⟩⟩]
lemma ha19_1_22_eq (j : Fin 7) : ha19_1_22 j = ((ha19_1_21 j).mul (piI.mul (atomPoints j).z)).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha19_1_22_contains (j : Fin 7) : (ha19_1_22 j).Contains (fullFactor true 19 22 ((j.val:ℝ)/6)) := by
  rw [ha19_1_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_1_21 j) true 19 21 j (ha19_1_21_contains j)
noncomputable def hk19_1_23 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_23 j i k)
lemma hk19_1_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_1_23 j i k).Contains (fullFactor true 19 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_1_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel19_0 j i k) (mpower1_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 23 (kernel19_0_contains j i k) (mpower1_23_contains j i k)
noncomputable def ha19_1_23 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-253),253⟩,⟨(-253),253⟩⟩,⟨⟨(-10),10⟩,⟨(-10),10⟩⟩,⟨⟨109,110⟩,⟨72,74⟩⟩,⟨⟨(-23365578623),(-23365578622)⟩,⟨110341124418,110341124420⟩⟩,⟨⟨(-11356254381754053),(-11356254381754050)⟩,⟨3679555987312379,3679555987312382⟩⟩,⟨⟨(-3879276961626668024),(-3879276961626667971)⟩,⟨7085638467945122390,7085638467945122443⟩⟩]
lemma ha19_1_23_eq (j : Fin 7) : ha19_1_23 j = ((ha19_1_22 j).mul (piI.mul (atomPoints j).z)).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha19_1_23_contains (j : Fin 7) : (ha19_1_23 j).Contains (fullFactor true 19 23 ((j.val:ℝ)/6)) := by
  rw [ha19_1_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_1_22 j) true 19 22 j (ha19_1_22_contains j)
noncomputable def hk19_1_24 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_24 j i k)
lemma hk19_1_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_1_24 j i k).Contains (fullFactor true 19 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_1_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel19_0 j i k) (mpower1_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 24 (kernel19_0_contains j i k) (mpower1_24_contains j i k)
noncomputable def ha19_1_24 : Fin 7 → CBox := ![⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-121),121⟩,⟨(-121),121⟩⟩,⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨2,3⟩,⟨(-33),(-31)⟩⟩,⟨⟨22715915964,22715915966⟩,⟨(-2469058938),(-2469058937)⟩⟩,⟨⟨959597610884631,959597610884633⟩,⟨1825088800909163,1825088800909164⟩⟩,⟨⟨1096452077255351093,1096452077255351102⟩,⟨528236500791581099,528236500791581109⟩⟩]
lemma ha19_1_24_eq (j : Fin 7) : ha19_1_24 j = ((ha19_1_23 j).mul (piI.mul (atomPoints j).z)).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha19_1_24_contains (j : Fin 7) : (ha19_1_24 j).Contains (fullFactor true 19 24 ((j.val:ℝ)/6)) := by
  rw [ha19_1_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_1_23 j) true 19 23 j (ha19_1_23_contains j)
noncomputable def hk19_1_25 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_25 j i k)
lemma hk19_1_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_1_25 j i k).Contains (fullFactor true 19 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_1_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel19_0 j i k) (mpower1_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 25 (kernel19_0_contains j i k) (mpower1_25_contains j i k)
noncomputable def ha19_1_25 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-56),56⟩,⟨(-56),56⟩⟩,⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-8),(-6)⟩,⟨2,4⟩⟩,⟨⟨(-1833189422),(-1833189421)⟩,⟨(-4048231278),(-4048231277)⟩⟩,⟨⟨271207144694150,271207144694151⟩,⟨(-208226382151770),(-208226382151769)⟩⟩,⟨⟨68063650993886843,68063650993886846⟩,⟨(-162340229620754464),(-162340229620754462)⟩⟩]
lemma ha19_1_25_eq (j : Fin 7) : ha19_1_25 j = ((ha19_1_24 j).mul (piI.mul (atomPoints j).z)).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha19_1_25_contains (j : Fin 7) : (ha19_1_25 j).Contains (fullFactor true 19 25 ((j.val:ℝ)/6)) := by
  rw [ha19_1_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_1_24 j) true 19 24 j (ha19_1_24_contains j)
noncomputable def hk19_1_26 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_26 j i k)
lemma hk19_1_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_1_26 j i k).Contains (fullFactor true 19 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_1_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel19_0 j i k) (mpower1_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 26 (kernel19_0_contains j i k) (mpower1_26_contains j i k)
noncomputable def ha19_1_26 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-25),25⟩,⟨(-25),25⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨1,2⟩,⟨0,2⟩⟩,⟨⟨(-612494206),(-612494205)⟩,⟨561685720,561685721⟩⟩,⟨⟨(-40064575853804),(-40064575853803)⟩,⟨(-36973330155125),(-36973330155124)⟩⟩,⟨⟨(-23038282165670420),(-23038282165670419)⟩,⟨(-8280632562132854),(-8280632562132852)⟩⟩]
lemma ha19_1_26_eq (j : Fin 7) : ha19_1_26 j = ((ha19_1_25 j).mul (piI.mul (atomPoints j).z)).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha19_1_26_contains (j : Fin 7) : (ha19_1_26 j).Contains (fullFactor true 19 26 ((j.val:ℝ)/6)) := by
  rw [ha19_1_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_1_25 j) true 19 25 j (ha19_1_25_contains j)
noncomputable def hk19_1_27 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_27 j i k)
lemma hk19_1_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_1_27 j i k).Contains (fullFactor true 19 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_1_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel19_0 j i k) (mpower1_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 27 (kernel19_0_contains j i k) (mpower1_27_contains j i k)
noncomputable def ha19_1_27 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-11),11⟩,⟨(-11),11⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),0⟩⟩,⟨⟨130486259,130486260⟩,⟨73280093,73280094⟩⟩,⟨⟨(-4549233949320),(-4549233949319)⟩,⟨7026524284556,7026524284557⟩⟩,⟨⟨(-947244603155260),(-947244603155259)⟩,⟨3138767367946408,3138767367946409⟩⟩]
lemma ha19_1_27_eq (j : Fin 7) : ha19_1_27 j = ((ha19_1_26 j).mul (piI.mul (atomPoints j).z)).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha19_1_27_contains (j : Fin 7) : (ha19_1_27 j).Contains (fullFactor true 19 27 ((j.val:ℝ)/6)) := by
  rw [ha19_1_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_1_26 j) true 19 26 j (ha19_1_26_contains j)
noncomputable def hk19_1_28 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_28 j i k)
lemma hk19_1_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_1_28 j i k).Contains (fullFactor true 19 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_1_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel19_0 j i k) (mpower1_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 28 (kernel19_0_contains j i k) (mpower1_28_contains j i k)
noncomputable def ha19_1_28 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨5029287,5029288⟩,⟨(-25496092),(-25496091)⟩⟩,⟨⟨1139624293182,1139624293183⟩,⟨487005392314,487005392315⟩⟩,⟨⟨411144213963953,411144213963954⟩,⟨101112430385583,101112430385584⟩⟩]
lemma ha19_1_28_eq (j : Fin 7) : ha19_1_28 j = ((ha19_1_27 j).mul (piI.mul (atomPoints j).z)).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha19_1_28_contains (j : Fin 7) : (ha19_1_28 j).Contains (fullFactor true 19 28 ((j.val:ℝ)/6)) := by
  rw [ha19_1_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_1_27 j) true 19 27 j (ha19_1_27_contains j)
noncomputable def hk19_1_29 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_29 j i k)
lemma hk19_1_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_1_29 j i k).Contains (fullFactor true 19 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_1_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel19_0 j i k) (mpower1_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 29 (kernel19_0_contains j i k) (mpower1_29_contains j i k)
noncomputable def ha19_1_29 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-4324581),(-4324580)⟩,⟨531048,531049⟩⟩,⟨⟨40928209307,40928209308⟩,⟨(-172369067627),(-172369067626)⟩⟩,⟨⟨9928196238362,9928196238363⟩,⟨(-51849609739056),(-51849609739055)⟩⟩]
lemma ha19_1_29_eq (j : Fin 7) : ha19_1_29 j = ((ha19_1_28 j).mul (piI.mul (atomPoints j).z)).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha19_1_29_contains (j : Fin 7) : (ha19_1_29 j).Contains (fullFactor true 19 29 ((j.val:ℝ)/6)) := by
  rw [ha19_1_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_1_28 j) true 19 28 j (ha19_1_28_contains j)
noncomputable def hk19_1_30 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_30 j i k)
lemma hk19_1_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk19_1_30 j i k).Contains (fullFactor true 19 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk19_1_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel19_0 j i k) (mpower1_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 19 30 (kernel19_0_contains j i k) (mpower1_30_contains j i k)
noncomputable def ha19_1_30 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨300223,300225⟩,⟨639159,639160⟩⟩,⟨⟨(-24433487104),(-24433487103)⟩,⟨(-1526781627),(-1526781626)⟩⟩,⟨⟨(-6303151385546),(-6303151385545)⟩,⟨(-870500000282),(-870500000281)⟩⟩]
lemma ha19_1_30_eq (j : Fin 7) : ha19_1_30 j = ((ha19_1_29 j).mul (piI.mul (atomPoints j).z)).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha19_1_30_contains (j : Fin 7) : (ha19_1_30 j).Contains (fullFactor true 19 30 ((j.val:ℝ)/6)) := by
  rw [ha19_1_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha19_1_29 j) true 19 29 j (ha19_1_29_contains j)
end SharpPlanar.CachedData

end OAI
