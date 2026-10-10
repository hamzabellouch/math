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
noncomputable def hk9_0_0 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_0 j i k)
lemma hk9_0_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_0_0 j i k).Contains (fullFactor false 9 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_0_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power9 j i k) (mpower0_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 0 (power9_contains j i k) (mpower0_0_contains j i k)
noncomputable def ha9_0_0 : Fin 7 → CBox := ![⟨⟨999999999999999999999999999893,1000000000000000000000000000143⟩,⟨(-143),143⟩⟩,⟨⟨(-15481194292),22551044425⟩,⟨(-1000000000000000000018917712483),(-999999999999999999981082287531)⟩⟩,⟨⟨(-1000000000000000000051861281538),(-999999999999999999948138718466)⟩,⟨(-58859103936),44719403622⟩⟩,⟨⟨(-40004849897),18795299435⟩,⟨999999999999999999970599925343,1000000000000000000029400074666⟩⟩,⟨⟨999999999999999999858301105358,1000000000000000000141698894621⟩,⟨(-127611850236),155891250888⟩⟩,⟨⟨(-160676030550),196025281331⟩,⟨(-1000000000000000000178402917707),(-999999999999999999821597082270)⟩⟩,⟨⟨(-1000000000000000000058978780073),(-999999999999999999941021219963)⟩,⟨(-80188330553),37769229557⟩⟩]
lemma ha9_0_0_eq (j : Fin 7) : ha9_0_0 j = ((atomPoints j).direct.powBin 7 9).conj := by fin_cases j <;> decide +kernel
lemma ha9_0_0_contains (j : Fin 7) : (ha9_0_0 j).Contains (fullFactor false 9 0 ((j.val:ℝ)/6)) := by
  rw [ha9_0_0_eq]
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @direct_factor_zero_full ((atomPoints j).direct.powBin 7 9) ((j.val:ℝ)/6) 9 (@direct_power_bin_contains (atomPoints j) ((j.val:ℝ)/6) (atomPoints_contains j) 9 (by norm_num))
noncomputable def hk9_0_1 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_1 j i k)
lemma hk9_0_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_0_1 j i k).Contains (fullFactor false 9 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_0_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power9 j i k) (mpower0_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 1 (power9_contains j i k) (mpower0_1_contains j i k)
noncomputable def ha9_0_1 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨523598775598298873066761375578,523598775598298873088238624429⟩,⟨(-8105934377),11807699250⟩⟩,⟨⟨(-46830049964),61637109508⟩,⟨(-1047197551196597746210975673698),(-1047197551196597746099024326307)⟩⟩,⟨⟨(-1570796326794896619281181529293),(-1570796326794896619183818470721)⟩,⟨(-62839471273),29523587314⟩⟩,⟨⟨(-326497872366),267269634142⟩,⟨2094395102393195492009893195711,2094395102393195492610106804244⟩⟩,⟨⟨2617993877991494364916275586899,2617993877991494365858724413042⟩,⟨(-420648864320),513192986457⟩⟩,⟨⟨(-118655534109),251919070169⟩,⟨(-3141592653589793238655287302196),(-3141592653589793238274712697918)⟩⟩]
lemma ha9_0_1_eq (j : Fin 7) : ha9_0_1 j = ((ha9_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha9_0_1_contains (j : Fin 7) : (ha9_0_1 j).Contains (fullFactor false 9 1 ((j.val:ℝ)/6)) := by
  rw [ha9_0_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_0_0 j) false 9 0 j (ha9_0_0_contains j)
noncomputable def hk9_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_2 j i k)
lemma hk9_0_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_0_2 j i k).Contains (fullFactor false 9 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_0_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power9 j i k) (mpower0_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 2 (power9_contains j i k) (mpower0_2_contains j i k)
noncomputable def ha9_0_2 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-3091248435),2122128658⟩,⟨137077838904018869703210719368,137077838904018869709269782284⟩⟩,⟨⟨548311355616075478794779544465,548311355616075478855142462141⟩,⟨(-24520156823),32273115070⟩⟩,⟨⟨(-23187771254),49354005327⟩,⟨(-1233700550136169827396360136536),(-1233700550136169827315964378333)⟩⟩,⟨⟨(-2193245422464301915617605782214),(-2193245422464301914982082244150)⟩,⟨(-341907772413),279884106383⟩⟩,⟨⟨(-671768048387),550628075787⟩,⟨3426945972600471742033720802391,3426945972600471743278291738803⟩⟩,⟨⟨4934802200544679309117892452934,4934802200544679309731405606674⟩,⟨(-186383677133),395713550072⟩⟩]
lemma ha9_0_2_eq (j : Fin 7) : ha9_0_2 j = ((ha9_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha9_0_2_contains (j : Fin 7) : (ha9_0_2 j).Contains (fullFactor false 9 2 ((j.val:ℝ)/6)) := by
  rw [ha9_0_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_0_1 j) false 9 1 j (ha9_0_1_contains j)
noncomputable def hk9_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_3 j i k)
lemma hk9_0_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_0_3 j i k).Contains (fullFactor false 9 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_0_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power9 j i k) (mpower0_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 3 (power9_contains j i k) (mpower0_3_contains j i k)
noncomputable def ha9_0_3 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-23924596203935046432315357705),(-23924596203935046431181697374)⟩,⟨(-539524632),370381323⟩⟩,⟨⟨(-11265442357),8559149394⟩,⟨191396769631480371443148286301,191396769631480371464828154334⟩⟩,⟨⟨645964097506246253635134599502,645964097506246253679285887645⟩,⟨(-12141088638),25841696761⟩⟩,⟨⟨(-195395967216),238696654671⟩,⟨(-1531174157051842971856182266143),(-1531174157051842971407629258896)⟩⟩,⟨⟨(-2990574525491880804516372104984),(-2990574525491880803420759779860)⟩,⟨(-586228212703),480513643821⟩⟩,⟨⟨(-414390260611),195180530277⟩,⟨5167712780049970028928222542209,5167712780049970029587141355102⟩⟩]
lemma ha9_0_3_eq (j : Fin 7) : ha9_0_3 j = ((ha9_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha9_0_3_contains (j : Fin 7) : (ha9_0_3 j).Contains (fullFactor false 9 3 ((j.val:ℝ)/6)) := by
  rw [ha9_0_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_0_2 j) false 9 2 j (ha9_0_2_contains j)
noncomputable def hk9_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_4 j i k)
lemma hk9_0_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_0_4 j i k).Contains (fullFactor false 9 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_0_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power9 j i k) (mpower0_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 4 (power9_contains j i k) (mpower0_4_contains j i k)
noncomputable def ha9_0_4 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-48482802),70623610⟩,⟨(-3131722319766024859799237881),(-3131722319766024859640873508)⟩⟩,⟨⟨(-50107557116256397758438527860),(-50107557116256397752603254372)⟩,⟨(-2949285913),2240780072⟩⟩,⟨⟨(-10148010588),4767794359⟩,⟨253669507901048013628251698558,253669507901048013646397323991⟩⟩,⟨⟨801720913860102363969627376684,801720913860102364207041139001⟩,⟨(-102309089192),124981276126⟩⟩,⟨⟨(-314495444454),383685467991⟩,⟨(-1957326449853765537686688285964),(-1957326449853765536963381332409)⟩⟩,⟨⟨(-4058712126416768218462408634160),(-4058712126416768217931975726735)⟩,⟨(-325461349614),153294430011⟩⟩]
lemma ha9_0_4_eq (j : Fin 7) : ha9_0_4 j = ((ha9_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha9_0_4_contains (j : Fin 7) : (ha9_0_4 j).Contains (fullFactor false 9 4 ((j.val:ℝ)/6)) := by
  rw [ha9_0_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_0_3 j) false 9 3 j (ha9_0_3_contains j)
noncomputable def hk9_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_5 j i k)
lemma hk9_0_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_0_5 j i k).Contains (fullFactor false 9 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_0_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power9 j i k) (mpower0_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 5 (power9_contains j i k) (mpower0_5_contains j i k)
noncomputable def ha9_0_5 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨327953194428670967566513063,327953194428670967584140850⟩,⟨(-5077108),7395688⟩⟩,⟨⟨(-469307881),617696998⟩,⟨(-10494502221717470963038233533),(-10494502221717470961782691673)⟩⟩,⟨⟨(-79692626246167045123781593325),(-79692626246167045117827307461)⟩,⟨(-3188091552),1497846774⟩⟩,⟨⟨(-52352034522),42855131067⟩,⟨335824071094959070746876500582,335824071094959070847393106010⟩⟩,⟨⟨1024853732589596773481904315566,1024853732589596773863889161582⟩,⟨(-164669429648),200897241255⟩⟩,⟨⟨(-96317731032),204493396995⟩,⟨(-2550164039877345444036441537248),(-2550164039877345443695043287957)⟩⟩]
lemma ha9_0_5_eq (j : Fin 7) : ha9_0_5 j = ((ha9_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha9_0_5_contains (j : Fin 7) : (ha9_0_5 j).Contains (fullFactor false 9 5 ((j.val:ℝ)/6)) := by
  rw [ha9_0_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_0_4 j) false 9 4 j (ha9_0_4_contains j)
noncomputable def hk9_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_6 j i k)
lemma hk9_0_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_0_6 j i k).Contains (fullFactor false 9 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_0_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power9 j i k) (mpower0_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 6 (power9_contains j i k) (mpower0_6_contains j i k)
noncomputable def ha9_0_6 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-645396),443062⟩,⟨28619315176067161690742961,28619315176067161692372375⟩⟩,⟨⟨1831636171268298348147208893,1831636171268298348372172567⟩,⟨(-81909678),107808464⟩⟩,⟨⟨(-392135369),834640417⟩,⟨(-20863480763352960873958159178),(-20863480763352960872332920262)⟩⟩,⟨⟨(-117224714961171094306350232815),(-117224714961171094270890180604)⟩,⟨(-18274307451),14959262770⟩⟩,⟨⟨(-87657957952),71850593119⟩,⟨447176799626049401346540687412,447176799626049401514636426768⟩⟩,⟨⟨1335262768854589495789811552731,1335262768854589495972817531452⟩,⟨(-50431846037),107072492285⟩⟩]
lemma ha9_0_6_eq (j : Fin 7) : ha9_0_6 j = ((ha9_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha9_0_6_contains (j : Fin 7) : (ha9_0_6 j).Contains (fullFactor false 9 6 ((j.val:ℝ)/6)) := by
  rw [ha9_0_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_0_5 j) false 9 5 j (ha9_0_5_contains j)
noncomputable def hk9_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_7 j i k)
lemma hk9_0_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_0_7 j i k).Contains (fullFactor false 9 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_0_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power9 j i k) (mpower0_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 7 (power9_contains j i k) (mpower0_7_contains j i k)
noncomputable def ha9_0_7 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-2140719769235797028281105),(-2140719769235797028152410)⟩,⟨(-48276),33141⟩⟩,⟨⟨(-16128109),12253660⟩,⟨274012130462182019594481548,274012130462182019629008243⟩⟩,⟨⟨4681754135318688100520244924,4681754135318688100899850171⟩,⟨(-87994972),187292872⟩⟩,⟨⟨(-4475800955),5467660004⟩,⟨(-35073552699159298515663979303),(-35073552699159298504942713904)⟩⟩,⟨⟨(-167243731971546642861134146643),(-167243731971546642797734133801)⟩,⟨(-32783999611),26872058988⟩⟩,⟨⟨(-48054022167),22633759574⟩,⟨599264529320792076848865881410,599264529320792076932906290839⟩⟩]
lemma ha9_0_7_eq (j : Fin 7) : ha9_0_7 j = ((ha9_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha9_0_7_contains (j : Fin 7) : (ha9_0_7 j).Contains (fullFactor false 9 7 ((j.val:ℝ)/6)) := by
  rw [ha9_0_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_0_6 j) false 9 6 j (ha9_0_6_contains j)
noncomputable def hk9_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_8 j i k)
lemma hk9_0_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_0_8 j i k).Contains (fullFactor false 9 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_0_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power9 j i k) (mpower0_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 8 (power9_contains j i k) (mpower0_8_contains j i k)
noncomputable def ha9_0_8 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-2170),3160⟩,⟨(-140109781258867029458365),(-140109781258867029449495)⟩⟩,⟨⟨(-35868104002269959542522857),(-35868104002269959537889150)⟩,⟨(-2111165),1604001⟩⟩,⟨⟨(-36774870),17277773⟩,⟨919260274839426580208502065,919260274839426580285963478⟩⟩,⟨⟨9182234624581109640874712580,9182234624581109643710761260⟩,⟨(-1171761950),1431430042⟩⟩,⟨⟨(-8793860740),10728538785⟩,⟨(-54730383304244933390902198618),(-54730383304244933369980380711)⟩⟩,⟨⟨(-235330630358893204560167425725),(-235330630358893204526415753454)⟩,⟨(-18870770377),8888256601⟩⟩]
lemma ha9_0_8_eq (j : Fin 7) : ha9_0_8 j = ((ha9_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha9_0_8_contains (j : Fin 7) : (ha9_0_8 j).Contains (fullFactor false 9 8 ((j.val:ℝ)/6)) := by
  rw [ha9_0_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_0_7 j) false 9 7 j (ha9_0_7_contains j)
noncomputable def hk9_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_9 j i k)
lemma hk9_0_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_0_9 j i k).Contains (fullFactor false 9 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_0_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power9 j i k) (mpower0_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 9 (power9_contains j i k) (mpower0_9_contains j i k)
noncomputable def ha9_0_9 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨8151256657387584304649,8151256657387584305192⟩,⟨(-127),184⟩⟩,⟨⟨(-186634),245646⟩,⟨(-4173443408582443164395357),(-4173443408582443163842915)⟩⟩,⟨⟨(-160441184787359821880759176),(-160441184787359821866728908)⟩,⟨(-6418426),3015541⟩⟩,⟨⟨(-333108897),272681388⟩,⟨2136803025194210899695607445,2136803025194210900362387597⟩⟩,⟨⟨15920423158960125592478947177,15920423158960125598615533591⟩,⟨(-2558030398),3120805429⟩⟩,⟨⟨(-3102586849),6587141510⟩,⟨(-82145886611128228805378466955),(-82145886611128228793335432292)⟩⟩]
lemma ha9_0_9_eq (j : Fin 7) : ha9_0_9 j = ((ha9_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha9_0_9_contains (j : Fin 7) : (ha9_0_9 j).Contains (fullFactor false 9 9 ((j.val:ℝ)/6)) := by
  rw [ha9_0_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_0_8 j) false 9 8 j (ha9_0_8_contains j)
noncomputable def hk9_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_10 j i k)
lemma hk9_0_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_0_10 j i k).Contains (fullFactor false 9 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_0_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power9 j i k) (mpower0_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 10 (power9_contains j i k) (mpower0_10_contains j i k)
noncomputable def ha9_0_10 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-10),7⟩,⟨426798800539562151439,426798800539562151470⟩⟩,⟨⟨437041971752511643059878,437041971752511643119122⟩,⟨(-19545),25724⟩⟩,⟨⟨(-473681),1008204⟩,⟨(-25202042373060605482384116),(-25202042373060605480100025)⟩⟩,⟨⟨(-447530979074571922594185238),(-447530979074571922453110593)⟩,⟨(-69766165),57110257⟩⟩,⟨⟨(-817024951),669690793⟩,⟨4167957036519161634488817362,4167957036519161636108638948⟩⟩,⟨⟨25806891390014060010859092218,25806891390014060014724669028⟩,⟨(-974706406),2069411538⟩⟩]
lemma ha9_0_10_eq (j : Fin 7) : ha9_0_10 j = ((ha9_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha9_0_10_contains (j : Fin 7) : (ha9_0_10 j).Contains (fullFactor false 9 10 ((j.val:ℝ)/6)) := by
  rw [ha9_0_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_0_9 j) false 9 9 j (ha9_0_9_contains j)
noncomputable def hk9_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_11 j i k)
lemma hk9_0_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_0_11 j i k).Contains (fullFactor false 9 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_0_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power9 j i k) (mpower0_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 11 (power9_contains j i k) (mpower0_11_contains j i k)
noncomputable def ha9_0_11 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-20315575399030665722),(-20315575399030665720)⟩,⟨(-1),1⟩⟩,⟨⟨(-2449),1861⟩,⟨41606298417214803393840,41606298417214803399613⟩⟩,⟨⟨3598843235212085340319424,3598843235212085340657048⟩,⟨(-67642),143972⟩⟩,⟨⟨(-10873768),13283447⟩,⟨(-85209699158455917370061735),(-85209699158455917342929954)⟩⟩,⟨⟨(-991971455030794224855365154),(-991971455030794224466690974)⟩,⟨(-194451484),159386037⟩⟩,⟨⟨(-591022554),278375499⟩,⟨7370430945714350776756173426,7370430945714350777883640392⟩⟩]
lemma ha9_0_11_eq (j : Fin 7) : ha9_0_11 j = ((ha9_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha9_0_11_contains (j : Fin 7) : (ha9_0_11 j).Contains (fullFactor false 9 11 ((j.val:ℝ)/6)) := by
  rw [ha9_0_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_0_10 j) false 9 10 j (ha9_0_10_contains j)
noncomputable def hk9_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_12 j i k)
lemma hk9_0_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_0_12 j i k).Contains (fullFactor false 9 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_0_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power9 j i k) (mpower0_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 12 (power9_contains j i k) (mpower0_12_contains j i k)
noncomputable def ha9_0_12 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-886434200375614886),(-886434200375614885)⟩⟩,⟨⟨(-3630834484738518571314),(-3630834484738518570798)⟩,⟨(-214),163⟩⟩,⟨⟨(-18846),8855⟩,⟨471087477881817150348421,471087477881817150394116⟩⟩,⟨⟨14871898049488972064655115,14871898049488972069437844⟩,⟨(-1897831),2318399⟩⟩,⟨⟨(-34772640),42422733⟩,⟨(-216414599701077852950892727),(-216414599701077852865408304)⟩⟩,⟨⟨(-1929574309403923048071370939),(-1929574309403923047770058750)⟩,⟨(-154729343),72878536⟩⟩]
lemma ha9_0_12_eq (j : Fin 7) : ha9_0_12 j = ((ha9_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha9_0_12_contains (j : Fin 7) : (ha9_0_12 j).Contains (fullFactor false 9 12 ((j.val:ℝ)/6)) := by
  rw [ha9_0_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_0_11 j) false 9 11 j (ha9_0_11_contains j)
noncomputable def hk9_0_13 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_13 j i k)
lemma hk9_0_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_0_13 j i k).Contains (fullFactor false 9 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_0_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power9 j i k) (mpower0_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 13 (power9_contains j i k) (mpower0_13_contains j i k)
noncomputable def ha9_0_13 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨35702758612702236,35702758612702237⟩,⟨(-1),1⟩⟩,⟨⟨(-14),18⟩,⟨(-292476998555256723048),(-292476998555256723004)⟩⟩,⟨⟨(-56921729219679268121159),(-56921729219679268115456)⟩,⟨(-2278),1070⟩⟩,⟨⟨(-373512),305755⟩,⟨2395971572164663074640913,2395971572164663075419073⟩⟩,⟨⟨43582469009646285022481088,43582469009646285039835024⟩,⟨(-7002659),8543266⟩⟩,⟨⟨(-17611898),37392044⟩,⟨(-466302805767612564462326024),(-466302805767612564388026339)⟩⟩]
lemma ha9_0_13_eq (j : Fin 7) : ha9_0_13 j = ((ha9_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha9_0_13_contains (j : Fin 7) : (ha9_0_13 j).Contains (fullFactor false 9 13 ((j.val:ℝ)/6)) := by
  rw [ha9_0_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_0_12 j) false 9 12 j (ha9_0_12_contains j)
noncomputable def hk9_0_14 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_14 j i k)
lemma hk9_0_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_0_14 j i k).Contains (fullFactor false 9 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_0_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power9 j i k) (mpower0_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 14 (power9_contains j i k) (mpower0_14_contains j i k)
noncomputable def ha9_0_14 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨1335280049649465,1335280049649466⟩⟩,⟨⟨21877228333456835515,21877228333456835520⟩,⟨(-2),2⟩⟩,⟨⟨(-121),256⟩,⟨(-6386603083791852241488),(-6386603083791852240826)⟩⟩,⟨⟨(-358436509015356793180286),(-358436509015356793062732)⟩,⟨(-55878),45741⟩⟩,⟨⟨(-1597588),1309495⟩,⟨8149902646786285755515023,8149902646786285758786145⟩⟩,⟨⟨104638104924845707110612683,104638104924845707127618568⟩,⟨(-3952101),8390756⟩⟩]
lemma ha9_0_14_eq (j : Fin 7) : ha9_0_14 j = ((ha9_0_13 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha9_0_14_contains (j : Fin 7) : (ha9_0_14 j).Contains (fullFactor false 9 14 ((j.val:ℝ)/6)) := by
  rw [ha9_0_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_0_13 j) false 9 13 j (ha9_0_13_contains j)
noncomputable def hk9_0_15 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_15 j i k)
lemma hk9_0_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_0_15 j i k).Contains (fullFactor false 9 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_0_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power9 j i k) (mpower0_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 15 (power9_contains j i k) (mpower0_15_contains j i k)
noncomputable def ha9_0_15 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-46610066605154),(-46610066605153)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨1527318662517654886,1527318662517654887⟩⟩,⟨⟨668803510981146723219,668803510981146723292⟩,⟨(-13),27⟩⟩,⟨⟨(-6387),7803⟩,⟨(-50047177933378515336306),(-50047177933378515319732)⟩⟩,⟨⟨(-1422426349034211493123578),(-1422426349034211492548131)⟩,⟨(-278832),228550⟩⟩,⟨⟨(-1757356),827727⟩,⟨21915353447830215825815512,21915353447830215829446976⟩⟩]
lemma ha9_0_15_eq (j : Fin 7) : ha9_0_15 j = ((ha9_0_14 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha9_0_15_contains (j : Fin 7) : (ha9_0_15 j).Contains (fullFactor false 9 15 ((j.val:ℝ)/6)) := by
  rw [ha9_0_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_0_14 j) false 9 14 j (ha9_0_14_contains j)
noncomputable def hk9_0_16 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_16 j i k)
lemma hk9_0_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_0_16 j i k).Contains (fullFactor false 9 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_0_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power9 j i k) (mpower0_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 16 (power9_contains j i k) (mpower0_16_contains j i k)
noncomputable def ha9_0_16 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-1525310862814),(-1525310862813)⟩⟩,⟨⟨(-99962772705334444),(-99962772705334443)⟩,⟨(-1),1⟩⟩,⟨⟨(-3),2⟩,⟨65659631149794723619,65659631149794723627⟩⟩,⟨⟨6551160272016798097734,6551160272016798099925⟩,⟨(-837),1022⟩⟩,⟨⟨(-37397),45624⟩,⟨(-232743967104084891423289),(-232743967104084891328390)⟩⟩,⟨⟨(-4303069587032947007712837),(-4303069587032947006986103)⟩,⟨(-345057),162524⟩⟩]
lemma ha9_0_16_eq (j : Fin 7) : ha9_0_16 j = ((ha9_0_15 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha9_0_16_contains (j : Fin 7) : (ha9_0_16 j).Contains (fullFactor false 9 16 ((j.val:ℝ)/6)) := by
  rw [ha9_0_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_0_15 j) false 9 15 j (ha9_0_15_contains j)
noncomputable def hk9_0_17 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_17 j i k)
lemma hk9_0_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_0_17 j i k).Contains (fullFactor false 9 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_0_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power9 j i k) (mpower0_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 17 (power9_contains j i k) (mpower0_17_contains j i k)
noncomputable def ha9_0_17 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨46979464716,46979464717⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-6157692399285196),(-6157692399285195)⟩⟩,⟨⟨(-6066935731106195668),(-6066935731106195666)⟩,⟨(-1),1⟩⟩,⟨⟨(-126),104⟩,⟨807101058159109193291,807101058159109193564⟩⟩,⟨⟨35842487118702823479211,35842487118702823493941⟩,⟨(-5760),7027⟩⟩,⟨⟨(-30035),63767⟩,⟨(-795205400147551278556878),(-795205400147551278420045)⟩⟩]
lemma ha9_0_17_eq (j : Fin 7) : ha9_0_17 j = ((ha9_0_16 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha9_0_17_contains (j : Fin 7) : (ha9_0_17 j).Contains (fullFactor false 9 17 ((j.val:ℝ)/6)) := by
  rw [ha9_0_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_0_16 j) false 9 16 j (ha9_0_16_contains j)
noncomputable def hk9_0_18 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_18 j i k)
lemma hk9_0_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_0_18 j i k).Contains (fullFactor false 9 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_0_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power9 j i k) (mpower0_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 18 (power9_contains j i k) (mpower0_18_contains j i k)
noncomputable def ha9_0_18 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨1366577233,1366577234⟩⟩,⟨⟨358240022308519,358240022308520⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-529440020073462377),(-529440020073462376)⟩⟩,⟨⟨(-93910472408044662756),(-93910472408044662723)⟩,⟨(-15),13⟩⟩,⟨⟨(-1023),838⟩,⟨5213078436041832670594,5213078436041832672754⟩⟩,⟨⟨138789524622137721134393,138789524622137721158717⟩,⟨(-5243),11130⟩⟩]
lemma ha9_0_18_eq (j : Fin 7) : ha9_0_18 j = ((ha9_0_17 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha9_0_18_contains (j : Fin 7) : (ha9_0_18 j).Contains (fullFactor false 9 18 ((j.val:ℝ)/6)) := by
  rw [ha9_0_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_0_17 j) false 9 17 j (ha9_0_17_contains j)
noncomputable def hk9_0_19 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_19 j i k)
lemma hk9_0_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_0_19 j i k).Contains (fullFactor false 9 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_0_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power9 j i k) (mpower0_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 19 (power9_contains j i k) (mpower0_19_contains j i k)
noncomputable def ha9_0_19 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-37659904),(-37659903)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨19744635479057,19744635479058⟩⟩,⟨⟨43770654673137422,43770654673137423⟩,⟨(-1),1⟩⟩,⟨⟨(-2),2⟩,⟨(-10351875446044213764),(-10351875446044213759)⟩⟩,⟨⟨(-718305654265631155201),(-718305654265631154900)⟩,⟨(-141),116⟩⟩,⟨⟨(-1841),867⟩,⟨22948428997269873108483,22948428997269873112579⟩⟩]
lemma ha9_0_19_eq (j : Fin 7) : ha9_0_19 j = ((ha9_0_18 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha9_0_19_contains (j : Fin 7) : (ha9_0_19 j).Contains (fullFactor false 9 19 ((j.val:ℝ)/6)) := by
  rw [ha9_0_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_0_18 j) false 9 18 j (ha9_0_18_contains j)
noncomputable def hk9_0_20 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_20 j i k)
lemma hk9_0_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_0_20 j i k).Contains (fullFactor false 9 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_0_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power9 j i k) (mpower0_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 20 (power9_contains j i k) (mpower0_20_contains j i k)
noncomputable def ha9_0_20 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-985934),(-985933)⟩⟩,⟨⟨(-1033826696147),(-1033826696146)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨3437739179098606,3437739179098608⟩⟩,⟨⟨1084045861738968866,1084045861738968868⟩,⟨(-1),1⟩⟩,⟨⟨(-16),19⟩,⟨(-94025990269704865235),(-94025990269704865194)⟩⟩,⟨⟨(-3604730797462500934241),(-3604730797462500933586)⟩,⟨(-290),137⟩⟩]
lemma ha9_0_20_eq (j : Fin 7) : ha9_0_20 j = ((ha9_0_19 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha9_0_20_contains (j : Fin 7) : (ha9_0_20 j).Contains (fullFactor false 9 20 ((j.val:ℝ)/6)) := by
  rw [ha9_0_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_0_19 j) false 9 19 j (ha9_0_19_contains j)
noncomputable def hk9_0_21 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_21 j i k)
lemma hk9_0_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_0_21 j i k).Contains (fullFactor false 9 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_0_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power9 j i k) (mpower0_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 21 (power9_contains j i k) (mpower0_21_contains j i k)
noncomputable def ha9_0_21 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨24582,24583⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-51553370694),(-51553370693)⟩⟩,⟨⟨(-257142289286048),(-257142289286047)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨108115254456938454,108115254456938455⟩⟩,⟨⟨11721879376103578820,11721879376103578826⟩,⟨(-2),3⟩⟩,⟨⟨(-21),44⟩,⟨(-539266466260812848994),(-539266466260812848893)⟩⟩]
lemma ha9_0_21_eq (j : Fin 7) : ha9_0_21 j = ((ha9_0_20 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha9_0_21_contains (j : Fin 7) : (ha9_0_21 j).Contains (fullFactor false 9 21 ((j.val:ℝ)/6)) := by
  rw [ha9_0_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_0_20 j) false 9 20 j (ha9_0_20_contains j)
noncomputable def hk9_0_22 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_22 j i k)
lemma hk9_0_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_0_22 j i k).Contains (fullFactor false 9 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_0_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power9 j i k) (mpower0_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 22 (power9_contains j i k) (mpower0_22_contains j i k)
noncomputable def ha9_0_22 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨585,586⟩⟩,⟨⟨2453934706,2453934707⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-18359916521553),(-18359916521552)⟩⟩,⟨⟨(-10292548155845728),(-10292548155845727)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨1394900383872451219,1394900383872451220⟩⟩,⟨⟨77007071306013533791,77007071306013533807⟩,⟨(-3),7⟩⟩]
lemma ha9_0_22_eq (j : Fin 7) : ha9_0_22 j = ((ha9_0_21 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha9_0_22_contains (j : Fin 7) : (ha9_0_22 j).Contains (fullFactor false 9 22 ((j.val:ℝ)/6)) := by
  rw [ha9_0_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_0_21 j) false 9 21 j (ha9_0_21_contains j)
noncomputable def hk9_0_23 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_23 j i k)
lemma hk9_0_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_0_23 j i k).Contains (fullFactor false 9 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_0_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power9 j i k) (mpower0_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 23 (power9_contains j i k) (mpower0_23_contains j i k)
noncomputable def ha9_0_23 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-14),(-13)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨111728452,111728453⟩⟩,⟨⟨1253899540535,1253899540536⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-937246193423888),(-937246193423887)⟩⟩,⟨⟨(-158775681103741858),(-158775681103741857)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨10518471716932064454,10518471716932064457⟩⟩]
lemma ha9_0_23_eq (j : Fin 7) : ha9_0_23 j = ((ha9_0_22 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha9_0_23_contains (j : Fin 7) : (ha9_0_23 j).Contains (fullFactor false 9 23 ((j.val:ℝ)/6)) := by
  rw [ha9_0_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_0_22 j) false 9 22 j (ha9_0_22_contains j)
noncomputable def hk9_0_24 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_24 j i k)
lemma hk9_0_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_0_24 j i k).Contains (fullFactor false 9 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_0_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power9 j i k) (mpower0_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 24 (power9_contains j i k) (mpower0_24_contains j i k)
noncomputable def ha9_0_24 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-1),0⟩⟩,⟨⟨(-4875074),(-4875073)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨82067533018,82067533019⟩⟩,⟨⟨81790159885152,81790159885153⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-17319740045980250),(-17319740045980249)⟩⟩,⟨⟨(-1376864728037741371),(-1376864728037741370)⟩,⟨(-1),1⟩⟩]
lemma ha9_0_24_eq (j : Fin 7) : ha9_0_24 j = ((ha9_0_23 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha9_0_24_contains (j : Fin 7) : (ha9_0_24 j).Contains (fullFactor false 9 24 ((j.val:ℝ)/6)) := by
  rw [ha9_0_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_0_23 j) false 9 23 j (ha9_0_23_contains j)
noncomputable def hk9_0_25 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_25 j i k)
lemma hk9_0_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_0_25 j i k).Contains (fullFactor false 9 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_0_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power9 j i k) (mpower0_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 25 (power9_contains j i k) (mpower0_25_contains j i k)
noncomputable def ha9_0_25 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-204207),(-204206)⟩⟩,⟨⟨(-5156455177),(-5156455176)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨6852036411496,6852036411497⟩⟩,⟨⟨1813718936351216,1813718936351217⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-173021924583611077),(-173021924583611076)⟩⟩]
lemma ha9_0_25_eq (j : Fin 7) : ha9_0_25 j = ((ha9_0_24 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha9_0_25_contains (j : Fin 7) : (ha9_0_25 j).Contains (fullFactor false 9 25 ((j.val:ℝ)/6)) := by
  rw [ha9_0_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_0_24 j) false 9 24 j (ha9_0_24_contains j)
noncomputable def hk9_0_26 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_26 j i k)
lemma hk9_0_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_0_26 j i k).Contains (fullFactor false 9 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_0_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power9 j i k) (mpower0_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 26 (power9_contains j i k) (mpower0_26_contains j i k)
noncomputable def ha9_0_26 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨0,1⟩⟩,⟨⟨8224,8225⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-311528495),(-311528494)⟩⟩,⟨⟨(-551956596218),(-551956596217)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨182627118144797,182627118144798⟩⟩,⟨⟨20906323353147684,20906323353147685⟩,⟨(-1),1⟩⟩]
lemma ha9_0_26_eq (j : Fin 7) : ha9_0_26 j = ((ha9_0_25 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha9_0_26_contains (j : Fin 7) : (ha9_0_26 j).Contains (fullFactor false 9 26 ((j.val:ℝ)/6)) := by
  rw [ha9_0_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_0_25 j) false 9 25 j (ha9_0_25_contains j)
noncomputable def hk9_0_27 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_27 j i k)
lemma hk9_0_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_0_27 j i k).Contains (fullFactor false 9 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_0_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power9 j i k) (mpower0_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 27 (power9_contains j i k) (mpower0_27_contains j i k)
noncomputable def ha9_0_27 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨318,320⟩⟩,⟨⟨18123993,18123994⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-42815377477),(-42815377475)⟩⟩,⟨⟨(-17708025083642),(-17708025083641)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨2432561179993388,2432561179993389⟩⟩]
lemma ha9_0_27_eq (j : Fin 7) : ha9_0_27 j = ((ha9_0_26 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha9_0_27_contains (j : Fin 7) : (ha9_0_27 j).Contains (fullFactor false 9 27 ((j.val:ℝ)/6)) := by
  rw [ha9_0_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_0_26 j) false 9 26 j (ha9_0_26_contains j)
noncomputable def hk9_0_28 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_28 j i k)
lemma hk9_0_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_0_28 j i k).Contains (fullFactor false 9 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_0_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power9 j i k) (mpower0_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 28 (power9_contains j i k) (mpower0_28_contains j i k)
noncomputable def ha9_0_28 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-1),0⟩⟩,⟨⟨(-12),(-11)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨1016753,1016754⟩⟩,⟨⟨3202582746,3202582747⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1655696473582),(-1655696473581)⟩⟩,⟨⟨(-272932726159820),(-272932726159819)⟩,⟨(-1),1⟩⟩]
lemma ha9_0_28_eq (j : Fin 7) : ha9_0_28 j = ((ha9_0_27 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha9_0_28_contains (j : Fin 7) : (ha9_0_28 j).Contains (fullFactor false 9 28 ((j.val:ℝ)/6)) := by
  rw [ha9_0_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_0_27 j) false 9 27 j (ha9_0_27_contains j)
noncomputable def hk9_0_29 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_29 j i k)
lemma hk9_0_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_0_29 j i k).Contains (fullFactor false 9 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_0_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power9 j i k) (mpower0_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 29 (power9_contains j i k) (mpower0_29_contains j i k)
noncomputable def ha9_0_29 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),0⟩⟩,⟨⟨(-55073),(-55072)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨231292193,231292194⟩⟩,⟨⟨149469076953,149469076954⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-29567015428550),(-29567015428549)⟩⟩]
lemma ha9_0_29_eq (j : Fin 7) : ha9_0_29 j = ((ha9_0_28 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha9_0_29_contains (j : Fin 7) : (ha9_0_29 j).Contains (fullFactor false 9 29 ((j.val:ℝ)/6)) := by
  rw [ha9_0_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_0_28 j) false 9 28 j (ha9_0_28_contains j)
noncomputable def hk9_0_30 (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).conj.mul (mpower0_30 j i k)
lemma hk9_0_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_0_30 j i k).Contains (fullFactor false 9 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_0_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power9 j i k) (mpower0_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 30 (power9_contains j i k) (mpower0_30_contains j i k)
noncomputable def ha9_0_30 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨0,1⟩⟩,⟨⟨0,1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-2884),(-2883)⟩⟩,⟨⟨(-16147242),(-16147241)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨13043637613,13043637614⟩⟩,⟨⟨3096250615296,3096250615297⟩,⟨(-1),1⟩⟩]
lemma ha9_0_30_eq (j : Fin 7) : ha9_0_30 j = ((ha9_0_29 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha9_0_30_contains (j : Fin 7) : (ha9_0_30 j).Contains (fullFactor false 9 30 ((j.val:ℝ)/6)) := by
  rw [ha9_0_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_0_29 j) false 9 29 j (ha9_0_29_contains j)
noncomputable def hk9_1_0 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_0 j i k)
lemma hk9_1_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_1_0 j i k).Contains (fullFactor true 9 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_1_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel9_0 j i k) (mpower1_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 0 (kernel9_0_contains j i k) (mpower1_0_contains j i k)
noncomputable def ha9_1_0 : Fin 7 → CBox := ![⟨⟨0,3⟩,⟨(-3),3⟩⟩,⟨⟨(-3),2⟩,⟨(-4),0⟩⟩,⟨⟨(-13055430470),(-13055430466)⟩,⟨(-125645570149),(-125645570145)⟩⟩,⟨⟨7154252614161620552,7154252614161620589⟩,⟨(-13924345974453591569),(-13924345974453591532)⟩⟩,⟨⟨(-1698695877854235861304740),(-1698695877854235858983332)⟩,⟨(-509093624274864032090577),(-509093624274864029767916)⟩⟩,⟨⟨(-1026692507277594175516071066),(-1026692507277594173128666505)⟩,⟨1953323598494588998753708432,1953323598494589001134169251⟩⟩,⟨⟨196702530130659703536642999895,196702530130659703684165160486⟩,⟨21124309294066164671702566946,21124309294066164817617441453⟩⟩]
lemma ha9_1_0_eq (j : Fin 7) : ha9_1_0 j = atomKernel9_0 j := by fin_cases j <;> decide +kernel
lemma ha9_1_0_contains (j : Fin 7) : (ha9_1_0 j).Contains (fullFactor true 9 0 ((j.val:ℝ)/6)) := by
  rw [ha9_1_0_eq]
  simpa only [fullFactor,ite_true] using atomKernel9_0_contains j
noncomputable def hk9_1_1 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_1 j i k)
lemma hk9_1_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_1_1 j i k).Contains (fullFactor true 9 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_1_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel9_0 j i k) (mpower1_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 1 (kernel9_0_contains j i k) (mpower1_1_contains j i k)
noncomputable def ha9_1_1 : Fin 7 → CBox := ![⟨⟨(-28),0⟩,⟨(-28),28⟩⟩,⟨⟨(-31),23⟩,⟨(-8),42⟩⟩,⟨⟨(-582814768607),(-582814768566)⟩,⟨685859094687,685859094729⟩⟩,⟨⟨(-91375913998733273822),(-91375913998733273527)⟩,⟨2859794631161188478,2859794631161188773⟩⟩,⟨⟨222122721895776563286434,222122721895776577550545⟩,⟨8619414914226240484798227,8619414914226240499070203⟩⟩,⟨⟨8703009863156394059139731164,8703009863156394070573781917⟩,⟨2818607183340039793692065116,2818607183340039805139620169⟩⟩,⟨⟨39344937084074217692613206192,39344937084074218247576725826⟩,⟨(-714264540569317372231588285146),(-714264540569317371669209421945)⟩⟩]
lemma ha9_1_1_eq (j : Fin 7) : ha9_1_1 j = ((ha9_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha9_1_1_contains (j : Fin 7) : (ha9_1_1 j).Contains (fullFactor true 9 1 ((j.val:ℝ)/6)) := by
  rw [ha9_1_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_1_0 j) true 9 0 j (ha9_1_0_contains j)
noncomputable def hk9_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_2 j i k)
lemma hk9_1_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_1_2 j i k).Contains (fullFactor true 9 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_1_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel9_0 j i k) (mpower1_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 2 (kernel9_0_contains j i k) (mpower1_2_contains j i k)
noncomputable def ha9_1_2 : Fin 7 → CBox := ![⟨⟨0,130⟩,⟨(-130),130⟩⟩,⟨⟨(-104),197⟩,⟨(-204),89⟩⟩,⟨⟨3200896687215,3200896687425⟩,⟨(-187636838327),(-187636838117)⟩⟩,⟨⟨136600665429248516037,136600665429248517209⟩,⟨229340319107349378769,229340319107349379942⟩⟩,⟨⟨19742504341373547697917781,19742504341373547741757490⟩,⟨(-7043845308215801203413309),(-7043845308215801159627302)⟩⟩,⟨⟨2692635538075423827809461096,2692635538075423855247398484⟩,⟨(-18769765476717899865438273884),(-18769765476717899837991501398)⟩⟩,⟨⟨(-1293307892625183252853903107632),(-1293307892625183251782300340739)⟩,⟨(-3977871933288998970321567459),(-3977871933288997915088246138)⟩⟩]
lemma ha9_1_2_eq (j : Fin 7) : ha9_1_2 j = ((ha9_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha9_1_2_contains (j : Fin 7) : (ha9_1_2 j).Contains (fullFactor true 9 2 ((j.val:ℝ)/6)) := by
  rw [ha9_1_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_1_1 j) true 9 1 j (ha9_1_1_contains j)
noncomputable def hk9_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_3 j i k)
lemma hk9_1_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_1_3 j i k).Contains (fullFactor true 9 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_1_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel9_0 j i k) (mpower1_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 3 (kernel9_0_contains j i k) (mpower1_3_contains j i k)
noncomputable def ha9_1_3 : Fin 7 → CBox := ![⟨⟨(-400),0⟩,⟨(-400),400⟩⟩,⟨⟨(-757),377⟩,⟨(-472),651⟩⟩,⟨⟨(-5575372588060),(-5575372587353)⟩,⟨(-5187088557639),(-5187088556933)⟩⟩,⟨⟨261652184958392015520,261652184958392018625⟩,⟨(-448941596942274237145),(-448941596942274234040)⟩⟩,⟨⟨(-20819806881801901813070960),(-20819806881801901723430132)⟩,⟨(-26845406767390610548821365),(-26845406767390610459083132)⟩⟩,⟨⟨(-26192161772521422379129645263),(-26192161772521422335228650217)⟩,⟨739809024142488190247004911,739809024142488234080368651⟩⟩,⟨⟨76161520544486145692686058175,76161520544486147030190118206⟩,⟨1556971804854247129341139471991,1556971804854247130702005531942⟩⟩]
lemma ha9_1_3_eq (j : Fin 7) : ha9_1_3 j = ((ha9_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha9_1_3_contains (j : Fin 7) : (ha9_1_3 j).Contains (fullFactor true 9 3 ((j.val:ℝ)/6)) := by
  rw [ha9_1_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_1_2 j) true 9 2 j (ha9_1_2_contains j)
noncomputable def hk9_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_4 j i k)
lemma hk9_1_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_1_4 j i k).Contains (fullFactor true 9 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_1_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel9_0 j i k) (mpower1_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 4 (kernel9_0_contains j i k) (mpower1_4_contains j i k)
noncomputable def ha9_1_4 : Fin 7 → CBox := ![⟨⟨0,922⟩,⟨(-922),922⟩⟩,⟨⟨(-1162),2056⟩,⟨(-1599),1609⟩⟩,⟨⟨184076260062,184076261842⟩,⟨13563220170516,13563220172296⟩⟩,⟨⟨(-758448033051428425526),(-758448033051428419361)⟩,⟨(-16523423985783738474),(-16523423985783732309)⟩⟩,⟨⟨(-23119015114920287065250108),(-23119015114920286927519436)⟩,⟨34216910834217679136948599,34216910834217679274588783⟩⟩,⟨⟨5367402585686739206551193708,5367402585686739259066268478⟩,⟨26620420876579341259374931442,26620420876579341312015651158⟩⟩,⟨⟨1401991156137427327394072183985,1401991156137427328689875221580⟩,⟨(-141844762929760366431298371768),(-141844762929760365159522772874)⟩⟩]
lemma ha9_1_4_eq (j : Fin 7) : ha9_1_4 j = ((ha9_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha9_1_4_contains (j : Fin 7) : (ha9_1_4 j).Contains (fullFactor true 9 4 ((j.val:ℝ)/6)) := by
  rw [ha9_1_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_1_3 j) true 9 3 j (ha9_1_3_contains j)
noncomputable def hk9_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_5 j i k)
lemma hk9_1_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_1_5 j i k).Contains (fullFactor true 9 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_1_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel9_0 j i k) (mpower1_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 5 (kernel9_0_contains j i k) (mpower1_5_contains j i k)
noncomputable def ha9_1_5 : Fin 7 → CBox := ![⟨⟨(-1700),0⟩,⟨(-1700),1700⟩⟩,⟨⟨(-4342),2979⟩,⟨(-3996),3316⟩⟩,⟨⟨13789267242824,13789267246411⟩,⟨(-13545429678265),(-13545429674678)⟩⟩,⟨⟨412398437232314253707,412398437232314263497⟩,⟨784225312294913144630,784225312294913154421⟩⟩,⟨⟨38623061442207697722712866,38623061442207697891757253⟩,⟨10991756662329869415200333,10991756662329869584278972⟩⟩,⟨⟨20994402254565462265129639042,20994402254565462315609190594⟩,⟨(-8135265006310953622437971642),(-8135265006310953572089126095)⟩⟩,⟨⟨(-155092342811337823484425252151),(-155092342811337822516785160812)⟩,⟨(-1007198380765596727908354253728),(-1007198380765596726921517513511)⟩⟩]
lemma ha9_1_5_eq (j : Fin 7) : ha9_1_5 j = ((ha9_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha9_1_5_contains (j : Fin 7) : (ha9_1_5 j).Contains (fullFactor true 9 5 ((j.val:ℝ)/6)) := by
  rw [ha9_1_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_1_4 j) true 9 4 j (ha9_1_4_contains j)
noncomputable def hk9_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_6 j i k)
lemma hk9_1_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_1_6 j i k).Contains (fullFactor true 9 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_1_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel9_0 j i k) (mpower1_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 6 (kernel9_0_contains j i k) (mpower1_6_contains j i k)
noncomputable def ha9_1_6 : Fin 7 → CBox := ![⟨⟨0,2612⟩,⟨(-2612),2612⟩⟩,⟨⟨(-6283),7603⟩,⟨(-6083),7797⟩⟩,⟨⟨(-22942183490918),(-22942183484895)⟩,⟨(-720880903737),(-720880897714)⟩⟩,⟨⟨473160103751570248353,473160103751570261310⟩,⟨(-720999141085659263772),(-720999141085659250816)⟩⟩,⟨⟨(-1290984748966059446520855),(-1290984748966059273578866)⟩,⟨(-32515759337148378579861221),(-32515759337148378406891445)⟩⟩,⟨⟨(-8003571526609040643382188445),(-8003571526609040603149555338)⟩,⟨(-13339773373207868626948550359),(-13339773373207868586619199547)⟩⟩,⟨⟨(-601316228266459635783903018074),(-601316228266459635157759704412)⟩,⟨124861251064675641912314993814,124861251064675642525958307922⟩⟩]
lemma ha9_1_6_eq (j : Fin 7) : ha9_1_6 j = ((ha9_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha9_1_6_contains (j : Fin 7) : (ha9_1_6 j).Contains (fullFactor true 9 6 ((j.val:ℝ)/6)) := by
  rw [ha9_1_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_1_5 j) true 9 5 j (ha9_1_5_contains j)
noncomputable def hk9_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_7 j i k)
lemma hk9_1_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_1_7 j i k).Contains (fullFactor true 9 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_1_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel9_0 j i k) (mpower1_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 7 (kernel9_0_contains j i k) (mpower1_7_contains j i k)
noncomputable def ha9_1_7 : Fin 7 → CBox := ![⟨⟨(-3439),0⟩,⟨(-3439),3439⟩⟩,⟨⟨(-11558),11023⟩,⟨(-12578),9999⟩⟩,⟨⟨15606318772377,15606318781045⟩,⟨17386431335831,17386431344500⟩⟩,⟨⟨(-717443316691677932663),(-717443316691677917966)⟩,⟨(-53802295195031030846),(-53802295195031016149)⟩⟩,⟨⟨(-21180879253952447470729166),(-21180879253952447319061786)⟩,⟨7891043062932220669019994,7891043062932220820630968⟩⟩,⟨⟨(-6979995367902027654093779187),(-6979995367902027626481665566)⟩,⟨6013175518710165388231369096,6013175518710165415788564138⟩⟩,⟨⟨80541199115523784843004293450,80541199115523785176611380588⟩,⟨306846134544329448742833908633,306846134544329449083295620533⟩⟩]
lemma ha9_1_7_eq (j : Fin 7) : ha9_1_7 j = ((ha9_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha9_1_7_contains (j : Fin 7) : (ha9_1_7 j).Contains (fullFactor true 9 7 ((j.val:ℝ)/6)) := by
  rw [ha9_1_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_1_6 j) true 9 6 j (ha9_1_6_contains j)
noncomputable def hk9_1_8 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_8 j i k)
lemma hk9_1_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_1_8 j i k).Contains (fullFactor true 9 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_1_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel9_0 j i k) (mpower1_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 8 (kernel9_0_contains j i k) (mpower1_8_contains j i k)
noncomputable def ha9_1_8 : Fin 7 → CBox := ![⟨⟨0,3962⟩,⟨(-3962),3962⟩⟩,⟨⟨(-16409),15723⟩,⟨(-14705),17425⟩⟩,⟨⟨1588043272067,1588043282984⟩,⟨(-20747224114107),(-20747224103190)⟩⟩,⟨⟨219439801316764780804,219439801316764795389⟩,⟨477145212418502667840,477145212418502682426⟩⟩,⟨⟨8569139478751380660132246,8569139478751380776443424⟩,⟨10737211283906283018943551,10737211283906283135293036⟩⟩,⟨⟨3685206002668269754258482632,3685206002668269770773544313⟩,⟨3035029702336479121085337762,3035029702336479137624909964⟩⟩,⟨⟨136613236324045010921023264668,136613236324045011082977481560⟩,⟨(-43556736879327671197978959789),(-43556736879327671039266124903)⟩⟩]
lemma ha9_1_8_eq (j : Fin 7) : ha9_1_8 j = ((ha9_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha9_1_8_contains (j : Fin 7) : (ha9_1_8 j).Contains (fullFactor true 9 8 ((j.val:ℝ)/6)) := by
  rw [ha9_1_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_1_7 j) true 9 7 j (ha9_1_7_contains j)
noncomputable def hk9_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_9 j i k)
lemma hk9_1_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_1_9 j i k).Contains (fullFactor true 9 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_1_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel9_0 j i k) (mpower1_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 9 (kernel9_0_contains j i k) (mpower1_9_contains j i k)
noncomputable def ha9_1_9 : Fin 7 → CBox := ![⟨⟨(-4057),0⟩,⟨(-4057),4057⟩⟩,⟨⟨(-19468),21176⟩,⟨(-21338),19305⟩⟩,⟨⟨(-12741128711433),(-12741128699212)⟩,⟨10441247965985,10441247978205⟩⟩,⟨⟨201819977400460323257,201819977400460336124⟩,⟨(-274586123399150917843),(-274586123399150904976)⟩⟩,⟨⟨4068944366274353442639076,4068944366274353521970798⟩,⟨(-6206670473105841624991819),(-6206670473105841545675692)⟩⟩,⟨⟨1089276185492577064284691213,1089276185492577073090071093⟩,⟨(-1910304910064375132865419100),(-1910304910064375124068469512)⟩⟩,⟨⟨(-20326315179388789957487019056),(-20326315179388789890363777725)⟩,⟨(-53903906556811653497127513785),(-53903906556811653428658709719)⟩⟩]
lemma ha9_1_9_eq (j : Fin 7) : ha9_1_9 j = ((ha9_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha9_1_9_contains (j : Fin 7) : (ha9_1_9 j).Contains (fullFactor true 9 9 ((j.val:ℝ)/6)) := by
  rw [ha9_1_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_1_8 j) true 9 8 j (ha9_1_8_contains j)
noncomputable def hk9_1_10 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_10 j i k)
lemma hk9_1_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_1_10 j i k).Contains (fullFactor true 9 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_1_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel9_0 j i k) (mpower1_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 10 (kernel9_0_contains j i k) (mpower1_10_contains j i k)
noncomputable def ha9_1_10 : Fin 7 → CBox := ![⟨⟨0,3739⟩,⟨(-3739),3739⟩⟩,⟨⟨(-24168),22102⟩,⟨(-22673),23597⟩⟩,⟨⟨11650553610829,11650553623140⟩,⟨1421079161758,1421079174069⟩⟩,⟨⟨(-197381102402241965027),(-197381102402241954811)⟩,⟨(-25387779826030942692),(-25387779826030932476)⟩⟩,⟨⟨(-3484065164802736851200611),(-3484065164802736802523971)⟩,⟨(-939316083876580953270226),(-939316083876580904590857)⟩⟩,⟨⟨(-857134378553481601465987409),(-857134378553481597249277394)⟩,⟨(-310457831497308956811382772),(-310457831497308952592706077)⟩⟩,⟨⟨(-19083166978354024617262689172),(-19083166978354024591214856705)⟩,⟨8352057071003376070862087225,8352057071003376096412711572⟩⟩]
lemma ha9_1_10_eq (j : Fin 7) : ha9_1_10 j = ((ha9_1_9 j).mul (piI.mul (atomPoints j).z)).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha9_1_10_contains (j : Fin 7) : (ha9_1_10 j).Contains (fullFactor true 9 10 ((j.val:ℝ)/6)) := by
  rw [ha9_1_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_1_9 j) true 9 9 j (ha9_1_9_contains j)
noncomputable def hk9_1_11 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_11 j i k)
lemma hk9_1_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_1_11 j i k).Contains (fullFactor true 9 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_1_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel9_0 j i k) (mpower1_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 11 (kernel9_0_contains j i k) (mpower1_11_contains j i k)
noncomputable def ha9_1_11 : Fin 7 → CBox := ![⟨⟨(-3133),0⟩,⟨(-3133),3133⟩⟩,⟨⟨(-23067),24819⟩,⟨(-23916),23970⟩⟩,⟨⟨(-4549386720770),(-4549386709495)⟩,⟨(-6090806212046),(-6090806200771)⟩⟩,⟨⟨38990741047750080122,38990741047750087495⟩,⟨98193198513013353492,98193198513013360866⟩⟩,⟨⟨85451862051436260983608,85451862051436288137358⟩,⟨1592703828497615188189894,1592703828497615215345160⟩⟩,⟨⟨(-60420735354598515653430023),(-60420735354598513816125291)⟩,⟨338209517787106953603163469,338209517787106955440398566⟩⟩,⟨⟨3067527802541374910162699502,3067527802541374919004741810⟩,⟨6121956280806660201934519275,6121956280806660210941925321⟩⟩]
lemma ha9_1_11_eq (j : Fin 7) : ha9_1_11 j = ((ha9_1_10 j).mul (piI.mul (atomPoints j).z)).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha9_1_11_contains (j : Fin 7) : (ha9_1_11 j).Contains (fullFactor true 9 11 ((j.val:ℝ)/6)) := by
  rw [ha9_1_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_1_10 j) true 9 10 j (ha9_1_10_contains j)
noncomputable def hk9_1_12 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_12 j i k)
lemma hk9_1_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_1_12 j i k).Contains (fullFactor true 9 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_1_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel9_0 j i k) (mpower1_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 12 (kernel9_0_contains j i k) (mpower1_12_contains j i k)
noncomputable def ha9_1_12 : Fin 7 → CBox := ![⟨⟨0,2406⟩,⟨(-2406),2406⟩⟩,⟨⟨(-23266),22163⟩,⟨(-23003),22426⟩⟩,⟨⟨(-747455499914),(-747455490448)⟩,⟨4451532687297,4451532696763⟩⟩,⟨⟨32604592802159065881,32604592802159070760⟩,⟨(-39755098218494496150),(-39755098218494491272)⟩⟩,⟨⟨602398704161514650572172,602398704161514664457879⟩,⟨(-234025059100093498634412),(-234025059100093484750338)⟩⟩,⟨⟨118686719286903063799932204,118686719286903064533616017⟩,⟨719493652991894027564389,719493652991894761018691⟩⟩,⟨⟨1794211962768628630960705577,1794211962768628633815578786⟩,⟨(-1018871919422432028502543557),(-1018871919422432025697617398)⟩⟩]
lemma ha9_1_12_eq (j : Fin 7) : ha9_1_12 j = ((ha9_1_11 j).mul (piI.mul (atomPoints j).z)).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha9_1_12_contains (j : Fin 7) : (ha9_1_12 j).Contains (fullFactor true 9 12 ((j.val:ℝ)/6)) := by
  rw [ha9_1_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_1_11 j) true 9 11 j (ha9_1_11_contains j)
noncomputable def hk9_1_13 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_13 j i k)
lemma hk9_1_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_1_13 j i k).Contains (fullFactor true 9 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_1_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel9_0 j i k) (mpower1_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 13 (kernel9_0_contains j i k) (mpower1_13_contains j i k)
noncomputable def ha9_1_13 : Fin 7 → CBox := ![⟨⟨(-1706),0⟩,⟨(-1706),1706⟩⟩,⟨⟨(-19649),20134⟩,⟨(-19564),20219⟩⟩,⟨⟨2046630798926,2046630806262⟩,⟨(-1389831782261),(-1389831774925)⟩⟩,⟨⟨(-22719291804146023451),(-22719291804146020471)⟩,⟨(-4157460093088943326),(-4157460093088940346)⟩⟩,⟨⟨(-153387846957154043747500),(-153387846957154037194236)⟩,⟨(-186803393916120003268136),(-186803393916119996714203)⟩⟩,⟨⟨(-6204023819422090639649442),(-6204023819422090369388626)⟩,⟨(-37336702086668004986989748),(-37336702086668004716571583)⟩⟩,⟨⟨(-308929094545510194049580369),(-308929094545510193228233130)⟩,⟨(-483663778363617350949786048),(-483663778363617350114636509)⟩⟩]
lemma ha9_1_13_eq (j : Fin 7) : ha9_1_13 j = ((ha9_1_12 j).mul (piI.mul (atomPoints j).z)).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha9_1_13_contains (j : Fin 7) : (ha9_1_13 j).Contains (fullFactor true 9 13 ((j.val:ℝ)/6)) := by
  rw [ha9_1_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_1_12 j) true 9 12 j (ha9_1_12_contains j)
noncomputable def hk9_1_14 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_14 j i k)
lemma hk9_1_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_1_14 j i k).Contains (fullFactor true 9 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_1_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel9_0 j i k) (mpower1_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 14 (kernel9_0_contains j i k) (mpower1_14_contains j i k)
noncomputable def ha9_1_14 : Fin 7 → CBox := ![⟨⟨0,1123⟩,⟨(-1123),1123⟩⟩,⟨⟨(-16221),16129⟩,⟨(-16419),15932⟩⟩,⟨⟨(-1231037434309),(-1231037429029)⟩,⟨(-264111424434),(-264111419154)⟩⟩,⟨⟨3075559939550879804,3075559939550881495⟩,⟨9130148636275798543,9130148636275800233⟩⟩,⟨⟨(-45042314109153599574023),(-45042314109153596701656)⟩,⟨70837423204632157736946,70837423204632160609140⟩⟩,⟨⟨(-10582996849900898767988285),(-10582996849900898675446588)⟩,⟨3688692948426796946839275,3688692948426797039319040⟩⟩,⟨⟨(-120608131812118024714845629),(-120608131812118024488008638)⟩,⟨86169298168791612940068772,86169298168791613163394851⟩⟩]
lemma ha9_1_14_eq (j : Fin 7) : ha9_1_14 j = ((ha9_1_13 j).mul (piI.mul (atomPoints j).z)).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha9_1_14_contains (j : Fin 7) : (ha9_1_14 j).Contains (fullFactor true 9 14 ((j.val:ℝ)/6)) := by
  rw [ha9_1_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_1_13 j) true 9 13 j (ha9_1_13_contains j)
noncomputable def hk9_1_15 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_15 j i k)
lemma hk9_1_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_1_15 j i k).Contains (fullFactor true 9 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_1_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel9_0 j i k) (mpower1_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 15 (kernel9_0_contains j i k) (mpower1_15_contains j i k)
noncomputable def ha9_1_15 : Fin 7 → CBox := ![⟨⟨(-690),0⟩,⟨(-690),690⟩⟩,⟨⟨(-12313),12240⟩,⟨(-12141),12412⟩⟩,⟨⟨313390298829,313390302376⟩,⟨509359617019,509359620566⟩⟩,⟨⟨2529037742481016868,2529037742481017763⟩,⟨(-2769935358086130445),(-2769935358086129549)⟩⟩,⟨⟨26368219427222726310275,26368219427222727485171⟩,⟨6716737197141222463958,6716737197141223638872⟩⟩,⟨⟨1501537378511149489572723,1501537378511149519109823⟩,⟨2709114005498712393800046,2709114005498712423356052⟩⟩,⟨⟨22253771523141716820394925,22253771523141716877067778⟩,⟨27955920420793263346723384,27955920420793263404222503⟩⟩]
lemma ha9_1_15_eq (j : Fin 7) : ha9_1_15 j = ((ha9_1_14 j).mul (piI.mul (atomPoints j).z)).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha9_1_15_contains (j : Fin 7) : (ha9_1_15 j).Contains (fullFactor true 9 15 ((j.val:ℝ)/6)) := by
  rw [ha9_1_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_1_14 j) true 9 14 j (ha9_1_14_contains j)
noncomputable def hk9_1_16 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_16 j i k)
lemma hk9_1_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_1_16 j i k).Contains (fullFactor true 9 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_1_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel9_0 j i k) (mpower1_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 16 (kernel9_0_contains j i k) (mpower1_16_contains j i k)
noncomputable def ha9_1_16 : Fin 7 → CBox := ![⟨⟨0,398⟩,⟨(-398),398⟩⟩,⟨⟨(-8686),8784⟩,⟨(-8792),8679⟩⟩,⟨⟨67518004586,67518006820⟩,⟨(-257616423587),(-257616421353)⟩⟩,⟨⟨(-1331672044033337788),(-1331672044033337343)⟩,⟨(-317509516626733124),(-317509516626732678)⟩⟩,⟨⟨(-557874891723565905934),(-557874891723565455389)⟩,⟨(-8249946247588780988706),(-8249946247588780538152)⟩⟩,⟨⟨625624523466886805121462,625624523466886813970635⟩,⟨(-502641709001863480346008),(-502641709001863471501642)⟩⟩,⟨⟨6048180703408985188146730,6048180703408985201809675⟩,⟨(-5350520335568938295105665),(-5350520335568938281623386)⟩⟩]
lemma ha9_1_16_eq (j : Fin 7) : ha9_1_16 j = ((ha9_1_15 j).mul (piI.mul (atomPoints j).z)).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha9_1_16_contains (j : Fin 7) : (ha9_1_16 j).Contains (fullFactor true 9 16 ((j.val:ℝ)/6)) := by
  rw [ha9_1_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_1_15 j) true 9 15 j (ha9_1_15_contains j)
noncomputable def hk9_1_17 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_17 j i k)
lemma hk9_1_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_1_17 j i k).Contains (fullFactor true 9 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_1_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel9_0 j i k) (mpower1_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 17 (kernel9_0_contains j i k) (mpower1_17_contains j i k)
noncomputable def ha9_1_17 : Fin 7 → CBox := ![⟨⟨(-216),0⟩,⟨(-216),216⟩⟩,⟨⟨(-5884),5816⟩,⟨(-5835),5865⟩⟩,⟨⟨(-97599510003),(-97599508679)⟩,⟨54156359195,54156360520⟩⟩,⟨⟨126275737001629171,126275737001629380⟩,⟨453006036678069645,453006036678069854⟩⟩,⟨⟨(-2192310777420104042514),(-2192310777420103879900)⟩,⟨886999134369535428190,886999134369535590798⟩⟩,⟨⟨(-146710040336986518917721),(-146710040336986516425231)⟩,⟨(-129520488224759660731943),(-129520488224759658238420)⟩⟩,⟨⟨(-1203326789892336651361098),(-1203326789892336648342537)⟩,⟨(-1225614873948593314041712),(-1225614873948593310986324)⟩⟩]
lemma ha9_1_17_eq (j : Fin 7) : ha9_1_17 j = ((ha9_1_16 j).mul (piI.mul (atomPoints j).z)).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha9_1_17_contains (j : Fin 7) : (ha9_1_17 j).Contains (fullFactor true 9 17 ((j.val:ℝ)/6)) := by
  rw [ha9_1_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_1_16 j) true 9 16 j (ha9_1_16_contains j)
noncomputable def hk9_1_18 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_18 j i k)
lemma hk9_1_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_1_18 j i k).Contains (fullFactor true 9 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_1_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel9_0 j i k) (mpower1_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 18 (kernel9_0_contains j i k) (mpower1_18_contains j i k)
noncomputable def ha9_1_18 : Fin 7 → CBox := ![⟨⟨0,111⟩,⟨(-111),111⟩⟩,⟨⟨(-3683),3718⟩,⟨(-3700),3701⟩⟩,⟨⟨42191614943,42191615685⟩,⟨13111722493,13111723235⟩⟩,⟨⟨108706847237476293,108706847237476386⟩,⟨(-107058519395772653),(-107058519395772560)⟩⟩,⟨⟨412225483840756596673,412225483840756652101⟩,⟨488018457879595715723,488018457879595771153⟩⟩,⟨⟨(-23655606502979579157110),(-23655606502979578493539)⟩,⟨38365326602746403882665,38365326602746404546053⟩⟩,⟨⟨(-233320806434969121312476),(-233320806434969120667214)⟩,⟨254187899269998218566318,254187899269998219204562⟩⟩]
lemma ha9_1_18_eq (j : Fin 7) : ha9_1_18 j = ((ha9_1_17 j).mul (piI.mul (atomPoints j).z)).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha9_1_18_contains (j : Fin 7) : (ha9_1_18 j).Contains (fullFactor true 9 18 ((j.val:ℝ)/6)) := by
  rw [ha9_1_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_1_17 j) true 9 17 j (ha9_1_17_contains j)
noncomputable def hk9_1_19 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_19 j i k)
lemma hk9_1_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_1_19 j i k).Contains (fullFactor true 9 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_1_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel9_0 j i k) (mpower1_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 19 (kernel9_0_contains j i k) (mpower1_19_contains j i k)
noncomputable def ha9_1_19 : Fin 7 → CBox := ![⟨⟨(-54),0⟩,⟨(-54),54⟩⟩,⟨⟨(-2225),2211⟩,⟨(-2221),2214⟩⟩,⟨⟨(-7379208676),(-7379208281)⟩,⟨(-14834178496),(-14834178101)⟩⟩,⟨⟨(-44974947072362385),(-44974947072362345)⟩,⟨(-13280569424316148),(-13280569424316108)⟩⟩,⟨⟨85787971296237366361,85787971296237384261⟩,⟨(-139157852781918556800),(-139157852781918538900)⟩⟩,⟨⟨9126025242066296846233,9126025242066297013500⟩,⟨3664171724245675069109,3664171724245675236400⟩⟩,⟨⟨50615292281439051339400,50615292281439051467240⟩,⟨41831462789043352062789,41831462789043352191882⟩⟩]
lemma ha9_1_19_eq (j : Fin 7) : ha9_1_19 j = ((ha9_1_18 j).mul (piI.mul (atomPoints j).z)).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha9_1_19_contains (j : Fin 7) : (ha9_1_19 j).Contains (fullFactor true 9 19 ((j.val:ℝ)/6)) := by
  rw [ha9_1_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_1_18 j) true 9 18 j (ha9_1_18_contains j)
noncomputable def hk9_1_20 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_20 j i k)
lemma hk9_1_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_1_20 j i k).Contains (fullFactor true 9 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_1_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel9_0 j i k) (mpower1_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 20 (kernel9_0_contains j i k) (mpower1_20_contains j i k)
noncomputable def ha9_1_20 : Fin 7 → CBox := ![⟨⟨0,25⟩,⟨(-25),25⟩⟩,⟨⟨(-1261),1265⟩,⟨(-1260),1265⟩⟩,⟨⟨(-2003320344),(-2003320144)⟩,⟨5552039499,5552039699⟩⟩,⟨⟨2971883117017843,2971883117017860⟩,⟨13366425082267105,13366425082267122⟩⟩,⟨⟨(-38645356632142089350),(-38645356632142083858)⟩,⟨(-9273287494870418761),(-9273287494870413268)⟩⟩,⟨⟨427086034164069794590,427086034164069834656⟩,⟨(-1993160468520435060438),(-1993160468520435020373)⟩⟩,⟨⟨7077514908428655459334,7077514908428655483869⟩,⟨(-9531398622551247483121),(-9531398622551247458796)⟩⟩]
lemma ha9_1_20_eq (j : Fin 7) : ha9_1_20 j = ((ha9_1_19 j).mul (piI.mul (atomPoints j).z)).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha9_1_20_contains (j : Fin 7) : (ha9_1_20 j).Contains (fullFactor true 9 20 ((j.val:ℝ)/6)) := by
  rw [ha9_1_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_1_19 j) true 9 19 j (ha9_1_19_contains j)
noncomputable def hk9_1_21 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_21 j i k)
lemma hk9_1_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_1_21 j i k).Contains (fullFactor true 9 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_1_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel9_0 j i k) (mpower1_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 21 (kernel9_0_contains j i k) (mpower1_21_contains j i k)
noncomputable def ha9_1_21 : Fin 7 → CBox := ![⟨⟨(-11),0⟩,⟨(-11),11⟩⟩,⟨⟨(-685),685⟩,⟨(-686),684⟩⟩,⟨⟨1831299239,1831299336⟩,⟨(-810395973),(-810395876)⟩⟩,⟨⟨2850907600950423,2850907600950430⟩,⟨(-2524191884079635),(-2524191884079628)⟩⟩,⟨⟨748523935329314346,748523935329315952⟩,⟨9171117438639129434,9171117438639131040⟩⟩,⟨⟨(-402069019581262721177),(-402069019581262712037)⟩,⟨(-16237139326884301157),(-16237139326884292017)⟩⟩,⟨⟨(-1702242729656619714741),(-1702242729656619710332)⟩,⟨(-1131778473106594025951),(-1131778473106594021509)⟩⟩]
lemma ha9_1_21_eq (j : Fin 7) : ha9_1_21 j = ((ha9_1_20 j).mul (piI.mul (atomPoints j).z)).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha9_1_21_contains (j : Fin 7) : (ha9_1_21 j).Contains (fullFactor true 9 21 ((j.val:ℝ)/6)) := by
  rw [ha9_1_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_1_20 j) true 9 20 j (ha9_1_20_contains j)
noncomputable def hk9_1_22 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_22 j i k)
lemma hk9_1_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_1_22 j i k).Contains (fullFactor true 9 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_1_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel9_0 j i k) (mpower1_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 22 (kernel9_0_contains j i k) (mpower1_22_contains j i k)
noncomputable def ha9_1_22 : Fin 7 → CBox := ![⟨⟨0,5⟩,⟨(-5),5⟩⟩,⟨⟨(-355),355⟩,⟨(-355),355⟩⟩,⟨⟨(-599552156),(-599552111)⟩,⟨(-247338592),(-247338546)⟩⟩,⟨⟨(-952832442508607),(-952832442508603)⟩,⟨(-337263855941651),(-337263855941647)⟩⟩,⟨⟨1874371950351768224,1874371950351768673⟩,⟨(-788894750813525623),(-788894750813525174)⟩⟩,⟨⟨9856623398087553564,9856623398087555555⟩,⟨75182130541141739241,75182130541141741232⟩⟩,⟨⟨(-171238441347373238006),(-171238441347373237238)⟩,⟨289061848214170109875,289061848214170110638⟩⟩]
lemma ha9_1_22_eq (j : Fin 7) : ha9_1_22 j = ((ha9_1_21 j).mul (piI.mul (atomPoints j).z)).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha9_1_22_contains (j : Fin 7) : (ha9_1_22 j).Contains (fullFactor true 9 22 ((j.val:ℝ)/6)) := by
  rw [ha9_1_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_1_21 j) true 9 21 j (ha9_1_21_contains j)
noncomputable def hk9_1_23 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_23 j i k)
lemma hk9_1_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_1_23 j i k).Contains (fullFactor true 9 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_1_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel9_0 j i k) (mpower1_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 23 (kernel9_0_contains j i k) (mpower1_23_contains j i k)
noncomputable def ha9_1_23 : Fin 7 → CBox := ![⟨⟨(-3),0⟩,⟨(-3),3⟩⟩,⟨⟨(-176),176⟩,⟨(-176),176⟩⟩,⟨⟨72960461,72960482⟩,⟨187198563,187198584⟩⟩,⟨⟨42333281320336,42333281320339⟩,⟨253121222536362,253121222536364⟩⟩,⟨⟨(-281957689679555390),(-281957689679555269)⟩,⟨(-324527017681290011),(-324527017681289890)⟩⟩,⟨⟨13052138719855043992,13052138719855044408⟩,⟨(-4052972945914228104),(-4052972945914227689)⟩⟩,⟨⟨46781038136375641332,46781038136375641459⟩,⟨24524711207015131070,24524711207015131198⟩⟩]
lemma ha9_1_23_eq (j : Fin 7) : ha9_1_23 j = ((ha9_1_22 j).mul (piI.mul (atomPoints j).z)).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha9_1_23_contains (j : Fin 7) : (ha9_1_23 j).Contains (fullFactor true 9 23 ((j.val:ℝ)/6)) := by
  rw [ha9_1_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_1_22 j) true 9 22 j (ha9_1_22_contains j)
noncomputable def hk9_1_24 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_24 j i k)
lemma hk9_1_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_1_24 j i k).Contains (fullFactor true 9 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_1_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel9_0 j i k) (mpower1_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 24 (kernel9_0_contains j i k) (mpower1_24_contains j i k)
noncomputable def ha9_1_24 : Fin 7 → CBox := ![⟨⟨0,2⟩,⟨(-2),2⟩⟩,⟨⟨(-84),84⟩,⟨(-84),84⟩⟩,⟨⟨25203200,25203209⟩,⟨(-54059928),(-54059918)⟩⟩,⟨⟨48883816965205,48883816965206⟩,⟨(-38857507855314),(-38857507855312)⟩⟩,⟨⟨(-44668537922808875),(-44668537922808843)⟩,⟨74767316321201932,74767316321201964⟩⟩,⟨⟨(-1072928390185788433),(-1072928390185788349)⟩,⟨(-2102805056046841348),(-2102805056046841264)⟩⟩,⟨⟨3323964096794532566,3323964096794532587⟩,⟨(-7230526420959238870),(-7230526420959238849)⟩⟩]
lemma ha9_1_24_eq (j : Fin 7) : ha9_1_24 j = ((ha9_1_23 j).mul (piI.mul (atomPoints j).z)).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha9_1_24_contains (j : Fin 7) : (ha9_1_24 j).Contains (fullFactor true 9 24 ((j.val:ℝ)/6)) := by
  rw [ha9_1_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_1_23 j) true 9 23 j (ha9_1_23_contains j)
noncomputable def hk9_1_25 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_25 j i k)
lemma hk9_1_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_1_25 j i k).Contains (fullFactor true 9 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_1_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel9_0 j i k) (mpower1_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 25 (kernel9_0_contains j i k) (mpower1_25_contains j i k)
noncomputable def ha9_1_25 : Fin 7 → CBox := ![⟨⟨(-1),0⟩,⟨(-1),1⟩⟩,⟨⟨(-39),39⟩,⟨(-39),39⟩⟩,⟨⟨(-16100240),(-16100235)⟩,⟨5454643,5454648⟩⟩,⟨⟨(-13473426049927),(-13473426049925)⟩,⟨(-5589839918321),(-5589839918320)⟩⟩,⟨⟨16524518039715132,16524518039715141⟩,⟨3722761084280405,3722761084280414⟩⟩,⟨⟨(-313396491823039453),(-313396491823039436)⟩,⟨234569851794820012,234569851794820029⟩⟩,⟨⟨(-1069350842639600658),(-1069350842639600654)⟩,⟨(-425808828304872129),(-425808828304872125)⟩⟩]
lemma ha9_1_25_eq (j : Fin 7) : ha9_1_25 j = ((ha9_1_24 j).mul (piI.mul (atomPoints j).z)).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha9_1_25_contains (j : Fin 7) : (ha9_1_25 j).Contains (fullFactor true 9 25 ((j.val:ℝ)/6)) := by
  rw [ha9_1_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_1_24 j) true 9 24 j (ha9_1_24_contains j)
noncomputable def hk9_1_26 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_26 j i k)
lemma hk9_1_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_1_26 j i k).Contains (fullFactor true 9 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_1_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel9_0 j i k) (mpower1_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 26 (kernel9_0_contains j i k) (mpower1_26_contains j i k)
noncomputable def ha9_1_26 : Fin 7 → CBox := ![⟨⟨0,1⟩,⟨(-1),1⟩⟩,⟨⟨(-18),18⟩,⟨(-18),18⟩⟩,⟨⟨4129325,4129328⟩,⟨2156248,2156251⟩⟩,⟨⟨368275234926,368275234927⟩,⟨3255585385202,3255585385204⟩⟩,⟨⟨(-301593042716862),(-301593042716859)⟩,⟨(-3153246340959908),(-3153246340959905)⟩⟩,⟨⟨45346692848594515,45346692848594520⟩,⟨42888796860089324,42888796860089328⟩⟩,⟨⟨(-51415814313273184),(-51415814313273183)⟩,⟨151592664962958008,151592664962958010⟩⟩]
lemma ha9_1_26_eq (j : Fin 7) : ha9_1_26 j = ((ha9_1_25 j).mul (piI.mul (atomPoints j).z)).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha9_1_26_contains (j : Fin 7) : (ha9_1_26 j).Contains (fullFactor true 9 26 ((j.val:ℝ)/6)) := by
  rw [ha9_1_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_1_25 j) true 9 25 j (ha9_1_25_contains j)
noncomputable def hk9_1_27 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_27 j i k)
lemma hk9_1_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_1_27 j i k).Contains (fullFactor true 9 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_1_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel9_0 j i k) (mpower1_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 27 (kernel9_0_contains j i k) (mpower1_27_contains j i k)
noncomputable def ha9_1_27 : Fin 7 → CBox := ![⟨⟨(-1),0⟩,⟨(-1),1⟩⟩,⟨⟨(-8),8⟩,⟨(-8),8⟩⟩,⟨⟨(-341702),(-341699)⟩,⟨(-1180855),(-1180853)⟩⟩,⟨⟨577341844100,577341844102⟩,⟨(-410908123227),(-410908123225)⟩⟩,⟨⟨(-522627520907417),(-522627520907416)⟩,⟨228579585207012,228579585207014⟩⟩,⟨⟨5306501026723676,5306501026723678⟩,⟨(-7980054085678830),(-7980054085678828)⟩⟩,⟨⟨20631836309111253,20631836309111255⟩,⟨5822177079202134,5822177079202135⟩⟩]
lemma ha9_1_27_eq (j : Fin 7) : ha9_1_27 j = ((ha9_1_26 j).mul (piI.mul (atomPoints j).z)).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha9_1_27_contains (j : Fin 7) : (ha9_1_27 j).Contains (fullFactor true 9 27 ((j.val:ℝ)/6)) := by
  rw [ha9_1_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_1_26 j) true 9 26 j (ha9_1_26_contains j)
noncomputable def hk9_1_28 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_28 j i k)
lemma hk9_1_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_1_28 j i k).Contains (fullFactor true 9 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_1_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel9_0 j i k) (mpower1_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 28 (kernel9_0_contains j i k) (mpower1_28_contains j i k)
noncomputable def ha9_1_28 : Fin 7 → CBox := ![⟨⟨0,1⟩,⟨(-1),1⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-157115),(-157113)⟩,⟨270492,270494⟩⟩,⟨⟨(-133318009619),(-133318009618)⟩,⟨(-63798548468),(-63798548466)⟩⟩,⟨⟨66000078653772,66000078653774⟩,⟨73862641075335,73862641075336⟩⟩,⟨⟨(-1297795669471852),(-1297795669471851)⟩,⟨(-573508404796806),(-573508404796804)⟩⟩,⟨⟨612497283260435,612497283260436⟩,⟨(-2699833851939530),(-2699833851939528)⟩⟩]
lemma ha9_1_28_eq (j : Fin 7) : ha9_1_28 j = ((ha9_1_27 j).mul (piI.mul (atomPoints j).z)).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha9_1_28_contains (j : Fin 7) : (ha9_1_28 j).Contains (fullFactor true 9 28 ((j.val:ℝ)/6)) := by
  rw [ha9_1_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_1_27 j) true 9 27 j (ha9_1_27_contains j)
noncomputable def hk9_1_29 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_29 j i k)
lemma hk9_1_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_1_29 j i k).Contains (fullFactor true 9 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_1_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel9_0 j i k) (mpower1_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 29 (kernel9_0_contains j i k) (mpower1_29_contains j i k)
noncomputable def ha9_1_29 : Fin 7 → CBox := ![⟨⟨(-1),0⟩,⟨(-1),1⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨74711,74712⟩,⟨(-18022),(-18021)⟩⟩,⟨⟨1771979597,1771979599⟩,⟨29709479896,29709479897⟩⟩,⟨⟨8318308912977,8318308912978⟩,⟨(-14374064840990),(-14374064840988)⟩⟩,⟨⟨(-49272675417273),(-49272675417272)⟩,⟨196751874673349,196751874673350⟩⟩,⟨⟨(-340144172705861),(-340144172705860)⟩,⟨(-58785751061675),(-58785751061674)⟩⟩]
lemma ha9_1_29_eq (j : Fin 7) : ha9_1_29 j = ((ha9_1_28 j).mul (piI.mul (atomPoints j).z)).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha9_1_29_contains (j : Fin 7) : (ha9_1_29 j).Contains (fullFactor true 9 29 ((j.val:ℝ)/6)) := by
  rw [ha9_1_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_1_28 j) true 9 28 j (ha9_1_28_contains j)
noncomputable def hk9_1_30 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_30 j i k)
lemma hk9_1_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk9_1_30 j i k).Contains (fullFactor true 9 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_1_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel9_0 j i k) (mpower1_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 30 (kernel9_0_contains j i k) (mpower1_30_contains j i k)
noncomputable def ha9_1_30 : Fin 7 → CBox := ![⟨⟨0,1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-15356),(-15355)⟩,⟨(-9869),(-9868)⟩⟩,⟨⟨4891656123,4891656124⟩,⟨(-3104307562),(-3104307560)⟩⟩,⟨⟨(-2633774246415),(-2633774246414)⟩,⟨(-554955511624),(-554955511622)⟩⟩,⟨⟨27949754921690,27949754921691⟩,⟨2090670976971,2090670976972⟩⟩,⟨⟨(-4946895520926),(-4946895520924)⟩,⟨41310262072222,41310262072223⟩⟩]
lemma ha9_1_30_eq (j : Fin 7) : ha9_1_30 j = ((ha9_1_29 j).mul (piI.mul (atomPoints j).z)).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha9_1_30_contains (j : Fin 7) : (ha9_1_30 j).Contains (fullFactor true 9 30 ((j.val:ℝ)/6)) := by
  rw [ha9_1_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha9_1_29 j) true 9 29 j (ha9_1_29_contains j)
end SharpPlanar.CachedData

end OAI
