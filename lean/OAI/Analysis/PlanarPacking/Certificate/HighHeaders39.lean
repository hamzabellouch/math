import OAI.Analysis.PlanarPacking.Certificate.Powers40
import OAI.Analysis.PlanarPacking.Certificate.KernelValues40
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
noncomputable def hk39_0_0 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_0 j i k)
lemma hk39_0_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_0_0 j i k).Contains (fullFactor false 39 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_0_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power39 j i k) (mpower0_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 0 (power39_contains j i k) (mpower0_0_contains j i k)
noncomputable def ha39_0_0 : Fin 7 → CBox := ![⟨⟨999999999999999999999999999533,1000000000000000000000000000623⟩,⟨(-623),623⟩⟩,⟨⟨(-212028541263),181392524018⟩,⟨999999999999999999803313554891,1000000000000000000196686445169⟩⟩,⟨⟨(-1000000000000000000537468457059),(-999999999999999999462531542959)⟩,⟨(-568086843834),506814809139⟩⟩,⟨⟨(-81446297555),173354349557⟩,⟨(-1000000000000000000127400323556),(-999999999999999999872599676483)⟩⟩,⟨⟨999999999999999998530229426155,1000000000000000001469770573755⟩,⟨(-1408511427887),1531055497378⟩⟩,⟨⟨(-1926459745886),1773279659168⟩,⟨999999999999999998150117505069,1000000000000000001849882494830⟩⟩,⟨⟨(-1000000000000000000255574713653),(-999999999999999999744425286503)⟩,⟨(-347482765733),163666661417⟩⟩]
lemma ha39_0_0_eq (j : Fin 7) : ha39_0_0 j = ((atomPoints j).direct.powBin 7 39).conj := by fin_cases j <;> decide +kernel
lemma ha39_0_0_contains (j : Fin 7) : (ha39_0_0 j).Contains (fullFactor false 39 0 ((j.val:ℝ)/6)) := by
  rw [ha39_0_0_eq]
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @direct_factor_zero_full ((atomPoints j).direct.powBin 7 39) ((j.val:ℝ)/6) 39 (@direct_power_bin_contains (atomPoints j) ((j.val:ℝ)/6) (atomPoints_contains j) 39 (by norm_num))
noncomputable def hk39_0_1 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_1 j i k)
lemma hk39_0_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_0_1 j i k).Contains (fullFactor false 39 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_0_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power39 j i k) (mpower0_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 1 (power39_contains j i k) (mpower0_1_contains j i k)
noncomputable def ha39_0_1 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-523598775598298873181318115203),(-523598775598298872973681884828)⟩,⟨(-111017884598),94976903479⟩⟩,⟨⟨(-530735227041),594899151730⟩,⟨(-1047197551196597746719502318747),(-1047197551196597745590497681273)⟩⟩,⟨⟨1570796326794896619029880039787,1570796326794896619435119960275⟩,⟨(-127935545031),272304375519⟩⟩,⟨⟨(-3206635135201),2949979436232⟩,⟨2094395102393195489228386375161,2094395102393195495391613624650⟩⟩,⟨⟨(-2617993877991494370234647713138),(-2617993877991494360540352286599)⟩,⟨(-5043459820927),4642435291669⟩⟩,⟨⟨(-514173981146),1091649304076⟩,⟨(-3141592653589793239272911642856),(-3141592653589793237657088357634)⟩⟩]
lemma ha39_0_1_eq (j : Fin 7) : ha39_0_1 j = ((ha39_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha39_0_1_contains (j : Fin 7) : (ha39_0_1 j).Contains (fullFactor false 39 1 ((j.val:ℝ)/6)) := by
  rw [ha39_0_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_0_0 j) false 39 0 j (ha39_0_0_contains j)
noncomputable def hk39_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_2 j i k)
lemma hk39_0_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_0_2 j i k).Contains (fullFactor false 39 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_0_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power39 j i k) (mpower0_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 2 (power39_contains j i k) (mpower0_2_contains j i k)
noncomputable def ha39_0_2 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-24864895186),29064414223⟩,⟨(-137077838904018869733637935985),(-137077838904018869678842565673)⟩⟩,⟨⟨548311355616075478528515615767,548311355616075479121406390848⟩,⟨(-277892315046),311488467451⟩⟩,⟨⟨(-213867356418),100480342101⟩,⟨1233700550136169827195061417401,1233700550136169827517263097505⟩⟩,⟨⟨(-2193245422464301918530392913180),(-2193245422464301912069295113034)⟩,⟨(-3357980461164),3089211241703⟩⟩,⟨⟨(-6076933586281),6601873467542⟩,⟨(-3426945972600471749006361943909),(-3426945972600471736305650597018)⟩⟩,⟨⟨4934802200544679308147730407877,4934802200544679310701567652322⟩,⟨(-807662600918),1714758716991⟩⟩]
lemma ha39_0_2_eq (j : Fin 7) : ha39_0_2 j = ((ha39_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha39_0_2_contains (j : Fin 7) : (ha39_0_2 j).Contains (fullFactor false 39 2 ((j.val:ℝ)/6)) := by
  rw [ha39_0_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_0_1 j) false 39 1 j (ha39_0_1_contains j)
noncomputable def hk39_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_3 j i k)
lemma hk39_0_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_0_3 j i k).Contains (fullFactor false 39 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_0_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power39 j i k) (mpower0_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 3 (power39_contains j i k) (mpower0_3_contains j i k)
noncomputable def ha39_0_3 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨23924596203935046426928652228,23924596203935046436568402852⟩,⟨(-4339742892),5072697234⟩⟩,⟨⟨(-108729986781),97002717271⟩,⟨191396769631480371350204641600,191396769631480371557771799039⟩⟩,⟨⟨(-645964097506246253742590529974),(-645964097506246253571829957192)⟩,⟨(-111980685961),52611384096⟩⟩,⟨⟨(-2156676298294),2344312610598⟩,⟨(-1531174157051842973889691299946),(-1531174157051842969374120224988)⟩⟩,⟨⟨2990574525491880798422075536402,2990574525491880809515056348209⟩,⟨(-5303124975282),5761221440434⟩⟩,⟨⟨(-1795691129326),845782297875⟩,⟨5167712780049970027912271224361,5167712780049970030603092673568⟩⟩]
lemma ha39_0_3_eq (j : Fin 7) : ha39_0_3 j = ((ha39_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha39_0_3_contains (j : Fin 7) : (ha39_0_3 j).Contains (fullFactor false 39 3 ((j.val:ℝ)/6)) := by
  rw [ha39_0_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_0_2 j) false 39 2 j (ha39_0_2_contains j)
noncomputable def hk39_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_4 j i k)
lemma hk39_0_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_0_4 j i k).Contains (fullFactor false 39 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_0_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power39 j i k) (mpower0_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 4 (power39_contains j i k) (mpower0_4_contains j i k)
noncomputable def ha39_0_4 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-664014516),568071017⟩,⟨3131722319766024859084151200,3131722319766024860355960189⟩⟩,⟨⟨(-50107557116256397782771117143),(-50107557116256397728270665089)⟩,⟨(-28465443975),25395251997⟩⟩,⟨⟨(-20660442222),43974712545⟩,⟨(-253669507901048013671256998901),(-253669507901048013603392023656)⟩⟩,⟨⟨801720913860102362904884536362,801720913860102365271783979268⟩,⟨(-1129233069149),1227479212529⟩⟩,⟨⟨(-3770710615203),3470887179879⟩,⟨1957326449853765533691750145563,1957326449853765540958319472658⟩⟩,⟨⟨(-4058712126416768219260334933784),(-4058712126416768217134049427596)⟩,⟨(-1410332515002),664275863386⟩⟩]
lemma ha39_0_4_eq (j : Fin 7) : ha39_0_4 j = ((ha39_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha39_0_4_contains (j : Fin 7) : (ha39_0_4 j).Contains (fullFactor false 39 4 ((j.val:ℝ)/6)) := by
  rw [ha39_0_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_0_3 j) false 39 3 j (ha39_0_3_contains j)
noncomputable def hk39_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_5 j i k)
lemma hk39_0_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_0_5 j i k).Contains (fullFactor false 39 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_0_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power39 j i k) (mpower0_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 5 (power39_contains j i k) (mpower0_5_contains j i k)
noncomputable def ha39_0_5 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-327953194428670967642440673),(-327953194428670967508213239)⟩,⟨(-69535438),59488258⟩⟩,⟨⟨(-5318769141),5961788645⟩,⟨(-10494502221717470968134439116),(-10494502221717470956686486091)⟩⟩,⟨⟨79692626246167045110017410256,79692626246167045131591490532⟩,⟨(-6490669351),13815063388⟩⟩,⟨⟨(-514165290203),473012041898⟩,⟨335824071094959070300878062566,335824071094959071293391544002⟩⟩,⟨⟨(-1024853732589596775576911245144),(-1024853732589596771768882231925)⟩,⟨(-1974339461256),1817352277625⟩⟩,⟨⟨(-417376834475),886138053650⟩,⟨(-2550164039877345444537793417449),(-2550164039877345443193691408061)⟩⟩]
lemma ha39_0_5_eq (j : Fin 7) : ha39_0_5 j = ((ha39_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha39_0_5_contains (j : Fin 7) : (ha39_0_5 j).Contains (fullFactor false 39 5 ((j.val:ℝ)/6)) := by
  rw [ha39_0_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_0_4 j) false 39 4 j (ha39_0_4_contains j)
noncomputable def hk39_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_6 j i k)
lemma hk39_0_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_0_6 j i k).Contains (fullFactor false 39 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_0_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power39 j i k) (mpower0_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 6 (power39_contains j i k) (mpower0_6_contains j i k)
noncomputable def ha39_0_6 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-5191330),6068112⟩,⟨(-28619315176067161697459994),(-28619315176067161685655341)⟩⟩,⟨⟨1831636171268298347257753225,1831636171268298349261628234⟩,⟨(-928300337),1040528412⟩⟩,⟨⟨(-3616775138),1699253263⟩,⟨20863480763352960870288293954,20863480763352960876002785486⟩⟩,⟨⟨(-117224714961171094462033056849),(-117224714961171094115207356562)⟩,⟨(-179477544271),165112350655⟩⟩,⟨⟨(-792969522830),861468103775⟩,⟨(-447176799626049402262083314706),(-447176799626049400599093799439)⟩⟩,⟨⟨1335262768854589495527304322273,1335262768854589496235324762069⟩,⟨(-218537999495),463980799903⟩⟩]
lemma ha39_0_6_eq (j : Fin 7) : ha39_0_6 j = ((ha39_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha39_0_6_contains (j : Fin 7) : (ha39_0_6 j).Contains (fullFactor false 39 6 ((j.val:ℝ)/6)) := by
  rw [ha39_0_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_0_5 j) false 39 5 j (ha39_0_5_contains j)
noncomputable def hk39_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_7 j i k)
lemma hk39_0_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_0_7 j i k).Contains (fullFactor false 39 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_0_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power39 j i k) (mpower0_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 7 (power39_contains j i k) (mpower0_7_contains j i k)
noncomputable def ha39_0_7 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2140719769235797027771856,2140719769235797028661658⟩,⟨(-388311),453894⟩⟩,⟨⟨(-155662687),138873406⟩,⟨274012130462182019461419291,274012130462182019762070500⟩⟩,⟨⟨(-4681754135318688101358663242),(-4681754135318688100061431854)⟩,⟨(-811602444),381311541⟩⟩,⟨⟨(-49401499794),53699555673⟩,⟨(-35073552699159298562244171329),(-35073552699159298458362521876)⟩⟩,⟨⟨167243731971546642518189651396,167243731971546643140678629035⟩,⟨(-296569908029),322188317396⟩⟩,⟨⟨(-208234096055),98079624821⟩,⟨599264529320792076731052911878,599264529320792077050719260442⟩⟩]
lemma ha39_0_7_eq (j : Fin 7) : ha39_0_7 j = ((ha39_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha39_0_7_contains (j : Fin 7) : (ha39_0_7 j).Contains (fullFactor false 39 7 ((j.val:ℝ)/6)) := by
  rw [ha39_0_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_0_6 j) false 39 6 j (ha39_0_6_contains j)
noncomputable def hk39_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_8 j i k)
lemma hk39_0_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_0_8 j i k).Contains (fullFactor false 39 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_0_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power39 j i k) (mpower0_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 8 (power39_contains j i k) (mpower0_8_contains j i k)
noncomputable def ha39_0_8 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-29708),25415⟩,⟨140109781258867029424588,140109781258867029483272⟩⟩,⟨⟨(-35868104002269959559940666),(-35868104002269959520471342)⟩,⟨(-20376199),18178487⟩⟩,⟨⟨(-74870346),159357768⟩,⟨(-919260274839426580376051214),(-919260274839426580118414329)⟩⟩,⟨⟨9182234624581109628680046824,9182234624581109655905427016⟩,⟨(-12933282403),14058510801⟩⟩,⟨⟨(-105435880313),97052275453⟩,⟨54730383304244933278499662765,54730383304244933482382916559⟩⟩,⟨⟨(-235330630358893204606432470700),(-235330630358893204480150708507)⟩,⟨(-81773338300),38515778601⟩⟩]
lemma ha39_0_8_eq (j : Fin 7) : ha39_0_8 j = ((ha39_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha39_0_8_contains (j : Fin 7) : (ha39_0_8 j).Contains (fullFactor false 39 8 ((j.val:ℝ)/6)) := by
  rw [ha39_0_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_0_7 j) false 39 7 j (ha39_0_7_contains j)
noncomputable def hk39_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_9 j i k)
lemma hk39_0_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_0_9 j i k).Contains (fullFactor false 39 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_0_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power39 j i k) (mpower0_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 9 (power39_contains j i k) (mpower0_9_contains j i k)
noncomputable def ha39_0_9 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-8151256657387584306641),(-8151256657387584303200)⟩,⟨(-1729),1479⟩⟩,⟨⟨(-2115164),2370879⟩,⟨(-4173443408582443166422011),(-4173443408582443161816261)⟩⟩,⟨⟨160441184787359821851005632,160441184787359821896482452⟩,⟨(-13067341),27813178⟩⟩,⟨⟨(-3271564019),3009711481⟩,⟨2136803025194210896857779863,2136803025194210903200215179⟩⟩,⟨⟨(-15920423158960125625226195761),(-15920423158960125565868285006)⟩,⟨(-30670054354),28231362554⟩⟩,⟨⟨(-13444543012),28544279874⟩,⟨(-82145886611128228821528014223),(-82145886611128228777185885034)⟩⟩]
lemma ha39_0_9_eq (j : Fin 7) : ha39_0_9 j = ((ha39_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha39_0_9_contains (j : Fin 7) : (ha39_0_9 j).Contains (fullFactor false 39 9 ((j.val:ℝ)/6)) := by
  rw [ha39_0_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_0_8 j) false 39 8 j (ha39_0_8_contains j)
noncomputable def hk39_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_10 j i k)
lemma hk39_0_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_0_10 j i k).Contains (fullFactor false 39 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_0_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power39 j i k) (mpower0_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 10 (power39_contains j i k) (mpower0_10_contains j i k)
noncomputable def ha39_0_10 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-78),91⟩,⟨(-426798800539562151546),(-426798800539562151363)⟩⟩,⟨⟨437041971752511642847647,437041971752511643331353⟩,⟨(-221500),248278⟩⟩,⟨⟨(-4368884),2052614⟩,⟨25202042373060605477630219,25202042373060605484853923⟩⟩,⟨⟨(-447530979074571923188538457),(-447530979074571921858757374)⟩,⟨(-685194766),630352499⟩⟩,⟨⟨(-7390953434),8029401454⟩,⟨(-4167957036519161643075294014),(-4167957036519161627522162297)⟩⟩,⟨⟨25806891390014060005785562316,25806891390014060019798198934⟩,⟨(-4223727756),8967449996⟩⟩]
lemma ha39_0_10_eq (j : Fin 7) : ha39_0_10 j = ((ha39_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha39_0_10_contains (j : Fin 7) : (ha39_0_10 j).Contains (fullFactor false 39 10 ((j.val:ℝ)/6)) := by
  rw [ha39_0_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_0_9 j) false 39 9 j (ha39_0_9_contains j)
noncomputable def hk39_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_11 j i k)
lemma hk39_0_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_0_11 j i k).Contains (fullFactor false 39 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_0_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power39 j i k) (mpower0_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 11 (power39_contains j i k) (mpower0_11_contains j i k)
noncomputable def ha39_0_11 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨20315575399030665716,20315575399030665726⟩,⟨(-4),5⟩⟩,⟨⟨(-23637),21087⟩,⟨41606298417214803373635,41606298417214803419818⟩⟩,⟨⟨(-3598843235212085341009735),(-3598843235212085339966736)⟩,⟨(-623876),293113⟩⟩,⟨⟨(-120018836),130460779⟩,⟨(-85209699158455917483226323),(-85209699158455917229765365)⟩⟩,⟨⟨991971455030794222808630946,991971455030794226513425182⟩,⟨(-1759042804),1910993078⟩⟩,⟨⟨(-2561097730),1206293827⟩,⟨7370430945714350775307176674,7370430945714350779332637145⟩⟩]
lemma ha39_0_11_eq (j : Fin 7) : ha39_0_11 j = ((ha39_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha39_0_11_contains (j : Fin 7) : (ha39_0_11 j).Contains (fullFactor false 39 11 ((j.val:ℝ)/6)) := by
  rw [ha39_0_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_0_10 j) false 39 10 j (ha39_0_10_contains j)
noncomputable def hk39_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_12 j i k)
lemma hk39_0_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_0_12 j i k).Contains (fullFactor false 39 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_0_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power39 j i k) (mpower0_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 12 (power39_contains j i k) (mpower0_12_contains j i k)
noncomputable def ha39_0_12 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨886434200375614885,886434200375614886⟩⟩,⟨⟨(-3630834484738518573078),(-3630834484738518569035)⟩,⟨(-2063),1841⟩⟩,⟨⟨(-38369),81666⟩,⟨(-471087477881817150440283),(-471087477881817150302254)⟩⟩,⟨⟨14871898049488972044904168,14871898049488972089188790⟩,⟨(-20947239),22769702⟩⟩,⟨⟨(-416914015),383763608⟩,⟨216414599701077852503675721,216414599701077853312625310⟩⟩,⟨⟨(-1929574309403923048450717401),(-1929574309403923047390712288)⟩,⟨(-670493818),315806986⟩⟩]
lemma ha39_0_12_eq (j : Fin 7) : ha39_0_12 j = ((ha39_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha39_0_12_contains (j : Fin 7) : (ha39_0_12 j).Contains (fullFactor false 39 12 ((j.val:ℝ)/6)) := by
  rw [ha39_0_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_0_11 j) false 39 11 j (ha39_0_11_contains j)
noncomputable def hk39_0_13 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_13 j i k)
lemma hk39_0_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_0_13 j i k).Contains (fullFactor false 39 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_0_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power39 j i k) (mpower0_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 13 (power39_contains j i k) (mpower0_13_contains j i k)
noncomputable def ha39_0_13 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-35702758612702237),(-35702758612702236)⟩,⟨(-1),1⟩⟩,⟨⟨(-149),167⟩,⟨(-292476998555256723190),(-292476998555256722862)⟩⟩,⟨⟨56921729219679268109878,56921729219679268126738⟩,⟨(-4637),9868⟩⟩,⟨⟨(-3668366),3374754⟩,⟨2395971572164663071458891,2395971572164663078601095⟩⟩,⟨⟨(-43582469009646285112682230),(-43582469009646284949633881)⟩,⟨(-83959873),77283906⟩⟩,⟨⟨(-76318224),162032189⟩,⟨(-466302805767612564553999260),(-466302805767612564296353103)⟩⟩]
lemma ha39_0_13_eq (j : Fin 7) : ha39_0_13 j = ((ha39_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha39_0_13_contains (j : Fin 7) : (ha39_0_13 j).Contains (fullFactor false 39 13 ((j.val:ℝ)/6)) := by
  rw [ha39_0_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_0_12 j) false 39 12 j (ha39_0_12_contains j)
noncomputable def hk39_0_14 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_14 j i k)
lemma hk39_0_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_0_14 j i k).Contains (fullFactor false 39 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_0_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power39 j i k) (mpower0_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 14 (power39_contains j i k) (mpower0_14_contains j i k)
noncomputable def ha39_0_14 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-1335280049649466),(-1335280049649465)⟩⟩,⟨⟨21877228333456835505,21877228333456835530⟩,⟨(-12),13⟩⟩,⟨⟨(-1108),521⟩,⟨6386603083791852240200,6386603083791852242114⟩⟩,⟨⟨(-358436509015356793656316),(-358436509015356792586702)⟩,⟨(-548787),504863⟩⟩,⟨⟨(-14452057),15700460⟩,⟨(-8149902646786285772408540),(-8149902646786285741892627)⟩⟩,⟨⟨104638104924845707090041257,104638104924845707148189994⟩,⟨(-17125770),36359939⟩⟩]
lemma ha39_0_14_eq (j : Fin 7) : ha39_0_14 j = ((ha39_0_13 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha39_0_14_contains (j : Fin 7) : (ha39_0_14 j).Contains (fullFactor false 39 14 ((j.val:ℝ)/6)) := by
  rw [ha39_0_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_0_13 j) false 39 13 j (ha39_0_13_contains j)
noncomputable def hk39_0_15 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_15 j i k)
lemma hk39_0_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_0_15 j i k).Contains (fullFactor false 39 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_0_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power39 j i k) (mpower0_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 15 (power39_contains j i k) (mpower0_15_contains j i k)
noncomputable def ha39_0_15 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨46610066605153,46610066605154⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨1527318662517654885,1527318662517654888⟩⟩,⟨⟨(-668803510981146723357),(-668803510981146723154)⟩,⟨(-117),55⟩⟩,⟨⟨(-70493),76626⟩,⟨(-50047177933378515402772),(-50047177933378515253266)⟩⟩,⟨⟨1422426349034211490170574,1422426349034211495501134⟩,⟨(-2522360),2740248⟩⟩,⟨⟨(-7615208),3586813⟩,⟨21915353447830215821507043,21915353447830215833755445⟩⟩]
lemma ha39_0_15_eq (j : Fin 7) : ha39_0_15 j = ((ha39_0_14 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha39_0_15_contains (j : Fin 7) : (ha39_0_15 j).Contains (fullFactor false 39 15 ((j.val:ℝ)/6)) := by
  rw [ha39_0_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_0_14 j) false 39 14 j (ha39_0_14_contains j)
noncomputable def hk39_0_16 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_16 j i k)
lemma hk39_0_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_0_16 j i k).Contains (fullFactor false 39 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_0_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power39 j i k) (mpower0_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 16 (power39_contains j i k) (mpower0_16_contains j i k)
noncomputable def ha39_0_16 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨1525310862813,1525310862814⟩⟩,⟨⟨(-99962772705334444),(-99962772705334443)⟩,⟨(-1),1⟩⟩,⟨⟨(-6),12⟩,⟨(-65659631149794723633),(-65659631149794723612)⟩⟩,⟨⟨6551160272016798089034,6551160272016798108626⟩,⟨(-9228),10031⟩⟩,⟨⟨(-448373),412721⟩,⟨232743967104084890939363,232743967104084891812316⟩⟩,⟨⟨(-4303069587032947008558803),(-4303069587032947006140137)⟩,⟨(-1495243),704270⟩⟩]
lemma ha39_0_16_eq (j : Fin 7) : ha39_0_16 j = ((ha39_0_15 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha39_0_16_contains (j : Fin 7) : (ha39_0_16 j).Contains (fullFactor false 39 16 ((j.val:ℝ)/6)) := by
  rw [ha39_0_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_0_15 j) false 39 15 j (ha39_0_15_contains j)
noncomputable def hk39_0_17 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_17 j i k)
lemma hk39_0_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_0_17 j i k).Contains (fullFactor false 39 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_0_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power39 j i k) (mpower0_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 17 (power39_contains j i k) (mpower0_17_contains j i k)
noncomputable def ha39_0_17 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-46979464717),(-46979464716)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-6157692399285196),(-6157692399285195)⟩⟩,⟨⟨6066935731106195666,6066935731106195669⟩,⟨(-1),2⟩⟩,⟨⟨(-1236),1137⟩,⟨807101058159109192219,807101058159109194636⟩⟩,⟨⟨(-35842487118702823553851),(-35842487118702823419301)⟩,⟨(-69050),63559⟩⟩,⟨⟨(-130149),276321⟩,⟨(-795205400147551278713212),(-795205400147551278263711)⟩⟩]
lemma ha39_0_17_eq (j : Fin 7) : ha39_0_17 j = ((ha39_0_16 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha39_0_17_contains (j : Fin 7) : (ha39_0_17 j).Contains (fullFactor false 39 17 ((j.val:ℝ)/6)) := by
  rw [ha39_0_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_0_16 j) false 39 16 j (ha39_0_16_contains j)
noncomputable def hk39_0_18 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_18 j i k)
lemma hk39_0_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_0_18 j i k).Contains (fullFactor false 39 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_0_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power39 j i k) (mpower0_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 18 (power39_contains j i k) (mpower0_18_contains j i k)
noncomputable def ha39_0_18 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-1366577234),(-1366577233)⟩⟩,⟨⟨358240022308519,358240022308520⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨529440020073462376,529440020073462377⟩⟩,⟨⟨(-93910472408044662880),(-93910472408044662598)⟩,⟨(-144),133⟩⟩,⟨⟨(-9245),10043⟩,⟨(-5213078436041832681468),(-5213078436041832661881)⟩⟩,⟨⟨138789524622137721107107,138789524622137721186003⟩,⟨(-22716),48228⟩⟩]
lemma ha39_0_18_eq (j : Fin 7) : ha39_0_18 j = ((ha39_0_17 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha39_0_18_contains (j : Fin 7) : (ha39_0_18 j).Contains (fullFactor false 39 18 ((j.val:ℝ)/6)) := by
  rw [ha39_0_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_0_17 j) false 39 17 j (ha39_0_17_contains j)
noncomputable def hk39_0_19 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_19 j i k)
lemma hk39_0_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_0_19 j i k).Contains (fullFactor false 39 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_0_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power39 j i k) (mpower0_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 19 (power39_contains j i k) (mpower0_19_contains j i k)
noncomputable def ha39_0_19 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨37659903,37659904⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨19744635479057,19744635479058⟩⟩,⟨⟨(-43770654673137423),(-43770654673137422)⟩,⟨(-1),1⟩⟩,⟨⟨(-15),16⟩,⟨(-10351875446044213778),(-10351875446044213745)⟩⟩,⟨⟨718305654265631153699,718305654265631156402⟩,⟨(-1274),1384⟩⟩,⟨⟨(-7975),3757⟩,⟨22948428997269873103971,22948428997269873117091⟩⟩]
lemma ha39_0_19_eq (j : Fin 7) : ha39_0_19 j = ((ha39_0_18 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha39_0_19_contains (j : Fin 7) : (ha39_0_19 j).Contains (fullFactor false 39 19 ((j.val:ℝ)/6)) := by
  rw [ha39_0_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_0_18 j) false 39 18 j (ha39_0_18_contains j)
noncomputable def hk39_0_20 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_20 j i k)
lemma hk39_0_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_0_20 j i k).Contains (fullFactor false 39 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_0_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power39 j i k) (mpower0_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 20 (power39_contains j i k) (mpower0_20_contains j i k)
noncomputable def ha39_0_20 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨985933,985934⟩⟩,⟨⟨(-1033826696147),(-1033826696146)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-3437739179098608),(-3437739179098606)⟩⟩,⟨⟨1084045861738968865,1084045861738968869⟩,⟨(-2),2⟩⟩,⟨⟨(-182),167⟩,⟨94025990269704865037,94025990269704865392⟩⟩,⟨⟨(-3604730797462500934950),(-3604730797462500932877)⟩,⟨(-1253),591⟩⟩]
lemma ha39_0_20_eq (j : Fin 7) : ha39_0_20 j = ((ha39_0_19 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha39_0_20_contains (j : Fin 7) : (ha39_0_20 j).Contains (fullFactor false 39 20 ((j.val:ℝ)/6)) := by
  rw [ha39_0_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_0_19 j) false 39 19 j (ha39_0_19_contains j)
noncomputable def hk39_0_21 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_21 j i k)
lemma hk39_0_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_0_21 j i k).Contains (fullFactor false 39 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_0_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power39 j i k) (mpower0_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 21 (power39_contains j i k) (mpower0_21_contains j i k)
noncomputable def ha39_0_21 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-24583),(-24582)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-51553370694),(-51553370693)⟩⟩,⟨⟨257142289286047,257142289286048⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨108115254456938454,108115254456938455⟩⟩,⟨⟨(-11721879376103578846),(-11721879376103578800)⟩,⟨(-23),21⟩⟩,⟨⟨(-89),188⟩,⟨(-539266466260812849100),(-539266466260812848787)⟩⟩]
lemma ha39_0_21_eq (j : Fin 7) : ha39_0_21 j = ((ha39_0_20 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha39_0_21_contains (j : Fin 7) : (ha39_0_21 j).Contains (fullFactor false 39 21 ((j.val:ℝ)/6)) := by
  rw [ha39_0_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_0_20 j) false 39 20 j (ha39_0_20_contains j)
noncomputable def hk39_0_22 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_22 j i k)
lemma hk39_0_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_0_22 j i k).Contains (fullFactor false 39 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_0_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power39 j i k) (mpower0_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 22 (power39_contains j i k) (mpower0_22_contains j i k)
noncomputable def ha39_0_22 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-586),(-585)⟩⟩,⟨⟨2453934706,2453934707⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨18359916521552,18359916521553⟩⟩,⟨⟨(-10292548155845728),(-10292548155845727)⟩,⟨(-1),1⟩⟩,⟨⟨(-3),3⟩,⟨(-1394900383872451223),(-1394900383872451216)⟩⟩,⟨⟨77007071306013533776,77007071306013533822⟩,⟨(-13),27⟩⟩]
lemma ha39_0_22_eq (j : Fin 7) : ha39_0_22 j = ((ha39_0_21 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha39_0_22_contains (j : Fin 7) : (ha39_0_22 j).Contains (fullFactor false 39 22 ((j.val:ℝ)/6)) := by
  rw [ha39_0_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_0_21 j) false 39 21 j (ha39_0_21_contains j)
noncomputable def hk39_0_23 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_23 j i k)
lemma hk39_0_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_0_23 j i k).Contains (fullFactor false 39 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_0_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power39 j i k) (mpower0_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 23 (power39_contains j i k) (mpower0_23_contains j i k)
noncomputable def ha39_0_23 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨13,14⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨111728452,111728453⟩⟩,⟨⟨(-1253899540536),(-1253899540535)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-937246193423888),(-937246193423887)⟩⟩,⟨⟨158775681103741856,158775681103741858⟩,⟨(-1),1⟩⟩,⟨⟨(-4),2⟩,⟨10518471716932064452,10518471716932064459⟩⟩]
lemma ha39_0_23_eq (j : Fin 7) : ha39_0_23 j = ((ha39_0_22 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha39_0_23_contains (j : Fin 7) : (ha39_0_23 j).Contains (fullFactor false 39 23 ((j.val:ℝ)/6)) := by
  rw [ha39_0_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_0_22 j) false 39 22 j (ha39_0_22_contains j)
noncomputable def hk39_0_24 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_24 j i k)
lemma hk39_0_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_0_24 j i k).Contains (fullFactor false 39 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_0_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power39 j i k) (mpower0_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 24 (power39_contains j i k) (mpower0_24_contains j i k)
noncomputable def ha39_0_24 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨0,1⟩⟩,⟨⟨(-4875074),(-4875073)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-82067533019),(-82067533018)⟩⟩,⟨⟨81790159885152,81790159885153⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨17319740045980248,17319740045980250⟩⟩,⟨⟨(-1376864728037741371),(-1376864728037741370)⟩,⟨(-1),1⟩⟩]
lemma ha39_0_24_eq (j : Fin 7) : ha39_0_24 j = ((ha39_0_23 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha39_0_24_contains (j : Fin 7) : (ha39_0_24 j).Contains (fullFactor false 39 24 ((j.val:ℝ)/6)) := by
  rw [ha39_0_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_0_23 j) false 39 23 j (ha39_0_23_contains j)
noncomputable def hk39_0_25 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_25 j i k)
lemma hk39_0_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_0_25 j i k).Contains (fullFactor false 39 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_0_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power39 j i k) (mpower0_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 25 (power39_contains j i k) (mpower0_25_contains j i k)
noncomputable def ha39_0_25 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-204207),(-204206)⟩⟩,⟨⟨5156455176,5156455177⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨6852036411496,6852036411497⟩⟩,⟨⟨(-1813718936351217),(-1813718936351216)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-173021924583611077),(-173021924583611076)⟩⟩]
lemma ha39_0_25_eq (j : Fin 7) : ha39_0_25 j = ((ha39_0_24 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha39_0_25_contains (j : Fin 7) : (ha39_0_25 j).Contains (fullFactor false 39 25 ((j.val:ℝ)/6)) := by
  rw [ha39_0_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_0_24 j) false 39 24 j (ha39_0_24_contains j)
noncomputable def hk39_0_26 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_26 j i k)
lemma hk39_0_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_0_26 j i k).Contains (fullFactor false 39 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_0_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power39 j i k) (mpower0_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 26 (power39_contains j i k) (mpower0_26_contains j i k)
noncomputable def ha39_0_26 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-1),0⟩⟩,⟨⟨8224,8225⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨311528494,311528495⟩⟩,⟨⟨(-551956596218),(-551956596217)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-182627118144798),(-182627118144797)⟩⟩,⟨⟨20906323353147684,20906323353147685⟩,⟨(-1),1⟩⟩]
lemma ha39_0_26_eq (j : Fin 7) : ha39_0_26 j = ((ha39_0_25 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha39_0_26_contains (j : Fin 7) : (ha39_0_26 j).Contains (fullFactor false 39 26 ((j.val:ℝ)/6)) := by
  rw [ha39_0_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_0_25 j) false 39 25 j (ha39_0_25_contains j)
noncomputable def hk39_0_27 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_27 j i k)
lemma hk39_0_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_0_27 j i k).Contains (fullFactor false 39 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_0_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power39 j i k) (mpower0_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 27 (power39_contains j i k) (mpower0_27_contains j i k)
noncomputable def ha39_0_27 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨318,320⟩⟩,⟨⟨(-18123994),(-18123993)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-42815377477),(-42815377475)⟩⟩,⟨⟨17708025083641,17708025083642⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨2432561179993388,2432561179993389⟩⟩]
lemma ha39_0_27_eq (j : Fin 7) : ha39_0_27 j = ((ha39_0_26 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha39_0_27_contains (j : Fin 7) : (ha39_0_27 j).Contains (fullFactor false 39 27 ((j.val:ℝ)/6)) := by
  rw [ha39_0_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_0_26 j) false 39 26 j (ha39_0_26_contains j)
noncomputable def hk39_0_28 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_28 j i k)
lemma hk39_0_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_0_28 j i k).Contains (fullFactor false 39 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_0_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power39 j i k) (mpower0_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 28 (power39_contains j i k) (mpower0_28_contains j i k)
noncomputable def ha39_0_28 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨0,1⟩⟩,⟨⟨(-12),(-11)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1016754),(-1016753)⟩⟩,⟨⟨3202582746,3202582747⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨1655696473581,1655696473582⟩⟩,⟨⟨(-272932726159820),(-272932726159819)⟩,⟨(-1),1⟩⟩]
lemma ha39_0_28_eq (j : Fin 7) : ha39_0_28 j = ((ha39_0_27 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha39_0_28_contains (j : Fin 7) : (ha39_0_28 j).Contains (fullFactor false 39 28 ((j.val:ℝ)/6)) := by
  rw [ha39_0_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_0_27 j) false 39 27 j (ha39_0_27_contains j)
noncomputable def hk39_0_29 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_29 j i k)
lemma hk39_0_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_0_29 j i k).Contains (fullFactor false 39 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_0_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power39 j i k) (mpower0_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 29 (power39_contains j i k) (mpower0_29_contains j i k)
noncomputable def ha39_0_29 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),0⟩⟩,⟨⟨55072,55073⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨231292193,231292194⟩⟩,⟨⟨(-149469076954),(-149469076953)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-29567015428550),(-29567015428549)⟩⟩]
lemma ha39_0_29_eq (j : Fin 7) : ha39_0_29 j = ((ha39_0_28 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha39_0_29_contains (j : Fin 7) : (ha39_0_29 j).Contains (fullFactor false 39 29 ((j.val:ℝ)/6)) := by
  rw [ha39_0_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_0_28 j) false 39 28 j (ha39_0_28_contains j)
noncomputable def hk39_0_30 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_30 j i k)
lemma hk39_0_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_0_30 j i k).Contains (fullFactor false 39 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_0_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power39 j i k) (mpower0_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 30 (power39_contains j i k) (mpower0_30_contains j i k)
noncomputable def ha39_0_30 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-1),0⟩⟩,⟨⟨0,1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨2883,2884⟩⟩,⟨⟨(-16147242),(-16147241)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-13043637614),(-13043637613)⟩⟩,⟨⟨3096250615296,3096250615297⟩,⟨(-1),1⟩⟩]
lemma ha39_0_30_eq (j : Fin 7) : ha39_0_30 j = ((ha39_0_29 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha39_0_30_contains (j : Fin 7) : (ha39_0_30 j).Contains (fullFactor false 39 30 ((j.val:ℝ)/6)) := by
  rw [ha39_0_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_0_29 j) false 39 29 j (ha39_0_29_contains j)
noncomputable def hk39_1_0 (j : Fin 6) (i k : Fin 16) : CBox := (kernel39_0 j i k).mul (mpower1_0 j i k)
lemma hk39_1_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_1_0 j i k).Contains (fullFactor true 39 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_1_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel39_0 j i k) (mpower1_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 0 (kernel39_0_contains j i k) (mpower1_0_contains j i k)
noncomputable def ha39_1_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-4),2⟩,⟨(-2),4⟩⟩,⟨⟨(-3),0⟩,⟨(-2),2⟩⟩,⟨⟨(-31926),(-31923)⟩,⟨2507,2510⟩⟩,⟨⟨635863206902312638,635863206902312662⟩,⟨(-1325938779881954263),(-1325938779881954239)⟩⟩,⟨⟨113546669637062691669758862,113546669637062697375502405⟩,⟨(-698503320922647562276889979),(-698503320922647556566360541)⟩⟩]
lemma ha39_1_0_eq (j : Fin 7) : ha39_1_0 j = atomKernel39_0 j := by fin_cases j <;> decide +kernel
lemma ha39_1_0_contains (j : Fin 7) : (ha39_1_0 j).Contains (fullFactor true 39 0 ((j.val:ℝ)/6)) := by
  rw [ha39_1_0_eq]
  simpa only [fullFactor,ite_true] using atomKernel39_0_contains j
noncomputable def hk39_1_1 (j : Fin 6) (i k : Fin 16) : CBox := (kernel39_0 j i k).mul (mpower1_1 j i k)
lemma hk39_1_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_1_1 j i k).Contains (fullFactor true 39 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_1_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel39_0 j i k) (mpower1_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 1 (kernel39_0_contains j i k) (mpower1_1_contains j i k)
noncomputable def ha39_1_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),46⟩,⟨(-46),46⟩⟩,⟨⟨(-21),41⟩,⟨(-30),31⟩⟩,⟨⟨(-11),19⟩,⟨(-6),21⟩⟩,⟨⟨59957,59976⟩,⟨143680,143699⟩⟩,⟨⟨(-5864694104202136490),(-5864694104202136374)⟩,⟨(-1663824078702990933),(-1663824078702990817)⟩⟩,⟨⟨(-2543634718900661190487942318),(-2543634718900661168787588579)⟩,⟨(-278859669301624039056922852),(-278859669301624017379326452)⟩⟩]
lemma ha39_1_1_eq (j : Fin 7) : ha39_1_1 j = ((ha39_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha39_1_1_contains (j : Fin 7) : (ha39_1_1 j).Contains (fullFactor true 39 1 ((j.val:ℝ)/6)) := by
  rw [ha39_1_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_1_0 j) true 39 0 j (ha39_1_0_contains j)
noncomputable def hk39_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel39_0 j i k).mul (mpower1_2 j i k)
lemma hk39_1_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_1_2 j i k).Contains (fullFactor true 39 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_1_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel39_0 j i k) (mpower1_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 2 (kernel39_0_contains j i k) (mpower1_2_contains j i k)
noncomputable def ha39_1_2 : Fin 7 → CBox := ![⟨⟨(-130),130⟩,⟨(-130),130⟩⟩,⟨⟨(-262),262⟩,⟨(-262),262⟩⟩,⟨⟨(-179),132⟩,⟨(-182),128⟩⟩,⟨⟨(-43),70⟩,⟨(-79),37⟩⟩,⟨⟨286457,286516⟩,⟨(-247422),(-247363)⟩⟩,⟨⟨(-1333340159599476396),(-1333340159599476117)⟩,⟨12565425635076138885,12565425635076139163⟩⟩,⟨⟨(-264671352213862046843782691),(-264671352213862005664863252)⟩,⟨4618746809031149370975874286,4618746809031149412206084906⟩⟩]
lemma ha39_1_2_eq (j : Fin 7) : ha39_1_2 j = ((ha39_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha39_1_2_contains (j : Fin 7) : (ha39_1_2 j).Contains (fullFactor true 39 2 ((j.val:ℝ)/6)) := by
  rw [ha39_1_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_1_1 j) true 39 1 j (ha39_1_1_contains j)
noncomputable def hk39_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel39_0 j i k).mul (mpower1_3 j i k)
lemma hk39_1_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_1_3 j i k).Contains (fullFactor true 39 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_1_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel39_0 j i k) (mpower1_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 3 (kernel39_0_contains j i k) (mpower1_3_contains j i k)
noncomputable def ha39_1_3 : Fin 7 → CBox := ![⟨⟨(-400),400⟩,⟨(-400),400⟩⟩,⟨⟨(-995),995⟩,⟨(-995),995⟩⟩,⟨⟨(-530),514⟩,⟨(-437),606⟩⟩,⟨⟨(-201),104⟩,⟨(-155),148⟩⟩,⟨⟨(-525754),(-525632)⟩,⟨(-316286),(-316165)⟩⟩,⟨⟨17424187253085025666,17424187253085026111⟩,⟨(-1134267765100067408),(-1134267765100066961)⟩⟩,⟨⟨5576037740222818895779760385,5576037740222818948002732113⟩,⟨29485854958038499753948179,29485854958038551902577547⟩⟩]
lemma ha39_1_3_eq (j : Fin 7) : ha39_1_3 j = ((ha39_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha39_1_3_contains (j : Fin 7) : (ha39_1_3 j).Contains (fullFactor true 39 3 ((j.val:ℝ)/6)) := by
  rw [ha39_1_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_1_2 j) true 39 2 j (ha39_1_2_contains j)
noncomputable def hk39_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel39_0 j i k).mul (mpower1_4 j i k)
lemma hk39_1_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_1_4 j i k).Contains (fullFactor true 39 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_1_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel39_0 j i k) (mpower1_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 4 (kernel39_0_contains j i k) (mpower1_4_contains j i k)
noncomputable def ha39_1_4 : Fin 7 → CBox := ![⟨⟨(-922),922⟩,⟨(-922),922⟩⟩,⟨⟨(-2832),2832⟩,⟨(-2832),2832⟩⟩,⟨⟨(-1196),1433⟩,⟨(-1408),1221⟩⟩,⟨⟨(-272),332⟩,⟨(-238),367⟩⟩,⟨⟨(-166180),(-165993)⟩,⟨726879,727066⟩⟩,⟨⟨(-4226440613975573151),(-4226440613975572616)⟩,⟨(-17596023164606756250),(-17596023164606755716)⟩⟩,⟨⟨(-235139279632710041730525931),(-235139279632709992200572728)⟩,⟨(-5035188532523026243567479098),(-5035188532523026193958793153)⟩⟩]
lemma ha39_1_4_eq (j : Fin 7) : ha39_1_4 j = ((ha39_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha39_1_4_contains (j : Fin 7) : (ha39_1_4 j).Contains (fullFactor true 39 4 ((j.val:ℝ)/6)) := by
  rw [ha39_1_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_1_3 j) true 39 3 j (ha39_1_3_contains j)
noncomputable def hk39_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel39_0 j i k).mul (mpower1_5 j i k)
lemma hk39_1_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_1_5 j i k).Contains (fullFactor true 39 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_1_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel39_0 j i k) (mpower1_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 5 (kernel39_0_contains j i k) (mpower1_5_contains j i k)
noncomputable def ha39_1_5 : Fin 7 → CBox := ![⟨⟨(-1700),1700⟩,⟨(-1700),1700⟩⟩,⟨⟨(-6448),6448⟩,⟨(-6448),6448⟩⟩,⟨⟨(-2862),2436⟩,⟨(-2679),2619⟩⟩,⟨⟨(-432),529⟩,⟨(-547),413⟩⟩,⟨⟨721942,722172⟩,⟨(-66976),(-66746)⟩⟩,⟨⟨(-13781652062838665666),(-13781652062838665153)⟩,⟨5931845768746299672,5931845768746300185⟩⟩,⟨⟨(-3627608801810058856332667871),(-3627608801810058818633332190)⟩,⟨358913660053250843344142840,358913660053250880979113310⟩⟩]
lemma ha39_1_5_eq (j : Fin 7) : ha39_1_5 j = ((ha39_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha39_1_5_contains (j : Fin 7) : (ha39_1_5 j).Contains (fullFactor true 39 5 ((j.val:ℝ)/6)) := by
  rw [ha39_1_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_1_4 j) true 39 4 j (ha39_1_4_contains j)
noncomputable def hk39_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel39_0 j i k).mul (mpower1_6 j i k)
lemma hk39_1_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_1_6 j i k).Contains (fullFactor true 39 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_1_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel39_0 j i k) (mpower1_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 6 (kernel39_0_contains j i k) (mpower1_6_contains j i k)
noncomputable def ha39_1_6 : Fin 7 → CBox := ![⟨⟨(-2612),2612⟩,⟨(-2612),2612⟩⟩,⟨⟨(-12235),12235⟩,⟨(-12235),12235⟩⟩,⟨⟨(-4299),4597⟩,⟨(-4241),4655⟩⟩,⟨⟨(-716),556⟩,⟨(-646),626⟩⟩,⟨⟨(-233963),(-233727)⟩,⟨(-539214),(-538978)⟩⟩,⟨⟨5656638831070983627,5656638831070984038⟩,⟨8687383287027658524,8687383287027658935⟩⟩,⟨⟨329535807301389510656101488,329535807301389534487115273⟩,⟨2171999236579299717255176066,2171999236579299741128849166⟩⟩]
lemma ha39_1_6_eq (j : Fin 7) : ha39_1_6 j = ((ha39_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha39_1_6_contains (j : Fin 7) : (ha39_1_6 j).Contains (fullFactor true 39 6 ((j.val:ℝ)/6)) := by
  rw [ha39_1_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_1_5 j) true 39 5 j (ha39_1_5_contains j)
noncomputable def hk39_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel39_0 j i k).mul (mpower1_7 j i k)
lemma hk39_1_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_1_7 j i k).Contains (fullFactor true 39 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_1_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel39_0 j i k) (mpower1_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 7 (kernel39_0_contains j i k) (mpower1_7_contains j i k)
noncomputable def ha39_1_7 : Fin 7 → CBox := ![⟨⟨(-3439),3439⟩,⟨(-3439),3439⟩⟩,⟨⟨(-19898),19898⟩,⟨(-19898),19898⟩⟩,⟨⟨(-6354),6449⟩,⟨(-6657),6146⟩⟩,⟨⟨(-697),747⟩,⟨(-659),784⟩⟩,⟨⟨(-305284),(-305076)⟩,⟨270937,271144⟩⟩,⟨⟨4500933329404715413,4500933329404715696⟩,⟨(-4175373145053176653),(-4175373145053176371)⟩⟩,⟨⟨1111609679332003332940782148,1111609679332003345899131730⟩,⟨(-228257994624846603135653625),(-228257994624846590201034060)⟩⟩]
lemma ha39_1_7_eq (j : Fin 7) : ha39_1_7 j = ((ha39_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha39_1_7_contains (j : Fin 7) : (ha39_1_7 j).Contains (fullFactor true 39 7 ((j.val:ℝ)/6)) := by
  rw [ha39_1_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_1_6 j) true 39 6 j (ha39_1_6_contains j)
noncomputable def hk39_1_8 (j : Fin 6) (i k : Fin 16) : CBox := (kernel39_0 j i k).mul (mpower1_8 j i k)
lemma hk39_1_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_1_8 j i k).Contains (fullFactor true 39 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_1_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel39_0 j i k) (mpower1_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 8 (kernel39_0_contains j i k) (mpower1_8_contains j i k)
noncomputable def ha39_1_8 : Fin 7 → CBox := ![⟨⟨(-3962),3962⟩,⟨(-3962),3962⟩⟩,⟨⟨(-28316),28316⟩,⟨(-28316),28316⟩⟩,⟨⟨(-8255),7868⟩,⟨(-7935),8188⟩⟩,⟨⟨(-686),748⟩,⟨(-755),679⟩⟩,⟨⟨214253,214413⟩,⟨124821,124981⟩⟩,⟨⟨(-2528458172988339448),(-2528458172988339278)⟩,⟨(-1930863595314489044),(-1930863595314488874)⟩⟩,⟨⟨(-129122029993317590974152550),(-129122029993317584831181439)⟩,⟨(-496398840950980832007197489),(-496398840950980825852868961)⟩⟩]
lemma ha39_1_8_eq (j : Fin 7) : ha39_1_8 j = ((ha39_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha39_1_8_contains (j : Fin 7) : (ha39_1_8 j).Contains (fullFactor true 39 8 ((j.val:ℝ)/6)) := by
  rw [ha39_1_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_1_7 j) true 39 7 j (ha39_1_7_contains j)
noncomputable def hk39_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel39_0 j i k).mul (mpower1_9 j i k)
lemma hk39_1_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_1_9 j i k).Contains (fullFactor true 39 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_1_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel39_0 j i k) (mpower1_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 9 (kernel39_0_contains j i k) (mpower1_9_contains j i k)
noncomputable def ha39_1_9 : Fin 7 → CBox := ![⟨⟨(-4057),4057⟩,⟨(-4057),4057⟩⟩,⟨⟨(-35817),35817⟩,⟨(-35817),35817⟩⟩,⟨⟨(-8845),9202⟩,⟨(-8982),9065⟩⟩,⟨⟨(-664),602⟩,⟨(-639),627⟩⟩,⟨⟨27973,28083⟩,⟨(-131109),(-130999)⟩⟩,⟨⟨(-678593729957289091),(-678593729957288999)⟩,⟨1298824123730242788,1298824123730242880⟩⟩,⟨⟨(-196473718173463857833440033),(-196473718173463855235361170)⟩,⟨62163720861644459994845295,62163720861644462588159564⟩⟩]
lemma ha39_1_9_eq (j : Fin 7) : ha39_1_9 j = ((ha39_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha39_1_9_contains (j : Fin 7) : (ha39_1_9 j).Contains (fullFactor true 39 9 ((j.val:ℝ)/6)) := by
  rw [ha39_1_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_1_8 j) true 39 8 j (ha39_1_8_contains j)
noncomputable def hk39_1_10 (j : Fin 6) (i k : Fin 16) : CBox := (kernel39_0 j i k).mul (mpower1_10 j i k)
lemma hk39_1_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_1_10 j i k).Contains (fullFactor true 39 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_1_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel39_0 j i k) (mpower1_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 10 (kernel39_0_contains j i k) (mpower1_10_contains j i k)
noncomputable def ha39_1_10 : Fin 7 → CBox := ![⟨⟨(-3739),3739⟩,⟨(-3739),3739⟩⟩,⟨⟨(-40775),40775⟩,⟨(-40775),40775⟩⟩,⟨⟨(-9157),9024⟩,⟨(-9203),8978⟩⟩,⟨⟨(-497),509⟩,⟨(-485),521⟩⟩,⟨⟨(-64828),(-64760)⟩,⟨6876,6945⟩⟩,⟨⟨578401802946355155,578401802946355200⟩,⟨185748790416667622,185748790416667667⟩⟩,⟨⟨26136734372400521050476922,26136734372400522035797652⟩,⟨69779902186290868882883274,69779902186290869869981397⟩⟩]
lemma ha39_1_10_eq (j : Fin 7) : ha39_1_10 j = ((ha39_1_9 j).mul (piI.mul (atomPoints j).z)).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha39_1_10_contains (j : Fin 7) : (ha39_1_10 j).Contains (fullFactor true 39 10 ((j.val:ℝ)/6)) := by
  rw [ha39_1_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_1_9 j) true 39 9 j (ha39_1_9_contains j)
noncomputable def hk39_1_11 (j : Fin 6) (i k : Fin 16) : CBox := (kernel39_0 j i k).mul (mpower1_11 j i k)
lemma hk39_1_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_1_11 j i k).Contains (fullFactor true 39 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_1_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel39_0 j i k) (mpower1_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 11 (kernel39_0_contains j i k) (mpower1_11_contains j i k)
noncomputable def ha39_1_11 : Fin 7 → CBox := ![⟨⟨(-3133),3133⟩,⟨(-3133),3133⟩⟩,⟨⟨(-42199),42199⟩,⟨(-42199),42199⟩⟩,⟨⟨(-8348),8303⟩,⟨(-8244),8407⟩⟩,⟨⟨(-357),370⟩,⟨(-371),356⟩⟩,⟨⟨11809,11848⟩,⟨26242,26281⟩⟩,⟨⟨31951590399716207,31951590399716228⟩,⟨(-226706036630800385),(-226706036630800364)⟩⟩,⟨⟨22460841953669943270891336,22460841953669943611825127⟩,⟨(-9771203150799157172047983),(-9771203150799156831710557)⟩⟩]
lemma ha39_1_11_eq (j : Fin 7) : ha39_1_11 j = ((ha39_1_10 j).mul (piI.mul (atomPoints j).z)).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha39_1_11_contains (j : Fin 7) : (ha39_1_11 j).Contains (fullFactor true 39 11 ((j.val:ℝ)/6)) := by
  rw [ha39_1_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_1_10 j) true 39 10 j (ha39_1_10_contains j)
noncomputable def hk39_1_12 (j : Fin 6) (i k : Fin 16) : CBox := (kernel39_0 j i k).mul (mpower1_12 j i k)
lemma hk39_1_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_1_12 j i k).Contains (fullFactor true 39 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_1_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel39_0 j i k) (mpower1_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 12 (kernel39_0_contains j i k) (mpower1_12_contains j i k)
noncomputable def ha39_1_12 : Fin 7 → CBox := ![⟨⟨(-2406),2406⟩,⟨(-2406),2406⟩⟩,⟨⟨(-40034),40034⟩,⟨(-40034),40034⟩⟩,⟨⟨(-6945),7034⟩,⟨(-7013),6966⟩⟩,⟨⟨(-246),236⟩,⟨(-242),240⟩⟩,⟨⟨8606,8627⟩,⟨(-7881),(-7860)⟩⟩,⟨⟨(-79055411617222979),(-79055411617222970)⟩,⟨2428208153497309,2428208153497319⟩⟩,⟨⟨(-3291801386129195433513775),(-3291801386129195325754497)⟩,⟨(-6605992796288902511727680),(-6605992796288902403786753)⟩⟩]
lemma ha39_1_12_eq (j : Fin 7) : ha39_1_12 j = ((ha39_1_11 j).mul (piI.mul (atomPoints j).z)).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha39_1_12_contains (j : Fin 7) : (ha39_1_12 j).Contains (fullFactor true 39 12 ((j.val:ℝ)/6)) := by
  rw [ha39_1_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_1_11 j) true 39 11 j (ha39_1_11_contains j)
noncomputable def hk39_1_13 (j : Fin 6) (i k : Fin 16) : CBox := (kernel39_0 j i k).mul (mpower1_13 j i k)
lemma hk39_1_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_1_13 j i k).Contains (fullFactor true 39 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_1_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel39_0 j i k) (mpower1_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 13 (kernel39_0_contains j i k) (mpower1_13_contains j i k)
noncomputable def ha39_1_13 : Fin 7 → CBox := ![⟨⟨(-1706),1706⟩,⟨(-1706),1706⟩⟩,⟨⟨(-35058),35058⟩,⟨(-35058),35058⟩⟩,⟨⟨(-5443),5390⟩,⟨(-5425),5408⟩⟩,⟨⟨(-147),148⟩,⟨(-145),150⟩⟩,⟨⟨(-3807),(-3796)⟩,⟨(-2150),(-2139)⟩⟩,⟨⟨5046082596681710,5046082596681714⟩,⟨24711889282048924,24711889282048929⟩⟩,⟨⟨(-1787407647020143448896309),(-1787407647020143417350945)⟩,⟨1009785380242402346052595,1009785380242402377547348⟩⟩]
lemma ha39_1_13_eq (j : Fin 7) : ha39_1_13 j = ((ha39_1_12 j).mul (piI.mul (atomPoints j).z)).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha39_1_13_contains (j : Fin 7) : (ha39_1_13 j).Contains (fullFactor true 39 13 ((j.val:ℝ)/6)) := by
  rw [ha39_1_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_1_12 j) true 39 12 j (ha39_1_12_contains j)
noncomputable def hk39_1_14 (j : Fin 6) (i k : Fin 16) : CBox := (kernel39_0 j i k).mul (mpower1_14 j i k)
lemma hk39_1_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_1_14 j i k).Contains (fullFactor true 39 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_1_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel39_0 j i k) (mpower1_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 14 (kernel39_0_contains j i k) (mpower1_14_contains j i k)
noncomputable def ha39_1_14 : Fin 7 → CBox := ![⟨⟨(-1123),1123⟩,⟨(-1123),1123⟩⟩,⟨⟨(-28508),28508⟩,⟨(-28508),28508⟩⟩,⟨⟨(-3892),3904⟩,⟨(-3885),3911⟩⟩,⟨⟨(-83),85⟩,⟨(-85),83⟩⟩,⟨⟨(-299),(-293)⟩,⟨1484,1490⟩⟩,⟨⟨6957242999795529,6957242999795531⟩,⟨(-2715674952715930),(-2715674952715928)⟩⟩,⟨⟨284427773594420328658753,284427773594420337206213⟩,⟨447483197665891762736212,447483197665891771296652⟩⟩]
lemma ha39_1_14_eq (j : Fin 7) : ha39_1_14 j = ((ha39_1_13 j).mul (piI.mul (atomPoints j).z)).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha39_1_14_contains (j : Fin 7) : (ha39_1_14 j).Contains (fullFactor true 39 14 ((j.val:ℝ)/6)) := by
  rw [ha39_1_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_1_13 j) true 39 13 j (ha39_1_13_contains j)
noncomputable def hk39_1_15 (j : Fin 6) (i k : Fin 16) : CBox := (kernel39_0 j i k).mul (mpower1_15 j i k)
lemma hk39_1_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_1_15 j i k).Contains (fullFactor true 39 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_1_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel39_0 j i k) (mpower1_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 15 (kernel39_0_contains j i k) (mpower1_15_contains j i k)
noncomputable def ha39_1_15 : Fin 7 → CBox := ![⟨⟨(-690),690⟩,⟨(-690),690⟩⟩,⟨⟨(-21636),21636⟩,⟨(-21636),21636⟩⟩,⟨⟨(-2616),2621⟩,⟨(-2625),2612⟩⟩,⟨⟨(-45),44⟩,⟨(-45),45⟩⟩,⟨⟨486,490⟩,⟨(-61),(-57)⟩⟩,⟨⟨(-1066290494316547),(-1066290494316545)⟩,⟨(-1767315581176763),(-1767315581176761)⟩⟩,⟨⟨104164368106051801950068,104164368106051804118220⟩,⟨(-74073434496054998141675),(-74073434496054995976604)⟩⟩]
lemma ha39_1_15_eq (j : Fin 7) : ha39_1_15 j = ((ha39_1_14 j).mul (piI.mul (atomPoints j).z)).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha39_1_15_contains (j : Fin 7) : (ha39_1_15 j).Contains (fullFactor true 39 15 ((j.val:ℝ)/6)) := by
  rw [ha39_1_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_1_14 j) true 39 14 j (ha39_1_14_contains j)
noncomputable def hk39_1_16 (j : Fin 6) (i k : Fin 16) : CBox := (kernel39_0 j i k).mul (mpower1_16 j i k)
lemma hk39_1_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_1_16 j i k).Contains (fullFactor true 39 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_1_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel39_0 j i k) (mpower1_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 16 (kernel39_0_contains j i k) (mpower1_16_contains j i k)
noncomputable def ha39_1_16 : Fin 7 → CBox := ![⟨⟨(-398),398⟩,⟨(-398),398⟩⟩,⟨⟨(-15395),15395⟩,⟨(-15395),15395⟩⟩,⟨⟨(-1652),1646⟩,⟨(-1648),1650⟩⟩,⟨⟨(-23),23⟩,⟨(-23),23⟩⟩,⟨⟨(-65),(-62)⟩,⟨(-137),(-134)⟩⟩,⟨⟨(-404313348527132),(-404313348527131)⟩,⟨350052599884329,350052599884331⟩⟩,⟨⟨(-17940024593863254793092),(-17940024593863254278955)⟩,⟨(-22639451768000633130989),(-22639451768000632616173)⟩⟩]
lemma ha39_1_16_eq (j : Fin 7) : ha39_1_16 j = ((ha39_1_15 j).mul (piI.mul (atomPoints j).z)).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha39_1_16_contains (j : Fin 7) : (ha39_1_16 j).Contains (fullFactor true 39 16 ((j.val:ℝ)/6)) := by
  rw [ha39_1_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_1_15 j) true 39 15 j (ha39_1_15_contains j)
noncomputable def hk39_1_17 (j : Fin 6) (i k : Fin 16) : CBox := (kernel39_0 j i k).mul (mpower1_17 j i k)
lemma hk39_1_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_1_17 j i k).Contains (fullFactor true 39 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_1_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel39_0 j i k) (mpower1_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 17 (kernel39_0_contains j i k) (mpower1_17_contains j i k)
noncomputable def ha39_1_17 : Fin 7 → CBox := ![⟨⟨(-216),216⟩,⟨(-216),216⟩⟩,⟨⟨(-10310),10310⟩,⟨(-10310),10310⟩⟩,⟨⟨(-976),979⟩,⟨(-977),978⟩⟩,⟨⟨(-11),11⟩,⟨(-11),11⟩⟩,⟨⟨(-32),(-30)⟩,⟨28,30⟩⟩,⟨⟨100872260439651,100872260439652⟩,⟨82658583042147,82658583042149⟩⟩,⟨⟨(-4610764190888951481069),(-4610764190888951366019)⟩,⟨4060763631358680080783,4060763631358680195692⟩⟩]
lemma ha39_1_17_eq (j : Fin 7) : ha39_1_17 j = ((ha39_1_16 j).mul (piI.mul (atomPoints j).z)).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha39_1_17_contains (j : Fin 7) : (ha39_1_17 j).Contains (fullFactor true 39 17 ((j.val:ℝ)/6)) := by
  rw [ha39_1_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_1_16 j) true 39 16 j (ha39_1_16_contains j)
noncomputable def hk39_1_18 (j : Fin 6) (i k : Fin 16) : CBox := (kernel39_0 j i k).mul (mpower1_18 j i k)
lemma hk39_1_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_1_18 j i k).Contains (fullFactor true 39 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_1_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel39_0 j i k) (mpower1_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 18 (kernel39_0_contains j i k) (mpower1_18_contains j i k)
noncomputable def ha39_1_18 : Fin 7 → CBox := ![⟨⟨(-111),111⟩,⟨(-111),111⟩⟩,⟨⟨(-6521),6521⟩,⟨(-6521),6521⟩⟩,⟨⟨(-548),547⟩,⟨(-548),547⟩⟩,⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨9,11⟩,⟨5,6⟩⟩,⟨⟨14813330040205,14813330040206⟩,⟨(-26128327908729),(-26128327908727)⟩⟩,⟨⟨862738992563006689043,862738992563006713300⟩,⟨882615908016288796936,882615908016288821219⟩⟩]
lemma ha39_1_18_eq (j : Fin 7) : ha39_1_18 j = ((ha39_1_17 j).mul (piI.mul (atomPoints j).z)).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha39_1_18_contains (j : Fin 7) : (ha39_1_18 j).Contains (fullFactor true 39 18 ((j.val:ℝ)/6)) := by
  rw [ha39_1_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_1_17 j) true 39 17 j (ha39_1_17_contains j)
noncomputable def hk39_1_19 (j : Fin 6) (i k : Fin 16) : CBox := (kernel39_0 j i k).mul (mpower1_19 j i k)
lemma hk39_1_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_1_19 j i k).Contains (fullFactor true 39 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_1_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel39_0 j i k) (mpower1_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 19 (kernel39_0_contains j i k) (mpower1_19_contains j i k)
noncomputable def ha39_1_19 : Fin 7 → CBox := ![⟨⟨(-54),54⟩,⟨(-54),54⟩⟩,⟨⟨(-3908),3908⟩,⟨(-3908),3908⟩⟩,⟨⟨(-291),291⟩,⟨(-291),291⟩⟩,⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨0,1⟩,⟨(-4),(-2)⟩⟩,⟨⟨(-6167108287377),(-6167108287375)⟩,⟨(-2216553977608),(-2216553977607)⟩⟩,⟨⟨159218401666871429126,159218401666871433982⟩,⟨(-172689721895632483532),(-172689721895632478681)⟩⟩]
lemma ha39_1_19_eq (j : Fin 7) : ha39_1_19 j = ((ha39_1_18 j).mul (piI.mul (atomPoints j).z)).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha39_1_19_contains (j : Fin 7) : (ha39_1_19 j).Contains (fullFactor true 39 19 ((j.val:ℝ)/6)) := by
  rw [ha39_1_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_1_18 j) true 39 18 j (ha39_1_18_contains j)
noncomputable def hk39_1_20 (j : Fin 6) (i k : Fin 16) : CBox := (kernel39_0 j i k).mul (mpower1_20 j i k)
lemma hk39_1_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_1_20 j i k).Contains (fullFactor true 39 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_1_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel39_0 j i k) (mpower1_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 20 (kernel39_0_contains j i k) (mpower1_20_contains j i k)
noncomputable def ha39_1_20 : Fin 7 → CBox := ![⟨⟨(-25),25⟩,⟨(-25),25⟩⟩,⟨⟨(-2225),2225⟩,⟨(-2225),2225⟩⟩,⟨⟨(-147),147⟩,⟨(-147),147⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-1),0⟩,⟨(-1),1⟩⟩,⟨⟨(-235587687654),(-235587687652)⟩,⟨1337779659328,1337779659329⟩⟩,⟨⟨(-32674202783299826846),(-32674202783299825924)⟩,⟨(-27125763298088933760),(-27125763298088932836)⟩⟩]
lemma ha39_1_20_eq (j : Fin 7) : ha39_1_20 j = ((ha39_1_19 j).mul (piI.mul (atomPoints j).z)).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha39_1_20_contains (j : Fin 7) : (ha39_1_20 j).Contains (fullFactor true 39 20 ((j.val:ℝ)/6)) := by
  rw [ha39_1_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_1_19 j) true 39 19 j (ha39_1_19_contains j)
noncomputable def hk39_1_21 (j : Fin 6) (i k : Fin 16) : CBox := (kernel39_0 j i k).mul (mpower1_21 j i k)
lemma hk39_1_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_1_21 j i k).Contains (fullFactor true 39 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_1_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel39_0 j i k) (mpower1_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 21 (kernel39_0_contains j i k) (mpower1_21_contains j i k)
noncomputable def ha39_1_21 : Fin 7 → CBox := ![⟨⟨(-11),11⟩,⟨(-11),11⟩⟩,⟨⟨(-1207),1207⟩,⟨(-1207),1207⟩⟩,⟨⟨(-71),71⟩,⟨(-71),71⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨268150073223,268150073224⟩,⟨963833074,963833076⟩⟩,⟨⟨(-4372213949542643887),(-4372213949542643719)⟩,⟨5860994885513578728,5860994885513578895⟩⟩]
lemma ha39_1_21_eq (j : Fin 7) : ha39_1_21 j = ((ha39_1_20 j).mul (piI.mul (atomPoints j).z)).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha39_1_21_contains (j : Fin 7) : (ha39_1_21 j).Contains (fullFactor true 39 21 ((j.val:ℝ)/6)) := by
  rw [ha39_1_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_1_20 j) true 39 20 j (ha39_1_20_contains j)
noncomputable def hk39_1_22 (j : Fin 6) (i k : Fin 16) : CBox := (kernel39_0 j i k).mul (mpower1_22 j i k)
lemma hk39_1_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_1_22 j i k).Contains (fullFactor true 39 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_1_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel39_0 j i k) (mpower1_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 22 (kernel39_0_contains j i k) (mpower1_22_contains j i k)
noncomputable def ha39_1_22 : Fin 7 → CBox := ![⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨(-625),625⟩,⟨(-625),625⟩⟩,⟨⟨(-33),33⟩,⟨(-33),33⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-8405541083),(-8405541082)⟩,⟨(-49825057471),(-49825057470)⟩⟩,⟨⟨999326837340372069,999326837340372099⟩,⟨667619988667869920,667619988667869950⟩⟩]
lemma ha39_1_22_eq (j : Fin 7) : ha39_1_22 j = ((ha39_1_21 j).mul (piI.mul (atomPoints j).z)).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha39_1_22_contains (j : Fin 7) : (ha39_1_22 j).Contains (fullFactor true 39 22 ((j.val:ℝ)/6)) := by
  rw [ha39_1_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_1_21 j) true 39 21 j (ha39_1_21_contains j)
noncomputable def hk39_1_23 (j : Fin 6) (i k : Fin 16) : CBox := (kernel39_0 j i k).mul (mpower1_23 j i k)
lemma hk39_1_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_1_23 j i k).Contains (fullFactor true 39 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_1_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel39_0 j i k) (mpower1_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 23 (kernel39_0_contains j i k) (mpower1_23_contains j i k)
noncomputable def ha39_1_23 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-310),310⟩,⟨(-310),310⟩⟩,⟨⟨(-15),15⟩,⟨(-15),15⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-8592610652),(-8592610651)⟩,⟨3018746201,3018746202⟩⟩,⟨⟨96658530912096557,96658530912096563⟩,⟨(-162345933703980344),(-162345933703980339)⟩⟩]
lemma ha39_1_23_eq (j : Fin 7) : ha39_1_23 j = ((ha39_1_22 j).mul (piI.mul (atomPoints j).z)).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha39_1_23_contains (j : Fin 7) : (ha39_1_23 j).Contains (fullFactor true 39 23 ((j.val:ℝ)/6)) := by
  rw [ha39_1_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_1_22 j) true 39 22 j (ha39_1_22_contains j)
noncomputable def hk39_1_24 (j : Fin 6) (i k : Fin 16) : CBox := (kernel39_0 j i k).mul (mpower1_24 j i k)
lemma hk39_1_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_1_24 j i k).Contains (fullFactor true 39 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_1_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel39_0 j i k) (mpower1_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 24 (kernel39_0_contains j i k) (mpower1_24_contains j i k)
noncomputable def ha39_1_24 : Fin 7 → CBox := ![⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-148),148⟩,⟨(-148),148⟩⟩,⟨⟨(-7),7⟩,⟨(-7),7⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨766012119,766012120⟩,⟨1374051670,1374051671⟩⟩,⟨⟨(-25182720433757277),(-25182720433757275)⟩,⟨(-13273009645673625),(-13273009645673623)⟩⟩]
lemma ha39_1_24_eq (j : Fin 7) : ha39_1_24 j = ((ha39_1_23 j).mul (piI.mul (atomPoints j).z)).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha39_1_24_contains (j : Fin 7) : (ha39_1_24 j).Contains (fullFactor true 39 24 ((j.val:ℝ)/6)) := by
  rw [ha39_1_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_1_23 j) true 39 23 j (ha39_1_23_contains j)
noncomputable def hk39_1_25 (j : Fin 6) (i k : Fin 16) : CBox := (kernel39_0 j i k).mul (mpower1_25 j i k)
lemma hk39_1_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_1_25 j i k).Contains (fullFactor true 39 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_1_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel39_0 j i k) (mpower1_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 25 (kernel39_0_contains j i k) (mpower1_25_contains j i k)
noncomputable def ha39_1_25 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-68),68⟩,⟨(-68),68⟩⟩,⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨202956065,202956067⟩,⟨(-163885512),(-163885511)⟩⟩,⟨⟨(-1728021582494054),(-1728021582494052)⟩,⟨3737111069930064,3737111069930066⟩⟩]
lemma ha39_1_25_eq (j : Fin 7) : ha39_1_25 j = ((ha39_1_24 j).mul (piI.mul (atomPoints j).z)).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha39_1_25_contains (j : Fin 7) : (ha39_1_25 j).Contains (fullFactor true 39 25 ((j.val:ℝ)/6)) := by
  rw [ha39_1_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_1_24 j) true 39 24 j (ha39_1_24_contains j)
noncomputable def hk39_1_26 (j : Fin 6) (i k : Fin 16) : CBox := (kernel39_0 j i k).mul (mpower1_26 j i k)
lemma hk39_1_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_1_26 j i k).Contains (fullFactor true 39 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_1_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel39_0 j i k) (mpower1_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 26 (kernel39_0_contains j i k) (mpower1_26_contains j i k)
noncomputable def ha39_1_26 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-30),30⟩,⟨(-30),30⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-31248609),(-31248607)⟩,⟨(-27450394),(-27450392)⟩⟩,⟨⟨531510838116684,531510838116685⟩,⟨213007732683243,213007732683244⟩⟩]
lemma ha39_1_26_eq (j : Fin 7) : ha39_1_26 j = ((ha39_1_25 j).mul (piI.mul (atomPoints j).z)).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha39_1_26_contains (j : Fin 7) : (ha39_1_26 j).Contains (fullFactor true 39 26 ((j.val:ℝ)/6)) := by
  rw [ha39_1_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_1_25 j) true 39 25 j (ha39_1_25_contains j)
noncomputable def hk39_1_27 (j : Fin 6) (i k : Fin 16) : CBox := (kernel39_0 j i k).mul (mpower1_27 j i k)
lemma hk39_1_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_1_27 j i k).Contains (fullFactor true 39 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_1_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel39_0 j i k) (mpower1_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 27 (kernel39_0_contains j i k) (mpower1_27_contains j i k)
noncomputable def ha39_1_27 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-13),13⟩,⟨(-13),13⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-3338313),(-3338312)⟩,⟨5444194,5444196⟩⟩,⟨⟨24791588754801,24791588754803⟩,⟨(-72566542690286),(-72566542690285)⟩⟩]
lemma ha39_1_27_eq (j : Fin 7) : ha39_1_27 j = ((ha39_1_26 j).mul (piI.mul (atomPoints j).z)).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha39_1_27_contains (j : Fin 7) : (ha39_1_27 j).Contains (fullFactor true 39 27 ((j.val:ℝ)/6)) := by
  rw [ha39_1_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_1_26 j) true 39 26 j (ha39_1_26_contains j)
noncomputable def hk39_1_28 (j : Fin 6) (i k : Fin 16) : CBox := (kernel39_0 j i k).mul (mpower1_28 j i k)
lemma hk39_1_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_1_28 j i k).Contains (fullFactor true 39 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_1_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel39_0 j i k) (mpower1_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 28 (kernel39_0_contains j i k) (mpower1_28_contains j i k)
noncomputable def ha39_1_28 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-6),6⟩,⟨(-6),6⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨878297,878298⟩,⟨350129,350130⟩⟩,⟨⟨(-9524816962790),(-9524816962789)⟩,⟨(-2710607479371),(-2710607479370)⟩⟩]
lemma ha39_1_28_eq (j : Fin 7) : ha39_1_28 j = ((ha39_1_27 j).mul (piI.mul (atomPoints j).z)).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha39_1_28_contains (j : Fin 7) : (ha39_1_28 j).Contains (fullFactor true 39 28 ((j.val:ℝ)/6)) := by
  rw [ha39_1_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_1_27 j) true 39 27 j (ha39_1_27_contains j)
noncomputable def hk39_1_29 (j : Fin 6) (i k : Fin 16) : CBox := (kernel39_0 j i k).mul (mpower1_29 j i k)
lemma hk39_1_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_1_29 j i k).Contains (fullFactor true 39 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_1_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel39_0 j i k) (mpower1_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 29 (kernel39_0_contains j i k) (mpower1_29_contains j i k)
noncomputable def ha39_1_29 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨27992,27993⟩,⟨(-132232),(-132231)⟩⟩,⟨⟨(-275847150381),(-275847150380)⟩,⟨1203563514600,1203563514601⟩⟩]
lemma ha39_1_29_eq (j : Fin 7) : ha39_1_29 j = ((ha39_1_28 j).mul (piI.mul (atomPoints j).z)).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha39_1_29_contains (j : Fin 7) : (ha39_1_29 j).Contains (fullFactor true 39 29 ((j.val:ℝ)/6)) := by
  rw [ha39_1_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_1_28 j) true 39 28 j (ha39_1_28_contains j)
noncomputable def hk39_1_30 (j : Fin 6) (i k : Fin 16) : CBox := (kernel39_0 j i k).mul (mpower1_30 j i k)
lemma hk39_1_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk39_1_30 j i k).Contains (fullFactor true 39 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk39_1_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel39_0 j i k) (mpower1_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 39 30 (kernel39_0_contains j i k) (mpower1_30_contains j i k)
noncomputable def ha39_1_30 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-18665),(-18663)⟩,⟨(-708),(-707)⟩⟩,⟨⟨146596531165,146596531166⟩,⟨25669802826,25669802827⟩⟩]
lemma ha39_1_30_eq (j : Fin 7) : ha39_1_30 j = ((ha39_1_29 j).mul (piI.mul (atomPoints j).z)).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha39_1_30_contains (j : Fin 7) : (ha39_1_30 j).Contains (fullFactor true 39 30 ((j.val:ℝ)/6)) := by
  rw [ha39_1_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha39_1_29 j) true 39 29 j (ha39_1_29_contains j)
end SharpPlanar.CachedData

end OAI
