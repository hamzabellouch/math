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
noncomputable def hk33_0_0 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_0 j i k)
lemma hk33_0_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_0_0 j i k).Contains (fullFactor false 33 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_0_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power33 j i k) (mpower0_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 0 (power33_contains j i k) (mpower0_0_contains j i k)
noncomputable def ha33_0_0 : Fin 7 → CBox := ![⟨⟨999999999999999999999999999605,1000000000000000000000000000527⟩,⟨(-527),527⟩⟩,⟨⟨(-122942317822),148865101642⟩,⟨(-1000000000000000000135775819551),(-999999999999999999864224180501)⟩⟩,⟨⟨(-1000000000000000000371215853760),(-999999999999999999628784146255)⟩,⟨(-397045029932),345199462115⟩⟩,⟨⟨(-146684449625),68916097931⟩,⟨999999999999999999892199726255,1000000000000000000107800273778⟩⟩,⟨⟨999999999999999998985007789769,1000000000000000001014992210156⟩,⟨(-963215074312),1066906210036⟩⟩,⟨⟨(-1212681522260),1342295441787⟩,⟨(-1000000000000000001277556401719),(-999999999999999998722443598198)⟩⟩,⟨⟨(-1000000000000000000216255526937),(-999999999999999999783744473195)⟩,⟨(-294023878697),138487175045⟩⟩]
lemma ha33_0_0_eq (j : Fin 7) : ha33_0_0 j = ((atomPoints j).direct.powBin 7 33).conj := by fin_cases j <;> decide +kernel
lemma ha33_0_0_contains (j : Fin 7) : (ha33_0_0 j).Contains (fullFactor false 33 0 ((j.val:ℝ)/6)) := by
  rw [ha33_0_0_eq]
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @direct_factor_zero_full ((atomPoints j).direct.powBin 7 33) ((j.val:ℝ)/6) 33 (@direct_power_bin_contains (atomPoints j) ((j.val:ℝ)/6) (atomPoints_contains j) 33 (by norm_num))
noncomputable def hk33_0_1 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_1 j i k)
lemma hk33_0_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_0_1 j i k).Contains (fullFactor false 33 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_0_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power33 j i k) (mpower0_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 1 (power33_contains j i k) (mpower0_1_contains j i k)
noncomputable def ha33_0_1 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨523598775598298873005574613818,523598775598298873149425386208⟩,⟨(-64372447081),77945584950⟩⟩,⟨⟨(-361492031402),415784583060⟩,⟨(-1047197551196597746545402999692),(-1047197551196597745764597000324)⟩⟩,⟨⟨(-1570796326794896619404332274078),(-1570796326794896619060667725973)⟩,⟨(-230411394669),108253153488⟩⟩,⟨⟨(-2234523141013),2017352934191⟩,⟨2094395102393195490180871952588,2094395102393195494439128047253⟩⟩,⟨⟨2617993877991494362038698494625,2617993877991494368736301505159⟩,⟨(-3174792801231),3514121249055⟩⟩,⟨⟨(-435070291738),923703257295⟩,⟨(-3141592653589793239149386774724),(-3141592653589793237780613225691)⟩⟩]
lemma ha33_0_1_eq (j : Fin 7) : ha33_0_1 j = ((ha33_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha33_0_1_contains (j : Fin 7) : (ha33_0_1 j).Contains (fullFactor false 33 1 ((j.val:ℝ)/6)) := by
  rw [ha33_0_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_0_0 j) false 33 0 j (ha33_0_0_contains j)
noncomputable def hk33_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_2 j i k)
lemma hk33_0_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_0_2 j i k).Contains (fullFactor false 33 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_0_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power33 j i k) (mpower0_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 2 (power33_contains j i k) (mpower0_2_contains j i k)
noncomputable def ha33_0_2 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-20406106422),16852667237⟩,⟨137077838904018869687192062598,137077838904018869725288439059⟩⟩,⟨⟨548311355616075478619673806054,548311355616075479030248200558⟩,⟨(-189276785031),217704298603⟩⟩,⟨⟨(-85021827932),180964686199⟩,⟨(-1233700550136169827493082505311),(-1233700550136169827219242009586)⟩⟩,⟨⟨(-2193245422464301917532952348980),(-2193245422464301913066735677265)⟩,⟨(-2339987161361),2112567052585⟩⟩,⟨⟨(-4599973958273),4155794058758⟩,⟨3426945972600471738266981196880,3426945972600471747045031344109⟩⟩,⟨⟨4934802200544679308341762816888,4934802200544679310507535243192⟩,⟨(-683406816160),1450949683608⟩⟩]
lemma ha33_0_2_eq (j : Fin 7) : ha33_0_2 j = ((ha33_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha33_0_2_contains (j : Fin 7) : (ha33_0_2 j).Contains (fullFactor false 33 2 ((j.val:ℝ)/6)) := by
  rw [ha33_0_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_0_1 j) false 33 1 j (ha33_0_1_contains j)
noncomputable def hk33_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_3 j i k)
lemma hk33_0_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_0_3 j i k).Contains (fullFactor false 33 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_0_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power33 j i k) (mpower0_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 3 (power33_contains j i k) (mpower0_3_contains j i k)
noncomputable def ha33_0_3 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-23924596203935046435111140730),(-23924596203935046428385914350)⟩,⟨(-3561537446),2941345311⟩⟩,⟨⟨(-75993136128),66070061928⟩,⟨191396769631480371382024852813,191396769631480371525951587824⟩⟩,⟨⟨645964097506246253584490885653,645964097506246253729929601508⟩,⟨(-44517325005),94752888121⟩⟩,⟨⟨(-1474850029471),1633619216806⟩,⟨(-1531174157051842973193346422416),(-1531174157051842970070465102540)⟩⟩,⟨⟨(-2990574525491880807803472513877),(-2990574525491880800133659370788)⟩,⟨(-4014234553894),3626614468008⟩⟩,⟨⟨(-1519430955584),715661944354⟩,⟨5167712780049970028115461487930,5167712780049970030399902409875⟩⟩]
lemma ha33_0_3_eq (j : Fin 7) : ha33_0_3 j = ((ha33_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha33_0_3_contains (j : Fin 7) : (ha33_0_3 j).Contains (fullFactor false 33 3 ((j.val:ℝ)/6)) := by
  rw [ha33_0_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_0_2 j) false 33 2 j (ha33_0_2_contains j)
noncomputable def hk33_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_4 j i k)
lemma hk33_0_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_0_4 j i k).Contains (fullFactor false 33 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_0_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power33 j i k) (mpower0_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 4 (power33_contains j i k) (mpower0_4_contains j i k)
noncomputable def ha33_0_4 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-385021201),466204162⟩,⟨(-3131722319766024860165205023),(-3131722319766024859274906366)⟩⟩,⟨⟨(-50107557116256397774440605328),(-50107557116256397736601176905)⟩,⟨(-19894956516),17297101765⟩⟩,⟨⟨(-37209372154),17481912650⟩,⟨253669507901048013608363958636,253669507901048013666285063919⟩⟩,⟨⟨801720913860102363269489861642,801720913860102364907178653999⟩,⟨(-772229669623),855361021714⟩⟩,⟨⟨(-2373613618771),2627310371730⟩,⟨(-1957326449853765539838090472671),(-1957326449853765534811979145586)⟩⟩,⟨⟨(-4058712126416768219100749673860),(-4058712126416768217293634687423)⟩,⟨(-1193358281925),562079576710⟩⟩]
lemma ha33_0_4_eq (j : Fin 7) : ha33_0_4 j = ((ha33_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha33_0_4_contains (j : Fin 7) : (ha33_0_4 j).Contains (fullFactor false 33 4 ((j.val:ℝ)/6)) := by
  rw [ha33_0_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_0_3 j) false 33 3 j (ha33_0_3_contains j)
noncomputable def hk33_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_5 j i k)
lemma hk33_0_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_0_5 j i k).Contains (fullFactor false 33 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_0_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power33 j i k) (mpower0_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 5 (power33_contains j i k) (mpower0_5_contains j i k)
noncomputable def ha33_0_5 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨327953194428670967528189073,327953194428670967622464839⟩,⟨(-40319326),48820786⟩⟩,⟨⟨(-3622696523),4166789949⟩,⟨(-10494502221717470966389700801),(-10494502221717470958431224405)⟩⟩,⟨⟨(-79692626246167045130029511090),(-79692626246167045111579389697)⟩,⟨(-11689669021),5492104836⟩⟩,⟨⟨(-358292786932),323470807597⟩,⟨335824071094959070453603584081,335824071094959071140666022492⟩⟩,⟨⟨1024853732589596772355432764726,1024853732589596774990360712361⟩,⟨(-1242821184532),1375656493755⟩⟩,⟨⟨(-353165013785),749809122320⟩,⟨(-2550164039877345444437523041410),(-2550164039877345443293961784039)⟩⟩]
lemma ha33_0_5_eq (j : Fin 7) : ha33_0_5 j = ((ha33_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha33_0_5_contains (j : Fin 7) : (ha33_0_5 j).Contains (fullFactor false 33 5 ((j.val:ℝ)/6)) := by
  rw [ha33_0_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_0_4 j) false 33 4 j (ha33_0_4_contains j)
noncomputable def hk33_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_6 j i k)
lemma hk33_0_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_0_6 j i k).Contains (fullFactor false 33 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_0_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power33 j i k) (mpower0_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 6 (power33_contains j i k) (mpower0_6_contains j i k)
noncomputable def ha33_0_6 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-4260418),3518525⟩,⟨28619315176067161687398562,28619315176067161695716773⟩⟩,⟨⟨1831636171268298347562267507,1831636171268298348957113953⟩,⟨(-632279822),727242039⟩⟩,⟨⟨(-1437829684),3060348194⟩,⟨(-20863480763352960875593860224),(-20863480763352960870697219216)⟩⟩,⟨⟨(-117224714961171094408721792806),(-117224714961171094168518620607)⟩,⟨(-125067776363),112912612534⟩⟩,⟨⟨(-600243379812),542283042091⟩,⟨447176799626049400855024750106,447176799626049402006152364046⟩⟩,⟨⟨1335262768854589495579805768364,1335262768854589496182823315946⟩,⟨(-184916768802),392599138380⟩⟩]
lemma ha33_0_6_eq (j : Fin 7) : ha33_0_6 j = ((ha33_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha33_0_6_contains (j : Fin 7) : (ha33_0_6 j).Contains (fullFactor false 33 6 ((j.val:ℝ)/6)) := by
  rw [ha33_0_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_0_5 j) false 33 5 j (ha33_0_5_contains j)
noncomputable def hk33_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_7 j i k)
lemma hk33_0_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_0_7 j i k).Contains (fullFactor false 33 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_0_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power33 j i k) (mpower0_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 7 (power33_contains j i k) (mpower0_7_contains j i k)
noncomputable def ha33_0_7 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-2140719769235797028531265),(-2140719769235797027902249)⟩,⟨(-318679),263186⟩⟩,⟨⟨(-108795155),94588841⟩,⟨274012130462182019506974521,274012130462182019716515270⟩⟩,⟨⟨4681754135318688100153194468,4681754135318688101266900628⟩,⟨(-322648227),686740529⟩⟩,⟨⟨(-33783374670),37420191184⟩,⟨(-35073552699159298546293478427),(-35073552699159298474313214778)⟩⟩,⟨⟨(-167243731971546643044960677318),(-167243731971546642613907603115)⟩,⟨(-224490499094),202813383477⟩⟩,⟨⟨(-176198081278),82990451771⟩,⟨599264529320792076754615505784,599264529320792077027156666522⟩⟩]
lemma ha33_0_7_eq (j : Fin 7) : ha33_0_7 j = ((ha33_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha33_0_7_contains (j : Fin 7) : (ha33_0_7 j).Contains (fullFactor false 33 7 ((j.val:ℝ)/6)) := by
  rw [ha33_0_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_0_6 j) false 33 6 j (ha33_0_6_contains j)
noncomputable def hk33_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_8 j i k)
lemma hk33_0_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_0_8 j i k).Contains (fullFactor false 33 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_0_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power33 j i k) (mpower0_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 8 (power33_contains j i k) (mpower0_8_contains j i k)
noncomputable def ha33_0_8 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-17226),20858⟩,⟨(-140109781258867029474738),(-140109781258867029433122)⟩⟩,⟨⟨(-35868104002269959553977500),(-35868104002269959526434507)⟩,⟨(-14241253),12381651⟩⟩,⟨⟨(-134841188),63351832⟩,⟨919260274839426580136431877,919260274839426580358033667⟩⟩,⟨⟨9182234624581109632855928461,9182234624581109651729545379⟩,⟨(-8844466807),9796583144⟩⟩,⟨⟨(-66370524540),73464344037⟩,⟨(-54730383304244933451059290108),(-54730383304244933309823289217)⟩⟩,⟨⟨(-235330630358893204597179461706),(-235330630358893204489403717496)⟩,⟨(-69192824715),32590274201⟩⟩]
lemma ha33_0_8_eq (j : Fin 7) : ha33_0_8 j = ((ha33_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha33_0_8_contains (j : Fin 7) : (ha33_0_8 j).Contains (fullFactor false 33 8 ((j.val:ℝ)/6)) := by
  rw [ha33_0_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_0_7 j) false 33 7 j (ha33_0_7_contains j)
noncomputable def hk33_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_9 j i k)
lemma hk33_0_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_0_9 j i k).Contains (fullFactor false 33 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_0_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power33 j i k) (mpower0_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 9 (power33_contains j i k) (mpower0_9_contains j i k)
noncomputable def ha33_0_9 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨8151256657387584303696,8151256657387584306144⟩,⟨(-1003),1214⟩⟩,⟨⟨(-1440671),1657046⟩,⟨(-4173443408582443165728165),(-4173443408582443162510107)⟩⟩,⟨⟨(-160441184787359821893337797),(-160441184787359821854150287)⟩,⟨(-23534227),11056981⟩⟩,⟨⟨(-2279768418),2058200885⟩,⟨2136803025194210897829551646,2136803025194210902228443396⟩⟩,⟨⟨15920423158960125574979958593,15920423158960125616114522174⟩,⟨(-19306402992),21369911438⟩⟩,⟨⟨(-11376151779),24152852201⟩,⟨(-82145886611128228818298104770),(-82145886611128228780415794485)⟩⟩]
lemma ha33_0_9_eq (j : Fin 7) : ha33_0_9 j = ((ha33_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha33_0_9_contains (j : Fin 7) : (ha33_0_9 j).Contains (fullFactor false 33 9 ((j.val:ℝ)/6)) := by
  rw [ha33_0_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_0_8 j) false 33 8 j (ha33_0_8_contains j)
noncomputable def hk33_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_10 j i k)
lemma hk33_0_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_0_10 j i k).Contains (fullFactor false 33 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_0_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power33 j i k) (mpower0_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 10 (power33_contains j i k) (mpower0_10_contains j i k)
noncomputable def ha33_0_10 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-64),53⟩,⟨426798800539562151389,426798800539562151520⟩⟩,⟨⟨437041971752511642920307,437041971752511643258693⟩,⟨(-150867),173526⟩⟩,⟨⟨(-1736827),3696748⟩,⟨(-25202042373060605484359962),(-25202042373060605478124180)⟩⟩,⟨⟨(-447530979074571922985011050),(-447530979074571922062284780)⟩,⟨(-477473581),431068586⟩⟩,⟨⟨(-5594629732),5054404484⟩,⟨4167957036519161629907592863,4167957036519161640689863447⟩⟩,⟨⟨25806891390014060006800268296,25806891390014060018783492953⟩,⟨(-3573923486),7587842304⟩⟩]
lemma ha33_0_10_eq (j : Fin 7) : ha33_0_10 j = ((ha33_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha33_0_10_contains (j : Fin 7) : (ha33_0_10 j).Contains (fullFactor false 33 10 ((j.val:ℝ)/6)) := by
  rw [ha33_0_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_0_9 j) false 33 9 j (ha33_0_9_contains j)
noncomputable def hk33_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_11 j i k)
lemma hk33_0_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_0_11 j i k).Contains (fullFactor false 33 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_0_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power33 j i k) (mpower0_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 11 (power33_contains j i k) (mpower0_11_contains j i k)
noncomputable def ha33_0_11 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-20315575399030665725),(-20315575399030665717)⟩,⟨(-4),3⟩⟩,⟨⟨(-16520),14363⟩,⟨41606298417214803380553,41606298417214803412900⟩⟩,⟨⟨3598843235212085340037274,3598843235212085340939198⟩,⟨(-248019),527895⟩⟩,⟨⟨(-82075267),90910758⟩,⟨(-85209699158455917444474796),(-85209699158455917268516893)⟩⟩,⟨⟨(-991971455030794225945694035),(-991971455030794223376362093)⟩,⟨(-1331518763),1202945455⟩⟩,⟨⟨(-2167082695),1020710161⟩,⟨7370430945714350775596976024,7370430945714350779042837795⟩⟩]
lemma ha33_0_11_eq (j : Fin 7) : ha33_0_11 j = ((ha33_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha33_0_11_contains (j : Fin 7) : (ha33_0_11 j).Contains (fullFactor false 33 11 ((j.val:ℝ)/6)) := by
  rw [ha33_0_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_0_10 j) false 33 10 j (ha33_0_10_contains j)
noncomputable def hk33_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_12 j i k)
lemma hk33_0_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_0_12 j i k).Contains (fullFactor false 33 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_0_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power33 j i k) (mpower0_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 12 (power33_contains j i k) (mpower0_12_contains j i k)
noncomputable def ha33_0_12 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-886434200375614886),(-886434200375614885)⟩⟩,⟨⟨(-3630834484738518572474),(-3630834484738518569639)⟩,⟨(-1442),1254⟩⟩,⟨⟨(-69102),32466⟩,⟨471087477881817150311487,471087477881817150431049⟩⟩,⟨⟨14871898049488972051667586,14871898049488972082425373⟩,⟨(-14324837),15866921⟩⟩,⟨⟨(-262441987),290492331⟩,⟨(-216414599701077853188765588),(-216414599701077852627535443)⟩⟩,⟨⟨(-1929574309403923048374848109),(-1929574309403923047466581580)⟩,⟨(-567340923),267221296⟩⟩]
lemma ha33_0_12_eq (j : Fin 7) : ha33_0_12 j = ((ha33_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha33_0_12_contains (j : Fin 7) : (ha33_0_12 j).Contains (fullFactor false 33 12 ((j.val:ℝ)/6)) := by
  rw [ha33_0_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_0_11 j) false 33 11 j (ha33_0_11_contains j)
noncomputable def hk33_0_13 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_13 j i k)
lemma hk33_0_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_0_13 j i k).Contains (fullFactor false 33 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_0_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power33 j i k) (mpower0_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 13 (power33_contains j i k) (mpower0_13_contains j i k)
noncomputable def ha33_0_13 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨35702758612702236,35702758612702237⟩,⟨(-1),1⟩⟩,⟨⟨(-102),117⟩,⟨(-292476998555256723141),(-292476998555256722911)⟩⟩,⟨⟨(-56921729219679268125622),(-56921729219679268110993)⟩,⟨(-8350),3923⟩⟩,⟨⟨(-2556278),2307837⟩,⟨2395971572164663072548527,2395971572164663077511459⟩⟩,⟨⟨43582469009646284974577265,43582469009646285087738846⟩,⟨(-52851656),58500550⟩⟩,⟨⟨(-64576959),137104160⟩,⟨(-466302805767612564535664613),(-466302805767612564314687750)⟩⟩]
lemma ha33_0_13_eq (j : Fin 7) : ha33_0_13 j = ((ha33_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha33_0_13_contains (j : Fin 7) : (ha33_0_13 j).Contains (fullFactor false 33 13 ((j.val:ℝ)/6)) := by
  rw [ha33_0_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_0_12 j) false 33 12 j (ha33_0_12_contains j)
noncomputable def hk33_0_14 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_14 j i k)
lemma hk33_0_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_0_14 j i k).Contains (fullFactor false 33 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_0_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power33 j i k) (mpower0_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 14 (power33_contains j i k) (mpower0_14_contains j i k)
noncomputable def ha33_0_14 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨1335280049649465,1335280049649466⟩⟩,⟨⟨21877228333456835509,21877228333456835527⟩,⟨(-8),9⟩⟩,⟨⟨(-441),937⟩,⟨(-6386603083791852241988),(-6386603083791852240326)⟩⟩,⟨⟨(-358436509015356793493306),(-358436509015356792749712)⟩,⟨(-382419),345252⟩⟩,⟨⟨(-10939578),9883237⟩,⟨8149902646786285746557029,8149902646786285767744138⟩⟩,⟨⟨104638104924845707094155542,104638104924845707144075709⟩,⟨(-14491036),30766102⟩⟩]
lemma ha33_0_14_eq (j : Fin 7) : ha33_0_14 j = ((ha33_0_13 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha33_0_14_contains (j : Fin 7) : (ha33_0_14 j).Contains (fullFactor false 33 14 ((j.val:ℝ)/6)) := by
  rw [ha33_0_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_0_13 j) false 33 13 j (ha33_0_13_contains j)
noncomputable def hk33_0_15 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_15 j i k)
lemma hk33_0_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_0_15 j i k).Contains (fullFactor false 33 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_0_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power33 j i k) (mpower0_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 15 (power33_contains j i k) (mpower0_15_contains j i k)
noncomputable def ha33_0_15 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-46610066605154),(-46610066605153)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨1527318662517654886,1527318662517654888⟩⟩,⟨⟨668803510981146723167,668803510981146723344⟩,⟨(-47),99⟩⟩,⟨⟨(-48207),53396⟩,⟨(-50047177933378515380012),(-50047177933378515276026)⟩⟩,⟨⟨(-1422426349034211494687043),(-1422426349034211490984666)⟩,⟨(-1909317),1724951⟩⟩,⟨⟨(-6443638),3034996⟩,⟨21915353447830215822368736,21915353447830215832893752⟩⟩]
lemma ha33_0_15_eq (j : Fin 7) : ha33_0_15 j = ((ha33_0_14 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha33_0_15_contains (j : Fin 7) : (ha33_0_15 j).Contains (fullFactor false 33 15 ((j.val:ℝ)/6)) := by
  rw [ha33_0_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_0_14 j) false 33 14 j (ha33_0_14_contains j)
noncomputable def hk33_0_16 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_16 j i k)
lemma hk33_0_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_0_16 j i k).Contains (fullFactor false 33 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_0_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power33 j i k) (mpower0_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 16 (power33_contains j i k) (mpower0_16_contains j i k)
noncomputable def ha33_0_16 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-1525310862814),(-1525310862813)⟩⟩,⟨⟨(-99962772705334444),(-99962772705334443)⟩,⟨(-1),1⟩⟩,⟨⟨(-10),5⟩,⟨65659631149794723614,65659631149794723632⟩⟩,⟨⟨6551160272016798092013,6551160272016798105647⟩,⟨(-6311),6990⟩⟩,⟨⟨(-282245),312412⟩,⟨(-232743967104084891679110),(-232743967104084891072568)⟩⟩,⟨⟨(-4303069587032947008389610),(-4303069587032947006309330)⟩,⟨(-1265206),595921⟩⟩]
lemma ha33_0_16_eq (j : Fin 7) : ha33_0_16 j = ((ha33_0_15 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha33_0_16_contains (j : Fin 7) : (ha33_0_16 j).Contains (fullFactor false 33 16 ((j.val:ℝ)/6)) := by
  rw [ha33_0_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_0_15 j) false 33 15 j (ha33_0_15_contains j)
noncomputable def hk33_0_17 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_17 j i k)
lemma hk33_0_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_0_17 j i k).Contains (fullFactor false 33 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_0_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power33 j i k) (mpower0_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 17 (power33_contains j i k) (mpower0_17_contains j i k)
noncomputable def ha33_0_17 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨46979464716,46979464717⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-6157692399285196),(-6157692399285195)⟩⟩,⟨⟨(-6066935731106195669),(-6066935731106195666)⟩,⟨(-1),1⟩⟩,⟨⟨(-862),778⟩,⟨807101058159109192586,807101058159109194269⟩⟩,⟨⟨35842487118702823439815,35842487118702823533337⟩,⟨(-43466),48112⟩⟩,⟨⟨(-110126),233810⟩,⟨(-795205400147551278681945),(-795205400147551278294978)⟩⟩]
lemma ha33_0_17_eq (j : Fin 7) : ha33_0_17 j = ((ha33_0_16 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha33_0_17_contains (j : Fin 7) : (ha33_0_17 j).Contains (fullFactor false 33 17 ((j.val:ℝ)/6)) := by
  rw [ha33_0_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_0_16 j) false 33 16 j (ha33_0_16_contains j)
noncomputable def hk33_0_18 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_18 j i k)
lemma hk33_0_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_0_18 j i k).Contains (fullFactor false 33 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_0_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power33 j i k) (mpower0_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 18 (power33_contains j i k) (mpower0_18_contains j i k)
noncomputable def ha33_0_18 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨1366577233,1366577234⟩⟩,⟨⟨358240022308519,358240022308520⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-529440020073462377),(-529440020073462376)⟩⟩,⟨⟨(-93910472408044662838),(-93910472408044662641)⟩,⟨(-101),91⟩⟩,⟨⟨(-6998),6322⟩,⟨5213078436041832664864,5213078436041832678484⟩⟩,⟨⟨138789524622137721112564,138789524622137721180546⟩,⟨(-19221),40808⟩⟩]
lemma ha33_0_18_eq (j : Fin 7) : ha33_0_18 j = ((ha33_0_17 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha33_0_18_contains (j : Fin 7) : (ha33_0_18 j).Contains (fullFactor false 33 18 ((j.val:ℝ)/6)) := by
  rw [ha33_0_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_0_17 j) false 33 17 j (ha33_0_17_contains j)
noncomputable def hk33_0_19 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_19 j i k)
lemma hk33_0_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_0_19 j i k).Contains (fullFactor false 33 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_0_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power33 j i k) (mpower0_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 19 (power33_contains j i k) (mpower0_19_contains j i k)
noncomputable def ha33_0_19 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-37659904),(-37659903)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨19744635479057,19744635479058⟩⟩,⟨⟨43770654673137422,43770654673137423⟩,⟨(-1),1⟩⟩,⟨⟨(-11),12⟩,⟨(-10351875446044213773),(-10351875446044213750)⟩⟩,⟨⟨(-718305654265631155990),(-718305654265631154111)⟩,⟨(-965),872⟩⟩,⟨⟨(-6748),3179⟩,⟨22948428997269873104874,22948428997269873116188⟩⟩]
lemma ha33_0_19_eq (j : Fin 7) : ha33_0_19 j = ((ha33_0_18 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha33_0_19_contains (j : Fin 7) : (ha33_0_19 j).Contains (fullFactor false 33 19 ((j.val:ℝ)/6)) := by
  rw [ha33_0_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_0_18 j) false 33 18 j (ha33_0_18_contains j)
noncomputable def hk33_0_20 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_20 j i k)
lemma hk33_0_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_0_20 j i k).Contains (fullFactor false 33 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_0_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power33 j i k) (mpower0_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 20 (power33_contains j i k) (mpower0_20_contains j i k)
noncomputable def ha33_0_20 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-985934),(-985933)⟩⟩,⟨⟨(-1033826696147),(-1033826696146)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨3437739179098606,3437739179098608⟩⟩,⟨⟨1084045861738968865,1084045861738968869⟩,⟨(-2),2⟩⟩,⟨⟨(-115),127⟩,⟨(-94025990269704865338),(-94025990269704865091)⟩⟩,⟨⟨(-3604730797462500934808),(-3604730797462500933019)⟩,⟨(-1060),500⟩⟩]
lemma ha33_0_20_eq (j : Fin 7) : ha33_0_20 j = ((ha33_0_19 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha33_0_20_contains (j : Fin 7) : (ha33_0_20 j).Contains (fullFactor false 33 20 ((j.val:ℝ)/6)) := by
  rw [ha33_0_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_0_19 j) false 33 19 j (ha33_0_19_contains j)
noncomputable def hk33_0_21 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_21 j i k)
lemma hk33_0_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_0_21 j i k).Contains (fullFactor false 33 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_0_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power33 j i k) (mpower0_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 21 (power33_contains j i k) (mpower0_21_contains j i k)
noncomputable def ha33_0_21 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨24582,24583⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-51553370694),(-51553370693)⟩⟩,⟨⟨(-257142289286048),(-257142289286047)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨108115254456938454,108115254456938455⟩⟩,⟨⟨11721879376103578807,11721879376103578839⟩,⟨(-15),16⟩⟩,⟨⟨(-75),159⟩,⟨(-539266466260812849079),(-539266466260812848809)⟩⟩]
lemma ha33_0_21_eq (j : Fin 7) : ha33_0_21 j = ((ha33_0_20 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha33_0_21_contains (j : Fin 7) : (ha33_0_21 j).Contains (fullFactor false 33 21 ((j.val:ℝ)/6)) := by
  rw [ha33_0_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_0_20 j) false 33 20 j (ha33_0_20_contains j)
noncomputable def hk33_0_22 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_22 j i k)
lemma hk33_0_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_0_22 j i k).Contains (fullFactor false 33 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_0_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power33 j i k) (mpower0_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 22 (power33_contains j i k) (mpower0_22_contains j i k)
noncomputable def ha33_0_22 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨585,586⟩⟩,⟨⟨2453934706,2453934707⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-18359916521553),(-18359916521552)⟩⟩,⟨⟨(-10292548155845728),(-10292548155845727)⟩,⟨(-1),1⟩⟩,⟨⟨(-2),2⟩,⟨1394900383872451217,1394900383872451222⟩⟩,⟨⟨77007071306013533779,77007071306013533819⟩,⟨(-11),23⟩⟩]
lemma ha33_0_22_eq (j : Fin 7) : ha33_0_22 j = ((ha33_0_21 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha33_0_22_contains (j : Fin 7) : (ha33_0_22 j).Contains (fullFactor false 33 22 ((j.val:ℝ)/6)) := by
  rw [ha33_0_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_0_21 j) false 33 21 j (ha33_0_21_contains j)
noncomputable def hk33_0_23 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_23 j i k)
lemma hk33_0_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_0_23 j i k).Contains (fullFactor false 33 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_0_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power33 j i k) (mpower0_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 23 (power33_contains j i k) (mpower0_23_contains j i k)
noncomputable def ha33_0_23 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-14),(-13)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨111728452,111728453⟩⟩,⟨⟨1253899540535,1253899540536⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-937246193423888),(-937246193423887)⟩⟩,⟨⟨(-158775681103741858),(-158775681103741856)⟩,⟨(-1),1⟩⟩,⟨⟨(-4),2⟩,⟨10518471716932064452,10518471716932064459⟩⟩]
lemma ha33_0_23_eq (j : Fin 7) : ha33_0_23 j = ((ha33_0_22 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha33_0_23_contains (j : Fin 7) : (ha33_0_23 j).Contains (fullFactor false 33 23 ((j.val:ℝ)/6)) := by
  rw [ha33_0_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_0_22 j) false 33 22 j (ha33_0_22_contains j)
noncomputable def hk33_0_24 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_24 j i k)
lemma hk33_0_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_0_24 j i k).Contains (fullFactor false 33 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_0_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power33 j i k) (mpower0_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 24 (power33_contains j i k) (mpower0_24_contains j i k)
noncomputable def ha33_0_24 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-1),0⟩⟩,⟨⟨(-4875074),(-4875073)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨82067533018,82067533019⟩⟩,⟨⟨81790159885152,81790159885153⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-17319740045980250),(-17319740045980248)⟩⟩,⟨⟨(-1376864728037741371),(-1376864728037741370)⟩,⟨(-1),1⟩⟩]
lemma ha33_0_24_eq (j : Fin 7) : ha33_0_24 j = ((ha33_0_23 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha33_0_24_contains (j : Fin 7) : (ha33_0_24 j).Contains (fullFactor false 33 24 ((j.val:ℝ)/6)) := by
  rw [ha33_0_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_0_23 j) false 33 23 j (ha33_0_23_contains j)
noncomputable def hk33_0_25 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_25 j i k)
lemma hk33_0_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_0_25 j i k).Contains (fullFactor false 33 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_0_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power33 j i k) (mpower0_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 25 (power33_contains j i k) (mpower0_25_contains j i k)
noncomputable def ha33_0_25 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-204207),(-204206)⟩⟩,⟨⟨(-5156455177),(-5156455176)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨6852036411496,6852036411497⟩⟩,⟨⟨1813718936351216,1813718936351217⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-173021924583611077),(-173021924583611076)⟩⟩]
lemma ha33_0_25_eq (j : Fin 7) : ha33_0_25 j = ((ha33_0_24 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha33_0_25_contains (j : Fin 7) : (ha33_0_25 j).Contains (fullFactor false 33 25 ((j.val:ℝ)/6)) := by
  rw [ha33_0_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_0_24 j) false 33 24 j (ha33_0_24_contains j)
noncomputable def hk33_0_26 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_26 j i k)
lemma hk33_0_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_0_26 j i k).Contains (fullFactor false 33 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_0_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power33 j i k) (mpower0_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 26 (power33_contains j i k) (mpower0_26_contains j i k)
noncomputable def ha33_0_26 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨0,1⟩⟩,⟨⟨8224,8225⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-311528495),(-311528494)⟩⟩,⟨⟨(-551956596218),(-551956596217)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨182627118144797,182627118144798⟩⟩,⟨⟨20906323353147684,20906323353147685⟩,⟨(-1),1⟩⟩]
lemma ha33_0_26_eq (j : Fin 7) : ha33_0_26 j = ((ha33_0_25 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha33_0_26_contains (j : Fin 7) : (ha33_0_26 j).Contains (fullFactor false 33 26 ((j.val:ℝ)/6)) := by
  rw [ha33_0_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_0_25 j) false 33 25 j (ha33_0_25_contains j)
noncomputable def hk33_0_27 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_27 j i k)
lemma hk33_0_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_0_27 j i k).Contains (fullFactor false 33 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_0_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power33 j i k) (mpower0_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 27 (power33_contains j i k) (mpower0_27_contains j i k)
noncomputable def ha33_0_27 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨318,320⟩⟩,⟨⟨18123993,18123994⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-42815377477),(-42815377475)⟩⟩,⟨⟨(-17708025083642),(-17708025083641)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨2432561179993388,2432561179993389⟩⟩]
lemma ha33_0_27_eq (j : Fin 7) : ha33_0_27 j = ((ha33_0_26 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha33_0_27_contains (j : Fin 7) : (ha33_0_27 j).Contains (fullFactor false 33 27 ((j.val:ℝ)/6)) := by
  rw [ha33_0_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_0_26 j) false 33 26 j (ha33_0_26_contains j)
noncomputable def hk33_0_28 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_28 j i k)
lemma hk33_0_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_0_28 j i k).Contains (fullFactor false 33 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_0_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power33 j i k) (mpower0_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 28 (power33_contains j i k) (mpower0_28_contains j i k)
noncomputable def ha33_0_28 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-1),0⟩⟩,⟨⟨(-12),(-11)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨1016753,1016754⟩⟩,⟨⟨3202582746,3202582747⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1655696473582),(-1655696473581)⟩⟩,⟨⟨(-272932726159820),(-272932726159819)⟩,⟨(-1),1⟩⟩]
lemma ha33_0_28_eq (j : Fin 7) : ha33_0_28 j = ((ha33_0_27 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha33_0_28_contains (j : Fin 7) : (ha33_0_28 j).Contains (fullFactor false 33 28 ((j.val:ℝ)/6)) := by
  rw [ha33_0_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_0_27 j) false 33 27 j (ha33_0_27_contains j)
noncomputable def hk33_0_29 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_29 j i k)
lemma hk33_0_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_0_29 j i k).Contains (fullFactor false 33 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_0_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power33 j i k) (mpower0_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 29 (power33_contains j i k) (mpower0_29_contains j i k)
noncomputable def ha33_0_29 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),0⟩⟩,⟨⟨(-55073),(-55072)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨231292193,231292194⟩⟩,⟨⟨149469076953,149469076954⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-29567015428550),(-29567015428549)⟩⟩]
lemma ha33_0_29_eq (j : Fin 7) : ha33_0_29 j = ((ha33_0_28 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha33_0_29_contains (j : Fin 7) : (ha33_0_29 j).Contains (fullFactor false 33 29 ((j.val:ℝ)/6)) := by
  rw [ha33_0_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_0_28 j) false 33 28 j (ha33_0_28_contains j)
noncomputable def hk33_0_30 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_30 j i k)
lemma hk33_0_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_0_30 j i k).Contains (fullFactor false 33 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_0_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power33 j i k) (mpower0_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 30 (power33_contains j i k) (mpower0_30_contains j i k)
noncomputable def ha33_0_30 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨0,1⟩⟩,⟨⟨0,1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-2884),(-2883)⟩⟩,⟨⟨(-16147242),(-16147241)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨13043637613,13043637614⟩⟩,⟨⟨3096250615296,3096250615297⟩,⟨(-1),1⟩⟩]
lemma ha33_0_30_eq (j : Fin 7) : ha33_0_30 j = ((ha33_0_29 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha33_0_30_contains (j : Fin 7) : (ha33_0_30 j).Contains (fullFactor false 33 30 ((j.val:ℝ)/6)) := by
  rw [ha33_0_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_0_29 j) false 33 29 j (ha33_0_29_contains j)
noncomputable def hk33_1_0 (j : Fin 6) (i k : Fin 16) : CBox := (kernel33_0 j i k).mul (mpower1_0 j i k)
lemma hk33_1_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_1_0 j i k).Contains (fullFactor true 33 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_1_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel33_0 j i k) (mpower1_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 0 (kernel33_0_contains j i k) (mpower1_0_contains j i k)
noncomputable def ha33_1_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),3⟩,⟨(-2),4⟩⟩,⟨⟨(-2),4⟩,⟨(-4),2⟩⟩,⟨⟨(-2),2⟩,⟨0,3⟩⟩,⟨⟨229435537,229435540⟩,⟨(-168277587),(-168277584)⟩⟩,⟨⟨(-17402041971918504781),(-17402041971918504071)⟩,⟨(-99113638007083976860),(-99113638007083976149)⟩⟩,⟨⟨356134034453168626612634853,356134034453168633806136668⟩,⟨2154120630586429646770321740,2154120630586429653996527604⟩⟩]
lemma ha33_1_0_eq (j : Fin 7) : ha33_1_0 j = atomKernel33_0 j := by fin_cases j <;> decide +kernel
lemma ha33_1_0_contains (j : Fin 7) : (ha33_1_0 j).Contains (fullFactor true 33 0 ((j.val:ℝ)/6)) := by
  rw [ha33_1_0_eq]
  simpa only [fullFactor,ite_true] using atomKernel33_0_contains j
noncomputable def hk33_1_1 (j : Fin 6) (i k : Fin 16) : CBox := (kernel33_0 j i k).mul (mpower1_1 j i k)
lemma hk33_1_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_1_1 j i k).Contains (fullFactor true 33 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_1_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel33_0 j i k) (mpower1_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 1 (kernel33_0_contains j i k) (mpower1_1_contains j i k)
noncomputable def ha33_1_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-31),46⟩,⟨(-42),31⟩⟩,⟨⟨(-41),21⟩,⟨(-31),30⟩⟩,⟨⟨(-6),21⟩,⟨(-19),11⟩⟩,⟨⟨(-1125117261),(-1125117242)⟩,⟨(-804989193),(-804989174)⟩⟩,⟨⟨(-392652206894016658349),(-392652206894016654942)⟩,⟨140898727616430839872,140898727616430843274⟩⟩,⟨⟨7711713205226792022808918861,7711713205226792050278657229⟩,⟨(-1690495727387573553837620386),(-1690495727387573526499428095)⟩⟩]
lemma ha33_1_1_eq (j : Fin 7) : ha33_1_1 j = ((ha33_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha33_1_1_contains (j : Fin 7) : (ha33_1_1 j).Contains (fullFactor true 33 1 ((j.val:ℝ)/6)) := by
  rw [ha33_1_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_1_0 j) true 33 0 j (ha33_1_0_contains j)
noncomputable def hk33_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel33_0 j i k).mul (mpower1_2 j i k)
lemma hk33_1_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_1_2 j i k).Contains (fullFactor true 33 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_1_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel33_0 j i k) (mpower1_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 2 (kernel33_0_contains j i k) (mpower1_2_contains j i k)
noncomputable def ha33_1_2 : Fin 7 → CBox := ![⟨⟨(-130),130⟩,⟨(-130),130⟩⟩,⟨⟨(-255),177⟩,⟨(-205),219⟩⟩,⟨⟨(-132),179⟩,⟨(-128),182⟩⟩,⟨⟨(-79),37⟩,⟨(-70),43⟩⟩,⟨⟨(-1007043850),(-1007043790)⟩,⟨3208937522,3208937581⟩⟩,⟨⟨426079970437935490372,426079970437935498523⟩,⟨752432410875996504339,752432410875996512500⟩⟩,⟨⟨(-3776239171722179916779642263),(-3776239171722179864829117560)⟩,⟨(-13764883566845648964671531965),(-13764883566845648912463044277)⟩⟩]
lemma ha33_1_2_eq (j : Fin 7) : ha33_1_2 j = ((ha33_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha33_1_2_contains (j : Fin 7) : (ha33_1_2 j).Contains (fullFactor true 33 2 ((j.val:ℝ)/6)) := by
  rw [ha33_1_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_1_1 j) true 33 1 j (ha33_1_1_contains j)
noncomputable def hk33_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel33_0 j i k).mul (mpower1_3 j i k)
lemma hk33_1_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_1_3 j i k).Contains (fullFactor true 33 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_1_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel33_0 j i k) (mpower1_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 3 (kernel33_0_contains j i k) (mpower1_3_contains j i k)
noncomputable def ha33_1_3 : Fin 7 → CBox := ![⟨⟨(-400),400⟩,⟨(-400),400⟩⟩,⟨⟨(-707),924⟩,⟨(-779),840⟩⟩,⟨⟨(-514),530⟩,⟨(-606),437⟩⟩,⟨⟨(-155),148⟩,⟨(-104),201⟩⟩,⟨⟨5450428997,5450429119⟩,⟨(-70050951),(-70050828)⟩⟩,⟨⟨924606292671925802738,924606292671925815769⟩,⟨(-756868250770792996471),(-756868250770792983452)⟩⟩,⟨⟨(-16332091961163593608827930229),(-16332091961163593542680727941)⟩,⟨5406925443991841488324205765,5406925443991841554140769965⟩⟩]
lemma ha33_1_3_eq (j : Fin 7) : ha33_1_3 j = ((ha33_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha33_1_3_contains (j : Fin 7) : (ha33_1_3 j).Contains (fullFactor true 33 3 ((j.val:ℝ)/6)) := by
  rw [ha33_1_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_1_2 j) true 33 2 j (ha33_1_2_contains j)
noncomputable def hk33_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel33_0 j i k).mul (mpower1_4 j i k)
lemma hk33_1_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_1_4 j i k).Contains (fullFactor true 33 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_1_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel33_0 j i k) (mpower1_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 4 (kernel33_0_contains j i k) (mpower1_4_contains j i k)
noncomputable def ha33_1_4 : Fin 7 → CBox := ![⟨⟨(-922),922⟩,⟨(-922),922⟩⟩,⟨⟨(-2495),2136⟩,⟨(-2469),2151⟩⟩,⟨⟨(-1433),1196⟩,⟨(-1221),1408⟩⟩,⟨⟨(-238),367⟩,⟨(-332),272⟩⟩,⟨⟨(-2145744399),(-2145744209)⟩,⟨(-6268692918),(-6268692730)⟩⟩,⟨⟨(-935808933931438190033),(-935808933931438174438)⟩,⟨(-811056075803995515709),(-811056075803995500103)⟩⟩,⟨⟨5647820063145290924850179127,5647820063145290987389658981⟩,⟨14490083202807509824161633725,14490083202807509887013839669⟩⟩]
lemma ha33_1_4_eq (j : Fin 7) : ha33_1_4 j = ((ha33_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha33_1_4_contains (j : Fin 7) : (ha33_1_4 j).Contains (fullFactor true 33 4 ((j.val:ℝ)/6)) := by
  rw [ha33_1_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_1_3 j) true 33 3 j (ha33_1_3_contains j)
noncomputable def hk33_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel33_0 j i k).mul (mpower1_5 j i k)
lemma hk33_1_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_1_5 j i k).Contains (fullFactor true 33 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_1_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel33_0 j i k) (mpower1_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 5 (kernel33_0_contains j i k) (mpower1_5_contains j i k)
noncomputable def ha33_1_5 : Fin 7 → CBox := ![⟨⟨(-1700),1700⟩,⟨(-1700),1700⟩⟩,⟨⟨(-5111),5425⟩,⟨(-4887),5641⟩⟩,⟨⟨(-2436),2862⟩,⟨(-2619),2679⟩⟩,⟨⟨(-547),413⟩,⟨(-529),432⟩⟩,⟨⟨(-5141945244),(-5141945011)⟩,⟨3882523813,3882524046⟩⟩,⟨⟨(-530861845519358357219),(-530861845519358342268)⟩,⟨878857482013637091211,878857482013637106155⟩⟩,⟨⟨10252711526171924584312879211,10252711526171924632087704918⟩,⟨(-4623055366447408034423132902),(-4623055366447407986881685317)⟩⟩]
lemma ha33_1_5_eq (j : Fin 7) : ha33_1_5 j = ((ha33_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha33_1_5_contains (j : Fin 7) : (ha33_1_5 j).Contains (fullFactor true 33 5 ((j.val:ℝ)/6)) := by
  rw [ha33_1_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_1_4 j) true 33 4 j (ha33_1_4_contains j)
noncomputable def hk33_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel33_0 j i k).mul (mpower1_6 j i k)
lemma hk33_1_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_1_6 j i k).Contains (fullFactor true 33 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_1_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel33_0 j i k) (mpower1_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 6 (kernel33_0_contains j i k) (mpower1_6_contains j i k)
noncomputable def ha33_1_6 : Fin 7 → CBox := ![⟨⟨(-2612),2612⟩,⟨(-2612),2612⟩⟩,⟨⟨(-9960),10026⟩,⟨(-10570),9412⟩⟩,⟨⟨(-4597),4299⟩,⟨(-4655),4241⟩⟩,⟨⟨(-646),626⟩,⟨(-556),716⟩⟩,⟨⟨4288182940,4288183179⟩,⟨2978720419,2978720659⟩⟩,⟨⟨660713610237594840710,660713610237594852643⟩,⟨258290673843763566348,258290673843763578285⟩⟩,⟨⟨(-3103193222852470612613818362),(-3103193222852470582496566523)⟩,⟨(-6025786945905339685507073848),(-6025786945905339655246445988)⟩⟩]
lemma ha33_1_6_eq (j : Fin 7) : ha33_1_6 j = ((ha33_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha33_1_6_contains (j : Fin 7) : (ha33_1_6 j).Contains (fullFactor true 33 6 ((j.val:ℝ)/6)) := by
  rw [ha33_1_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_1_5 j) true 33 5 j (ha33_1_5_contains j)
noncomputable def hk33_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel33_0 j i k).mul (mpower1_7 j i k)
lemma hk33_1_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_1_7 j i k).Contains (fullFactor true 33 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_1_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel33_0 j i k) (mpower1_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 7 (kernel33_0_contains j i k) (mpower1_7_contains j i k)
noncomputable def ha33_1_7 : Fin 7 → CBox := ![⟨⟨(-3439),3439⟩,⟨(-3439),3439⟩⟩,⟨⟨(-16595),15907⟩,⟨(-15633),16866⟩⟩,⟨⟨(-6449),6354⟩,⟨(-6146),6657⟩⟩,⟨⟨(-659),784⟩,⟨(-747),697⟩⟩,⟨⟨1037647155,1037647366⟩,⟨(-3475026221),(-3475026010)⟩⟩,⟨⟨84264277557540367981,84264277557540376150⟩,⟨(-411589445297043512327),(-411589445297043504160)⟩⟩,⟨⟨(-3025225223597894629230914973),(-3025225223597894612802593652)⟩,⟨1762456250846196591740634812,1762456250846196608094290627⟩⟩]
lemma ha33_1_7_eq (j : Fin 7) : ha33_1_7 j = ((ha33_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha33_1_7_contains (j : Fin 7) : (ha33_1_7 j).Contains (fullFactor true 33 7 ((j.val:ℝ)/6)) := by
  rw [ha33_1_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_1_6 j) true 33 6 j (ha33_1_6_contains j)
noncomputable def hk33_1_8 (j : Fin 6) (i k : Fin 16) : CBox := (kernel33_0 j i k).mul (mpower1_8 j i k)
lemma hk33_1_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_1_8 j i k).Contains (fullFactor true 33 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_1_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel33_0 j i k) (mpower1_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 8 (kernel33_0_contains j i k) (mpower1_8_contains j i k)
noncomputable def ha33_1_8 : Fin 7 → CBox := ![⟨⟨(-3962),3962⟩,⟨(-3962),3962⟩⟩,⟨⟨(-22509),23741⟩,⟨(-23555),22694⟩⟩,⟨⟨(-7868),8255⟩,⟨(-8188),7935⟩⟩,⟨⟨(-755),679⟩,⟨(-748),686⟩⟩,⟨⟨(-2203373655),(-2203373492)⟩,⟨58997934,58998097⟩⟩,⟨⟨(-217601560684657503820),(-217601560684657498929)⟩,⟨(-6794999972307240690),(-6794999972307235798)⟩⟩,⟨⟨866541512572288026186930715,866541512572288033956973749⟩,⟨1324153091694429687866434678,1324153091694429695670147553⟩⟩]
lemma ha33_1_8_eq (j : Fin 7) : ha33_1_8 j = ((ha33_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha33_1_8_contains (j : Fin 7) : (ha33_1_8 j).Contains (fullFactor true 33 8 ((j.val:ℝ)/6)) := by
  rw [ha33_1_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_1_7 j) true 33 7 j (ha33_1_7_contains j)
noncomputable def hk33_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel33_0 j i k).mul (mpower1_9 j i k)
lemma hk33_1_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_1_9 j i k).Contains (fullFactor true 33 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_1_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel33_0 j i k) (mpower1_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 9 (kernel33_0_contains j i k) (mpower1_9_contains j i k)
noncomputable def ha33_1_9 : Fin 7 → CBox := ![⟨⟨(-4057),4057⟩,⟨(-4057),4057⟩⟩,⟨⟨(-29954),28549⟩,⟨(-29139),29363⟩⟩,⟨⟨(-9202),8845⟩,⟨(-9065),8982⟩⟩,⟨⟨(-639),627⟩,⟨(-602),664⟩⟩,⟨⟨401274007,401274119⟩,⟨1121128731,1121128843⟩⟩,⟨⟨13944254309806885845,13944254309806888449⟩,⟨99305838504317855184,99305838504317857789⟩⟩,⟨⟨513204209667840666195845554,513204209667840669490751723⟩,⟨(-375304959186800768568344201),(-375304959186800765286798783)⟩⟩]
lemma ha33_1_9_eq (j : Fin 7) : ha33_1_9 j = ((ha33_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha33_1_9_contains (j : Fin 7) : (ha33_1_9 j).Contains (fullFactor true 33 9 ((j.val:ℝ)/6)) := by
  rw [ha33_1_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_1_8 j) true 33 8 j (ha33_1_8_contains j)
noncomputable def hk33_1_10 (j : Fin 6) (i k : Fin 16) : CBox := (kernel33_0 j i k).mul (mpower1_10 j i k)
lemma hk33_1_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_1_10 j i k).Contains (fullFactor true 33 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_1_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel33_0 j i k) (mpower1_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 10 (kernel33_0_contains j i k) (mpower1_10_contains j i k)
noncomputable def ha33_1_10 : Fin 7 → CBox := ![⟨⟨(-3739),3739⟩,⟨(-3739),3739⟩⟩,⟨⟨(-32720),33881⟩,⟨(-33125),33476⟩⟩,⟨⟨(-9024),9157⟩,⟨(-8978),9203⟩⟩,⟨⟨(-485),521⟩,⟨(-509),497⟩⟩,⟨⟨457152929,457152999⟩,⟨(-355279193),(-355279123)⟩⟩,⟨⟨39587274009137781130,39587274009137782379⟩,⟨(-12690800915682939736),(-12690800915682938488)⟩⟩,⟨⟨(-145160205578279353368480829),(-145160205578279352121174615)⟩,⟨(-178272149327208796117996423),(-178272149327208794865966224)⟩⟩]
lemma ha33_1_10_eq (j : Fin 7) : ha33_1_10 j = ((ha33_1_9 j).mul (piI.mul (atomPoints j).z)).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha33_1_10_contains (j : Fin 7) : (ha33_1_10 j).Contains (fullFactor true 33 10 ((j.val:ℝ)/6)) := by
  rw [ha33_1_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_1_9 j) true 33 9 j (ha33_1_9_contains j)
noncomputable def hk33_1_11 (j : Fin 6) (i k : Fin 16) : CBox := (kernel33_0 j i k).mul (mpower1_11 j i k)
lemma hk33_1_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_1_11 j i k).Contains (fullFactor true 33 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_1_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel33_0 j i k) (mpower1_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 11 (kernel33_0_contains j i k) (mpower1_11_contains j i k)
noncomputable def ha33_1_11 : Fin 7 → CBox := ![⟨⟨(-3133),3133⟩,⟨(-3133),3133⟩⟩,⟨⟨(-34809),34119⟩,⟨(-34782),34145⟩⟩,⟨⟨(-8303),8348⟩,⟨(-8407),8244⟩⟩,⟨⟨(-371),356⟩,⟨(-370),357⟩⟩,⟨⟨(-212194162),(-212194122)⟩,⟨(-143060674),(-143060634)⟩⟩,⟨⟨(-7247926835729381000),(-7247926835729380456)⟩,⟨(-13889776243161612755),(-13889776243161612210)⟩⟩,⟨⟨(-56044377682678141614527233),(-56044377682678141182030833)⟩,⟨50695640138029223386918459,50695640138029223817911932⟩⟩]
lemma ha33_1_11_eq (j : Fin 7) : ha33_1_11 j = ((ha33_1_10 j).mul (piI.mul (atomPoints j).z)).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha33_1_11_contains (j : Fin 7) : (ha33_1_11 j).Contains (fullFactor true 33 11 ((j.val:ℝ)/6)) := by
  rw [ha33_1_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_1_10 j) true 33 10 j (ha33_1_10_contains j)
noncomputable def hk33_1_12 (j : Fin 6) (i k : Fin 16) : CBox := (kernel33_0 j i k).mul (mpower1_12 j i k)
lemma hk33_1_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_1_12 j i k).Contains (fullFactor true 33 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_1_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel33_0 j i k) (mpower1_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 12 (kernel33_0_contains j i k) (mpower1_12_contains j i k)
noncomputable def ha33_1_12 : Fin 7 → CBox := ![⟨⟨(-2406),2406⟩,⟨(-2406),2406⟩⟩,⟨⟨(-32574),32817⟩,⟨(-32385),33006⟩⟩,⟨⟨(-7034),6945⟩,⟨(-6966),7013⟩⟩,⟨⟨(-242),240⟩,⟨(-236),246⟩⟩,⟨⟨(-28282420),(-28282399)⟩,⟨99760200,99760221⟩⟩,⟨⟨(-4303258040256849138),(-4303258040256848920)⟩,⟨3282713846709560778,3282713846709560996⟩⟩,⟨⟨16132243112760149149183848,16132243112760149285696863⟩,⟨16071534728958511180911956,16071534728958511317858569⟩⟩]
lemma ha33_1_12_eq (j : Fin 7) : ha33_1_12 j = ((ha33_1_11 j).mul (piI.mul (atomPoints j).z)).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha33_1_12_contains (j : Fin 7) : (ha33_1_12 j).Contains (fullFactor true 33 12 ((j.val:ℝ)/6)) := by
  rw [ha33_1_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_1_11 j) true 33 11 j (ha33_1_11_contains j)
noncomputable def hk33_1_13 (j : Fin 6) (i k : Fin 16) : CBox := (kernel33_0 j i k).mul (mpower1_13 j i k)
lemma hk33_1_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_1_13 j i k).Contains (fullFactor true 33 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_1_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel33_0 j i k) (mpower1_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 13 (kernel33_0_contains j i k) (mpower1_13_contains j i k)
noncomputable def ha33_1_13 : Fin 7 → CBox := ![⟨⟨(-1706),1706⟩,⟨(-1706),1706⟩⟩,⟨⟨(-28615),28649⟩,⟨(-28850),28414⟩⟩,⟨⟨(-5390),5443⟩,⟨(-5408),5425⟩⟩,⟨⟨(-145),150⟩,⟨(-148),147⟩⟩,⟨⟨38749920,38749931⟩,⟨(-1577533),(-1577522)⟩⟩,⟨⟨1264743398986832203,1264743398986832285⟩,⟨1174465471310263141,1174465471310263223⟩⟩,⟨⟨4231194229979023232789915,4231194229979023272816506⟩,⟨(-4713211993958011178873868),(-4713211993958011138961405)⟩⟩]
lemma ha33_1_13_eq (j : Fin 7) : ha33_1_13 j = ((ha33_1_12 j).mul (piI.mul (atomPoints j).z)).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha33_1_13_contains (j : Fin 7) : (ha33_1_13 j).Contains (fullFactor true 33 13 ((j.val:ℝ)/6)) := by
  rw [ha33_1_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_1_12 j) true 33 12 j (ha33_1_12_contains j)
noncomputable def hk33_1_14 (j : Fin 6) (i k : Fin 16) : CBox := (kernel33_0 j i k).mul (mpower1_14 j i k)
lemma hk33_1_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_1_14 j i k).Contains (fullFactor true 33 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_1_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel33_0 j i k) (mpower1_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 14 (kernel33_0_contains j i k) (mpower1_14_contains j i k)
noncomputable def ha33_1_14 : Fin 7 → CBox := ![⟨⟨(-1123),1123⟩,⟨(-1123),1123⟩⟩,⟨⟨(-23350),23215⟩,⟨(-23168),23397⟩⟩,⟨⟨(-3904),3892⟩,⟨(-3911),3885⟩⟩,⟨⟨(-85),83⟩,⟨(-85),83⟩⟩,⟨⟨(-4714868),(-4714862)⟩,⟨(-12616697),(-12616691)⟩⟩,⟨⟨279090999343703338,279090999343703367⟩,⟨(-428145224631312672),(-428145224631312643)⟩⟩,⟨⟨(-1272431197691962003205230),(-1272431197691961992369688)⟩,⟨(-1028138351043684120729484),(-1028138351043684109866410)⟩⟩]
lemma ha33_1_14_eq (j : Fin 7) : ha33_1_14 j = ((ha33_1_13 j).mul (piI.mul (atomPoints j).z)).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha33_1_14_contains (j : Fin 7) : (ha33_1_14 j).Contains (fullFactor true 33 14 ((j.val:ℝ)/6)) := by
  rw [ha33_1_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_1_13 j) true 33 13 j (ha33_1_13_contains j)
noncomputable def hk33_1_15 (j : Fin 6) (i k : Fin 16) : CBox := (kernel33_0 j i k).mul (mpower1_15 j i k)
lemma hk33_1_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_1_15 j i k).Contains (fullFactor true 33 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_1_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel33_0 j i k) (mpower1_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 15 (kernel33_0_contains j i k) (mpower1_15_contains j i k)
noncomputable def ha33_1_15 : Fin 7 → CBox := ![⟨⟨(-690),690⟩,⟨(-690),690⟩⟩,⟨⟨(-17608),17733⟩,⟨(-17712),17629⟩⟩,⟨⟨(-2621),2616⟩,⟨(-2612),2625⟩⟩,⟨⟨(-45),45⟩,⟨(-44),45⟩⟩,⟨⟨(-3409621),(-3409618)⟩,⟨2726759,2726763⟩⟩,⟨⟨(-129711012447214624),(-129711012447214614)⟩,⟨(-55908301046935676),(-55908301046935665)⟩⟩,⟨⟨(-231580378878440645256398),(-231580378878440642504794)⟩,⟨319189278250896037510302,319189278250896040255801⟩⟩]
lemma ha33_1_15_eq (j : Fin 7) : ha33_1_15 j = ((ha33_1_14 j).mul (piI.mul (atomPoints j).z)).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha33_1_15_contains (j : Fin 7) : (ha33_1_15 j).Contains (fullFactor true 33 15 ((j.val:ℝ)/6)) := by
  rw [ha33_1_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_1_14 j) true 33 14 j (ha33_1_14_contains j)
noncomputable def hk33_1_16 (j : Fin 6) (i k : Fin 16) : CBox := (kernel33_0 j i k).mul (mpower1_16 j i k)
lemma hk33_1_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_1_16 j i k).Contains (fullFactor true 33 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_1_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel33_0 j i k) (mpower1_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 16 (kernel33_0_contains j i k) (mpower1_16_contains j i k)
noncomputable def ha33_1_16 : Fin 7 → CBox := ![⟨⟨(-398),398⟩,⟨(-398),398⟩⟩,⟨⟨(-12613),12534⟩,⟨(-12568),12579⟩⟩,⟨⟨(-1646),1652⟩,⟨(-1650),1648⟩⟩,⟨⟨(-23),23⟩,⟨(-23),23⟩⟩,⟨⟨1110273,1110276⟩,⟨726273,726276⟩⟩,⟨⟨(-8565365084986799),(-8565365084986795)⟩,⟨35580273958560173,35580273958560177⟩⟩,⟨⟨74755338717072267421660,74755338717072268073821⟩,⟨48519221051282513579924,48519221051282514233331⟩⟩]
lemma ha33_1_16_eq (j : Fin 7) : ha33_1_16 j = ((ha33_1_15 j).mul (piI.mul (atomPoints j).z)).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha33_1_16_contains (j : Fin 7) : (ha33_1_16 j).Contains (fullFactor true 33 16 ((j.val:ℝ)/6)) := by
  rw [ha33_1_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_1_15 j) true 33 15 j (ha33_1_15_contains j)
noncomputable def hk33_1_17 (j : Fin 6) (i k : Fin 16) : CBox := (kernel33_0 j i k).mul (mpower1_17 j i k)
lemma hk33_1_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_1_17 j i k).Contains (fullFactor true 33 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_1_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel33_0 j i k) (mpower1_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 17 (kernel33_0_contains j i k) (mpower1_17_contains j i k)
noncomputable def ha33_1_17 : Fin 7 → CBox := ![⟨⟨(-216),216⟩,⟨(-216),216⟩⟩,⟨⟨(-8401),8439⟩,⟨(-8414),8427⟩⟩,⟨⟨(-979),976⟩,⟨(-978),977⟩⟩,⟨⟨(-11),11⟩,⟨(-11),11⟩⟩,⟨⟨98406,98408⟩,⟨(-366473),(-366471)⟩⟩,⟨⟨8905210707309764,8905210707309766⟩,⟨584275640103846,584275640103848⟩⟩,⟨⟨9480418229901251104154,9480418229901251250186⟩,⟨(-16414946559001116478788),(-16414946559001116332990)⟩⟩]
lemma ha33_1_17_eq (j : Fin 7) : ha33_1_17 j = ((ha33_1_16 j).mul (piI.mul (atomPoints j).z)).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha33_1_17_contains (j : Fin 7) : (ha33_1_17 j).Contains (fullFactor true 33 17 ((j.val:ℝ)/6)) := by
  rw [ha33_1_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_1_16 j) true 33 16 j (ha33_1_16_contains j)
noncomputable def hk33_1_18 (j : Fin 6) (i k : Fin 16) : CBox := (kernel33_0 j i k).mul (mpower1_18 j i k)
lemma hk33_1_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_1_18 j i k).Contains (fullFactor true 33 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_1_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel33_0 j i k) (mpower1_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 18 (kernel33_0_contains j i k) (mpower1_18_contains j i k)
noncomputable def ha33_1_18 : Fin 7 → CBox := ![⟨⟨(-111),111⟩,⟨(-111),111⟩⟩,⟨⟨(-5333),5319⟩,⟨(-5333),5319⟩⟩,⟨⟨(-547),548⟩,⟨(-547),548⟩⟩,⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨(-102346),(-102345)⟩,⟨5593,5595⟩⟩,⟨⟨(-215835877728262),(-215835877728260)⟩,⟨(-2043996127818229),(-2043996127818227)⟩⟩,⟨⟨(-3391942743075084431953),(-3391942743075084401169)⟩,⟨(-1730652639657568349857),(-1730652639657568319033)⟩⟩]
lemma ha33_1_18_eq (j : Fin 7) : ha33_1_18 j = ((ha33_1_17 j).mul (piI.mul (atomPoints j).z)).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha33_1_18_contains (j : Fin 7) : (ha33_1_18 j).Contains (fullFactor true 33 18 ((j.val:ℝ)/6)) := by
  rw [ha33_1_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_1_17 j) true 33 17 j (ha33_1_17_contains j)
noncomputable def hk33_1_19 (j : Fin 6) (i k : Fin 16) : CBox := (kernel33_0 j i k).mul (mpower1_19 j i k)
lemma hk33_1_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_1_19 j i k).Contains (fullFactor true 33 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_1_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel33_0 j i k) (mpower1_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 19 (kernel33_0_contains j i k) (mpower1_19_contains j i k)
noncomputable def ha33_1_19 : Fin 7 → CBox := ![⟨⟨(-54),54⟩,⟨(-54),54⟩⟩,⟨⟨(-3190),3193⟩,⟨(-3187),3196⟩⟩,⟨⟨(-291),291⟩,⟨(-291),291⟩⟩,⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨9522,9524⟩,⟨24439,24441⟩⟩,⟨⟨(-431490262514956),(-431490262514954)⟩,⟨122176327618126,122176327618128⟩⟩,⟨⟨(-295395541059033379405),(-295395541059033373240)⟩,⟨661756000920291874915,661756000920291881074⟩⟩]
lemma ha33_1_19_eq (j : Fin 7) : ha33_1_19 j = ((ha33_1_18 j).mul (piI.mul (atomPoints j).z)).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha33_1_19_contains (j : Fin 7) : (ha33_1_19 j).Contains (fullFactor true 33 19 ((j.val:ℝ)/6)) := by
  rw [ha33_1_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_1_18 j) true 33 18 j (ha33_1_18_contains j)
noncomputable def hk33_1_20 (j : Fin 6) (i k : Fin 16) : CBox := (kernel33_0 j i k).mul (mpower1_20 j i k)
lemma hk33_1_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_1_20 j i k).Contains (fullFactor true 33 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_1_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel33_0 j i k) (mpower1_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 20 (kernel33_0_contains j i k) (mpower1_20_contains j i k)
noncomputable def ha33_1_20 : Fin 7 → CBox := ![⟨⟨(-25),25⟩,⟨(-25),25⟩⟩,⟨⟨(-1817),1817⟩,⟨(-1819),1815⟩⟩,⟨⟨(-147),147⟩,⟨(-147),147⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨4923,4925⟩,⟨(-4052),(-4051)⟩⟩,⟨⟨40151361626720,40151361626721⟩,⟨83835802857328,83835802857330⟩⟩,⟨⟨122254278101623560880,122254278101623562052⟩,⟨47121042331282391220,47121042331282392392⟩⟩]
lemma ha33_1_20_eq (j : Fin 7) : ha33_1_20 j = ((ha33_1_19 j).mul (piI.mul (atomPoints j).z)).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha33_1_20_contains (j : Fin 7) : (ha33_1_20 j).Contains (fullFactor true 33 20 ((j.val:ℝ)/6)) := by
  rw [ha33_1_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_1_19 j) true 33 19 j (ha33_1_19_contains j)
noncomputable def hk33_1_21 (j : Fin 6) (i k : Fin 16) : CBox := (kernel33_0 j i k).mul (mpower1_21 j i k)
lemma hk33_1_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_1_21 j i k).Contains (fullFactor true 33 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_1_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel33_0 j i k) (mpower1_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 21 (kernel33_0_contains j i k) (mpower1_21_contains j i k)
noncomputable def ha33_1_21 : Fin 7 → CBox := ![⟨⟨(-11),11⟩,⟨(-11),11⟩⟩,⟨⟨(-986),985⟩,⟨(-985),986⟩⟩,⟨⟨(-71),71⟩,⟨(-71),71⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1247),(-1246)⟩,⟨(-792),(-790)⟩⟩,⟨⟨14962631764677,14962631764678⟩,⟨(-10622675087111),(-10622675087110)⟩⟩,⟨⟨7009486427796565430,7009486427796565643⟩,⟨(-21443402748532651275),(-21443402748532651061)⟩⟩]
lemma ha33_1_21_eq (j : Fin 7) : ha33_1_21 j = ((ha33_1_20 j).mul (piI.mul (atomPoints j).z)).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha33_1_21_contains (j : Fin 7) : (ha33_1_21 j).Contains (fullFactor true 33 21 ((j.val:ℝ)/6)) := by
  rw [ha33_1_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_1_20 j) true 33 20 j (ha33_1_20_contains j)
noncomputable def hk33_1_22 (j : Fin 6) (i k : Fin 16) : CBox := (kernel33_0 j i k).mul (mpower1_22 j i k)
lemma hk33_1_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_1_22 j i k).Contains (fullFactor true 33 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_1_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel33_0 j i k) (mpower1_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 22 (kernel33_0_contains j i k) (mpower1_22_contains j i k)
noncomputable def ha33_1_22 : Fin 7 → CBox := ![⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨(-510),511⟩,⟨(-511),510⟩⟩,⟨⟨(-33),33⟩,⟨(-33),33⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-81),(-80)⟩,⟨316,317⟩⟩,⟨⟨(-2451592244117),(-2451592244116)⟩,⟨(-2438417122856),(-2438417122855)⟩⟩,⟨⟨(-3579494566261312252),(-3579494566261312214)⟩,⟨(-967497197846377782),(-967497197846377744)⟩⟩]
lemma ha33_1_22_eq (j : Fin 7) : ha33_1_22 j = ((ha33_1_21 j).mul (piI.mul (atomPoints j).z)).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha33_1_22_contains (j : Fin 7) : (ha33_1_22 j).Contains (fullFactor true 33 22 ((j.val:ℝ)/6)) := by
  rw [ha33_1_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_1_21 j) true 33 21 j (ha33_1_21_contains j)
noncomputable def hk33_1_23 (j : Fin 6) (i k : Fin 16) : CBox := (kernel33_0 j i k).mul (mpower1_23 j i k)
lemma hk33_1_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_1_23 j i k).Contains (fullFactor true 33 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_1_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel33_0 j i k) (mpower1_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 23 (kernel33_0_contains j i k) (mpower1_23_contains j i k)
noncomputable def ha33_1_23 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-253),253⟩,⟨(-253),253⟩⟩,⟨⟨(-15),15⟩,⟨(-15),15⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨68,70⟩,⟨(-5),(-4)⟩⟩,⟨⟨(-358042915039),(-358042915037)⟩,⟨510124762820,510124762821⟩⟩,⟨⟨(-122674951015016134),(-122674951015016127)⟩,⟨569883403376587314,569883403376587321⟩⟩]
lemma ha33_1_23_eq (j : Fin 7) : ha33_1_23 j = ((ha33_1_22 j).mul (piI.mul (atomPoints j).z)).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha33_1_23_contains (j : Fin 7) : (ha33_1_23 j).Contains (fullFactor true 33 23 ((j.val:ℝ)/6)) := by
  rw [ha33_1_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_1_22 j) true 33 22 j (ha33_1_22_contains j)
noncomputable def hk33_1_24 (j : Fin 6) (i k : Fin 16) : CBox := (kernel33_0 j i k).mul (mpower1_24 j i k)
lemma hk33_1_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_1_24 j i k).Contains (fullFactor true 33 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_1_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel33_0 j i k) (mpower1_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 24 (kernel33_0_contains j i k) (mpower1_24_contains j i k)
noncomputable def ha33_1_24 : Fin 7 → CBox := ![⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-121),121⟩,⟨(-121),121⟩⟩,⟨⟨(-7),7⟩,⟨(-7),7⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-6),(-5)⟩,⟨(-14),(-12)⟩⟩,⟨⟨97340920883,97340920885⟩,⟨45976160934,45976160936⟩⟩,⟨⟨86704120648698521,86704120648698523⟩,⟨13998896848124011,13998896848124013⟩⟩]
lemma ha33_1_24_eq (j : Fin 7) : ha33_1_24 j = ((ha33_1_23 j).mul (piI.mul (atomPoints j).z)).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha33_1_24_contains (j : Fin 7) : (ha33_1_24 j).Contains (fullFactor true 33 24 ((j.val:ℝ)/6)) := by
  rw [ha33_1_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_1_23 j) true 33 23 j (ha33_1_23_contains j)
noncomputable def hk33_1_25 (j : Fin 6) (i k : Fin 16) : CBox := (kernel33_0 j i k).mul (mpower1_25 j i k)
lemma hk33_1_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_1_25 j i k).Contains (fullFactor true 33 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_1_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel33_0 j i k) (mpower1_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 25 (kernel33_0_contains j i k) (mpower1_25_contains j i k)
noncomputable def ha33_1_25 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-56),56⟩,⟨(-56),56⟩⟩,⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-3),(-1)⟩,⟨1,2⟩⟩,⟨⟨4770741089,4770741090⟩,⟨(-17201908809),(-17201908807)⟩⟩,⟨⟨1370786299595409,1370786299595410⟩,⟨(-12628778285228903),(-12628778285228901)⟩⟩]
lemma ha33_1_25_eq (j : Fin 7) : ha33_1_25 j = ((ha33_1_24 j).mul (piI.mul (atomPoints j).z)).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha33_1_25_contains (j : Fin 7) : (ha33_1_25 j).Contains (fullFactor true 33 25 ((j.val:ℝ)/6)) := by
  rw [ha33_1_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_1_24 j) true 33 24 j (ha33_1_24_contains j)
noncomputable def hk33_1_26 (j : Fin 6) (i k : Fin 16) : CBox := (kernel33_0 j i k).mul (mpower1_26 j i k)
lemma hk33_1_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_1_26 j i k).Contains (fullFactor true 33 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_1_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel33_0 j i k) (mpower1_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 26 (kernel33_0_contains j i k) (mpower1_26_contains j i k)
noncomputable def ha33_1_26 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-25),25⟩,⟨(-25),25⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨0,1⟩,⟨0,1⟩⟩,⟨⟨(-2832113342),(-2832113341)⟩,⟨(-283634564),(-283634563)⟩⟩,⟨⟨(-1763855552495529),(-1763855552495528)⟩,⟨(-99176806368110),(-99176806368108)⟩⟩]
lemma ha33_1_26_eq (j : Fin 7) : ha33_1_26 j = ((ha33_1_25 j).mul (piI.mul (atomPoints j).z)).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha33_1_26_contains (j : Fin 7) : (ha33_1_26 j).Contains (fullFactor true 33 26 ((j.val:ℝ)/6)) := by
  rw [ha33_1_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_1_25 j) true 33 25 j (ha33_1_25_contains j)
noncomputable def hk33_1_27 (j : Fin 6) (i k : Fin 16) : CBox := (kernel33_0 j i k).mul (mpower1_27 j i k)
lemma hk33_1_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_1_27 j i k).Contains (fullFactor true 33 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_1_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel33_0 j i k) (mpower1_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 27 (kernel33_0_contains j i k) (mpower1_27_contains j i k)
noncomputable def ha33_1_27 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-11),11⟩,⟨(-11),11⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),0⟩⟩,⟨⟨30960760,30960761⟩,⟨435918024,435918025⟩⟩,⟨⟨(-997220634971),(-997220634969)⟩,⟨236590781110290,236590781110291⟩⟩]
lemma ha33_1_27_eq (j : Fin 7) : ha33_1_27 j = ((ha33_1_26 j).mul (piI.mul (atomPoints j).z)).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha33_1_27_contains (j : Fin 7) : (ha33_1_27 j).Contains (fullFactor true 33 27 ((j.val:ℝ)/6)) := by
  rw [ha33_1_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_1_26 j) true 33 26 j (ha33_1_26_contains j)
noncomputable def hk33_1_28 (j : Fin 6) (i k : Fin 16) : CBox := (kernel33_0 j i k).mul (mpower1_28 j i k)
lemma hk33_1_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_1_28 j i k).Contains (fullFactor true 33 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_1_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel33_0 j i k) (mpower1_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 28 (kernel33_0_contains j i k) (mpower1_28_contains j i k)
noncomputable def ha33_1_28 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨62823155,62823156⟩,⟨(-15482255),(-15482254)⟩⟩,⟨⟨30518668662407,30518668662408⟩,⟨(-1458016243474),(-1458016243473)⟩⟩]
lemma ha33_1_28_eq (j : Fin 7) : ha33_1_28 j = ((ha33_1_27 j).mul (piI.mul (atomPoints j).z)).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha33_1_28_contains (j : Fin 7) : (ha33_1_28 j).Contains (fullFactor true 33 28 ((j.val:ℝ)/6)) := by
  rw [ha33_1_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_1_27 j) true 33 27 j (ha33_1_27_contains j)
noncomputable def hk33_1_29 (j : Fin 6) (i k : Fin 16) : CBox := (kernel33_0 j i k).mul (mpower1_29 j i k)
lemma hk33_1_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_1_29 j i k).Contains (fullFactor true 33 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_1_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel33_0 j i k) (mpower1_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 29 (kernel33_0_contains j i k) (mpower1_29_contains j i k)
noncomputable def ha33_1_29 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-3706768),(-3706767)⟩,⟨(-8474034),(-8474032)⟩⟩,⟨⟨(-379156117052),(-379156117051)⟩,⟨(-3790687262187),(-3790687262186)⟩⟩]
lemma ha33_1_29_eq (j : Fin 7) : ha33_1_29 j = ((ha33_1_28 j).mul (piI.mul (atomPoints j).z)).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha33_1_29_contains (j : Fin 7) : (ha33_1_29 j).Contains (fullFactor true 33 29 ((j.val:ℝ)/6)) := by
  rw [ha33_1_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_1_28 j) true 33 28 j (ha33_1_28_contains j)
noncomputable def hk33_1_30 (j : Fin 6) (i k : Fin 16) : CBox := (kernel33_0 j i k).mul (mpower1_30 j i k)
lemma hk33_1_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk33_1_30 j i k).Contains (fullFactor true 33 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk33_1_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel33_0 j i k) (mpower1_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 33 30 (kernel33_0_contains j i k) (mpower1_30_contains j i k)
noncomputable def ha33_1_30 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1066942),(-1066941)⟩,⟨703718,703719⟩⟩,⟨⟨(-453902499740),(-453902499739)⟩,⟨69364422419,69364422420⟩⟩]
lemma ha33_1_30_eq (j : Fin 7) : ha33_1_30 j = ((ha33_1_29 j).mul (piI.mul (atomPoints j).z)).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha33_1_30_contains (j : Fin 7) : (ha33_1_30 j).Contains (fullFactor true 33 30 ((j.val:ℝ)/6)) := by
  rw [ha33_1_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha33_1_29 j) true 33 29 j (ha33_1_29_contains j)
end SharpPlanar.CachedData

end OAI
