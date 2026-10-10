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
noncomputable def hk3_0_0 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_0 j i k)
lemma hk3_0_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_0_0 j i k).Contains (fullFactor false 3 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_0_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power3 j i k) (mpower0_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 0 (power3_contains j i k) (mpower0_0_contains j i k)
noncomputable def ha3_0_0 : Fin 7 → CBox := ![⟨⟨999999999999999999999999999965,1000000000000000000000000000047⟩,⟨(-47),47⟩⟩,⟨⟨(-4508926683),2152309972⟩,⟨999999999999999999996712771924,1000000000000000000003287228080⟩⟩,⟨⟨(-1000000000000000000009057192871),(-999999999999999999990942807131)⟩,⟨(-11382050607),6668817169⟩⟩,⟨⟨(-6265099811),13334949965⟩,⟨(-1000000000000000000009800024888),(-999999999999999999990199975115)⟩⟩,⟨⟨999999999999999999975286562235,1000000000000000000024713437758⟩,⟨(-20023421740),29449888624⟩⟩,⟨⟨(-36999211493),25216127899⟩,⟨999999999999999999968869286671,1000000000000000000031130713320⟩⟩,⟨⟨(-1000000000000000000019659593357),(-999999999999999999980340406655)⟩,⟨(-26729443517),12589743185⟩⟩]
lemma ha3_0_0_eq (j : Fin 7) : ha3_0_0 j = ((atomPoints j).direct.powBin 7 3).conj := by fin_cases j <;> decide +kernel
lemma ha3_0_0_contains (j : Fin 7) : (ha3_0_0 j).Contains (fullFactor false 3 0 ((j.val:ℝ)/6)) := by
  rw [ha3_0_0_eq]
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @direct_factor_zero_full ((atomPoints j).direct.powBin 7 3) ((j.val:ℝ)/6) 3 (@direct_power_bin_contains (atomPoints j) ((j.val:ℝ)/6) (atomPoints_contains j) 3 (by norm_num))
noncomputable def hk3_0_1 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_1 j i k)
lemma hk3_0_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_0_1 j i k).Contains (fullFactor false 3 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_0_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power3 j i k) (mpower0_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 1 (power3_contains j i k) (mpower0_1_contains j i k)
noncomputable def ha3_0_1 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-523598775598298873080054521933),(-523598775598298873074945478068)⟩,⟨(-2360868491),1126946867⟩⟩,⟨⟨(-6983569009),11919255524⟩,⟨(-1047197551196597746166151336865),(-1047197551196597746143848663138)⟩⟩,⟨⟨1570796326794896619214606156908,1570796326794896619250393843097⟩,⟨(-9841195771),20946490424⟩⟩,⟨⟨(-61679702501),41936956426⟩,⟨2094395102393195492254906963645,2094395102393195492365093036339⟩⟩,⟨⟨(-2617993877991494365473166683559),(-2617993877991494365301833316419)⟩,⟨(-96863709180),66015668467⟩⟩,⟨⟨(-39551844701),83973023388⟩,⟨(-3141592653589793238531762434063),(-3141592653589793238398237565974)⟩⟩]
lemma ha3_0_1_eq (j : Fin 7) : ha3_0_1 j = ((ha3_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha3_0_1_contains (j : Fin 7) : (ha3_0_1 j).Contains (fullFactor false 3 1 ((j.val:ℝ)/6)) := by
  rw [ha3_0_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_0_0 j) false 3 0 j (ha3_0_0_contains j)
noncomputable def hk3_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_2 j i k)
lemma hk3_0_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_0_2 j i k).Contains (fullFactor false 3 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_0_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power3 j i k) (mpower0_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 2 (power3_contains j i k) (mpower0_2_contains j i k)
noncomputable def ha3_0_2 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-295034000),618073926⟩,⟨(-137077838904018869707127189261),(-137077838904018869705353312390)⟩⟩,⟨⟨548311355616075478818249512347,548311355616075478831672494258⟩,⟨(-3656588183),6240907599⟩⟩,⟨⟨(-16451335109),7729257085⟩,⟨1233700550136169827340144970519,1233700550136169827372179544342⟩⟩,⟨⟨(-2193245422464301915361027964455),(-2193245422464301915238660061940)⟩,⟨(-64590833418),43916278074⟩⟩,⟨⟨(-86414307950),126794298817⟩,⟨(-3426945972600471742773597851104),(-3426945972600471742538414690139)⟩⟩,⟨⟨4934802200544679309311924861944,4934802200544679309537373197543⟩,⟨(-62127892375),131904516688⟩⟩]
lemma ha3_0_2_eq (j : Fin 7) : ha3_0_2 j = ((ha3_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha3_0_2_contains (j : Fin 7) : (ha3_0_2 j).Contains (fullFactor false 3 2 ((j.val:ℝ)/6)) := by
  rw [ha3_0_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_0_1 j) false 3 1 j (ha3_0_1_contains j)
noncomputable def hk3_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_3 j i k)
lemma hk3_0_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_0_3 j i k).Contains (fullFactor false 3 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_0_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power3 j i k) (mpower0_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 3 (power3_contains j i k) (mpower0_3_contains j i k)
noncomputable def ha3_0_3 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨23924596203935046431555650402,23924596203935046431941404677⟩,⟨(-51493148),107874251⟩⟩,⟨⟨(-2178487719),1276390064⟩,⟨191396769631480371451340850599,191396769631480371456635590036⟩⟩,⟨⟨(-645964097506246253666624959179),(-645964097506246253647795527964)⟩,⟨(-8613898921),4047029546⟩⟩,⟨⟨(-30659345905),45092908391⟩,⟨(-1531174157051842971677057157843),(-1531174157051842971586754367217)⟩⟩,⟨⟨2990574525491880803861188282654,2990574525491880804075943602232⟩,⟨(-75410709728),110648899356⟩⟩,⟨⟨(-138130086868),65060176757⟩,⟨5167712780049970029131412805777,5167712780049970029383951091407⟩⟩]
lemma ha3_0_3_eq (j : Fin 7) : ha3_0_3 j = ((ha3_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha3_0_3_contains (j : Fin 7) : (ha3_0_3 j).Contains (fullFactor false 3 3 ((j.val:ℝ)/6)) := by
  rw [ha3_0_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_0_2 j) false 3 2 j (ha3_0_2_contains j)
noncomputable def hk3_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_4 j i k)
lemma hk3_0_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_0_4 j i k).Contains (fullFactor false 3 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_0_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power3 j i k) (mpower0_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 4 (power3_contains j i k) (mpower0_4_contains j i k)
noncomputable def ha3_0_4 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-14120707),6740438⟩,⟨3131722319766024859689823845,3131722319766024859750287544⟩⟩,⟨⟨(-50107557116256397756293719542),(-50107557116256397754748062690)⟩,⟨(-570326752),334158138⟩⟩,⟨⟨(-1589264787),3382670197⟩,⟨(-253669507901048013641425389009),(-253669507901048013633223633539)⟩⟩,⟨⟨801720913860102364063417064080,801720913860102364113251451616⟩,⟨(-16053195977),23610591622⟩⟩,⟨⟨(-72419535281),49356194101⟩,⟨1957326449853765537251641113411,1957326449853765537398428504990⟩⟩,⟨⟨(-4058712126416768218302823374234),(-4058712126416768218091560986561)⟩,⟨(-108487116537),51098143336⟩⟩]
lemma ha3_0_4_eq (j : Fin 7) : ha3_0_4 j = ((ha3_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha3_0_4_contains (j : Fin 7) : (ha3_0_4 j).Contains (fullFactor false 3 4 ((j.val:ℝ)/6)) := by
  rw [ha3_0_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_0_3 j) false 3 3 j (ha3_0_3_contains j)
noncomputable def hk3_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_5 j i k)
lemma hk3_0_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_0_5 j i k).Contains (fullFactor false 3 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_0_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power3 j i k) (mpower0_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 5 (power3_contains j i k) (mpower0_5_contains j i k)
noncomputable def ha3_0_5 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-327953194428670967579014782),(-327953194428670967571639130)⟩,⟨(-1478717),705858⟩⟩,⟨⟨(-69985917),119448956⟩,⟨(-10494502221717470962589025930),(-10494502221717470962231899277)⟩⟩,⟨⟨79692626246167045119389286902,79692626246167045122219613884⟩,⟨(-499282258),1062697185⟩⟩,⟨⟨(-9889981492),6724347007⟩,⟨335824071094959070786163032969,335824071094959070808106573627⟩⟩,⟨⟨(-1024853732589596773712956693210),(-1024853732589596773632836783953)⟩,⟨(-37918780003),25842842800⟩⟩,⟨⟨(-32105910344),68164465665⟩,⟨(-2550164039877345443936171161207),(-2550164039877345443795313663935)⟩⟩]
lemma ha3_0_5_eq (j : Fin 7) : ha3_0_5 j = ((ha3_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha3_0_5_contains (j : Fin 7) : (ha3_0_5 j).Contains (fullFactor false 3 5 ((j.val:ℝ)/6)) := by
  rw [ha3_0_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_0_4 j) false 3 4 j (ha3_0_4_contains j)
noncomputable def hk3_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_6 j i k)
lemma hk3_0_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_0_6 j i k).Contains (fullFactor false 3 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_0_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power3 j i k) (mpower0_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 6 (power3_contains j i k) (mpower0_6_contains j i k)
noncomputable def ha3_0_6 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-61598),129043⟩,⟨(-28619315176067161691925041),(-28619315176067161691190295)⟩⟩,⟨⟨1831636171268298348225610410,1831636171268298348293771050⟩,⟨(-12214847),20847776⟩⟩,⟨⟨(-278213473),130711790⟩,⟨20863480763352960872741845523,20863480763352960873549233917⟩⟩,⟨⟨(-117224714961171094292636645980),(-117224714961171094284603767441)⟩,⟨(-3452254800),2347239907⟩⟩,⟨⟨(-11276067374),16545188985⟩,⟨(-447176799626049401448779713736),(-447176799626049401412397400449)⟩⟩,⟨⟨1335262768854589495842312998822,1335262768854589495920316085328⟩,⟨(-16810615346),35690830762⟩⟩]
lemma ha3_0_6_eq (j : Fin 7) : ha3_0_6 j = ((ha3_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha3_0_6_contains (j : Fin 7) : (ha3_0_6 j).Contains (fullFactor false 3 6 ((j.val:ℝ)/6)) := by
  rw [ha3_0_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_0_5 j) false 3 5 j (ha3_0_5_contains j)
noncomputable def hk3_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_7 j i k)
lemma hk3_0_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_0_7 j i k).Contains (fullFactor false 3 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_0_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power3 j i k) (mpower0_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 7 (power3_contains j i k) (mpower0_7_contains j i k)
noncomputable def ha3_0_7 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2140719769235797028185870,2140719769235797028247644⟩,⟨(-4608),9653⟩⟩,⟨⟨(-3118820),1827337⟩,⟨274012130462182019606210387,274012130462182019617279404⟩⟩,⟨⟨(-4681754135318688100808087557),(-4681754135318688100612007538)⟩,⟨(-62430958),29331658⟩⟩,⟨⟨(-702292538),1032912221⟩,⟨(-35073552699159298511560883716),(-35073552699159298509045809491)⟩⟩,⟨⟨167243731971546642822364486881,167243731971546642836503793565⟩,⟨(-4217239337),6187886211⟩⟩,⟨⟨(-16018007389),7544586525⟩,⟨599264529320792076872428475316,599264529320792076909343696918⟩⟩]
lemma ha3_0_7_eq (j : Fin 7) : ha3_0_7 j = ((ha3_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha3_0_7_contains (j : Fin 7) : (ha3_0_7 j).Contains (fullFactor false 3 7 ((j.val:ℝ)/6)) := by
  rw [ha3_0_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_0_6 j) false 3 6 j (ha3_0_6_contains j)
noncomputable def hk3_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_8 j i k)
lemma hk3_0_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_0_8 j i k).Contains (fullFactor false 3 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_0_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power3 j i k) (mpower0_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 8 (power3_contains j i k) (mpower0_8_contains j i k)
noncomputable def ha3_0_8 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-632),302⟩,⟨140109781258867029451685,140109781258867029456175⟩⟩,⟨⟨(-35868104002269959540987555),(-35868104002269959539424452)⟩,⟨(-408253),239198⟩⟩,⟨⟨(-5759258),12258290⟩,⟨(-919260274839426580267945931),(-919260274839426580226519612)⟩⟩,⟨⟨9182234624581109641948900493,9182234624581109642636573347⟩,⟨(-183859757),270415788⟩⟩,⟨⟨(-2024981028),1380088346⟩,⟨54730383304244933378040644908,54730383304244933382841934422⟩⟩,⟨⟨(-235330630358893204550914416730),(-235330630358893204535668762443)⟩,⟨(-6290256793),2962752201⟩⟩]
lemma ha3_0_8_eq (j : Fin 7) : ha3_0_8 j = ((ha3_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha3_0_8_contains (j : Fin 7) : (ha3_0_8 j).Contains (fullFactor false 3 8 ((j.val:ℝ)/6)) := by
  rw [ha3_0_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_0_7 j) false 3 7 j (ha3_0_7_contains j)
noncomputable def hk3_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_9 j i k)
lemma hk3_0_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_0_9 j i k).Contains (fullFactor false 3 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_0_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power3 j i k) (mpower0_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 9 (power3_contains j i k) (mpower0_9_contains j i k)
noncomputable def ha3_0_9 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-8151256657387584305064),(-8151256657387584304776)⟩,⟨(-37),18⟩⟩,⟨⟨(-27832),47503⟩,⟨(-4173443408582443164216716),(-4173443408582443164021555)⟩⟩,⟨⟨160441184787359821869873563,160441184787359821877614521⟩,⟨(-1005181),2139476⟩⟩,⟨⟨(-62928612),42786109⟩,⟨2136803025194210899945582323,2136803025194210900112412719⟩⟩,⟨⟨(-15920423158960125596270897778),(-15920423158960125594823582990)⟩,⟨(-589043104),401451427⟩⟩,⟨⟨(-1034195617),2195713837⟩,⟨(-82145886611128228802148557501),(-82145886611128228796565341744)⟩⟩]
lemma ha3_0_9_eq (j : Fin 7) : ha3_0_9 j = ((ha3_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha3_0_9_contains (j : Fin 7) : (ha3_0_9 j).Contains (fullFactor false 3 9 ((j.val:ℝ)/6)) := by
  rw [ha3_0_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_0_8 j) false 3 8 j (ha3_0_8_contains j)
noncomputable def hk3_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_10 j i k)
lemma hk3_0_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_0_10 j i k).Contains (fullFactor false 3 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_0_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power3 j i k) (mpower0_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 10 (power3_contains j i k) (mpower0_10_contains j i k)
noncomputable def ha3_0_10 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),2⟩,⟨(-426798800539562151463),(-426798800539562151446)⟩⟩,⟨⟨437041971752511643078585,437041971752511643100415⟩,⟨(-2915),4975⟩⟩,⟨⟨(-336069),157894⟩,⟨25202042373060605480593987,25202042373060605481890155⟩⟩,⟨⟨(-447530979074571922541830622),(-447530979074571922505465209)⟩,⟨(-13179738),8961102⟩⟩,⟨⟨(-105099738),154211125⟩,⟨(-4167957036519161635494814728),(-4167957036519161635102641582)⟩⟩,⟨⟨25806891390014060011873798199,25806891390014060013709963047⟩,⟨(-324902136),689803846⟩⟩]
lemma ha3_0_10_eq (j : Fin 7) : ha3_0_10 j = ((ha3_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha3_0_10_contains (j : Fin 7) : (ha3_0_10 j).Contains (fullFactor false 3 10 ((j.val:ℝ)/6)) := by
  rw [ha3_0_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_0_9 j) false 3 9 j (ha3_0_9_contains j)
noncomputable def hk3_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_11 j i k)
lemma hk3_0_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_0_11 j i k).Contains (fullFactor false 3 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_0_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power3 j i k) (mpower0_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 11 (power3_contains j i k) (mpower0_11_contains j i k)
noncomputable def ha3_0_11 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨20315575399030665720,20315575399030665722⟩,⟨(-1),1⟩⟩,⟨⟨(-474),278⟩,⟨41606298417214803395621,41606298417214803397832⟩⟩,⟨⟨(-3598843235212085340586510),(-3598843235212085340389961)⟩,⟨(-47991),22548⟩⟩,⟨⟨(-1706190),2509417⟩,⟨(-85209699158455917360093440),(-85209699158455917352898249)⟩⟩,⟨⟨991971455030794224612780797,991971455030794224709275331⟩,⟨(-25013680),36702162⟩⟩,⟨⟨(-197007518),92791834⟩,⟨7370430945714350777045972776,7370430945714350777593841042⟩⟩]
lemma ha3_0_11_eq (j : Fin 7) : ha3_0_11 j = ((ha3_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha3_0_11_contains (j : Fin 7) : (ha3_0_11 j).Contains (fullFactor false 3 11 ((j.val:ℝ)/6)) := by
  rw [ha3_0_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_0_10 j) false 3 10 j (ha3_0_10_contains j)
noncomputable def hk3_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_12 j i k)
lemma hk3_0_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_0_12 j i k).Contains (fullFactor false 3 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_0_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power3 j i k) (mpower0_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 12 (power3_contains j i k) (mpower0_12_contains j i k)
noncomputable def ha3_0_12 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨886434200375614885,886434200375614886⟩⟩,⟨⟨(-3630834484738518571159),(-3630834484738518570954)⟩,⟨(-42),25⟩⟩,⟨⟨(-2952),6283⟩,⟨(-471087477881817150384883),(-471087477881817150357654)⟩⟩,⟨⟨14871898049488972066394911,14871898049488972067698048⟩,⟨(-297787),437976⟩⟩,⟨⟨(-8007170),5457139⟩,⟨216414599701077852897280160,216414599701077852919020871⟩⟩,⟨⟨(-1929574309403923047995501646),(-1929574309403923047845928043)⟩,⟨(-51576448),24292846⟩⟩]
lemma ha3_0_12_eq (j : Fin 7) : ha3_0_12 j = ((ha3_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha3_0_12_contains (j : Fin 7) : (ha3_0_12 j).Contains (fullFactor false 3 12 ((j.val:ℝ)/6)) := by
  rw [ha3_0_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_0_11 j) false 3 11 j (ha3_0_11_contains j)
noncomputable def hk3_0_13 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_13 j i k)
lemma hk3_0_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_0_13 j i k).Contains (fullFactor false 3 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_0_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power3 j i k) (mpower0_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 13 (power3_contains j i k) (mpower0_13_contains j i k)
noncomputable def ha3_0_13 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-35702758612702237),(-35702758612702236)⟩,⟨(-1),1⟩⟩,⟨⟨(-3),4⟩,⟨(-292476998555256723035),(-292476998555256723017)⟩⟩,⟨⟨56921729219679268116572,56921729219679268120044⟩,⟨(-357),760⟩⟩,⟨⟨(-70562),47976⟩,⟨2395971572164663074921207,2395971572164663075138779⟩⟩,⟨⟨(-43582469009646285033416537),(-43582469009646285028899574)⟩,⟨(-1612518),1098982⟩⟩,⟨⟨(-5870633),12464015⟩,⟨(-466302805767612564443991377),(-466302805767612564406360986)⟩⟩]
lemma ha3_0_13_eq (j : Fin 7) : ha3_0_13 j = ((ha3_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha3_0_13_contains (j : Fin 7) : (ha3_0_13 j).Contains (fullFactor false 3 13 ((j.val:ℝ)/6)) := by
  rw [ha3_0_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_0_12 j) false 3 12 j (ha3_0_12_contains j)
noncomputable def hk3_0_14 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_14 j i k)
lemma hk3_0_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_0_14 j i k).Contains (fullFactor false 3 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_0_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power3 j i k) (mpower0_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 14 (power3_contains j i k) (mpower0_14_contains j i k)
noncomputable def ha3_0_14 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-1335280049649466),(-1335280049649465)⟩⟩,⟨⟨21877228333456835516,21877228333456835519⟩,⟨(-1),1⟩⟩,⟨⟨(-86),41⟩,⟨6386603083791852240952,6386603083791852241362⟩⟩,⟨⟨(-358436509015356793138354),(-358436509015356793104664)⟩,⟨(-10557),7178⟩⟩,⟨⟨(-205510),301541⟩,⟨(-8149902646786285757585890),(-8149902646786285756715277)⟩⟩,⟨⟨104638104924845707114726968,104638104924845707123504283⟩,⟨(-1317367),2796919⟩⟩]
lemma ha3_0_14_eq (j : Fin 7) : ha3_0_14 j = ((ha3_0_13 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha3_0_14_contains (j : Fin 7) : (ha3_0_14 j).Contains (fullFactor false 3 14 ((j.val:ℝ)/6)) := by
  rw [ha3_0_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_0_13 j) false 3 13 j (ha3_0_13_contains j)
noncomputable def hk3_0_15 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_15 j i k)
lemma hk3_0_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_0_15 j i k).Contains (fullFactor false 3 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_0_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power3 j i k) (mpower0_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 15 (power3_contains j i k) (mpower0_15_contains j i k)
noncomputable def ha3_0_15 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨46610066605153,46610066605154⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨1527318662517654886,1527318662517654887⟩⟩,⟨⟨(-668803510981146723278),(-668803510981146723232)⟩,⟨(-10),5⟩⟩,⟨⟨(-1003),1475⟩,⟨(-50047177933378515330451),(-50047177933378515325587)⟩⟩,⟨⟨1422426349034211492757614,1422426349034211492914094⟩,⟨(-35869),52629⟩⟩,⟨⟨(-585786),275909⟩,⟨21915353447830215826677206,21915353447830215828585282⟩⟩]
lemma ha3_0_15_eq (j : Fin 7) : ha3_0_15 j = ((ha3_0_14 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha3_0_15_contains (j : Fin 7) : (ha3_0_15 j).Contains (fullFactor false 3 15 ((j.val:ℝ)/6)) := by
  rw [ha3_0_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_0_14 j) false 3 14 j (ha3_0_14_contains j)
noncomputable def hk3_0_16 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_16 j i k)
lemma hk3_0_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_0_16 j i k).Contains (fullFactor false 3 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_0_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power3 j i k) (mpower0_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 16 (power3_contains j i k) (mpower0_16_contains j i k)
noncomputable def ha3_0_16 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨1525310862813,1525310862814⟩⟩,⟨⟨(-99962772705334444),(-99962772705334443)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-65659631149794723626),(-65659631149794723620)⟩⟩,⟨⟨6551160272016798098500,6551160272016798099159⟩,⟨(-132),194⟩⟩,⟨⟨(-8612),5870⟩,⟨232743967104084891362666,232743967104084891389012⟩⟩,⟨⟨(-4303069587032947007543644),(-4303069587032947007155296)⟩,⟨(-115019),54175⟩⟩]
lemma ha3_0_16_eq (j : Fin 7) : ha3_0_16 j = ((ha3_0_15 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha3_0_16_contains (j : Fin 7) : (ha3_0_16 j).Contains (fullFactor false 3 16 ((j.val:ℝ)/6)) := by
  rw [ha3_0_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_0_15 j) false 3 15 j (ha3_0_15_contains j)
noncomputable def hk3_0_17 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_17 j i k)
lemma hk3_0_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_0_17 j i k).Contains (fullFactor false 3 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_0_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power3 j i k) (mpower0_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 17 (power3_contains j i k) (mpower0_17_contains j i k)
noncomputable def ha3_0_17 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-46979464717),(-46979464716)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-6157692399285196),(-6157692399285195)⟩⟩,⟨⟨6066935731106195666,6066935731106195668⟩,⟨(-1),1⟩⟩,⟨⟨(-24),17⟩,⟨807101058159109193385,807101058159109193470⟩⟩,⟨⟨(-35842487118702823488662),(-35842487118702823484490)⟩,⟨(-1327),904⟩⟩,⟨⟨(-10012),21256⟩,⟨(-795205400147551278525611),(-795205400147551278451312)⟩⟩]
lemma ha3_0_17_eq (j : Fin 7) : ha3_0_17 j = ((ha3_0_16 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha3_0_17_contains (j : Fin 7) : (ha3_0_17 j).Contains (fullFactor false 3 17 ((j.val:ℝ)/6)) := by
  rw [ha3_0_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_0_16 j) false 3 16 j (ha3_0_16_contains j)
noncomputable def hk3_0_18 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_18 j i k)
lemma hk3_0_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_0_18 j i k).Contains (fullFactor false 3 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_0_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power3 j i k) (mpower0_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 18 (power3_contains j i k) (mpower0_18_contains j i k)
noncomputable def ha3_0_18 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-1366577234),(-1366577233)⟩⟩,⟨⟨358240022308519,358240022308520⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨529440020073462376,529440020073462377⟩⟩,⟨⟨(-93910472408044662745),(-93910472408044662734)⟩,⟨(-3),2⟩⟩,⟨⟨(-132),194⟩,⟨(-5213078436041832671986),(-5213078436041832671362)⟩⟩,⟨⟨138789524622137721139850,138789524622137721153260⟩,⟨(-1748),3710⟩⟩]
lemma ha3_0_18_eq (j : Fin 7) : ha3_0_18 j = ((ha3_0_17 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha3_0_18_contains (j : Fin 7) : (ha3_0_18 j).Contains (fullFactor false 3 18 ((j.val:ℝ)/6)) := by
  rw [ha3_0_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_0_17 j) false 3 17 j (ha3_0_17_contains j)
noncomputable def hk3_0_19 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_19 j i k)
lemma hk3_0_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_0_19 j i k).Contains (fullFactor false 3 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_0_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power3 j i k) (mpower0_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 19 (power3_contains j i k) (mpower0_19_contains j i k)
noncomputable def ha3_0_19 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨37659903,37659904⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨19744635479057,19744635479058⟩⟩,⟨⟨(-43770654673137423),(-43770654673137422)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-10351875446044213763),(-10351875446044213760)⟩⟩,⟨⟨718305654265631155006,718305654265631155095⟩,⟨(-19),27⟩⟩,⟨⟨(-614),290⟩,⟨22948428997269873109385,22948428997269873111677⟩⟩]
lemma ha3_0_19_eq (j : Fin 7) : ha3_0_19 j = ((ha3_0_18 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha3_0_19_contains (j : Fin 7) : (ha3_0_19 j).Contains (fullFactor false 3 19 ((j.val:ℝ)/6)) := by
  rw [ha3_0_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_0_18 j) false 3 18 j (ha3_0_18_contains j)
noncomputable def hk3_0_20 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_20 j i k)
lemma hk3_0_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_0_20 j i k).Contains (fullFactor false 3 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_0_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power3 j i k) (mpower0_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 20 (power3_contains j i k) (mpower0_20_contains j i k)
noncomputable def ha3_0_20 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨985933,985934⟩⟩,⟨⟨(-1033826696147),(-1033826696146)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-3437739179098608),(-3437739179098606)⟩⟩,⟨⟨1084045861738968866,1084045861738968868⟩,⟨(-1),1⟩⟩,⟨⟨(-4),3⟩,⟨94025990269704865208,94025990269704865221⟩⟩,⟨⟨(-3604730797462500934100),(-3604730797462500933727)⟩,⟨(-97),46⟩⟩]
lemma ha3_0_20_eq (j : Fin 7) : ha3_0_20 j = ((ha3_0_19 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha3_0_20_contains (j : Fin 7) : (ha3_0_20 j).Contains (fullFactor false 3 20 ((j.val:ℝ)/6)) := by
  rw [ha3_0_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_0_19 j) false 3 19 j (ha3_0_19_contains j)
noncomputable def hk3_0_21 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_21 j i k)
lemma hk3_0_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_0_21 j i k).Contains (fullFactor false 3 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_0_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power3 j i k) (mpower0_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 21 (power3_contains j i k) (mpower0_21_contains j i k)
noncomputable def ha3_0_21 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-24583),(-24582)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-51553370694),(-51553370693)⟩⟩,⟨⟨257142289286047,257142289286048⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨108115254456938454,108115254456938455⟩⟩,⟨⟨(-11721879376103578824),(-11721879376103578822)⟩,⟨(-1),1⟩⟩,⟨⟨(-7),15⟩,⟨(-539266466260812848973),(-539266466260812848914)⟩⟩]
lemma ha3_0_21_eq (j : Fin 7) : ha3_0_21 j = ((ha3_0_20 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha3_0_21_contains (j : Fin 7) : (ha3_0_21 j).Contains (fullFactor false 3 21 ((j.val:ℝ)/6)) := by
  rw [ha3_0_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_0_20 j) false 3 20 j (ha3_0_20_contains j)
noncomputable def hk3_0_22 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_22 j i k)
lemma hk3_0_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_0_22 j i k).Contains (fullFactor false 3 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_0_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power3 j i k) (mpower0_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 22 (power3_contains j i k) (mpower0_22_contains j i k)
noncomputable def ha3_0_22 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-586),(-585)⟩⟩,⟨⟨2453934706,2453934707⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨18359916521552,18359916521553⟩⟩,⟨⟨(-10292548155845728),(-10292548155845727)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1394900383872451220),(-1394900383872451219)⟩⟩,⟨⟨77007071306013533794,77007071306013533804⟩,⟨(-1),3⟩⟩]
lemma ha3_0_22_eq (j : Fin 7) : ha3_0_22 j = ((ha3_0_21 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha3_0_22_contains (j : Fin 7) : (ha3_0_22 j).Contains (fullFactor false 3 22 ((j.val:ℝ)/6)) := by
  rw [ha3_0_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_0_21 j) false 3 21 j (ha3_0_21_contains j)
noncomputable def hk3_0_23 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_23 j i k)
lemma hk3_0_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_0_23 j i k).Contains (fullFactor false 3 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_0_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power3 j i k) (mpower0_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 23 (power3_contains j i k) (mpower0_23_contains j i k)
noncomputable def ha3_0_23 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨13,14⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨111728452,111728453⟩⟩,⟨⟨(-1253899540536),(-1253899540535)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-937246193423888),(-937246193423887)⟩⟩,⟨⟨158775681103741857,158775681103741858⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨10518471716932064454,10518471716932064456⟩⟩]
lemma ha3_0_23_eq (j : Fin 7) : ha3_0_23 j = ((ha3_0_22 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha3_0_23_contains (j : Fin 7) : (ha3_0_23 j).Contains (fullFactor false 3 23 ((j.val:ℝ)/6)) := by
  rw [ha3_0_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_0_22 j) false 3 22 j (ha3_0_22_contains j)
noncomputable def hk3_0_24 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_24 j i k)
lemma hk3_0_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_0_24 j i k).Contains (fullFactor false 3 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_0_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power3 j i k) (mpower0_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 24 (power3_contains j i k) (mpower0_24_contains j i k)
noncomputable def ha3_0_24 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨0,1⟩⟩,⟨⟨(-4875074),(-4875073)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-82067533019),(-82067533018)⟩⟩,⟨⟨81790159885152,81790159885153⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨17319740045980249,17319740045980250⟩⟩,⟨⟨(-1376864728037741371),(-1376864728037741370)⟩,⟨(-1),1⟩⟩]
lemma ha3_0_24_eq (j : Fin 7) : ha3_0_24 j = ((ha3_0_23 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha3_0_24_contains (j : Fin 7) : (ha3_0_24 j).Contains (fullFactor false 3 24 ((j.val:ℝ)/6)) := by
  rw [ha3_0_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_0_23 j) false 3 23 j (ha3_0_23_contains j)
noncomputable def hk3_0_25 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_25 j i k)
lemma hk3_0_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_0_25 j i k).Contains (fullFactor false 3 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_0_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power3 j i k) (mpower0_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 25 (power3_contains j i k) (mpower0_25_contains j i k)
noncomputable def ha3_0_25 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-204207),(-204206)⟩⟩,⟨⟨5156455176,5156455177⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨6852036411496,6852036411497⟩⟩,⟨⟨(-1813718936351217),(-1813718936351216)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-173021924583611077),(-173021924583611076)⟩⟩]
lemma ha3_0_25_eq (j : Fin 7) : ha3_0_25 j = ((ha3_0_24 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha3_0_25_contains (j : Fin 7) : (ha3_0_25 j).Contains (fullFactor false 3 25 ((j.val:ℝ)/6)) := by
  rw [ha3_0_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_0_24 j) false 3 24 j (ha3_0_24_contains j)
noncomputable def hk3_0_26 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_26 j i k)
lemma hk3_0_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_0_26 j i k).Contains (fullFactor false 3 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_0_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power3 j i k) (mpower0_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 26 (power3_contains j i k) (mpower0_26_contains j i k)
noncomputable def ha3_0_26 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-1),0⟩⟩,⟨⟨8224,8225⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨311528494,311528495⟩⟩,⟨⟨(-551956596218),(-551956596217)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-182627118144798),(-182627118144797)⟩⟩,⟨⟨20906323353147684,20906323353147685⟩,⟨(-1),1⟩⟩]
lemma ha3_0_26_eq (j : Fin 7) : ha3_0_26 j = ((ha3_0_25 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha3_0_26_contains (j : Fin 7) : (ha3_0_26 j).Contains (fullFactor false 3 26 ((j.val:ℝ)/6)) := by
  rw [ha3_0_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_0_25 j) false 3 25 j (ha3_0_25_contains j)
noncomputable def hk3_0_27 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_27 j i k)
lemma hk3_0_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_0_27 j i k).Contains (fullFactor false 3 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_0_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power3 j i k) (mpower0_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 27 (power3_contains j i k) (mpower0_27_contains j i k)
noncomputable def ha3_0_27 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨318,320⟩⟩,⟨⟨(-18123994),(-18123993)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-42815377477),(-42815377475)⟩⟩,⟨⟨17708025083641,17708025083642⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨2432561179993388,2432561179993389⟩⟩]
lemma ha3_0_27_eq (j : Fin 7) : ha3_0_27 j = ((ha3_0_26 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha3_0_27_contains (j : Fin 7) : (ha3_0_27 j).Contains (fullFactor false 3 27 ((j.val:ℝ)/6)) := by
  rw [ha3_0_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_0_26 j) false 3 26 j (ha3_0_26_contains j)
noncomputable def hk3_0_28 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_28 j i k)
lemma hk3_0_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_0_28 j i k).Contains (fullFactor false 3 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_0_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power3 j i k) (mpower0_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 28 (power3_contains j i k) (mpower0_28_contains j i k)
noncomputable def ha3_0_28 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨0,1⟩⟩,⟨⟨(-12),(-11)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1016754),(-1016753)⟩⟩,⟨⟨3202582746,3202582747⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨1655696473581,1655696473582⟩⟩,⟨⟨(-272932726159820),(-272932726159819)⟩,⟨(-1),1⟩⟩]
lemma ha3_0_28_eq (j : Fin 7) : ha3_0_28 j = ((ha3_0_27 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha3_0_28_contains (j : Fin 7) : (ha3_0_28 j).Contains (fullFactor false 3 28 ((j.val:ℝ)/6)) := by
  rw [ha3_0_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_0_27 j) false 3 27 j (ha3_0_27_contains j)
noncomputable def hk3_0_29 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_29 j i k)
lemma hk3_0_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_0_29 j i k).Contains (fullFactor false 3 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_0_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power3 j i k) (mpower0_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 29 (power3_contains j i k) (mpower0_29_contains j i k)
noncomputable def ha3_0_29 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),0⟩⟩,⟨⟨55072,55073⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨231292193,231292194⟩⟩,⟨⟨(-149469076954),(-149469076953)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-29567015428550),(-29567015428549)⟩⟩]
lemma ha3_0_29_eq (j : Fin 7) : ha3_0_29 j = ((ha3_0_28 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha3_0_29_contains (j : Fin 7) : (ha3_0_29 j).Contains (fullFactor false 3 29 ((j.val:ℝ)/6)) := by
  rw [ha3_0_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_0_28 j) false 3 28 j (ha3_0_28_contains j)
noncomputable def hk3_0_30 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_30 j i k)
lemma hk3_0_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_0_30 j i k).Contains (fullFactor false 3 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_0_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power3 j i k) (mpower0_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 30 (power3_contains j i k) (mpower0_30_contains j i k)
noncomputable def ha3_0_30 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-1),0⟩⟩,⟨⟨0,1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨2883,2884⟩⟩,⟨⟨(-16147242),(-16147241)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-13043637614),(-13043637613)⟩⟩,⟨⟨3096250615296,3096250615297⟩,⟨(-1),1⟩⟩]
lemma ha3_0_30_eq (j : Fin 7) : ha3_0_30 j = ((ha3_0_29 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha3_0_30_contains (j : Fin 7) : (ha3_0_30 j).Contains (fullFactor false 3 30 ((j.val:ℝ)/6)) := by
  rw [ha3_0_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_0_29 j) false 3 29 j (ha3_0_29_contains j)
noncomputable def hk3_1_0 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_0 j i k)
lemma hk3_1_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_1_0 j i k).Contains (fullFactor true 3 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_1_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel3_0 j i k) (mpower1_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 0 (kernel3_0_contains j i k) (mpower1_0_contains j i k)
noncomputable def ha3_1_0 : Fin 7 → CBox := ![⟨⟨2843789610077025929,2843789610077025936⟩,⟨(-3),3⟩⟩,⟨⟨(-64228312723007910724),(-64228312723007910558)⟩,⟨266166603357464236131,266166603357464236302⟩⟩,⟨⟨(-494776904616736031147973),(-494776904616736030744849)⟩,⟨(-695181898442626142129027),(-695181898442626141728600)⟩⟩,⟨⟨(-106555917680778035558591732),(-106555917680778035421458844)⟩,⟨(-354976034124043666142003790),(-354976034124043666003755425)⟩⟩,⟨⟨15213751127784570539427089845,15213751127784570544253007311⟩,⟨(-4099688160756901354180537737),(-4099688160756901349483904669)⟩⟩,⟨⟨20629052952773211972690043554,20629052952773211997040008897⟩,⟨149592350264871972775750070482,149592350264871972801712808839⟩⟩,⟨⟨(-595922937275834702091915645087),(-595922937275834701979420127280)⟩,⟨132015435447815391188745737182,132015435447815391291484111950⟩⟩]
lemma ha3_1_0_eq (j : Fin 7) : ha3_1_0 j = atomKernel3_0 j := by fin_cases j <;> decide +kernel
lemma ha3_1_0_contains (j : Fin 7) : (ha3_1_0 j).Contains (fullFactor true 3 0 ((j.val:ℝ)/6)) := by
  rw [ha3_1_0_eq]
  simpa only [fullFactor,ite_true] using atomKernel3_0_contains j
noncomputable def hk3_1_1 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_1 j i k)
lemma hk3_1_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_1_1 j i k).Contains (fullFactor true 3 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_1_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel3_0 j i k) (mpower1_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 1 (kernel3_0_contains j i k) (mpower1_1_contains j i k)
noncomputable def ha3_1_1 : Fin 7 → CBox := ![⟨⟨(-26206483738960704163),(-26206483738960704098)⟩,⟨(-28),28⟩⟩,⟨⟨1481959463502825266027,1481959463502825267941⟩,⟨(-1801702358473668140785),(-1801702358473668138848)⟩⟩,⟨⟨(-1144235911228454129864486),(-1144235911228454125798275)⟩,⟨5970935715710382851586040,5970935715710382855652717⟩⟩,⟨⟨(-1511765319270662542217988349),(-1511765319270662541116960688)⟩,⟨1548895291282867661132607122,1548895291282867662229291849⟩⟩,⟨⟨(-41994771009654300602998834631),(-41994771009654300573853781897)⟩,⟨(-64074876924145524496005170041),(-64074876924145524466348903640)⟩⟩,⟨⟨596599890019863798301114245875,596599890019863798426321053128⟩,⟨(-189634434098775036919004515716),(-189634434098775036800638386208)⟩⟩,⟨⟨588609623562744722558957134694,588609623562744722952945344464⟩,⟨2127104262412552993036337815244,2127104262412552993468782183206⟩⟩]
lemma ha3_1_1_eq (j : Fin 7) : ha3_1_1 j = ((ha3_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha3_1_1_contains (j : Fin 7) : (ha3_1_1 j).Contains (fullFactor true 3 1 ((j.val:ℝ)/6)) := by
  rw [ha3_1_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_1_0 j) true 3 0 j (ha3_1_0_contains j)
noncomputable def hk3_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_2 j i k)
lemma hk3_1_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_1_2 j i k).Contains (fullFactor true 3 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_1_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel3_0 j i k) (mpower1_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 2 (kernel3_0_contains j i k) (mpower1_2_contains j i k)
noncomputable def ha3_1_2 : Fin 7 → CBox := ![⟨⟨120750808626417676319,120750808626417676620⟩,⟨(-130),130⟩⟩,⟨⟨(-9029760369223308801402),(-9029760369223308790435)⟩,⟨4151272276095303051415,4151272276095303062429⟩⟩,⟨⟨18192461552773175521159842,18192461552773175541699841⟩,⟨(-11752591593888755694446934),(-11752591593888755673908729)⟩⟩,⟨⟨6095234490319404936856610149,6095234490319404941235045892⟩,⟨1669583651340407660105761894,1669583651340407664489010242⟩⟩,⟨⟨(-116194095883841057874140715987),(-116194095883841057782979908570)⟩,⟨145555833407333191032293738274,145555833407333191122551878647⟩⟩,⟨⟨(-597450555008754758946733123985),(-597450555008754758658959147301)⟩,⟨(-1151863340061965034546216729911),(-1151863340061965034244688731333)⟩⟩,⟨⟨3785251837595132000167293885354,3785251837595132000997468709104⟩,⟨(-1262449089469047539803437474687),(-1262449089469047539047467367527)⟩⟩]
lemma ha3_1_2_eq (j : Fin 7) : ha3_1_2 j = ((ha3_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha3_1_2_contains (j : Fin 7) : (ha3_1_2 j).Contains (fullFactor true 3 2 ((j.val:ℝ)/6)) := by
  rw [ha3_1_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_1_1 j) true 3 1 j (ha3_1_1_contains j)
noncomputable def hk3_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_3 j i k)
lemma hk3_1_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_1_3 j i k).Contains (fullFactor true 3 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_1_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel3_0 j i k) (mpower1_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 3 (kernel3_0_contains j i k) (mpower1_3_contains j i k)
noncomputable def ha3_1_3 : Fin 7 → CBox := ![⟨⟨(-370919856555874564935),(-370919856555874564008)⟩,⟨(-400),400⟩⟩,⟨⟨28219356825619465215280,28219356825619465257046⟩,⟨582262826925070975078,582262826925071016885⟩⟩,⟨⟨(-50033012907132862185474099),(-50033012907132862116346675)⟩,⟨(-11943174749198354387362816),(-11943174749198354318233708)⟩⟩,⟨⟨(-2906911861877585082538948334),(-2906911861877585070917669660)⟩,⟨(-11953689949653953915471739766),(-11953689949653953903843417613)⟩⟩,⟨⟨282847283740151868944126237442,282847283740151869130070818815⟩,⟨105415498583111998387838487021,105415498583111998574620497262⟩⟩,⟨⟨(-1428305101584093675146921370367),(-1428305101584093674663311395541)⟩,⟨1084008512647987889141524443258,1084008512647987889607644807910⟩⟩,⟨⟨(-1756501989266606212111809624477),(-1756501989266606211144314354171)⟩,⟨(-4477196216151633520338424332317),(-4477196216151633519277091946707)⟩⟩]
lemma ha3_1_3_eq (j : Fin 7) : ha3_1_3 j = ((ha3_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha3_1_3_contains (j : Fin 7) : (ha3_1_3 j).Contains (fullFactor true 3 3 ((j.val:ℝ)/6)) := by
  rw [ha3_1_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_1_2 j) true 3 2 j (ha3_1_2_contains j)
noncomputable def hk3_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_4 j i k)
lemma hk3_1_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_1_4 j i k).Contains (fullFactor true 3 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_1_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel3_0 j i k) (mpower1_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 4 (kernel3_0_contains j i k) (mpower1_4_contains j i k)
noncomputable def ha3_1_4 : Fin 7 → CBox := ![⟨⟨854538004046111320968,854538004046111323107⟩,⟨(-922),922⟩⟩,⟨⟨(-53542824396151617786868),(-53542824396151617667788)⟩,⟨(-27344852589898870700217),(-27344852589898870581184)⟩⟩,⟨⟨46207659229019142777133640,46207659229019142951472970⟩,⟨79120094211605436628852890,79120094211605436803198994⟩⟩,⟨⟨(-13209069949135841248572051687),(-13209069949135841225444711046)⟩,⟨12169528837008859704904165572,12169528837008859728011092553⟩⟩,⟨⟨14601001747881748835674117471,14601001747881749122578552835⟩,⟨(-366623362878199169140262737704),(-366623362878199168853569918729)⟩⟩,⟨⟨1358614539966023619922958117441,1358614539966023620488494876950⟩,⟨1267894129398617422807690583816,1267894129398617423388936729416⟩⟩,⟨⟨(-3959361961659830116318546932967),(-3959361961659830115301876782785)⟩,⟨1795868142541842386257516117400,1795868142541842387186467682020⟩⟩]
lemma ha3_1_4_eq (j : Fin 7) : ha3_1_4 j = ((ha3_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha3_1_4_contains (j : Fin 7) : (ha3_1_4 j).Contains (fullFactor true 3 4 ((j.val:ℝ)/6)) := by
  rw [ha3_1_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_1_3 j) true 3 3 j (ha3_1_3_contains j)
noncomputable def hk3_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_5 j i k)
lemma hk3_1_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_1_5 j i k).Contains (fullFactor true 3 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_1_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel3_0 j i k) (mpower1_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 5 (kernel3_0_contains j i k) (mpower1_5_contains j i k)
noncomputable def ha3_1_5 : Fin 7 → CBox := ![⟨⟨(-1574971385225068361048),(-1574971385225068357100)⟩,⟨(-1700),1700⟩⟩,⟨⟨61761444652058965354257,61761444652058965625672⟩,⟨81739341030025490402813,81739341030025490674126⟩⟩,⟨⟨35995000732812252235811489,35995000732812252587471033⟩,⟨(-125505564853774618569211161),(-125505564853774618217556672)⟩⟩,⟨⟨19909374592707441908303938160,19909374592707441945064662786⟩,⟨6607204548875766574484640343,6607204548875766611256174386⟩⟩,⟨⟨(-343184339586920015031767115579),(-343184339586920014678818682920)⟩,⟨97621721937127819222573225451,97621721937127819574957294500⟩⟩,⟨⟨844568760031360187920906616874,844568760031360188479387891880⟩,⟨(-1288665363940605269991255001902),(-1288665363940605269443201118368)⟩⟩,⟨⟨1445677859979626714395123163559,1445677859979626715108799269612⟩,⟨2792028591070177955378015769649,2792028591070177956156463376867⟩⟩]
lemma ha3_1_5_eq (j : Fin 7) : ha3_1_5 j = ((ha3_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha3_1_5_contains (j : Fin 7) : (ha3_1_5 j).Contains (fullFactor true 3 5 ((j.val:ℝ)/6)) := by
  rw [ha3_1_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_1_4 j) true 3 4 j (ha3_1_4_contains j)
noncomputable def hk3_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_6 j i k)
lemma hk3_1_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_1_6 j i k).Contains (fullFactor true 3 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_1_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel3_0 j i k) (mpower1_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 6 (kernel3_0_contains j i k) (mpower1_6_contains j i k)
noncomputable def ha3_1_6 : Fin 7 → CBox := ![⟨⟨2418982394124860654865,2418982394124860660938⟩,⟨(-2612),2612⟩⟩,⟨⟨(-28263649891130446354299),(-28263649891130445838980)⟩,⟨(-142708838973634928534757),(-142708838973634928019463)⟩⟩,⟨⟨(-137265955924376708935678431),(-137265955924376708344827217)⟩,⟨72092100217979848669426233,72092100217979849260266877⟩⟩,⟨⟨(-3765304345590307725836956954),(-3765304345590307677143874998)⟩,⟨(-20066830200117961788487451699),(-20066830200117961739782396285)⟩⟩,⟨⟨161842984238362614426573738464,161842984238362614787564447057⟩,⟨239596039109724466649996021379,239596039109724467011683209672⟩⟩,⟨⟨(-976568923007012275590989366915),(-976568923007012275149163595753)⟩,⟨(-423783317117408079278614062021),(-423783317117408078831709034797)⟩⟩,⟨⟨1635104693718682526110046500828,1635104693718682526606373217741⟩,⟨(-957441494809575308766832453610),(-957441494809575308309905702636)⟩⟩]
lemma ha3_1_6_eq (j : Fin 7) : ha3_1_6 j = ((ha3_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha3_1_6_contains (j : Fin 7) : (ha3_1_6 j).Contains (fullFactor true 3 6 ((j.val:ℝ)/6)) := by
  rw [ha3_1_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_1_5 j) true 3 5 j (ha3_1_5_contains j)
noncomputable def hk3_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_7 j i k)
lemma hk3_1_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_1_7 j i k).Contains (fullFactor true 3 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_1_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel3_0 j i k) (mpower1_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 7 (kernel3_0_contains j i k) (mpower1_7_contains j i k)
noncomputable def ha3_1_7 : Fin 7 → CBox := ![⟨⟨(-3184534495390584108493),(-3184534495390584100487)⟩,⟨(-3439),3439⟩⟩,⟨⟨(-44842287769613143438356),(-44842287769613142599966)⟩,⟨171302722500924379018174,171302722500924379856755⟩⟩,⟨⟨149588629396484016330390763,149588629396484017181152880⟩,⟨50284543990658276481062411,50284543990658277331831586⟩⟩,⟨⟨(-13121605405062001229866909567),(-13121605405062001174586892519)⟩,⟨10860444409204354507347261159,10860444409204354562606492744⟩⟩,⟨⟨123097328729395898963207508004,123097328729395899280682454999⟩,⟨(-158683749072160228782744283511),(-158683749072160228465688007489)⟩⟩,⟨⟨(-149068270729794245227005959192),(-149068270729794244920631725921)⟩,⟨612577982474023366463322154728,612577982474023366768092984496⟩⟩,⟨⟨(-537767894385041978033484919263),(-537767894385041977782748675484)⟩,⟨(-817803374874768601964218239493),(-817803374874768601693159105532)⟩⟩]
lemma ha3_1_7_eq (j : Fin 7) : ha3_1_7 j = ((ha3_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha3_1_7_contains (j : Fin 7) : (ha3_1_7 j).Contains (fullFactor true 3 7 ((j.val:ℝ)/6)) := by
  rw [ha3_1_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_1_6 j) true 3 6 j (ha3_1_6_contains j)
noncomputable def hk3_1_8 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_8 j i k)
lemma hk3_1_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_1_8 j i k).Contains (fullFactor true 3 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_1_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel3_0 j i k) (mpower1_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 8 (kernel3_0_contains j i k) (mpower1_8_contains j i k)
noncomputable def ha3_1_8 : Fin 7 → CBox := ![⟨⟨3668320397801524039113,3668320397801524048348⟩,⟨(-3962),3962⟩⟩,⟨⟨122581376141489953640518,122581376141489954834037⟩,⟨(-143316076404219185886973),(-143316076404219184693162)⟩⟩,⟨⟨(-59691667512049772956055205),(-59691667512049771884364588)⟩,⟨(-127247798521958596487309881),(-127247798521958595415610510)⟩⟩,⟨⟨11576522328530066732551375888,11576522328530066787428403492⟩,⟨4536740237904876153081145432,4536740237904876207966142210⟩⟩,⟨⟨(-114956692278342366342945074639),(-114956692278342366099343621049)⟩,⟨(-41030735644269367429114276114),(-41030735644269367185394304768)⟩⟩,⟨⟨325943992374629027794416535870,325943992374629027978061545226⟩,⟨22193282155358369897270882663,22193282155358370080969990522⟩⟩,⟨⟨(-356516349991094073503536843378),(-356516349991094073374086263441)⟩,⟨261931943996415281708389802370,261931943996415281828762656123⟩⟩]
lemma ha3_1_8_eq (j : Fin 7) : ha3_1_8 j = ((ha3_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha3_1_8_contains (j : Fin 7) : (ha3_1_8 j).Contains (fullFactor true 3 8 ((j.val:ℝ)/6)) := by
  rw [ha3_1_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_1_7 j) true 3 7 j (ha3_1_7_contains j)
noncomputable def hk3_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_9 j i k)
lemma hk3_1_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_1_9 j i k).Contains (fullFactor true 3 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_1_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel3_0 j i k) (mpower1_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 9 (kernel3_0_contains j i k) (mpower1_9_contains j i k)
noncomputable def ha3_1_9 : Fin 7 → CBox := ![⟨⟨(-3756090445636012283445),(-3756090445636012273976)⟩,⟨(-4057),4057⟩⟩,⟨⟨(-163618472166411634981019),(-163618472166411633470696)⟩,⟨71439268931558071404523,71439268931558072915004⟩⟩,⟨⟨(-40161207407591968489125034),(-40161207407591967289241337)⟩,⟨103770160328136386133931848,103770160328136387333809911⟩⟩,⟨⟨(-1065163449529194018662091281),(-1065163449529193970234610558)⟩,⟨(-7997227145816584795249382252),(-7997227145816584746818246350)⟩⟩,⟨⟨(-1706798838274707418035230471),(-1706798838274707251781390444)⟩,⟨65919429617459010688062748569,65919429617459010854356878406⟩⟩,⟨⟨(-15433096438910464651661251811),(-15433096438910464553791622158)⟩,⟨(-149689837913799218231569500343),(-149689837913799218133356974324)⟩⟩,⟨⟨112531926767879715029905856548,112531926767879715081261487777⟩,⟨137578442595745575518857433449,137578442595745575573780397389⟩⟩]
lemma ha3_1_9_eq (j : Fin 7) : ha3_1_9 j = ((ha3_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha3_1_9_contains (j : Fin 7) : (ha3_1_9 j).Contains (fullFactor true 3 9 ((j.val:ℝ)/6)) := by
  rw [ha3_1_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_1_8 j) true 3 8 j (ha3_1_8_contains j)
noncomputable def hk3_1_10 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_10 j i k)
lemma hk3_1_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_1_10 j i k).Contains (fullFactor true 3 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_1_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel3_0 j i k) (mpower1_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 10 (kernel3_0_contains j i k) (mpower1_10_contains j i k)
noncomputable def ha3_1_10 : Fin 7 → CBox := ![⟨⟨3461364470733813253872,3461364470733813262610⟩,⟨(-3739),3739⟩⟩,⟨⟨151993806312621580441974,151993806312621582161883⟩,⟨6064091613144275728809,6064091613144277448664⟩⟩,⟨⟨73216760773287174458314254,73216760773287175667270901⟩,⟨(-30408075732848886668724391),(-30408075732848885459772204)⟩⟩,⟨⟨(-3783768210465414114604028347),(-3783768210465414076145164700)⟩,⟨2807320701760530463468918831,2807320701760530501921922566⟩⟩,⟨⟨30713346130859398550142375383,30713346130859398652261230318⟩,⟨(-9200604108213715811667310682),(-9200604108213715709624421441)⟩⟩,⟨⟨(-60065769427074819595477572685),(-60065769427074819548263725933)⟩,⟨16847607457877419564652890205,16847607457877419611606316515⟩⟩,⟨⟨47566884124235523831054904958,47566884124235523852016914349⟩,⟨(-43218928333900428367791674571),(-43218928333900428348078145374)⟩⟩]
lemma ha3_1_10_eq (j : Fin 7) : ha3_1_10 j = ((ha3_1_9 j).mul (piI.mul (atomPoints j).z)).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha3_1_10_contains (j : Fin 7) : (ha3_1_10 j).Contains (fullFactor true 3 10 ((j.val:ℝ)/6)) := by
  rw [ha3_1_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_1_9 j) true 3 9 j (ha3_1_9_contains j)
noncomputable def hk3_1_11 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_11 j i k)
lemma hk3_1_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_1_11 j i k).Contains (fullFactor true 3 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_1_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel3_0 j i k) (mpower1_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 11 (kernel3_0_contains j i k) (mpower1_11_contains j i k)
noncomputable def ha3_1_11 : Fin 7 → CBox := ![⟨⟨(-2899785918041085500056),(-2899785918041085492726)⟩,⟨(-3133),3133⟩⟩,⟨⟨(-103879452147605481309944),(-103879452147605479529654)⟩,⟨(-55598234833680371752263),(-55598234833680369972159)⟩⟩,⟨⟨(-47008385489636431563930734),(-47008385489636430456632001)⟩,⟨(-20669263945677123543828760),(-20669263945677122436527128)⟩⟩,⟨⟨2277145373785598421977450076,2277145373785598449736229616⟩,⟨1034897062735591089332585875,1034897062735591117093222854⟩⟩,⟨⟨(-8095305358091592468200683278),(-8095305358091592411249141300)⟩,⟨(-11632102952096796699968609677),(-11632102952096796642976300236)⟩⟩,⟨⟨10102917087844958614064747119,10102917087844958634557959939⟩,⟨21229145008548126990987942878,21229145008548127011603482450⟩⟩,⟨⟨(-14999678995108236494734330411),(-14999678995108236487857296399)⟩,⟨(-14877263092566918442879253088),(-14877263092566918435609378994)⟩⟩]
lemma ha3_1_11_eq (j : Fin 7) : ha3_1_11 j = ((ha3_1_10 j).mul (piI.mul (atomPoints j).z)).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha3_1_11_contains (j : Fin 7) : (ha3_1_11 j).Contains (fullFactor true 3 11 ((j.val:ℝ)/6)) := by
  rw [ha3_1_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_1_10 j) true 3 10 j (ha3_1_10_contains j)
noncomputable def hk3_1_12 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_12 j i k)
lemma hk3_1_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_1_12 j i k).Contains (fullFactor true 3 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_1_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel3_0 j i k) (mpower1_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 12 (kernel3_0_contains j i k) (mpower1_12_contains j i k)
noncomputable def ha3_1_12 : Fin 7 → CBox := ![⟨⟨2226875722402468735530,2226875722402468741167⟩,⟨(-2406),2406⟩⟩,⟨⟨49138101638723075304389,49138101638723076993514⟩,⟨67703184449361513725729,67703184449361515414742⟩⟩,⟨⟨10416505192624511164025872,10416505192624512093666084⟩,⟨28655531739954259670075278,28655531739954260599717018⟩⟩,⟨⟨(-96479023142334125828825891),(-96479023142334107461870268)⟩,⟨(-1213420302535277861642897746),(-1213420302535277843275544037)⟩⟩,⟨⟨(-3456076394127468888667737295),(-3456076394127468859516416542)⟩,⟨4585583800566406675351941947,4585583800566406704489802710⟩⟩,⟨⟨6634317217499993090625137840,6634317217499993098871201700⟩,⟨(-4685433409790482367676713463),(-4685433409790482359475093471)⟩⟩,⟨⟨(-4242137031378780300482073434),(-4242137031378780298171823705)⟩,⟨4746482084288119683033101867,4746482084288119685231396851⟩⟩]
lemma ha3_1_12_eq (j : Fin 7) : ha3_1_12 j = ((ha3_1_11 j).mul (piI.mul (atomPoints j).z)).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha3_1_12_contains (j : Fin 7) : (ha3_1_12 j).Contains (fullFactor true 3 12 ((j.val:ℝ)/6)) := by
  rw [ha3_1_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_1_11 j) true 3 11 j (ha3_1_11_contains j)
noncomputable def hk3_1_13 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_13 j i k)
lemma hk3_1_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_1_13 j i k).Contains (fullFactor true 3 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_1_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel3_0 j i k) (mpower1_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 13 (kernel3_0_contains j i k) (mpower1_13_contains j i k)
noncomputable def ha3_1_13 : Fin 7 → CBox := ![⟨⟨(-1578570266862105744683),(-1578570266862105740681)⟩,⟨(-1706),1706⟩⟩,⟨⟨(-9614841064523069425147),(-9614841064523067945859)⟩,⟨(-53978215217868471956531),(-53978215217868470477259)⟩⟩,⟨⟨7407246673650242969197333,7407246673650243689624626⟩,⟨(-14979491530419265575087743),(-14979491530419264854661489)⟩⟩,⟨⟨(-455804394286304355592051046),(-455804394286304344374785352)⟩,⟨302062019893804364389607721,302062019893804375606180565⟩⟩,⟨⟨2032502715064658520698756797,2032502715064658534458399075⟩,⟨693710891097758926792548923,693710891097758940554547057⟩⟩,⟨⟨(-1831843506241165918728304431),(-1831843506241165915698335800)⟩,⟨(-1831013499650748005568733992),(-1831013499650748002525593188)⟩⟩,⟨⟨1379710053592110315745319225,1379710053592110316393703577⟩,⟨1109784955304000336030279833,1109784955304000336707722167⟩⟩]
lemma ha3_1_13_eq (j : Fin 7) : ha3_1_13 j = ((ha3_1_12 j).mul (piI.mul (atomPoints j).z)).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha3_1_13_contains (j : Fin 7) : (ha3_1_13 j).Contains (fullFactor true 3 13 ((j.val:ℝ)/6)) := by
  rw [ha3_1_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_1_12 j) true 3 12 j (ha3_1_12_contains j)
noncomputable def hk3_1_14 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_14 j i k)
lemma hk3_1_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_1_14 j i k).Contains (fullFactor true 3 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_1_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel3_0 j i k) (mpower1_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 14 (kernel3_0_contains j i k) (mpower1_14_contains j i k)
noncomputable def ha3_1_14 : Fin 7 → CBox := ![⟨⟨1039075662648418649856,1039075662648418652495⟩,⟨(-1123),1123⟩⟩,⟨⟨(-9069566323206616292811),(-9069566323206615089869)⟩,⟨32111145546080576779888,32111145546080577982864⟩⟩,⟨⟨(-8115469321250466293627589),(-8115469321250465775218828)⟩,⟨2543125591236969860587000,2543125591236970378995387⟩⟩,⟨⟨202352739219885546629763914,202352739219885552990559811⟩,⟨105253218446981810156844506,105253218446981816517832793⟩⟩,⟨⟨8926479309670190361917610,8926479309670196394135534⟩,⟨(-745811418792236046885247409),(-745811418792236040852606888)⟩⟩,⟨⟨(-442146827715742761173214737),(-442146827715742760130781141)⟩,⟨626658217845702091751473681,626658217845702092790726842⟩⟩,⟨⟨267742113324152619713965192,267742113324152619898364623⟩,⟨(-370754069466882180912570487),(-370754069466882180735066168)⟩⟩]
lemma ha3_1_14_eq (j : Fin 7) : ha3_1_14 j = ((ha3_1_13 j).mul (piI.mul (atomPoints j).z)).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha3_1_14_contains (j : Fin 7) : (ha3_1_14 j).Contains (fullFactor true 3 14 ((j.val:ℝ)/6)) := by
  rw [ha3_1_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_1_13 j) true 3 13 j (ha3_1_13_contains j)
noncomputable def hk3_1_15 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_15 j i k)
lemma hk3_1_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_1_15 j i k).Contains (fullFactor true 3 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_1_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel3_0 j i k) (mpower1_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 15 (kernel3_0_contains j i k) (mpower1_15_contains j i k)
noncomputable def ha3_1_15 : Fin 7 → CBox := ![⟨⟨(-638362260467598257230),(-638362260467598255606)⟩,⟨(-690),690⟩⟩,⟨⟨12594277203327832603170,12594277203327833516179⟩,⟨(-14163468526568395436742),(-14163468526568394523704)⟩⟩,⟨⟨3536957543984352498775239,3536957543984352846939226⟩,⟨1951647056958397712400542,1951647056958398060564802⟩⟩,⟨⟨(-2332849334198170030744114),(-2332849334198166664196029)⟩,⟨(-88769326366413923146835002),(-88769326366413919780269194)⟩⟩,⟨⟨(-230611166364566750656170371),(-230611166364566748187990018)⟩,⟨72595327385234273425405295,72595327385234275893012704⟩⟩,⟨⟨191432704847570100193564335,191432704847570100526163556⟩,⟨90996142957706596584289817,90996142957706596917473525⟩⟩,⟨⟨(-92605162226208172070618105),(-92605162226208172025283465)⟩,⟨(-59813733847327859456059288),(-59813733847327859409225899)⟩⟩]
lemma ha3_1_15_eq (j : Fin 7) : ha3_1_15 j = ((ha3_1_14 j).mul (piI.mul (atomPoints j).z)).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha3_1_15_contains (j : Fin 7) : (ha3_1_15 j).Contains (fullFactor true 3 15 ((j.val:ℝ)/6)) := by
  rw [ha3_1_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_1_14 j) true 3 14 j (ha3_1_14_contains j)
noncomputable def hk3_1_16 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_16 j i k)
lemma hk3_1_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_1_16 j i k).Contains (fullFactor true 3 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_1_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel3_0 j i k) (mpower1_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 16 (kernel3_0_contains j i k) (mpower1_16_contains j i k)
noncomputable def ha3_1_16 : Fin 7 → CBox := ![⟨⟨367670267765896474367,367670267765896475305⟩,⟨(-398),398⟩⟩,⟨⟨(-9325526897392541809657),(-9325526897392541160009)⟩,⟨3859789291662485272653,3859789291662485922310⟩⟩,⟨⟨(-460193224068138040751323),(-460193224068137821539611)⟩,⟨(-1739055693677571379710674),(-1739055693677571160498895)⟩⟩,⟨⟨(-27928544090028747941581625),(-27928544090028746271199325)⟩,⟨16445808491038470657308358,16445808491038472327648957⟩⟩,⟨⟨42802984256878160534690507,42802984256878161481107542⟩,⟨59713331195369669078048927,59713331195369670024674733⟩⟩,⟨⟨14807447754050061937031786,14807447754050062036845403⟩,⟨(-52884269536544138293203223),(-52884269536544138193445559)⟩⟩,⟨⟨(-12412510529967984103305619),(-12412510529967984092157362)⟩,⟨21601942345542436398384093,21601942345542436409234019⟩⟩]
lemma ha3_1_16_eq (j : Fin 7) : ha3_1_16 j = ((ha3_1_15 j).mul (piI.mul (atomPoints j).z)).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha3_1_16_contains (j : Fin 7) : (ha3_1_16 j).Contains (fullFactor true 3 16 ((j.val:ℝ)/6)) := by
  rw [ha3_1_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_1_15 j) true 3 15 j (ha3_1_15_contains j)
noncomputable def hk3_1_17 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_17 j i k)
lemma hk3_1_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_1_17 j i k).Contains (fullFactor true 3 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_1_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel3_0 j i k) (mpower1_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 17 (kernel3_0_contains j i k) (mpower1_17_contains j i k)
noncomputable def ha3_1_17 : Fin 7 → CBox := ![⟨⟨(-199306232685867573579),(-199306232685867573069)⟩,⟨(-216),216⟩⟩,⟨⟨5049517138014745256212,5049517138014745691269⟩,⟨298881344460001522814,298881344460001957870⟩⟩,⟨⟨(-393565813323348531640146),(-393565813323348401739647)⟩,⟨643081431184360712450030,643081431184360842350473⟩⟩,⟨⟨9591014011461214219169395,9591014011461214999184030⟩,⟨5654435933845688442694937,5654435933845689222720059⟩⟩,⟨⟨12412539203443044334860277,12412539203443044676545264⟩,⟨(-16955076870889724429687271),(-16955076870889724088050242)⟩⟩,⟨⟨(-13322168051426541533206045),(-13322168051426541505055472)⟩,⟨(-1367420602068309155788921),(-1367420602068309127651326)⟩⟩,⟨⟨4725642060479456406920388,4725642060479456409363238⟩,⟨2397978209465855166268376,2397978209465855168765409⟩⟩]
lemma ha3_1_17_eq (j : Fin 7) : ha3_1_17 j = ((ha3_1_16 j).mul (piI.mul (atomPoints j).z)).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha3_1_17_contains (j : Fin 7) : (ha3_1_17 j).Contains (fullFactor true 3 17 ((j.val:ℝ)/6)) := by
  rw [ha3_1_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_1_16 j) true 3 16 j (ha3_1_16_contains j)
noncomputable def hk3_1_18 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_18 j i k)
lemma hk3_1_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_1_18 j i k).Contains (fullFactor true 3 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_1_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel3_0 j i k) (mpower1_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 18 (kernel3_0_contains j i k) (mpower1_18_contains j i k)
noncomputable def ha3_1_18 : Fin 7 → CBox := ![⟨⟨102037466083353695140,102037466083353695402⟩,⟨(-111),111⟩⟩,⟨⟨(-2088864369655679407735),(-2088864369655679132576)⟩,⟨(-1170260917166284316542),(-1170260917166284041387)⟩⟩,⟨⟨291650340175275889338141,291650340175275962037847⟩,⟨(-63295376724394149588670),(-63295376724394076888973)⟩⟩,⟨⟨96777562415753775675586,96777562415754119686550⟩,⟨(-3610865294573012533501906),(-3610865294573012189490683)⟩⟩,⟨⟨(-5396760743961361497734813),(-5396760743961361381265749)⟩,⟨(-1758489545266251117152814),(-1758489545266251000677972)⟩⟩,⟨⟨210919560792516622988659,210919560792516630478918⟩,⟨3077115643456388264269568,3077115643456388271769412⟩⟩,⟨⟨431767338603453570175169,431767338603453570703277⟩,⟨(-973038496709205821908517),(-973038496709205821389304)⟩⟩]
lemma ha3_1_18_eq (j : Fin 7) : ha3_1_18 j = ((ha3_1_17 j).mul (piI.mul (atomPoints j).z)).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha3_1_18_contains (j : Fin 7) : (ha3_1_18 j).Contains (fullFactor true 3 18 ((j.val:ℝ)/6)) := by
  rw [ha3_1_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_1_17 j) true 3 17 j (ha3_1_17_contains j)
noncomputable def hk3_1_19 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_19 j i k)
lemma hk3_1_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_1_19 j i k).Contains (fullFactor true 3 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_1_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel3_0 j i k) (mpower1_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 19 (kernel3_0_contains j i k) (mpower1_19_contains j i k)
noncomputable def ha3_1_19 : Fin 7 → CBox := ![⟨⟨(-49489988662767695286),(-49489988662767695157)⟩,⟨(-54),54⟩⟩,⟨⟨613834020265220558210,613834020265220723079⟩,⟨880926135818806326797,880926135818806491664⟩⟩,⟨⟨(-92733391520815811609945),(-92733391520815773064661)⟩,⟨(-62652942223562785365287),(-62652942223562746819994)⟩⟩,⟨⟨(-985220680253667520803636),(-985220680253667377071413)⟩,⟨511807199641042083412144,511807199641042227142995⟩⟩,⟨⟨2832291368408028393688,2832291368408066007191⟩,⟨1452511306260736425029294,1452511306260736462643745⟩⟩,⟨⟨653809296793516555818585,653809296793516557710954⟩,⟨(-159415625966559743788309),(-159415625966559741899269)⟩⟩,⟨⟨(-189196934184546992764988),(-189196934184546992660487)⟩,⟨(-72442757905910358138011),(-72442757905910358032218)⟩⟩]
lemma ha3_1_19_eq (j : Fin 7) : ha3_1_19 j = ((ha3_1_18 j).mul (piI.mul (atomPoints j).z)).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha3_1_19_contains (j : Fin 7) : (ha3_1_19 j).Contains (fullFactor true 3 19 ((j.val:ℝ)/6)) := by
  rw [ha3_1_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_1_18 j) true 3 18 j (ha3_1_18_contains j)
noncomputable def hk3_1_20 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_20 j i k)
lemma hk3_1_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_1_20 j i k).Contains (fullFactor true 3 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_1_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel3_0 j i k) (mpower1_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 20 (kernel3_0_contains j i k) (mpower1_20_contains j i k)
noncomputable def ha3_1_20 : Fin 7 → CBox := ![⟨⟨22803349772014994810,22803349772014994871⟩,⟨(-25),25⟩⟩,⟨⟨(-71531576351852352561),(-71531576351852258715)⟩,⟨(-451776585125906692363),(-451776585125906598517)⟩⟩,⟨⟨6695243827949407143958,6695243827949426558761⟩,⟨39303282257944000452977,39303282257944019867781⟩⟩,⟨⟨270130854864957249570289,270130854864957306620046⟩,⟨179218791556927548287043,179218791556927605337128⟩⟩,⟨⟨335314730582127644843484,335314730582127656383365⟩,⟨(-110707877075691571231179),(-110707877075691559692162)⟩⟩,⟨⟨(-55587060311191311201586),(-55587060311191310748903)⟩,⟨(-127936365088034932779060),(-127936365088034932325548)⟩⟩,⟨⟨(-11303327110354362284522),(-11303327110354362264391)⟩,⟨34839893769547128122270,34839893769547128142243⟩⟩]
lemma ha3_1_20_eq (j : Fin 7) : ha3_1_20 j = ((ha3_1_19 j).mul (piI.mul (atomPoints j).z)).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha3_1_20_contains (j : Fin 7) : (ha3_1_20 j).Contains (fullFactor true 3 20 ((j.val:ℝ)/6)) := by
  rw [ha3_1_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_1_19 j) true 3 19 j (ha3_1_19_contains j)
noncomputable def hk3_1_21 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_21 j i k)
lemma hk3_1_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_1_21 j i k).Contains (fullFactor true 3 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_1_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel3_0 j i k) (mpower1_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 21 (kernel3_0_contains j i k) (mpower1_21_contains j i k)
noncomputable def ha3_1_21 : Fin 7 → CBox := ![⟨⟨(-10006694569282650647),(-10006694569282650619)⟩,⟨(-11),11⟩⟩,⟨⟨(-53869767299326317425),(-53869767299326266550)⟩,⟨177588929423108327679,177588929423108378555⟩⟩,⟨⟨8069216084925468775995,8069216084925478089310⟩,⟨(-10856809984703068397434),(-10856809984703059084119)⟩⟩,⟨⟨7192045255164772198842,7192045255164793764714⟩,⟨(-89861485119992938091688),(-89861485119992916525820)⟩⟩,⟨⟨(-48551930379925316017886),(-48551930379925312646436)⟩,⟨(-65780406495081531358278),(-65780406495081527986595)⟩⟩,⟨⟨(-23024175185733036772876),(-23024175185733036669382)⟩,⟨15104563030059161237662,15104563030059161340985⟩⟩,⟨⟨6091915582245794765859,6091915582245794769494⟩,⟨1632124038667881289029,1632124038667881292678⟩⟩]
lemma ha3_1_21_eq (j : Fin 7) : ha3_1_21 j = ((ha3_1_20 j).mul (piI.mul (atomPoints j).z)).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha3_1_21_contains (j : Fin 7) : (ha3_1_21 j).Contains (fullFactor true 3 21 ((j.val:ℝ)/6)) := by
  rw [ha3_1_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_1_20 j) true 3 20 j (ha3_1_20_contains j)
noncomputable def hk3_1_22 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_22 j i k)
lemma hk3_1_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_1_22 j i k).Contains (fullFactor true 3 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_1_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel3_0 j i k) (mpower1_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 22 (kernel3_0_contains j i k) (mpower1_22_contains j i k)
noncomputable def ha3_1_22 : Fin 7 → CBox := ![⟨⟨4191594419410034061,4191594419410034074⟩,⟨(-5),5⟩⟩,⟨⟨48783135668268379012,48783135668268405339⟩,⟨(-52779872812534259601),(-52779872812534233273)⟩⟩,⟨⟨(-4347425939135485050984),(-4347425939135480786446)⟩,⟨540741195171458956800,540741195171463221338⟩⟩,⟨⟨(-21790504175583226427153),(-21790504175583218645462)⟩,⟨9889449815932339502411,9889449815932347284075⟩⟩,⟨⟨(-10469603916909664389588),(-10469603916909663449255)⟩,⟨14726825341441761502201,14726825341441762442493⟩⟩,⟨⟨3541938821204688782999,3541938821204688805511⟩,⟨3791925084147362819022,3791925084147362841564⟩⟩,⟨⟨215897408211794435643,215897408211794436275⟩,⟨(-1013842508972473632271),(-1013842508972473631639)⟩⟩]
lemma ha3_1_22_eq (j : Fin 7) : ha3_1_22 j = ((ha3_1_21 j).mul (piI.mul (atomPoints j).z)).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha3_1_22_contains (j : Fin 7) : (ha3_1_22 j).Contains (fullFactor true 3 22 ((j.val:ℝ)/6)) := by
  rw [ha3_1_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_1_21 j) true 3 21 j (ha3_1_21_contains j)
noncomputable def hk3_1_23 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_23 j i k)
lemma hk3_1_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_1_23 j i k).Contains (fullFactor true 3 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_1_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel3_0 j i k) (mpower1_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 23 (kernel3_0_contains j i k) (mpower1_23_contains j i k)
noncomputable def ha3_1_23 : Fin 7 → CBox := ![⟨⟨(-1679433096618109155),(-1679433096618109149)⟩,⟨(-3),3⟩⟩,⟨⟨(-24791780801317887149),(-24791780801317874117)⟩,⟨9706682690944295090,9706682690944308122⟩⟩,⟨⟨1051723801667252300148,1051723801667254167964⟩,⟨857719139207729014458,857719139207730882274⟩⟩,⟨⟨4877606132975508315015,4877606132975511000814⟩,⟨3622825786857048028827,3622825786857050714633⟩⟩,⟨⟨3647954602929601421813,3647954602929601672655⟩,⟨1132742048839631371937,1132742048839631622783⟩⟩,⟨⟨565066572688439679145,565066572688439683842⟩,⟨(-745240894418225100993),(-745240894418225096300)⟩⟩,⟨⟨(-160937020843901259584),(-160937020843901259478)⟩,⟨(-25619067581550814906),(-25619067581550814801)⟩⟩]
lemma ha3_1_23_eq (j : Fin 7) : ha3_1_23 j = ((ha3_1_22 j).mul (piI.mul (atomPoints j).z)).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha3_1_23_contains (j : Fin 7) : (ha3_1_23 j).Contains (fullFactor true 3 23 ((j.val:ℝ)/6)) := by
  rw [ha3_1_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_1_22 j) true 3 22 j (ha3_1_22_contains j)
noncomputable def hk3_1_24 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_24 j i k)
lemma hk3_1_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_1_24 j i k).Contains (fullFactor true 3 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_1_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel3_0 j i k) (mpower1_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 24 (kernel3_0_contains j i k) (mpower1_24_contains j i k)
noncomputable def ha3_1_24 : Fin 7 → CBox := ![⟨⟨644856016264901116,644856016264901119⟩,⟨(-2),2⟩⟩,⟨⟨9422815968501706332,9422815968501712515⟩,⟨739947480355619167,739947480355625350⟩⟩,⟨⟨(-31701076537731099405),(-31701076537730315411)⟩,⟨(-401648178487178602855),(-401648178487177818861)⟩⟩,⟨⟨195951944030806953346,195951944030807841710⟩,⟨(-1465363885395898614401),(-1465363885395897726037)⟩⟩,⟨⟨(-12278980513748252464),(-12278980513748188335)⟩,⟨(-773750784661769028457),(-773750784661768964328)⟩⟩,⟨⟨(-143437871128441372742),(-143437871128441371804)⟩,⟨(-74316138130764867417),(-74316138130764866478)⟩⟩,⟨⟨(-2595476497250068721),(-2595476497250068703)⟩,⟨24414931295409036773,24414931295409036791⟩⟩]
lemma ha3_1_24_eq (j : Fin 7) : ha3_1_24 j = ((ha3_1_23 j).mul (piI.mul (atomPoints j).z)).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha3_1_24_contains (j : Fin 7) : (ha3_1_24 j).Contains (fullFactor true 3 24 ((j.val:ℝ)/6)) := by
  rw [ha3_1_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_1_23 j) true 3 23 j (ha3_1_23_contains j)
noncomputable def hk3_1_25 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_25 j i k)
lemma hk3_1_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_1_25 j i k).Contains (fullFactor true 3 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_1_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel3_0 j i k) (mpower1_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 25 (kernel3_0_contains j i k) (mpower1_25_contains j i k)
noncomputable def ha3_1_25 : Fin 7 → CBox := ![⟨⟨(-237702657669663247),(-237702657669663245)⟩,⟨(-1),1⟩⟩,⟨⟨(-2779457966458301334),(-2779457966458298518)⟩,⟨(-1628213140859876883),(-1628213140859874067)⟩⟩,⟨⟨(-76498697701268272427),(-76498697701267956517)⟩,⟨85631932949697536579,85631932949697852489⟩⟩,⟨⟨(-321601266682923540222),(-321601266682923258137)⟩,⟨125839359174146949031,125839359174147231116⟩⟩,⟨⟨(-142244529339456871283),(-142244529339456855543)⟩,⟨49169480181109765237,49169480181109780976⟩⟩,⟨⟨(-8103176382538899870),(-8103176382538899690)⟩,⟨25533095884286614634,25533095884286614815⟩⟩,⟨⟨3546012558628299070,3546012558628299073⟩,⟨191514387078475572,191514387078475576⟩⟩]
lemma ha3_1_25_eq (j : Fin 7) : ha3_1_25 j = ((ha3_1_24 j).mul (piI.mul (atomPoints j).z)).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha3_1_25_contains (j : Fin 7) : (ha3_1_25 j).Contains (fullFactor true 3 25 ((j.val:ℝ)/6)) := by
  rw [ha3_1_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_1_24 j) true 3 24 j (ha3_1_24_contains j)
noncomputable def hk3_1_26 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_26 j i k)
lemma hk3_1_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_1_26 j i k).Contains (fullFactor true 3 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_1_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel3_0 j i k) (mpower1_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 26 (kernel3_0_contains j i k) (mpower1_26_contains j i k)
noncomputable def ha3_1_26 : Fin 7 → CBox := ![⟨⟨84250401577555069,84250401577555071⟩,⟨(-1),1⟩⟩,⟨⟨586711258449261527,586711258449262760⟩,⟨877534407072659800,877534407072661034⟩⟩,⟨⟨31448548380821172653,31448548380821295053⟩,⟨(-1062799249395099129),(-1062799249394976729)⟩⟩,⟨⟨59728859553412531760,59728859553412617887⟩,⟨49488682257555740283,49488682257555826410⟩⟩,⟨⟨17027447429212043344,17027447429212047060⟩,⟨22409957675041625500,22409957675041629215⟩⟩,⟨⟨4231437054167551596,4231437054167551630⟩,⟨581568705088867172,581568705088867206⟩⟩,⟨⟨989106423910377,989106423910379⟩,⟨(-493873268509369580),(-493873268509369578)⟩⟩]
lemma ha3_1_26_eq (j : Fin 7) : ha3_1_26 j = ((ha3_1_25 j).mul (piI.mul (atomPoints j).z)).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha3_1_26_contains (j : Fin 7) : (ha3_1_26 j).Contains (fullFactor true 3 26 ((j.val:ℝ)/6)) := by
  rw [ha3_1_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_1_25 j) true 3 25 j (ha3_1_25_contains j)
noncomputable def hk3_1_27 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_27 j i k)
lemma hk3_1_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_1_27 j i k).Contains (fullFactor true 3 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_1_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel3_0 j i k) (mpower1_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 27 (kernel3_0_contains j i k) (mpower1_27_contains j i k)
noncomputable def ha3_1_27 : Fin 7 → CBox := ![⟨⟨(-28755406115934878),(-28755406115934876)⟩,⟨(-1),1⟩⟩,⟨⟨(-45752303065155052),(-45752303065154531)⟩,⟨(-329951528488761285),(-329951528488760764)⟩⟩,⟨⟨(-5937478786690024140),(-5937478786689978472)⟩,⟨(-5804891139461658937),(-5804891139461613268)⟩⟩,⟨⟨3102598321077493327,3102598321077518650⟩,⟨(-16487560604737105519),(-16487560604737080196)⟩⟩,⟨⟨2878929998267173685,2878929998267174531⟩,⟨(-4171322119168104857),(-4171322119168104012)⟩⟩,⟨⟨(-22383040894020982),(-22383040894020975)⟩,⟨(-655417585290226240),(-655417585290226233)⟩⟩,⟨⟨(-66058331858923524),(-66058331858923523)⟩,⟨3302390778927298,3302390778927300⟩⟩]
lemma ha3_1_27_eq (j : Fin 7) : ha3_1_27 j = ((ha3_1_26 j).mul (piI.mul (atomPoints j).z)).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha3_1_27_contains (j : Fin 7) : (ha3_1_27 j).Contains (fullFactor true 3 27 ((j.val:ℝ)/6)) := by
  rw [ha3_1_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_1_26 j) true 3 26 j (ha3_1_26_contains j)
noncomputable def hk3_1_28 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_28 j i k)
lemma hk3_1_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_1_28 j i k).Contains (fullFactor true 3 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_1_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel3_0 j i k) (mpower1_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 28 (kernel3_0_contains j i k) (mpower1_28_contains j i k)
noncomputable def ha3_1_28 : Fin 7 → CBox := ![⟨⟨9463957130027925,9463957130027927⟩,⟨(-1),1⟩⟩,⟨⟨(-31284510710159025),(-31284510710158812)⟩,⟨96413746388363250,96413746388363463⟩⟩,⟨⟨(-23665209013092340),(-23665209013075908)⟩,⟨2112841484072144946,2112841484072161377⟩⟩,⟨⟨(-3321550100042053753),(-3321550100042046573)⟩,⟨1100380273162070255,1100380273162077435⟩⟩,⟨⟨(-844073867357085498),(-844073867357085311)⟩,⟨(-249270913720877686),(-249270913720877500)⟩⟩,⟨⟨(-95064656296048884),(-95064656296048882)⟩,⟨19751973391920797,19751973391920800⟩⟩,⟨⟨868893343773932,868893343773933⟩,⟨8497080550601476,8497080550601477⟩⟩]
lemma ha3_1_28_eq (j : Fin 7) : ha3_1_28 j = ((ha3_1_27 j).mul (piI.mul (atomPoints j).z)).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha3_1_28_contains (j : Fin 7) : (ha3_1_28 j).Contains (fullFactor true 3 28 ((j.val:ℝ)/6)) := by
  rw [ha3_1_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_1_27 j) true 3 27 j (ha3_1_27_contains j)
noncomputable def hk3_1_29 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_29 j i k)
lemma hk3_1_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_1_29 j i k).Contains (fullFactor true 3 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_1_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel3_0 j i k) (mpower1_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 29 (kernel3_0_contains j i k) (mpower1_29_contains j i k)
noncomputable def ha3_1_29 : Fin 7 → CBox := ![⟨⟨(-3007364414983258),(-3007364414983257)⟩,⟨(-1),1⟩⟩,⟨⟨20630591843062691,20630591843062775⟩,⟨(-21476498436056345),(-21476498436056261)⟩⟩,⟨⟨379240389354640051,379240389354645759⟩,⟨(-354510039415434389),(-354510039415428680)⟩⟩,⟨⟨517965403865700865,517965403865702832⟩,⟨477701653278196805,477701653278198772⟩⟩,⟨⟨4394615732020839,4394615732020880⟩,⟨147494704714110418,147494704714110459⟩⟩,⟨⟨5091281893907678,5091281893907679⟩,⟨12912270669457335,12912270669457336⟩⟩,⟨⟨1052414624239458,1052414624239459⟩,⟨(-163211096669015),(-163211096669014)⟩⟩]
lemma ha3_1_29_eq (j : Fin 7) : ha3_1_29 j = ((ha3_1_28 j).mul (piI.mul (atomPoints j).z)).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha3_1_29_contains (j : Fin 7) : (ha3_1_29 j).Contains (fullFactor true 3 29 ((j.val:ℝ)/6)) := by
  rw [ha3_1_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_1_28 j) true 3 28 j (ha3_1_28_contains j)
noncomputable def hk3_1_30 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_30 j i k)
lemma hk3_1_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk3_1_30 j i k).Contains (fullFactor true 3 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk3_1_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel3_0 j i k) (mpower1_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 3 30 (kernel3_0_contains j i k) (mpower1_30_contains j i k)
noncomputable def ha3_1_30 : Fin 7 → CBox := ![⟨⟨923796030938368,923796030938369⟩,⟨(-1),1⟩⟩,⟨⟨(-7933516451134029),(-7933516451133997)⟩,⟨2931403118415560,2931403118415593⟩⟩,⟨⟨(-123099591719247913),(-123099591719245995)⟩,⟨(-6923313423475851),(-6923313423473934)⟩⟩,⟨⟨32479950684937654,32479950684938176⟩,⟨(-133260080548342362),(-133260080548341840)⟩⟩,⟨⟨22492151099683881,22492151099683890⟩,⟨(-8127004342778989),(-8127004342778980)⟩⟩,⟨⟨1638821091028528,1638821091028529⟩,⟨(-996452367466598),(-996452367466597)⟩⟩,⟨⟨(-26232498122064),(-26232498122063)⟩,⟨(-125654997216958),(-125654997216957)⟩⟩]
lemma ha3_1_30_eq (j : Fin 7) : ha3_1_30 j = ((ha3_1_29 j).mul (piI.mul (atomPoints j).z)).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha3_1_30_contains (j : Fin 7) : (ha3_1_30 j).Contains (fullFactor true 3 30 ((j.val:ℝ)/6)) := by
  rw [ha3_1_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha3_1_29 j) true 3 29 j (ha3_1_29_contains j)
end SharpPlanar.CachedData

end OAI
