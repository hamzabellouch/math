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
noncomputable def hk12_0_0 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_0 j i k)
lemma hk12_0_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_0_0 j i k).Contains (fullFactor false 12 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_0_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power12 j i k) (mpower0_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 0 (power12_contains j i k) (mpower0_0_contains j i k)
noncomputable def ha12_0_0 : Fin 7 → CBox := ![⟨⟨999999999999999999999999999857,1000000000000000000000000000191⟩,⟨(-191),191⟩⟩,⟨⟨999999999999999999986851087693,1000000000000000000013148912323⟩,⟨(-8609239891),18035706735⟩⟩,⟨⟨999999999999999999963771228521,1000000000000000000036228771487⟩,⟨(-26675268679),45528202431⟩⟩,⟨⟨999999999999999999960799900457,1000000000000000000039200099555⟩,⟨(-25060399247),53339799863⟩⟩,⟨⟨999999999999999999901146248937,1000000000000000000098853751035⟩,⟨(-80093686963),117799554499⟩⟩,⟨⟨999999999999999999875477146681,1000000000000000000124522853283⟩,⟨(-100864511599),147996845975⟩⟩,⟨⟨999999999999999999921361626617,1000000000000000000078638373431⟩,⟨(-50358972743),106917774071⟩⟩]
lemma ha12_0_0_eq (j : Fin 7) : ha12_0_0 j = ((atomPoints j).direct.powBin 7 12).conj := by fin_cases j <;> decide +kernel
lemma ha12_0_0_contains (j : Fin 7) : (ha12_0_0 j).Contains (fullFactor false 12 0 ((j.val:ℝ)/6)) := by
  rw [ha12_0_0_eq]
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @direct_factor_zero_full ((atomPoints j).direct.powBin 7 12) ((j.val:ℝ)/6) 12 (@direct_power_bin_contains (atomPoints j) ((j.val:ℝ)/6) (atomPoints_contains j) 12 (by norm_num))
noncomputable def hk12_0_1 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_1 j i k)
lemma hk12_0_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_0_1 j i k).Contains (fullFactor false 12 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_0_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power12 j i k) (mpower0_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 1 (power12_contains j i k) (mpower0_1_contains j i k)
noncomputable def ha12_0_1 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-9443473964),4507787466⟩,⟨523598775598298873069781912279,523598775598298873085218087728⟩⟩,⟨⟨(-47677022097),27934276039⟩,⟨1047197551196597746115394652556,1047197551196597746194605347454⟩⟩,⟨⟨(-83785961697),39364783086⟩,⟨1570796326794896619168424627627,1570796326794896619296575372391⟩⟩,⟨⟨(-246718810007),167747825708⟩,⟨2094395102393195492099627854584,2094395102393195492520372145356⟩⟩,⟨⟨(-387454836725),264062673873⟩,⟨2617993877991494365057333265672,2617993877991494365717666734234⟩⟩,⟨⟨(-335892093560),158207378812⟩,⟨3141592653589793238212950263889,3141592653589793238717049736262⟩⟩]
lemma ha12_0_1_eq (j : Fin 7) : ha12_0_1 j = ((ha12_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha12_0_1_contains (j : Fin 7) : (ha12_0_1 j).Contains (fullFactor false 12 1 ((j.val:ℝ)/6)) := by
  rw [ha12_0_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_0_0 j) false 12 0 j (ha12_0_0_contains j)
noncomputable def hk12_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_2 j i k)
lemma hk12_0_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_0_2 j i k).Contains (fullFactor false 12 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_0_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power12 j i k) (mpower0_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 2 (power12_contains j i k) (mpower0_2_contains j i k)
noncomputable def ha12_0_2 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-137077838904018869708479007625),(-137077838904018869704001494027)⟩,⟨(-2472295703),1180135999⟩⟩,⟨⟨(-548311355616075478846570979363),(-548311355616075478803351027246)⟩,⟨(-24963630395),14626352732⟩⟩,⟨⟨(-1233700550136169827408450432633),(-1233700550136169827303874082239)⟩,⟨(-65805340436),30917028339⟩⟩,⟨⟨(-2193245422464301915523635867169),(-2193245422464301915076052159180)⟩,⟨(-258363333674),175665112300⟩⟩,⟨⟨(-3426945972600471743093647669022),(-3426945972600471742218364872127)⟩,⟨(-507177195273),345657231803⟩⟩,⟨⟨(-4934802200544679309828421811239),(-4934802200544679309020876248427)⟩,⟨(-527618066764),248511569510⟩⟩]
lemma ha12_0_2_eq (j : Fin 7) : ha12_0_2 j = ((ha12_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha12_0_2_contains (j : Fin 7) : (ha12_0_2 j).Contains (fullFactor false 12 2 ((j.val:ℝ)/6)) := by
  rw [ha12_0_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_0_1 j) false 12 1 j (ha12_0_1_contains j)
noncomputable def hk12_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_3 j i k)
lemma hk12_0_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_0_3 j i k).Contains (fullFactor false 12 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_0_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power12 j i k) (mpower0_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 3 (power12_contains j i k) (mpower0_3_contains j i k)
noncomputable def ha12_0_3 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-205972589),431497002⟩,⟨(-23924596203935046432177341491),(-23924596203935046431319713589)⟩⟩,⟨⟨(-5105560255),8713950873⟩,⟨(-191396769631480371461836142409),(-191396769631480371446140298228)⟩⟩,⟨⟨(-16188118184),34455595681⟩,⟨(-645964097506246253685616351878),(-645964097506246253628804135270)⟩⟩,⟨⟨(-122637383621),180371633562⟩,⟨(-1531174157051842971790578889528),(-1531174157051842971473232635500)⟩⟩,⟨⟨(-301642838915),442595597428⟩,⟨(-2990574525491880804355239756886),(-2990574525491880803581892127919)⟩⟩,⟨⟨(-260240707035),552520347483⟩,⟨(-5167712780049970029688736486949),(-5167712780049970028826627410423)⟩⟩]
lemma ha12_0_3_eq (j : Fin 7) : ha12_0_3 j = ((ha12_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha12_0_3_contains (j : Fin 7) : (ha12_0_3 j).Contains (fullFactor false 12 3 ((j.val:ℝ)/6)) := by
  rw [ha12_0_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_0_2 j) false 12 2 j (ha12_0_2_contains j)
noncomputable def hk12_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_4 j i k)
lemma hk12_0_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_0_4 j i k).Contains (fullFactor false 12 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_0_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power12 j i k) (mpower0_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 4 (power12_contains j i k) (mpower0_4_contains j i k)
noncomputable def ha12_0_4 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨3131722319766024859658939788,3131722319766024859781171601⟩,⟨(-26961749),56482826⟩⟩,⟨⟨50107557116256397753386561263,50107557116256397757655220970⟩,⟨(-1336632550),2281307004⟩⟩,⟨⟨253669507901048013625765731068,253669507901048013648883291482⟩,⟨(-6357059146),13530680784⟩⟩,⟨⟨801720913860102364003977224349,801720913860102364172691291330⟩,⟨(-64212783907),94442366486⟩⟩,⟨⟨1957326449853765537068842207601,1957326449853765537581227410748⟩,⟨(-197424776405),289678141124⟩⟩,⟨⟨4058712126416768217852183096820,4058712126416768218542201264123⟩,⟨(-204392573347),433948466153⟩⟩]
lemma ha12_0_4_eq (j : Fin 7) : ha12_0_4 j = ((ha12_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha12_0_4_contains (j : Fin 7) : (ha12_0_4 j).Contains (fullFactor false 12 4 ((j.val:ℝ)/6)) := by
  rw [ha12_0_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_0_3 j) false 12 3 j (ha12_0_3_contains j)
noncomputable def hk12_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_5 j i k)
lemma hk12_0_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_0_5 j i k).Contains (fullFactor false 12 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_0_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power12 j i k) (mpower0_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 5 (power12_contains j i k) (mpower0_5_contains j i k)
noncomputable def ha12_0_5 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-5914868),2823428⟩,⟨327953194428670967568404959,327953194428670967582248953⟩⟩,⟨⟨(-477795822),279943667⟩,⟨10494502221717470961946747085,10494502221717470962874178122⟩⟩,⟨⟨(-4250788735),1997129032⟩,⟨79692626246167045117046317740,79692626246167045124562583046⟩⟩,⟨⟨(-39559925966),26897388026⟩,⟨335824071094959070761264931125,335824071094959070833004675464⟩⟩,⟨⟨(-151675120011),103371371199⟩,⟨1024853732589596773537123500690,1024853732589596773808669976445⟩⟩,⟨⟨(-272657862661),128423641376⟩,⟨2550164039877345443644908099966,2550164039877345444086576725269⟩⟩]
lemma ha12_0_5_eq (j : Fin 7) : ha12_0_5 j = ((ha12_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha12_0_5_contains (j : Fin 7) : (ha12_0_5 j).Contains (fullFactor false 12 5 ((j.val:ℝ)/6)) := by
  rw [ha12_0_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_0_4 j) false 12 4 j (ha12_0_4_contains j)
noncomputable def hk12_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_6 j i k)
lemma hk12_0_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_0_6 j i k).Contains (fullFactor false 12 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_0_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power12 j i k) (mpower0_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 6 (power12_contains j i k) (mpower0_6_contains j i k)
noncomputable def ha12_0_6 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-28619315176067161692207275),(-28619315176067161690908060)⟩,⟨(-516170),246391⟩⟩,⟨⟨(-1831636171268298348343539496),(-1831636171268298348175841964)⟩,⟨(-83391103),48859388⟩⟩,⟨⟨(-20863480763352960874162621809),(-20863480763352960872128457631)⟩,⟨(-1112853889),522847158⟩⟩,⟨⟨(-117224714961171094301327723071),(-117224714961171094275912690348)⟩,⟨(-13809019200),9388959625⟩⟩,⟨⟨(-447176799626049401490542511995),(-447176799626049401370634602179)⟩,⟨(-66180755939),45104269494⟩⟩,⟨⟨(-1335262768854589495999068254514),(-1335262768854589495763560829684)⟩,⟨(-142763323047),67242461383⟩⟩]
lemma ha12_0_6_eq (j : Fin 7) : ha12_0_6 j = ((ha12_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha12_0_6_contains (j : Fin 7) : (ha12_0_6 j).Contains (fullFactor false 12 6 ((j.val:ℝ)/6)) := by
  rw [ha12_0_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_0_5 j) false 12 5 j (ha12_0_5_contains j)
noncomputable def hk12_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_7 j i k)
lemma hk12_0_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_0_7 j i k).Contains (fullFactor false 12 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_0_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power12 j i k) (mpower0_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 7 (power12_contains j i k) (mpower0_7_contains j i k)
noncomputable def ha12_0_7 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-18431),38610⟩,⟨(-2140719769235797028268755),(-2140719769235797028164759)⟩⟩,⟨⟨(-7309348),12475280⟩,⟨(-274012130462182019624724746),(-274012130462182019598765045)⟩⟩,⟨⟨(-117326628),249723829⟩,⟨(-4681754135318688100945731479),(-4681754135318688100474363617)⟩⟩,⟨⟨(-2809170151),4131648884⟩,⟨(-35073552699159298514161247901),(-35073552699159298506445445306)⟩⟩,⟨⟨(-16868957344),24751544842⟩,⟨(-167243731971546642852123043589),(-167243731971546642806745236852)⟩⟩,⟨⟨(-30178346099),64072029556⟩,⟨(-599264529320792076944687587800),(-599264529320792076837084584456)⟩⟩]
lemma ha12_0_7_eq (j : Fin 7) : ha12_0_7 j = ((ha12_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha12_0_7_contains (j : Fin 7) : (ha12_0_7 j).Contains (fullFactor false 12 7 ((j.val:ℝ)/6)) := by
  rw [ha12_0_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_0_6 j) false 12 6 j (ha12_0_6_contains j)
noncomputable def hk12_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_8 j i k)
lemma hk12_0_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_0_8 j i k).Contains (fullFactor false 12 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_0_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power12 j i k) (mpower0_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 8 (power12_contains j i k) (mpower0_8_contains j i k)
noncomputable def ha12_0_8 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨140109781258867029450303,140109781258867029457556⟩,⟨(-1207),2528⟩⟩,⟨⟨35868104002269959538449859,35868104002269959541962148⟩,⟨(-956792),1633011⟩⟩,⟨⟨919260274839426580199493292,919260274839426580294972252⟩,⟨(-23037030),49033160⟩⟩,⟨⟨9182234624581109641268126742,9182234624581109643317347099⟩,⟨(-735439026),1081663149⟩⟩,⟨⟨54730383304244933372929257288,54730383304244933387953322039⟩,⟨(-5520353382),8099924109⟩⟩,⟨⟨235330630358893204521789248959,235330630358893204564793930223⟩,⟨(-11851008801),25161027170⟩⟩]
lemma ha12_0_8_eq (j : Fin 7) : ha12_0_8 j = ((ha12_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha12_0_8_contains (j : Fin 7) : (ha12_0_8 j).Contains (fullFactor false 12 8 ((j.val:ℝ)/6)) := by
  rw [ha12_0_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_0_7 j) false 12 7 j (ha12_0_7_contains j)
noncomputable def hk12_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_9 j i k)
lemma hk12_0_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_0_9 j i k).Contains (fullFactor false 12 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_0_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power12 j i k) (mpower0_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 9 (power12_contains j i k) (mpower0_9_contains j i k)
noncomputable def ha12_0_9 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-148),71⟩,⟨8151256657387584304696,8151256657387584305145⟩⟩,⟨⟨(-190010),111328⟩,⟨4173443408582443163908156,4173443408582443164330115⟩⟩,⟨⟨(-8557901),4020721⟩,⟨160441184787359821865156581,160441184787359821882331504⟩⟩,⟨⟨(-251714445),171144433⟩,⟨2136803025194210899787159077,2136803025194210900270835965⟩⟩,⟨⟨(-2356172415),1605805707⟩,⟨15920423158960125593336740602,15920423158960125597757740166⟩⟩,⟨⟨(-8782855347),4136782466⟩,⟨82145886611128228791720477566,82145886611128228806993421682⟩⟩]
lemma ha12_0_9_eq (j : Fin 7) : ha12_0_9 j = ((ha12_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha12_0_9_contains (j : Fin 7) : (ha12_0_9 j).Contains (fullFactor false 12 9 ((j.val:ℝ)/6)) := by
  rw [ha12_0_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_0_8 j) false 12 8 j (ha12_0_8_contains j)
noncomputable def hk12_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_10 j i k)
lemma hk12_0_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_0_10 j i k).Contains (fullFactor false 12 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_0_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power12 j i k) (mpower0_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 10 (power12_contains j i k) (mpower0_10_contains j i k)
noncomputable def ha12_0_10 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-426798800539562151468),(-426798800539562151442)⟩,⟨(-8),4⟩⟩,⟨⟨(-437041971752511643112290),(-437041971752511643066710)⟩,⟨(-19898),11659⟩⟩,⟨⟨(-25202042373060605482631097),(-25202042373060605479853045)⟩,⟨(-1344272),631574⟩⟩,⟨⟨(-447530979074571922575010709),(-447530979074571922472285122)⟩,⟨(-52718951),35844407⟩⟩,⟨⟨(-4167957036519161635884069155),(-4167957036519161634713387155)⟩,⟨(-616844496),420398952⟩⟩,⟨⟨(-25806891390014060015232022019),(-25806891390014060010351739228)⟩,⟨(-2759215384),1299608541⟩⟩]
lemma ha12_0_10_eq (j : Fin 7) : ha12_0_10 j = ((ha12_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha12_0_10_contains (j : Fin 7) : (ha12_0_10 j).Contains (fullFactor false 12 10 ((j.val:ℝ)/6)) := by
  rw [ha12_0_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_0_9 j) false 12 9 j (ha12_0_9_contains j)
noncomputable def hk12_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_11 j i k)
lemma hk12_0_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_0_11 j i k).Contains (fullFactor false 12 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_0_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power12 j i k) (mpower0_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 11 (power12_contains j i k) (mpower0_11_contains j i k)
noncomputable def ha12_0_11 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-20315575399030665722),(-20315575399030665720)⟩⟩,⟨⟨(-1110),1895⟩,⟨(-41606298417214803398963),(-41606298417214803394490)⟩⟩,⟨⟨(-90189),191962⟩,⟨(-3598843235212085340692316),(-3598843235212085340284155)⟩⟩,⟨⟨(-6824760),10037665⟩,⟨(-85209699158455917366410913),(-85209699158455917346580775)⟩⟩,⟨⟨(-100054717),146808647⟩,⟨(-991971455030794224801917668),(-991971455030794224520138460)⟩⟩,⟨⟨(-371167332),788030071⟩,⟨(-7370430945714350778028540068),(-7370430945714350776611273751)⟩⟩]
lemma ha12_0_11_eq (j : Fin 7) : ha12_0_11 j = ((ha12_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha12_0_11_contains (j : Fin 7) : (ha12_0_11 j).Contains (fullFactor false 12 11 ((j.val:ℝ)/6)) := by
  rw [ha12_0_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_0_10 j) false 12 10 j (ha12_0_10_contains j)
noncomputable def hk12_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_12 j i k)
lemma hk12_0_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_0_12 j i k).Contains (fullFactor false 12 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_0_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power12 j i k) (mpower0_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 12 (power12_contains j i k) (mpower0_12_contains j i k)
noncomputable def ha12_0_12 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨886434200375614885,886434200375614886⟩,⟨(-1),1⟩⟩,⟨⟨3630834484738518570855,3630834484738518571258⟩,⟨(-97),166⟩⟩,⟨⟨471087477881817150343804,471087477881817150398733⟩,⟨(-11806),25128⟩⟩,⟨⟨14871898049488972065292303,14871898049488972068800655⟩,⟨(-1191146),1751904⟩⟩,⟨⟨216414599701077852877068737,216414599701077852939232294⟩,⟨(-21828554),32028679⟩⟩,⟨⟨1929574309403923047732124104,1929574309403923048109305585⟩,⟨(-97171381),206305791⟩⟩]
lemma ha12_0_12_eq (j : Fin 7) : ha12_0_12 j = ((ha12_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha12_0_12_contains (j : Fin 7) : (ha12_0_12 j).Contains (fullFactor false 12 12 ((j.val:ℝ)/6)) := by
  rw [ha12_0_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_0_11 j) false 12 11 j (ha12_0_11_contains j)
noncomputable def hk12_0_13 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_13 j i k)
lemma hk12_0_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_0_13 j i k).Contains (fullFactor false 12 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_0_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power12 j i k) (mpower0_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 13 (power12_contains j i k) (mpower0_13_contains j i k)
noncomputable def ha12_0_13 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨35702758612702236,35702758612702237⟩⟩,⟨⟨(-14),8⟩,⟨292476998555256723009,292476998555256723043⟩⟩,⟨⟨(-3037),1427⟩,⟨56921729219679268114898,56921729219679268121717⟩⟩,⟨⟨(-282245),191903⟩,⟨2395971572164663074743568,2395971572164663075316417⟩⟩,⟨⟨(-6450069),4395925⟩,⟨43582469009646285024829314,43582469009646285037486797⟩⟩,⟨⟨(-49856059),23482531⟩,⟨466302805767612564378859015,466302805767612564471493348⟩⟩]
lemma ha12_0_13_eq (j : Fin 7) : ha12_0_13 j = ((ha12_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha12_0_13_contains (j : Fin 7) : (ha12_0_13 j).Contains (fullFactor false 12 13 ((j.val:ℝ)/6)) := by
  rw [ha12_0_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_0_12 j) false 12 12 j (ha12_0_12_contains j)
noncomputable def hk12_0_14 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_14 j i k)
lemma hk12_0_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_0_14 j i k).Contains (fullFactor false 12 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_0_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power12 j i k) (mpower0_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 14 (power12_contains j i k) (mpower0_14_contains j i k)
noncomputable def ha12_0_14 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1335280049649466),(-1335280049649465)⟩,⟨(-1),1⟩⟩,⟨⟨(-21877228333456835519),(-21877228333456835516)⟩,⟨(-2),1⟩⟩,⟨⟨(-6386603083791852241550),(-6386603083791852240764)⟩,⟨(-341),161⟩⟩,⟨⟨(-358436509015356793164929),(-358436509015356793078089)⟩,⟨(-42224),28709⟩⟩,⟨⟨(-8149902646786285758347027),(-8149902646786285755954140)⟩,⟨(-1206161),822037⟩⟩,⟨⟨(-104638104924845707129675710),(-104638104924845707108555540)⟩,⟨(-11187674),5269468⟩⟩]
lemma ha12_0_14_eq (j : Fin 7) : ha12_0_14 j = ((ha12_0_13 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha12_0_14_contains (j : Fin 7) : (ha12_0_14 j).Contains (fullFactor false 12 14 ((j.val:ℝ)/6)) := by
  rw [ha12_0_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_0_13 j) false 12 13 j (ha12_0_13_contains j)
noncomputable def hk12_0_15 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_15 j i k)
lemma hk12_0_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_0_15 j i k).Contains (fullFactor false 12 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_0_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power12 j i k) (mpower0_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 15 (power12_contains j i k) (mpower0_15_contains j i k)
noncomputable def ha12_0_15 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-46610066605154),(-46610066605153)⟩⟩,⟨⟨(-1),1⟩,⟨(-1527318662517654887),(-1527318662517654886)⟩⟩,⟨⟨(-17),36⟩,⟨(-668803510981146723298),(-668803510981146723213)⟩⟩,⟨⟨(-4009),5896⟩,⟨(-50047177933378515334162),(-50047177933378515321876)⟩⟩,⟨⟨(-143473),210515⟩,⟨(-1422426349034211493046937),(-1422426349034211492624771)⟩⟩,⟨⟨(-1103635),2343141⟩,⟨(-21915353447830215829877823),(-21915353447830215825384665)⟩⟩]
lemma ha12_0_15_eq (j : Fin 7) : ha12_0_15 j = ((ha12_0_14 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha12_0_15_contains (j : Fin 7) : (ha12_0_15 j).Contains (fullFactor false 12 15 ((j.val:ℝ)/6)) := by
  rw [ha12_0_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_0_14 j) false 12 14 j (ha12_0_14_contains j)
noncomputable def hk12_0_16 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_16 j i k)
lemma hk12_0_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_0_16 j i k).Contains (fullFactor false 12 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_0_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power12 j i k) (mpower0_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 16 (power12_contains j i k) (mpower0_16_contains j i k)
noncomputable def ha12_0_16 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1525310862813,1525310862814⟩,⟨(-1),1⟩⟩,⟨⟨99962772705334443,99962772705334444⟩,⟨(-1),1⟩⟩,⟨⟨65659631149794723618,65659631149794723628⟩,⟨(-2),4⟩⟩,⟨⟨6551160272016798098015,6551160272016798099645⟩,⟨(-525),772⟩⟩,⟨⟨232743967104084891340930,232743967104084891410749⟩,⟨(-23476),34446⟩⟩,⟨⟨4303069587032947006901506,4303069587032947007797434⟩,⟨(-216699),460075⟩⟩]
lemma ha12_0_16_eq (j : Fin 7) : ha12_0_16 j = ((ha12_0_15 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha12_0_16_contains (j : Fin 7) : (ha12_0_16 j).Contains (fullFactor false 12 16 ((j.val:ℝ)/6)) := by
  rw [ha12_0_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_0_15 j) false 12 15 j (ha12_0_15_contains j)
noncomputable def hk12_0_17 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_17 j i k)
lemma hk12_0_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_0_17 j i k).Contains (fullFactor false 12 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_0_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power12 j i k) (mpower0_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 17 (power12_contains j i k) (mpower0_17_contains j i k)
noncomputable def ha12_0_17 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨46979464716,46979464717⟩⟩,⟨⟨(-1),1⟩,⟨6157692399285195,6157692399285196⟩⟩,⟨⟨(-1),1⟩,⟨6066935731106195666,6066935731106195668⟩⟩,⟨⟨(-96),65⟩,⟨807101058159109193325,807101058159109193530⟩⟩,⟨⟨(-5305),3616⟩,⟨35842487118702823481142,35842487118702823492010⟩⟩,⟨⟨(-85022),40046⟩,⟨795205400147551278404412,795205400147551278572511⟩⟩]
lemma ha12_0_17_eq (j : Fin 7) : ha12_0_17 j = ((ha12_0_16 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha12_0_17_contains (j : Fin 7) : (ha12_0_17 j).Contains (fullFactor false 12 17 ((j.val:ℝ)/6)) := by
  rw [ha12_0_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_0_16 j) false 12 16 j (ha12_0_16_contains j)
noncomputable def hk12_0_18 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_18 j i k)
lemma hk12_0_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_0_18 j i k).Contains (fullFactor false 12 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_0_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power12 j i k) (mpower0_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 18 (power12_contains j i k) (mpower0_18_contains j i k)
noncomputable def ha12_0_18 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1366577234),(-1366577233)⟩,⟨(-1),1⟩⟩,⟨⟨(-358240022308520),(-358240022308519)⟩,⟨(-1),1⟩⟩,⟨⟨(-529440020073462377),(-529440020073462376)⟩,⟨(-1),1⟩⟩,⟨⟨(-93910472408044662752),(-93910472408044662727)⟩,⟨(-12),8⟩⟩,⟨⟨(-5213078436041832672473),(-5213078436041832670875)⟩,⟨(-772),526⟩⟩,⟨⟨(-138789524622137721161446),(-138789524622137721131664)⟩,⟨(-14840),6990⟩⟩]
lemma ha12_0_18_eq (j : Fin 7) : ha12_0_18 j = ((ha12_0_17 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha12_0_18_contains (j : Fin 7) : (ha12_0_18 j).Contains (fullFactor false 12 18 ((j.val:ℝ)/6)) := by
  rw [ha12_0_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_0_17 j) false 12 17 j (ha12_0_17_contains j)
noncomputable def hk12_0_19 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_19 j i k)
lemma hk12_0_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_0_19 j i k).Contains (fullFactor false 12 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_0_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power12 j i k) (mpower0_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 19 (power12_contains j i k) (mpower0_19_contains j i k)
noncomputable def ha12_0_19 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-37659904),(-37659903)⟩⟩,⟨⟨(-1),1⟩,⟨(-19744635479058),(-19744635479057)⟩⟩,⟨⟨(-1),1⟩,⟨(-43770654673137423),(-43770654673137422)⟩⟩,⟨⟨(-1),2⟩,⟨(-10351875446044213763),(-10351875446044213760)⟩⟩,⟨⟨(-73),107⟩,⟨(-718305654265631155162),(-718305654265631154939)⟩⟩,⟨⟨(-1156),2454⟩,⟨(-22948428997269873113030),(-22948428997269873108032)⟩⟩]
lemma ha12_0_19_eq (j : Fin 7) : ha12_0_19 j = ((ha12_0_18 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha12_0_19_contains (j : Fin 7) : (ha12_0_19 j).Contains (fullFactor false 12 19 ((j.val:ℝ)/6)) := by
  rw [ha12_0_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_0_18 j) false 12 18 j (ha12_0_18_contains j)
noncomputable def hk12_0_20 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_20 j i k)
lemma hk12_0_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_0_20 j i k).Contains (fullFactor false 12 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_0_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power12 j i k) (mpower0_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 20 (power12_contains j i k) (mpower0_20_contains j i k)
noncomputable def ha12_0_20 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨985933,985934⟩,⟨(-1),1⟩⟩,⟨⟨1033826696146,1033826696147⟩,⟨(-1),1⟩⟩,⟨⟨3437739179098606,3437739179098608⟩,⟨(-1),1⟩⟩,⟨⟨1084045861738968866,1084045861738968868⟩,⟨(-1),1⟩⟩,⟨⟨94025990269704865199,94025990269704865230⟩,⟨(-10),15⟩⟩,⟨⟨3604730797462500933515,3604730797462500934312⟩,⟨(-182),386⟩⟩]
lemma ha12_0_20_eq (j : Fin 7) : ha12_0_20 j = ((ha12_0_19 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha12_0_20_contains (j : Fin 7) : (ha12_0_20 j).Contains (fullFactor false 12 20 ((j.val:ℝ)/6)) := by
  rw [ha12_0_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_0_19 j) false 12 19 j (ha12_0_19_contains j)
noncomputable def hk12_0_21 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_21 j i k)
lemma hk12_0_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_0_21 j i k).Contains (fullFactor false 12 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_0_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power12 j i k) (mpower0_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 21 (power12_contains j i k) (mpower0_21_contains j i k)
noncomputable def ha12_0_21 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨24582,24583⟩⟩,⟨⟨(-1),1⟩,⟨51553370693,51553370694⟩⟩,⟨⟨(-1),1⟩,⟨257142289286047,257142289286048⟩⟩,⟨⟨(-1),1⟩,⟨108115254456938454,108115254456938455⟩⟩,⟨⟨(-2),2⟩,⟨11721879376103578820,11721879376103578825⟩⟩,⟨⟨(-58),28⟩,⟨539266466260812848883,539266466260812849005⟩⟩]
lemma ha12_0_21_eq (j : Fin 7) : ha12_0_21 j = ((ha12_0_20 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha12_0_21_contains (j : Fin 7) : (ha12_0_21 j).Contains (fullFactor false 12 21 ((j.val:ℝ)/6)) := by
  rw [ha12_0_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_0_20 j) false 12 20 j (ha12_0_20_contains j)
noncomputable def hk12_0_22 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_22 j i k)
lemma hk12_0_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_0_22 j i k).Contains (fullFactor false 12 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_0_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power12 j i k) (mpower0_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 22 (power12_contains j i k) (mpower0_22_contains j i k)
noncomputable def ha12_0_22 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-586),(-585)⟩,⟨(-1),1⟩⟩,⟨⟨(-2453934707),(-2453934706)⟩,⟨(-1),1⟩⟩,⟨⟨(-18359916521553),(-18359916521552)⟩,⟨(-1),1⟩⟩,⟨⟨(-10292548155845728),(-10292548155845727)⟩,⟨(-1),1⟩⟩,⟨⟨(-1394900383872451220),(-1394900383872451219)⟩,⟨(-1),1⟩⟩,⟨⟨(-77007071306013533809),(-77007071306013533790)⟩,⟨(-9),4⟩⟩]
lemma ha12_0_22_eq (j : Fin 7) : ha12_0_22 j = ((ha12_0_21 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha12_0_22_contains (j : Fin 7) : (ha12_0_22 j).Contains (fullFactor false 12 22 ((j.val:ℝ)/6)) := by
  rw [ha12_0_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_0_21 j) false 12 21 j (ha12_0_21_contains j)
noncomputable def hk12_0_23 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_23 j i k)
lemma hk12_0_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_0_23 j i k).Contains (fullFactor false 12 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_0_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power12 j i k) (mpower0_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 23 (power12_contains j i k) (mpower0_23_contains j i k)
noncomputable def ha12_0_23 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-14),(-13)⟩⟩,⟨⟨(-1),1⟩,⟨(-111728453),(-111728452)⟩⟩,⟨⟨(-1),1⟩,⟨(-1253899540536),(-1253899540535)⟩⟩,⟨⟨(-1),1⟩,⟨(-937246193423888),(-937246193423887)⟩⟩,⟨⟨(-1),1⟩,⟨(-158775681103741858),(-158775681103741857)⟩⟩,⟨⟨(-1),2⟩,⟨(-10518471716932064457),(-10518471716932064454)⟩⟩]
lemma ha12_0_23_eq (j : Fin 7) : ha12_0_23 j = ((ha12_0_22 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha12_0_23_contains (j : Fin 7) : (ha12_0_23 j).Contains (fullFactor false 12 23 ((j.val:ℝ)/6)) := by
  rw [ha12_0_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_0_22 j) false 12 22 j (ha12_0_22_contains j)
noncomputable def hk12_0_24 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_24 j i k)
lemma hk12_0_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_0_24 j i k).Contains (fullFactor false 12 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_0_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power12 j i k) (mpower0_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 24 (power12_contains j i k) (mpower0_24_contains j i k)
noncomputable def ha12_0_24 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨(-1),1⟩⟩,⟨⟨4875073,4875074⟩,⟨(-1),1⟩⟩,⟨⟨82067533018,82067533019⟩,⟨(-1),1⟩⟩,⟨⟨81790159885152,81790159885153⟩,⟨(-1),1⟩⟩,⟨⟨17319740045980249,17319740045980250⟩,⟨(-1),1⟩⟩,⟨⟨1376864728037741370,1376864728037741371⟩,⟨(-1),1⟩⟩]
lemma ha12_0_24_eq (j : Fin 7) : ha12_0_24 j = ((ha12_0_23 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha12_0_24_contains (j : Fin 7) : (ha12_0_24 j).Contains (fullFactor false 12 24 ((j.val:ℝ)/6)) := by
  rw [ha12_0_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_0_23 j) false 12 23 j (ha12_0_23_contains j)
noncomputable def hk12_0_25 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_25 j i k)
lemma hk12_0_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_0_25 j i k).Contains (fullFactor false 12 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_0_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power12 j i k) (mpower0_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 25 (power12_contains j i k) (mpower0_25_contains j i k)
noncomputable def ha12_0_25 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨0,1⟩⟩,⟨⟨(-1),1⟩,⟨204206,204207⟩⟩,⟨⟨(-1),1⟩,⟨5156455176,5156455177⟩⟩,⟨⟨(-1),1⟩,⟨6852036411496,6852036411497⟩⟩,⟨⟨(-1),1⟩,⟨1813718936351216,1813718936351217⟩⟩,⟨⟨(-1),1⟩,⟨173021924583611076,173021924583611077⟩⟩]
lemma ha12_0_25_eq (j : Fin 7) : ha12_0_25 j = ((ha12_0_24 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha12_0_25_contains (j : Fin 7) : (ha12_0_25 j).Contains (fullFactor false 12 25 ((j.val:ℝ)/6)) := by
  rw [ha12_0_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_0_24 j) false 12 24 j (ha12_0_24_contains j)
noncomputable def hk12_0_26 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_26 j i k)
lemma hk12_0_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_0_26 j i k).Contains (fullFactor false 12 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_0_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power12 j i k) (mpower0_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 26 (power12_contains j i k) (mpower0_26_contains j i k)
noncomputable def ha12_0_26 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),1⟩⟩,⟨⟨(-8225),(-8224)⟩,⟨(-1),1⟩⟩,⟨⟨(-311528495),(-311528494)⟩,⟨(-1),1⟩⟩,⟨⟨(-551956596218),(-551956596217)⟩,⟨(-1),1⟩⟩,⟨⟨(-182627118144798),(-182627118144797)⟩,⟨(-1),1⟩⟩,⟨⟨(-20906323353147685),(-20906323353147684)⟩,⟨(-1),1⟩⟩]
lemma ha12_0_26_eq (j : Fin 7) : ha12_0_26 j = ((ha12_0_25 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha12_0_26_contains (j : Fin 7) : (ha12_0_26 j).Contains (fullFactor false 12 26 ((j.val:ℝ)/6)) := by
  rw [ha12_0_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_0_25 j) false 12 25 j (ha12_0_25_contains j)
noncomputable def hk12_0_27 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_27 j i k)
lemma hk12_0_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_0_27 j i k).Contains (fullFactor false 12 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_0_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power12 j i k) (mpower0_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 27 (power12_contains j i k) (mpower0_27_contains j i k)
noncomputable def ha12_0_27 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-1),0⟩⟩,⟨⟨(-1),1⟩,⟨(-320),(-318)⟩⟩,⟨⟨(-1),1⟩,⟨(-18123994),(-18123993)⟩⟩,⟨⟨(-1),1⟩,⟨(-42815377477),(-42815377475)⟩⟩,⟨⟨(-1),1⟩,⟨(-17708025083642),(-17708025083641)⟩⟩,⟨⟨(-1),1⟩,⟨(-2432561179993389),(-2432561179993388)⟩⟩]
lemma ha12_0_27_eq (j : Fin 7) : ha12_0_27 j = ((ha12_0_26 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha12_0_27_contains (j : Fin 7) : (ha12_0_27 j).Contains (fullFactor false 12 27 ((j.val:ℝ)/6)) := by
  rw [ha12_0_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_0_26 j) false 12 26 j (ha12_0_26_contains j)
noncomputable def hk12_0_28 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_28 j i k)
lemma hk12_0_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_0_28 j i k).Contains (fullFactor false 12 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_0_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power12 j i k) (mpower0_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 28 (power12_contains j i k) (mpower0_28_contains j i k)
noncomputable def ha12_0_28 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨(-1),1⟩⟩,⟨⟨11,12⟩,⟨(-1),1⟩⟩,⟨⟨1016753,1016754⟩,⟨(-1),1⟩⟩,⟨⟨3202582746,3202582747⟩,⟨(-1),1⟩⟩,⟨⟨1655696473581,1655696473582⟩,⟨(-1),1⟩⟩,⟨⟨272932726159819,272932726159820⟩,⟨(-1),1⟩⟩]
lemma ha12_0_28_eq (j : Fin 7) : ha12_0_28 j = ((ha12_0_27 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha12_0_28_contains (j : Fin 7) : (ha12_0_28 j).Contains (fullFactor false 12 28 ((j.val:ℝ)/6)) := by
  rw [ha12_0_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_0_27 j) false 12 27 j (ha12_0_27_contains j)
noncomputable def hk12_0_29 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_29 j i k)
lemma hk12_0_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_0_29 j i k).Contains (fullFactor false 12 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_0_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power12 j i k) (mpower0_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 29 (power12_contains j i k) (mpower0_29_contains j i k)
noncomputable def ha12_0_29 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨0,1⟩⟩,⟨⟨(-1),1⟩,⟨0,1⟩⟩,⟨⟨(-1),1⟩,⟨55072,55073⟩⟩,⟨⟨(-1),1⟩,⟨231292193,231292194⟩⟩,⟨⟨(-1),1⟩,⟨149469076953,149469076954⟩⟩,⟨⟨(-1),1⟩,⟨29567015428549,29567015428550⟩⟩]
lemma ha12_0_29_eq (j : Fin 7) : ha12_0_29 j = ((ha12_0_28 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha12_0_29_contains (j : Fin 7) : (ha12_0_29 j).Contains (fullFactor false 12 29 ((j.val:ℝ)/6)) := by
  rw [ha12_0_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_0_28 j) false 12 28 j (ha12_0_28_contains j)
noncomputable def hk12_0_30 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_30 j i k)
lemma hk12_0_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_0_30 j i k).Contains (fullFactor false 12 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_0_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power12 j i k) (mpower0_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 30 (power12_contains j i k) (mpower0_30_contains j i k)
noncomputable def ha12_0_30 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),1⟩⟩,⟨⟨(-1),0⟩,⟨(-1),1⟩⟩,⟨⟨(-2884),(-2883)⟩,⟨(-1),1⟩⟩,⟨⟨(-16147242),(-16147241)⟩,⟨(-1),1⟩⟩,⟨⟨(-13043637614),(-13043637613)⟩,⟨(-1),1⟩⟩,⟨⟨(-3096250615297),(-3096250615296)⟩,⟨(-1),1⟩⟩]
lemma ha12_0_30_eq (j : Fin 7) : ha12_0_30 j = ((ha12_0_29 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha12_0_30_contains (j : Fin 7) : (ha12_0_30 j).Contains (fullFactor false 12 30 ((j.val:ℝ)/6)) := by
  rw [ha12_0_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_0_29 j) false 12 29 j (ha12_0_29_contains j)
noncomputable def hk12_1_0 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_0 j i k)
lemma hk12_1_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_1_0 j i k).Contains (fullFactor true 12 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_1_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel12_0 j i k) (mpower1_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 0 (kernel12_0_contains j i k) (mpower1_0_contains j i k)
noncomputable def ha12_1_0 : Fin 7 → CBox := ![⟨⟨0,3⟩,⟨(-3),3⟩⟩,⟨⟨0,4⟩,⟨(-3),2⟩⟩,⟨⟨(-7456),(-7452)⟩,⟨48027,48031⟩⟩,⟨⟨(-2433521169088633),(-2433521169088629)⟩,⟨2104633841203363,2104633841203366⟩⟩,⟨⟨(-10126433418478817995544),(-10126433418478817959972)⟩,⟨15855193807734678938298,15855193807734678973769⟩⟩,⟨⟨(-190318804329798986529500314),(-190318804329798986262853704)⟩,⟨186919098208693442779401710,186919098208693443043376098⟩⟩,⟨⟨(-29985267079005839469470031008),(-29985267079005839367492391446)⟩,⟨108564951811294072989478110531,108564951811294073091885636862⟩⟩]
lemma ha12_1_0_eq (j : Fin 7) : ha12_1_0 j = atomKernel12_0 j := by fin_cases j <;> decide +kernel
lemma ha12_1_0_contains (j : Fin 7) : (ha12_1_0 j).Contains (fullFactor true 12 0 ((j.val:ℝ)/6)) := by
  rw [ha12_1_0_eq]
  simpa only [fullFactor,ite_true] using atomKernel12_0_contains j
noncomputable def hk12_1_1 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_1 j i k)
lemma hk12_1_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_1_1 j i k).Contains (fullFactor true 12 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_1_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel12_0 j i k) (mpower1_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 1 (kernel12_0_contains j i k) (mpower1_1_contains j i k)
noncomputable def ha12_1_1 : Fin 7 → CBox := ![⟨⟨(-28),0⟩,⟨(-28),28⟩⟩,⟨⟨(-42),8⟩,⟨(-31),23⟩⟩,⟨⟨284036,284077⟩,⟨(-198104),(-198063)⟩⟩,⟨⟨17637895069707079,17637895069707107⟩,⟨6475021789587754,6475021789587784⟩⟩,⟨⟨88595980360819229063312,88595980360819229281375⟩,⟨22757742687381368101870,22757742687381368320190⟩⟩,⟨⟨897662343959606823409130490,897662343959606824678201911⟩,⟨645860594990278562951585548,645860594990278564229728316⟩⟩,⟨⟨397661302041150198906510073424,397661302041150199296720796209⟩,⟨87891975067646749052475051597,87891975067646749440357915747⟩⟩]
lemma ha12_1_1_eq (j : Fin 7) : ha12_1_1 j = ((ha12_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha12_1_1_contains (j : Fin 7) : (ha12_1_1 j).Contains (fullFactor true 12 1 ((j.val:ℝ)/6)) := by
  rw [ha12_1_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_1_0 j) true 12 0 j (ha12_1_0_contains j)
noncomputable def hk12_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_2 j i k)
lemma hk12_1_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_1_2 j i k).Contains (fullFactor true 12 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_1_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel12_0 j i k) (mpower1_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 2 (kernel12_0_contains j i k) (mpower1_2_contains j i k)
noncomputable def ha12_1_2 : Fin 7 → CBox := ![⟨⟨0,130⟩,⟨(-130),130⟩⟩,⟨⟨(-89),204⟩,⟨(-104),197⟩⟩,⟨⟨(-1209466),(-1209259)⟩,⟨(-243934),(-243727)⟩⟩,⟨⟨(-8419396997543991),(-8419396997543874)⟩,⟨(-54211775273678897),(-54211775273678782)⟩⟩,⟨⟨(-14556982751376640076510),(-14556982751376639406589)⟩,⟨(-221899282215820242350707),(-221899282215820241680859)⟩⟩,⟨⟨1003151809858409199745334801,1003151809858409202808242868⟩,⟨(-2061049643971255242679803127),(-2061049643971255239630875182)⟩⟩,⟨⟨121355007055359754570274445483,121355007055359755307861562369⟩,⟨(-726234543583272508307474649490),(-726234543583272507564215399696)⟩⟩]
lemma ha12_1_2_eq (j : Fin 7) : ha12_1_2 j = ((ha12_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha12_1_2_contains (j : Fin 7) : (ha12_1_2 j).Contains (fullFactor true 12 2 ((j.val:ℝ)/6)) := by
  rw [ha12_1_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_1_1 j) true 12 1 j (ha12_1_1_contains j)
noncomputable def hk12_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_3 j i k)
lemma hk12_1_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_1_3 j i k).Contains (fullFactor true 12 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_1_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel12_0 j i k) (mpower1_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 3 (kernel12_0_contains j i k) (mpower1_3_contains j i k)
noncomputable def ha12_1_3 : Fin 7 → CBox := ![⟨⟨(-400),0⟩,⟨(-400),400⟩⟩,⟨⟨(-651),472⟩,⟨(-757),377⟩⟩,⟨⟨1565848,1566544⟩,⟨2475956,2476652⟩⟩,⟨⟨(-84367392959080205),(-84367392959079898)⟩,⟨65475763810682239,65475763810682548⟩⟩,⟨⟨(-334371089579930022060605),(-334371089579930020689539)⟩,⟨134503204342974931346563,134503204342974932717021⟩⟩,⟨⟨(-3042174272738510667139680138),(-3042174272738510662258998317)⟩,⟨(-882188156327165039792445665),(-882188156327165034899803331)⟩⟩,⟨⟨(-881746361238965949165084040176),(-881746361238965948221468117250)⟩,⟨(-100616198115873475850220498452),(-100616198115873474915273990647)⟩⟩]
lemma ha12_1_3_eq (j : Fin 7) : ha12_1_3 j = ((ha12_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha12_1_3_contains (j : Fin 7) : (ha12_1_3 j).Contains (fullFactor true 12 3 ((j.val:ℝ)/6)) := by
  rw [ha12_1_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_1_2 j) true 12 2 j (ha12_1_2_contains j)
noncomputable def hk12_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_4 j i k)
lemma hk12_1_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_1_4 j i k).Contains (fullFactor true 12 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_1_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel12_0 j i k) (mpower1_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 4 (kernel12_0_contains j i k) (mpower1_4_contains j i k)
noncomputable def ha12_1_4 : Fin 7 → CBox := ![⟨⟨0,922⟩,⟨(-922),922⟩⟩,⟨⟨(-1609),1599⟩,⟨(-1162),2056⟩⟩,⟨⟨1259649,1261403⟩,⟨(-5065462),(-5063709)⟩⟩,⟨⟨143306813236192521,143306813236193134⟩,⟨61419183329985352,61419183329985963⟩⟩,⟨⟨282023685098541581227140,282023685098541583330327⟩,⟨335242630588426771929975,335242630588426774034128⟩⟩,⟨⟨(-365345279102973091818743130),(-365345279102973085957824832)⟩,⟨3262378016722954847165573977,3262378016722954853022194137⟩⟩,⟨⟨(-49439809917090287570797620483),(-49439809917090286682051210487)⟩,⟨800725527717580900573211989170,800725527717580901471505705119⟩⟩]
lemma ha12_1_4_eq (j : Fin 7) : ha12_1_4 j = ((ha12_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha12_1_4_contains (j : Fin 7) : (ha12_1_4 j).Contains (fullFactor true 12 4 ((j.val:ℝ)/6)) := by
  rw [ha12_1_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_1_3 j) true 12 3 j (ha12_1_3_contains j)
noncomputable def hk12_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_5 j i k)
lemma hk12_1_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_1_5 j i k).Contains (fullFactor true 12 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_1_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel12_0 j i k) (mpower1_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 5 (kernel12_0_contains j i k) (mpower1_5_contains j i k)
noncomputable def ha12_1_5 : Fin 7 → CBox := ![⟨⟨(-1700),0⟩,⟨(-1700),1700⟩⟩,⟨⟨(-3316),3996⟩,⟨(-4342),2979⟩⟩,⟨⟨(-6459695),(-6456161)⟩,⟨3686996,3690530⟩⟩,⟨⟨(-18362012620301129),(-18362012620300157)⟩,⟨(-181173391290789430),(-181173391290788457)⟩⟩,⟨⟨224290183885505711843934,224290183885505714426841⟩,⟨(-362191692607018569302627),(-362191692607018566720424)⟩⟩,⟨⟨2717018901613117668572573769,2717018901613117674192002593⟩,⟨(-161033129697945136053872206),(-161033129697945130437772579)⟩⟩,⟨⟨580144841859343371046372105467,580144841859343371730347742431⟩,⟨5634704595080413397679880952,5634704595080414073481665032⟩⟩]
lemma ha12_1_5_eq (j : Fin 7) : ha12_1_5 j = ((ha12_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha12_1_5_contains (j : Fin 7) : (ha12_1_5 j).Contains (fullFactor true 12 5 ((j.val:ℝ)/6)) := by
  rw [ha12_1_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_1_4 j) true 12 4 j (ha12_1_4_contains j)
noncomputable def hk12_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_6 j i k)
lemma hk12_1_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_1_6 j i k).Contains (fullFactor true 12 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_1_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel12_0 j i k) (mpower1_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 6 (kernel12_0_contains j i k) (mpower1_6_contains j i k)
noncomputable def ha12_1_6 : Fin 7 → CBox := ![⟨⟨0,2612⟩,⟨(-2612),2612⟩⟩,⟨⟨(-7797),6083⟩,⟨(-6283),7603⟩⟩,⟨⟨8462631,8468566⟩,⟨2513286,2519220⟩⟩,⟨⟨(-145586713028482100),(-145586713028480812)⟩,⟨101086125539641714,101086125539643002⟩⟩,⟨⟨(-335533547526137494846980),(-335533547526137492205282)⟩,⟨(-81228117760337498069450),(-81228117760337495427615)⟩⟩,⟨⟨(-428579684156756623710990271),(-428579684156756619226089127)⟩,⟨(-1831068351809184380019116382),(-1831068351809184375527754642)⟩⟩,⟨⟨(-14764779625578476764683221683),(-14764779625578476336486261911)⟩,⟨(-349329362916570933261791842100),(-349329362916570932827887991785)⟩⟩]
lemma ha12_1_6_eq (j : Fin 7) : ha12_1_6 j = ((ha12_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha12_1_6_contains (j : Fin 7) : (ha12_1_6 j).Contains (fullFactor true 12 6 ((j.val:ℝ)/6)) := by
  rw [ha12_1_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_1_5 j) true 12 5 j (ha12_1_5_contains j)
noncomputable def hk12_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_7 j i k)
lemma hk12_1_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_1_7 j i k).Contains (fullFactor true 12 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_1_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel12_0 j i k) (mpower1_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 7 (kernel12_0_contains j i k) (mpower1_7_contains j i k)
noncomputable def ha12_1_7 : Fin 7 → CBox := ![⟨⟨(-3439),0⟩,⟨(-3439),3439⟩⟩,⟨⟨(-9999),12578⟩,⟨(-11558),11023⟩⟩,⟨⟨(-4107367),(-4098825)⟩,⟨(-8002557),(-7994016)⟩⟩,⟨⟨132626412875364609,132626412875366070⟩,⟨65375046744878292,65375046744879754⟩⟩,⟨⟨19025700156272412036256,19025700156272414352139⟩,⟨239035845330222402287450,239035845330222404603631⟩⟩,⟨⟨(-1025515064786729755508828481),(-1025515064786729752432820959)⟩,⟨434357935598569773825031536,434357935598569776895762366⟩⟩,⟨⟨(-179809284764419594904920963680),(-179809284764419594669025794248)⟩,⟨16987249972927504572110876586,16987249972927504804694370495⟩⟩]
lemma ha12_1_7_eq (j : Fin 7) : ha12_1_7 j = ((ha12_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha12_1_7_contains (j : Fin 7) : (ha12_1_7 j).Contains (fullFactor true 12 7 ((j.val:ℝ)/6)) := by
  rw [ha12_1_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_1_6 j) true 12 6 j (ha12_1_6_contains j)
noncomputable def hk12_1_8 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_8 j i k)
lemma hk12_1_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_1_8 j i k).Contains (fullFactor true 12 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_1_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel12_0 j i k) (mpower1_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 8 (kernel12_0_contains j i k) (mpower1_8_contains j i k)
noncomputable def ha12_1_8 : Fin 7 → CBox := ![⟨⟨0,3962⟩,⟨(-3962),3962⟩⟩,⟨⟨(-17425),14705⟩,⟨(-16409),15723⟩⟩,⟨⟨(-2629205),(-2618448)⟩,⟨7558558,7569315⟩⟩,⟨⟨(-5172125299657550),(-5172125299656099)⟩,⟨(-107812939643808127),(-107812939643806676)⟩⟩,⟨⟨134439038177650509380385,134439038177650511157102⟩,⟨(-56265380089764138489733),(-56265380089764136713404)⟩⟩,⟨⟨312094522408203376760596274,312094522408203378600501213⟩,⟨485451518706925730875613496,485451518706925732718543747⟩⟩,⟨⟨11888099307316885150631782042,11888099307316885261189608016⟩,⟨80763282045648610158473863463,80763282045648610270670552043⟩⟩]
lemma ha12_1_8_eq (j : Fin 7) : ha12_1_8 j = ((ha12_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha12_1_8_contains (j : Fin 7) : (ha12_1_8 j).Contains (fullFactor true 12 8 ((j.val:ℝ)/6)) := by
  rw [ha12_1_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_1_7 j) true 12 7 j (ha12_1_7_contains j)
noncomputable def hk12_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_9 j i k)
lemma hk12_1_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_1_9 j i k).Contains (fullFactor true 12 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_1_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel12_0 j i k) (mpower1_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 9 (kernel12_0_contains j i k) (mpower1_9_contains j i k)
noncomputable def ha12_1_9 : Fin 7 → CBox := ![⟨⟨(-4057),0⟩,⟨(-4057),4057⟩⟩,⟨⟨(-19305),21338⟩,⟨(-19468),21176⟩⟩,⟨⟨5757752,5769793⟩,⟨(-2642496),(-2630455)⟩⟩,⟨⟨(-59566856971790963),(-59566856971789683)⟩,⟨36836660294892444,36836660294893724⟩⟩,⟨⟨(-51518723627657546463402),(-51518723627657545252239)⟩,⟨(-59538310774410478478294),(-59538310774410477266912)⟩⟩,⟨⟨195933713564883926082194220,195933713564883927063503378⟩,⟨(-179656051765103063237525125),(-179656051765103062257559770)⟩⟩,⟨⟨32156227350071706879117530623,32156227350071706926544241382⟩,⟨(-6454825388740991421378976578),(-6454825388740991374659015020)⟩⟩]
lemma ha12_1_9_eq (j : Fin 7) : ha12_1_9 j = ((ha12_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha12_1_9_contains (j : Fin 7) : (ha12_1_9 j).Contains (fullFactor true 12 9 ((j.val:ℝ)/6)) := by
  rw [ha12_1_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_1_8 j) true 12 8 j (ha12_1_8_contains j)
noncomputable def hk12_1_10 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_10 j i k)
lemma hk12_1_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_1_10 j i k).Contains (fullFactor true 12 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_1_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel12_0 j i k) (mpower1_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 10 (kernel12_0_contains j i k) (mpower1_10_contains j i k)
noncomputable def ha12_1_10 : Fin 7 → CBox := ![⟨⟨0,3739⟩,⟨(-3739),3739⟩⟩,⟨⟨(-23597),22673⟩,⟨(-24168),22102⟩⟩,⟨⟨(-4201710),(-4189579)⟩,⟨(-1676415),(-1664284)⟩⟩,⟨⟨35674546456790503,35674546456791520⟩,⟨20003693883524556,20003693883525573⟩⟩,⟨⟨(-19699712207640474563068),(-19699712207640473819763)⟩,⟨32823771021233969849599,32823771021233970592828⟩⟩,⟨⟨(-87194525795308043228230677),(-87194525795308042758494171)⟩,⟨(-67391456163921622735072291),(-67391456163921622264863928)⟩⟩,⟨⟨(-2934662521517390782245028598),(-2934662521517390764474440250)⟩,⟨(-11490493005176072737951515324),(-11490493005176072719910983201)⟩⟩]
lemma ha12_1_10_eq (j : Fin 7) : ha12_1_10 j = ((ha12_1_9 j).mul (piI.mul (atomPoints j).z)).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha12_1_10_contains (j : Fin 7) : (ha12_1_10 j).Contains (fullFactor true 12 10 ((j.val:ℝ)/6)) := by
  rw [ha12_1_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_1_9 j) true 12 9 j (ha12_1_9_contains j)
noncomputable def hk12_1_11 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_11 j i k)
lemma hk12_1_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_1_11 j i k).Contains (fullFactor true 12 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_1_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel12_0 j i k) (mpower1_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 11 (kernel12_0_contains j i k) (mpower1_11_contains j i k)
noncomputable def ha12_1_11 : Fin 7 → CBox := ![⟨⟨(-3133),0⟩,⟨(-3133),3133⟩⟩,⟨⟨(-23970),23916⟩,⟨(-23067),24819⟩⟩,⟨⟨1090344,1101454⟩,⟨2706467,2717578⟩⟩,⟨⟨111451143979659,111451143980394⟩,⟨(-21713254791105582),(-21713254791104847)⟩⟩,⟨⟨16499777598985442559887,16499777598985442974493⟩,⟨3752067657357486987944,3752067657357487402560⟩⟩,⟨⟨(-19445682288577721204839725),(-19445682288577721000035180)⟩,⟨36698144803440582446380892,36698144803440582651059781⟩⟩,⟨⟨(-3721947092145361633426796985),(-3721947092145361627189023992)⟩,⟨1159522835501150289178579955,1159522835501150295323869784⟩⟩]
lemma ha12_1_11_eq (j : Fin 7) : ha12_1_11 j = ((ha12_1_10 j).mul (piI.mul (atomPoints j).z)).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha12_1_11_contains (j : Fin 7) : (ha12_1_11 j).Contains (fullFactor true 12 11 ((j.val:ℝ)/6)) := by
  rw [ha12_1_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_1_10 j) true 12 10 j (ha12_1_10_contains j)
noncomputable def hk12_1_12 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_12 j i k)
lemma hk12_1_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_1_12 j i k).Contains (fullFactor true 12 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_1_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel12_0 j i k) (mpower1_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 12 (kernel12_0_contains j i k) (mpower1_12_contains j i k)
noncomputable def ha12_1_12 : Fin 7 → CBox := ![⟨⟨0,2406⟩,⟨(-2406),2406⟩⟩,⟨⟨(-22426),23003⟩,⟨(-23266),22163⟩⟩,⟨⟨709638,718966⟩,⟨(-1587732),(-1578404)⟩⟩,⟨⟨(-9269400545525877),(-9269400545525390)⟩,⟨5073243044346633,5073243044347120⟩⟩,⟨⟨(-639044372753523510328),(-639044372753523298333)⟩,⟨(-6826209516733269815607),(-6826209516733269603603)⟩⟩,⟨⟨13634873130783275536921651,13634873130783275618666613⟩,⟨4466223382015006406271286,4466223382015006488036179⟩⟩,⟨⟨407162470023963183778106510,407162470023963185726243312⟩,⟨1101860031015938724259271972,1101860031015938726236118342⟩⟩]
lemma ha12_1_12_eq (j : Fin 7) : ha12_1_12 j = ((ha12_1_11 j).mul (piI.mul (atomPoints j).z)).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha12_1_12_contains (j : Fin 7) : (ha12_1_12 j).Contains (fullFactor true 12 12 ((j.val:ℝ)/6)) := by
  rw [ha12_1_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_1_11 j) true 12 11 j (ha12_1_11_contains j)
noncomputable def hk12_1_13 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_13 j i k)
lemma hk12_1_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_1_13 j i k).Contains (fullFactor true 12 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_1_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel12_0 j i k) (mpower1_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 13 (kernel12_0_contains j i k) (mpower1_13_contains j i k)
noncomputable def ha12_1_13 : Fin 7 → CBox := ![⟨⟨(-1706),0⟩,⟨(-1706),1706⟩⟩,⟨⟨(-20219),19564⟩,⟨(-19649),20134⟩⟩,⟨⟨(-901302),(-894073)⟩,⟨312966,320195⟩⟩,⟨⟨4011372127826766,4011372127827064⟩,⟨2537960439248751,2537960439249049⟩⟩,⟨⟨(-2351433400295992433173),(-2351433400295992333110)⟩,⟨1022809135565645839958,1022809135565645940014⟩⟩,⟨⟨664825758783034719549813,664825758783034749680262⟩,⟨(-4526775139293341501751547),(-4526775139293341471618691)⟩⟩,⟨⟨300183923098352559350460168,300183923098352559928703270⟩,⟨(-129013402682440290084988849),(-129013402682440289514888047)⟩⟩]
lemma ha12_1_13_eq (j : Fin 7) : ha12_1_13 j = ((ha12_1_12 j).mul (piI.mul (atomPoints j).z)).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha12_1_13_contains (j : Fin 7) : (ha12_1_13 j).Contains (fullFactor true 12 13 ((j.val:ℝ)/6)) := by
  rw [ha12_1_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_1_12 j) true 12 12 j (ha12_1_12_contains j)
noncomputable def hk12_1_14 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_14 j i k)
lemma hk12_1_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_1_14 j i k).Contains (fullFactor true 12 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_1_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel12_0 j i k) (mpower1_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 14 (kernel12_0_contains j i k) (mpower1_14_contains j i k)
noncomputable def ha12_1_14 : Fin 7 → CBox := ![⟨⟨0,1123⟩,⟨(-1123),1123⟩⟩,⟨⟨(-15932),16419⟩,⟨(-16221),16129⟩⟩,⟨⟨429559,434762⟩,⟨216294,221496⟩⟩,⟨⟨115177237867249,115177237867419⟩,⟨(-1976686525918239),(-1976686525918069)⟩⟩,⟨⟨592044781526464558595,592044781526464602447⟩,⟨665262605590692995240,665262605590693039095⟩⟩,⟨⟨(-1354389762449831494643053),(-1354389762449831484329979)⟩,⟨33730035249169909361574,33730035249169919671098⟩⟩,⟨⟨(-37302664176799394749652024),(-37302664176799394594731321)⟩,⟨(-75696191667594046603359272),(-75696191667594046446314404)⟩⟩]
lemma ha12_1_14_eq (j : Fin 7) : ha12_1_14 j = ((ha12_1_13 j).mul (piI.mul (atomPoints j).z)).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha12_1_14_contains (j : Fin 7) : (ha12_1_14 j).Contains (fullFactor true 12 14 ((j.val:ℝ)/6)) := by
  rw [ha12_1_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_1_13 j) true 12 13 j (ha12_1_13_contains j)
noncomputable def hk12_1_15 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_15 j i k)
lemma hk12_1_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_1_15 j i k).Contains (fullFactor true 12 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_1_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel12_0 j i k) (mpower1_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 15 (kernel12_0_contains j i k) (mpower1_15_contains j i k)
noncomputable def ha12_1_15 : Fin 7 → CBox := ![⟨⟨(-690),0⟩,⟨(-690),690⟩⟩,⟨⟨(-12412),12141⟩,⟨(-12313),12240⟩⟩,⟨⟨(-68442),(-64947)⟩,⟨(-221976),(-218481)⟩⟩,⟨⟨(-694894656750334),(-694894656750243)⟩,⟨333709370046484,333709370046575⟩⟩,⟨⟨145089811229911627220,145089811229911645159⟩,⟨(-249556698605227573365),(-249556698605227555426)⟩⟩,⟨⟨72780047412093170491536,72780047412093173783836⟩,⟨367288459824434332656522,367288459824434335950570⟩⟩,⟨⟨(-17755764851287819942344986),(-17755764851287819902539954)⟩,⟨9927641296462630329576723,9927641296462630368869094⟩⟩]
lemma ha12_1_15_eq (j : Fin 7) : ha12_1_15 j = ((ha12_1_14 j).mul (piI.mul (atomPoints j).z)).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha12_1_15_contains (j : Fin 7) : (ha12_1_15 j).Contains (fullFactor true 12 15 ((j.val:ℝ)/6)) := by
  rw [ha12_1_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_1_14 j) true 12 14 j (ha12_1_14_contains j)
noncomputable def hk12_1_16 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_16 j i k)
lemma hk12_1_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_1_16 j i k).Contains (fullFactor true 12 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_1_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel12_0 j i k) (mpower1_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 16 (kernel12_0_contains j i k) (mpower1_16_contains j i k)
noncomputable def ha12_1_16 : Fin 7 → CBox := ![⟨⟨0,398⟩,⟨(-398),398⟩⟩,⟨⟨(-8679),8792⟩,⟨(-8686),8784⟩⟩,⟨⟨(-51466),(-49264)⟩,⟨88136,90338⟩⟩,⟨⟨229451522452512,229451522452558⟩,⟨162832727143196,162832727143242⟩⟩,⟨⟨(-85800752104362923376),(-85800752104362916495)⟩,⟨(-18259125369958110177),(-18259125369958103297)⟩⟩,⟨⟨90576420994478944542385,90576420994478945528691⟩,⟨(-34750696979472963738664),(-34750696979472962752925)⟩⟩,⟨⟨2448939421412117926768433,2448939421412117936111235⟩,⟨3890773919362264140698550,3890773919362264150156369⟩⟩]
lemma ha12_1_16_eq (j : Fin 7) : ha12_1_16 j = ((ha12_1_15 j).mul (piI.mul (atomPoints j).z)).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha12_1_16_contains (j : Fin 7) : (ha12_1_16 j).Contains (fullFactor true 12 16 ((j.val:ℝ)/6)) := by
  rw [ha12_1_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_1_15 j) true 12 15 j (ha12_1_15_contains j)
noncomputable def hk12_1_17 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_17 j i k)
lemma hk12_1_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_1_17 j i k).Contains (fullFactor true 12 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_1_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel12_0 j i k) (mpower1_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 17 (kernel12_0_contains j i k) (mpower1_17_contains j i k)
noncomputable def ha12_1_17 : Fin 7 → CBox := ![⟨⟨(-216),0⟩,⟨(-216),216⟩⟩,⟨⟨(-5865),5835⟩,⟨(-5884),5816⟩⟩,⟨⟨40968,42274⟩,⟨(-11240),(-9934)⟩⟩,⟨⟨10732372738145,10732372738168⟩,⟨(-96053963494581),(-96053963494558)⟩⟩,⟨⟨2685985983682311391,2685985983682313875⟩,⟨24945154781658022493,24945154781658024978⟩⟩,⟨⟨(-12103547896911307343880),(-12103547896911307066094)⟩,⟨(-20326847232071309020638),(-20326847232071308742703)⟩⟩,⟨⟨799402374366918776037730,799402374366918778152610⟩,⟨(-563162805071724530034411),(-563162805071724527943616)⟩⟩]
lemma ha12_1_17_eq (j : Fin 7) : ha12_1_17 j = ((ha12_1_16 j).mul (piI.mul (atomPoints j).z)).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha12_1_17_contains (j : Fin 7) : (ha12_1_17 j).Contains (fullFactor true 12 17 ((j.val:ℝ)/6)) := by
  rw [ha12_1_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_1_16 j) true 12 16 j (ha12_1_16_contains j)
noncomputable def hk12_1_18 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_18 j i k)
lemma hk12_1_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_1_18 j i k).Contains (fullFactor true 12 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_1_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel12_0 j i k) (mpower1_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 18 (kernel12_0_contains j i k) (mpower1_18_contains j i k)
noncomputable def ha12_1_18 : Fin 7 → CBox := ![⟨⟨0,111⟩,⟨(-111),111⟩⟩,⟨⟨(-3701),3700⟩,⟨(-3683),3718⟩⟩,⟨⟨(-14780),(-14048)⟩,⟨(-9379),(-8647)⟩⟩,⟨⟨(-28946838471415),(-28946838471404)⟩,⟨12055974768646,12055974768657⟩⟩,⟨⟨6176451077383268828,6176451077383269676⟩,⟨(-2789445976758883829),(-2789445976758882981)⟩⟩,⟨⟨(-4139811040120070668450),(-4139811040120070594484)⟩,⟨3542382064852513198377,3542382064852513272311⟩⟩,⟨⟨(-121316778784812561895302),(-121316778784812561453413)⟩,⟨(-154495323355782595617540),(-154495323355782595170928)⟩⟩]
lemma ha12_1_18_eq (j : Fin 7) : ha12_1_18 j = ((ha12_1_17 j).mul (piI.mul (atomPoints j).z)).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha12_1_18_contains (j : Fin 7) : (ha12_1_18 j).Contains (fullFactor true 12 18 ((j.val:ℝ)/6)) := by
  rw [ha12_1_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_1_17 j) true 12 17 j (ha12_1_17_contains j)
noncomputable def hk12_1_19 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_19 j i k)
lemma hk12_1_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_1_19 j i k).Contains (fullFactor true 12 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_1_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel12_0 j i k) (mpower1_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 19 (kernel12_0_contains j i k) (mpower1_19_contains j i k)
noncomputable def ha12_1_19 : Fin 7 → CBox := ![⟨⟨(-54),0⟩,⟨(-54),54⟩⟩,⟨⟨(-2214),2221⟩,⟨(-2225),2211⟩⟩,⟨⟨1098,1487⟩,⟨6048,6437⟩⟩,⟨⟨7552868186813,7552868186819⟩,⟨5986858901887,5986858901893⟩⟩,⟨⟨(-1170880804984483039),(-1170880804984482764)⟩,⟨(-1279375383114849324),(-1279375383114849049)⟩⟩,⟨⟨915124693907503222479,915124693907503241122⟩,⟨758812426888307749312,758812426888307767961⟩⟩,⟨⟨(-28163504054274280263151),(-28163504054274280173806)⟩,⟨24583586955638690226656,24583586955638690315132⟩⟩]
lemma ha12_1_19_eq (j : Fin 7) : ha12_1_19 j = ((ha12_1_18 j).mul (piI.mul (atomPoints j).z)).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha12_1_19_contains (j : Fin 7) : (ha12_1_19 j).Contains (fullFactor true 12 19 ((j.val:ℝ)/6)) := by
  rw [ha12_1_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_1_18 j) true 12 18 j (ha12_1_18_contains j)
noncomputable def hk12_1_20 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_20 j i k)
lemma hk12_1_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_1_20 j i k).Contains (fullFactor true 12 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_1_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel12_0 j i k) (mpower1_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 20 (kernel12_0_contains j i k) (mpower1_20_contains j i k)
noncomputable def ha12_1_20 : Fin 7 → CBox := ![⟨⟨0,25⟩,⟨(-25),25⟩⟩,⟨⟨(-1265),1260⟩,⟨(-1261),1265⟩⟩,⟨⟨1191,1388⟩,⟨(-1968),(-1771)⟩⟩,⟨⟨460401661652,460401661655⟩,⟨(-2776245354990),(-2776245354986)⟩⟩,⟨⟨(-206819933032496471),(-206819933032496385)⟩,⟨367408320818785892,367408320818785978⟩⟩,⟨⟨122772323504097661794,122772323504097666261⟩,⟨(-213649535057756680219),(-213649535057756675752)⟩⟩,⟨⟨4703016411804920125259,4703016411804920142088⟩,⟨4854150195112699790509,4854150195112699807489⟩⟩]
lemma ha12_1_20_eq (j : Fin 7) : ha12_1_20 j = ((ha12_1_19 j).mul (piI.mul (atomPoints j).z)).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha12_1_20_contains (j : Fin 7) : (ha12_1_20 j).Contains (fullFactor true 12 20 ((j.val:ℝ)/6)) := by
  rw [ha12_1_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_1_19 j) true 12 19 j (ha12_1_19_contains j)
noncomputable def hk12_1_21 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_21 j i k)
lemma hk12_1_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_1_21 j i k).Contains (fullFactor true 12 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_1_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel12_0 j i k) (mpower1_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 21 (kernel12_0_contains j i k) (mpower1_21_contains j i k)
noncomputable def ha12_1_21 : Fin 7 → CBox := ![⟨⟨(-11),0⟩,⟨(-11),11⟩⟩,⟨⟨(-684),686⟩,⟨(-685),685⟩⟩,⟨⟨(-809),(-713)⟩,⟨74,170⟩⟩,⟨⟨(-737370077630),(-737370077628)⟩,⟨262137085294,262137085296⟩⟩,⟨⟨95753733033877437,95753733033877463⟩,⟨18988156434296078,18988156434296104⟩⟩,⟨⟨(-45680512621259045580),(-45680512621259044560)⟩,⟨(-16718421102142236901),(-16718421102142235881)⟩⟩,⟨⟨792636265917762104832,792636265917762107906⟩,⟨(-852104513620291070903),(-852104513620291067854)⟩⟩]
lemma ha12_1_21_eq (j : Fin 7) : ha12_1_21 j = ((ha12_1_20 j).mul (piI.mul (atomPoints j).z)).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha12_1_21_contains (j : Fin 7) : (ha12_1_21 j).Contains (fullFactor true 12 21 ((j.val:ℝ)/6)) := by
  rw [ha12_1_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_1_20 j) true 12 20 j (ha12_1_20_contains j)
noncomputable def hk12_1_22 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_22 j i k)
lemma hk12_1_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_1_22 j i k).Contains (fullFactor true 12 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_1_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel12_0 j i k) (mpower1_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 22 (kernel12_0_contains j i k) (mpower1_22_contains j i k)
noncomputable def ha12_1_22 : Fin 7 → CBox := ![⟨⟨0,5⟩,⟨(-5),5⟩⟩,⟨⟨(-355),355⟩,⟨(-355),355⟩⟩,⟨⟨176,221⟩,⟨128,173⟩⟩,⟨⟨155718997593,155718997595⟩,⟨137493121900,137493121902⟩⟩,⟨⟨(-2607998181537085),(-2607998181537076)⟩,⟨(-21416138072061820),(-21416138072061812)⟩⟩,⟨⟨(-1642122016580049803),(-1642122016580049580)⟩,⟨9017876610944314623,9017876610944314846⟩⟩,⟨⟨(-146627616202662846276),(-146627616202662845747)⟩,⟨(-122828530585784551379),(-122828530585784550847)⟩⟩]
lemma ha12_1_22_eq (j : Fin 7) : ha12_1_22 j = ((ha12_1_21 j).mul (piI.mul (atomPoints j).z)).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha12_1_22_contains (j : Fin 7) : (ha12_1_22 j).Contains (fullFactor true 12 22 ((j.val:ℝ)/6)) := by
  rw [ha12_1_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_1_21 j) true 12 21 j (ha12_1_21_contains j)
noncomputable def hk12_1_23 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_23 j i k)
lemma hk12_1_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_1_23 j i k).Contains (fullFactor true 12 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_1_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel12_0 j i k) (mpower1_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 23 (kernel12_0_contains j i k) (mpower1_23_contains j i k)
noncomputable def ha12_1_23 : Fin 7 → CBox := ![⟨⟨(-3),0⟩,⟨(-3),3⟩⟩,⟨⟨(-176),176⟩,⟨(-176),176⟩⟩,⟨⟨(-19),2⟩,⟨(-87),(-66)⟩⟩,⟨⟨11376984564,11376984566⟩,⟨(-51502616354),(-51502616353)⟩⟩,⟨⟨(-4130012158259014),(-4130012158259011)⟩,⟨1934869848805713,1934869848805716⟩⟩,⟨⟨1652054365299038671,1652054365299038719⟩,⟨15531245591146493,15531245591146540⟩⟩,⟨⟨(-18087141867166175134),(-18087141867166175045)⟩,⟨24023481097517485766,24023481097517485854⟩⟩]
lemma ha12_1_23_eq (j : Fin 7) : ha12_1_23 j = ((ha12_1_22 j).mul (piI.mul (atomPoints j).z)).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha12_1_23_contains (j : Fin 7) : (ha12_1_23 j).Contains (fullFactor true 12 23 ((j.val:ℝ)/6)) := by
  rw [ha12_1_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_1_22 j) true 12 22 j (ha12_1_22_contains j)
noncomputable def hk12_1_24 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_24 j i k)
lemma hk12_1_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_1_24 j i k).Contains (fullFactor true 12 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_1_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel12_0 j i k) (mpower1_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 24 (kernel12_0_contains j i k) (mpower1_24_contains j i k)
noncomputable def ha12_1_24 : Fin 7 → CBox := ![⟨⟨0,2⟩,⟨(-2),2⟩⟩,⟨⟨(-84),84⟩,⟨(-84),84⟩⟩,⟨⟨(-20),(-10)⟩,⟨13,22⟩⟩,⟨⟨(-12303606146),(-12303606144)⟩,⟨3651455452,3651455454⟩⟩,⟨⟨633229932800537,633229932800539⟩,⟨672858084776373,672858084776375⟩⟩,⟨⟨(-45837519785308592),(-45837519785308582)⟩,⟨(-281669578683673109),(-281669578683673099)⟩⟩,⟨⟨3756070794749000448,3756070794749000463⟩,⟨2533423776072111742,2533423776072111758⟩⟩]
lemma ha12_1_24_eq (j : Fin 7) : ha12_1_24 j = ((ha12_1_23 j).mul (piI.mul (atomPoints j).z)).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha12_1_24_contains (j : Fin 7) : (ha12_1_24 j).Contains (fullFactor true 12 24 ((j.val:ℝ)/6)) := by
  rw [ha12_1_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_1_23 j) true 12 23 j (ha12_1_23_contains j)
noncomputable def hk12_1_25 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_25 j i k)
lemma hk12_1_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_1_25 j i k).Contains (fullFactor true 12 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_1_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel12_0 j i k) (mpower1_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 25 (kernel12_0_contains j i k) (mpower1_25_contains j i k)
noncomputable def ha12_1_25 : Fin 7 → CBox := ![⟨⟨(-1),0⟩,⟨(-1),1⟩⟩,⟨⟨(-39),39⟩,⟨(-39),39⟩⟩,⟨⟨4,9⟩,⟨(-3),2⟩⟩,⟨⟨2138868459,2138868461⟩,⟨2100668034,2100668036⟩⟩,⟨⟨85961120613435,85961120613437⟩,⟨(-157805411657712),(-157805411657710)⟩⟩,⟨⟨(-44736800715453273),(-44736800715453270)⟩,⟨15425645641545957,15425645641545960⟩⟩,⟨⟨337718768448286647,337718768448286651⟩,⟨(-561559156890124354),(-561559156890124351)⟩⟩]
lemma ha12_1_25_eq (j : Fin 7) : ha12_1_25 j = ((ha12_1_24 j).mul (piI.mul (atomPoints j).z)).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha12_1_25_contains (j : Fin 7) : (ha12_1_25 j).Contains (fullFactor true 12 25 ((j.val:ℝ)/6)) := by
  rw [ha12_1_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_1_24 j) true 12 24 j (ha12_1_24_contains j)
noncomputable def hk12_1_26 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_26 j i k)
lemma hk12_1_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_1_26 j i k).Contains (fullFactor true 12 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_1_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel12_0 j i k) (mpower1_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 26 (kernel12_0_contains j i k) (mpower1_26_contains j i k)
noncomputable def ha12_1_26 : Fin 7 → CBox := ![⟨⟨0,1⟩,⟨(-1),1⟩⟩,⟨⟨(-18),18⟩,⟨(-18),18⟩⟩,⟨⟨(-3),0⟩,⟨(-3),0⟩⟩,⟨⟨179916576,179916577⟩,⟨(-648877112),(-648877111)⟩⟩,⟨⟨(-33050809081732),(-33050809081731)⟩,⟨(-6077230735886),(-6077230735884)⟩⟩,⟨⟨3635641658270842,3635641658270843⟩,⟨6611489031238316,6611489031238318⟩⟩,⟨⟨(-80431512446630962),(-80431512446630960)⟩,⟨(-42848670008874491),(-42848670008874489)⟩⟩]
lemma ha12_1_26_eq (j : Fin 7) : ha12_1_26 j = ((ha12_1_25 j).mul (piI.mul (atomPoints j).z)).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha12_1_26_contains (j : Fin 7) : (ha12_1_26 j).Contains (fullFactor true 12 26 ((j.val:ℝ)/6)) := by
  rw [ha12_1_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_1_25 j) true 12 25 j (ha12_1_25_contains j)
noncomputable def hk12_1_27 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_27 j i k)
lemma hk12_1_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_1_27 j i k).Contains (fullFactor true 12 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_1_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel12_0 j i k) (mpower1_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 27 (kernel12_0_contains j i k) (mpower1_27_contains j i k)
noncomputable def ha12_1_27 : Fin 7 → CBox := ![⟨⟨(-1),0⟩,⟨(-1),1⟩⟩,⟨⟨(-8),8⟩,⟨(-8),8⟩⟩,⟨⟨(-1),1⟩,⟨0,2⟩⟩,⟨⟨(-141622524),(-141622522)⟩,⟨33972212,33972214⟩⟩,⟨⟨815074688456,815074688457⟩,⟨5996427841651,5996427841652⟩⟩,⟨⟨905529230184848,905529230184850⟩,⟨(-722562129290903),(-722562129290902)⟩⟩,⟨⟨(-5171287713399826),(-5171287713399825)⟩,⟨11055041638956256,11055041638956257⟩⟩]
lemma ha12_1_27_eq (j : Fin 7) : ha12_1_27 j = ((ha12_1_26 j).mul (piI.mul (atomPoints j).z)).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha12_1_27_contains (j : Fin 7) : (ha12_1_27 j).Contains (fullFactor true 12 27 ((j.val:ℝ)/6)) := by
  rw [ha12_1_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_1_26 j) true 12 26 j (ha12_1_26_contains j)
noncomputable def hk12_1_28 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_28 j i k)
lemma hk12_1_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_1_28 j i k).Contains (fullFactor true 12 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_1_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel12_0 j i k) (mpower1_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 28 (kernel12_0_contains j i k) (mpower1_28_contains j i k)
noncomputable def ha12_1_28 : Fin 7 → CBox := ![⟨⟨0,1⟩,⟨(-1),1⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨20511770,20511771⟩,⟨22403809,22403810⟩⟩,⟨⟨945296541218,945296541219⟩,⟨(-459012925014),(-459012925013)⟩⟩,⟨⟨(-128201750083820),(-128201750083819)⟩,⟨(-113944672484683),(-113944672484681)⟩⟩,⟨⟨1460395473380750,1460395473380751⟩,⟨592779012106575,592779012106577⟩⟩]
lemma ha12_1_28_eq (j : Fin 7) : ha12_1_28 j = ((ha12_1_27 j).mul (piI.mul (atomPoints j).z)).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha12_1_28_contains (j : Fin 7) : (ha12_1_28 j).Contains (fullFactor true 12 28 ((j.val:ℝ)/6)) := by
  rw [ha12_1_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_1_27 j) true 12 27 j (ha12_1_27_contains j)
noncomputable def hk12_1_29 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_29 j i k)
lemma hk12_1_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_1_29 j i k).Contains (fullFactor true 12 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_1_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel12_0 j i k) (mpower1_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 29 (kernel12_0_contains j i k) (mpower1_29_contains j i k)
noncomputable def ha12_1_29 : Fin 7 → CBox := ![⟨⟨(-1),0⟩,⟨(-1),1⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨1944720,1944721⟩,⟨(-5799393),(-5799392)⟩⟩,⟨⟨(-122520550745),(-122520550744)⟩,⟨(-126610055462),(-126610055460)⟩⟩,⟨⟨(-12938088991960),(-12938088991958)⟩,⟨20827376155776,20827376155777⟩⟩,⟨⟨64355761780807,64355761780808⟩,⟨(-185683937390799),(-185683937390798)⟩⟩]
lemma ha12_1_29_eq (j : Fin 7) : ha12_1_29 j = ((ha12_1_28 j).mul (piI.mul (atomPoints j).z)).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha12_1_29_contains (j : Fin 7) : (ha12_1_29 j).Contains (fullFactor true 12 29 ((j.val:ℝ)/6)) := by
  rw [ha12_1_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_1_28 j) true 12 28 j (ha12_1_28_contains j)
noncomputable def hk12_1_30 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_30 j i k)
lemma hk12_1_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk12_1_30 j i k).Contains (fullFactor true 12 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk12_1_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel12_0 j i k) (mpower1_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 12 30 (kernel12_0_contains j i k) (mpower1_30_contains j i k)
noncomputable def ha12_1_30 : Fin 7 → CBox := ![⟨⟨0,1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1170949),(-1170948)⟩,⟨215934,215935⟩⟩,⟨⟨(-13309159360),(-13309159359)⟩,⟨25263432859,25263432860⟩⟩,⟨⟨3139945284923,3139945284924⟩,⟨1272903258987,1272903258988⟩⟩,⟨⟨(-22753127670298),(-22753127670296)⟩,⟨(-6584127860527),(-6584127860526)⟩⟩]
lemma ha12_1_30_eq (j : Fin 7) : ha12_1_30 j = ((ha12_1_29 j).mul (piI.mul (atomPoints j).z)).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha12_1_30_contains (j : Fin 7) : (ha12_1_30 j).Contains (fullFactor true 12 30 ((j.val:ℝ)/6)) := by
  rw [ha12_1_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha12_1_29 j) true 12 29 j (ha12_1_29_contains j)
end SharpPlanar.CachedData

end OAI
