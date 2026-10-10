import OAI.Analysis.PlanarPacking.Certificate.Powers30
import OAI.Analysis.PlanarPacking.Certificate.KernelValues30
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
noncomputable def hk24_0_0 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_0 j i k)
lemma hk24_0_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_0_0 j i k).Contains (fullFactor false 24 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_0_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power24 j i k) (mpower0_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 0 (power24_contains j i k) (mpower0_0_contains j i k)
noncomputable def ha24_0_0 : Fin 7 → CBox := ![⟨⟨999999999999999999999999999713,1000000000000000000000000000383⟩,⟨(-383),383⟩⟩,⟨⟨999999999999999999973702175385,1000000000000000000026297824647⟩,⟨(-17218479783),36071413471⟩⟩,⟨⟨999999999999999999927542457041,1000000000000000000072457542975⟩,⟨(-53350537359),91056404863⟩⟩,⟨⟨999999999999999999921599800913,1000000000000000000078400199111⟩,⟨(-50120798495),106679599727⟩⟩,⟨⟨999999999999999999802292497873,1000000000000000000197707502071⟩,⟨(-160187373927),235599108999⟩⟩,⟨⟨999999999999999999750954293361,1000000000000000000249045706567⟩,⟨(-201729023199),295993691951⟩⟩,⟨⟨999999999999999999842723253233,1000000000000000000157276746863⟩,⟨(-100717945487),213835548143⟩⟩]
lemma ha24_0_0_eq (j : Fin 7) : ha24_0_0 j = ((atomPoints j).direct.powBin 7 24).conj := by fin_cases j <;> decide +kernel
lemma ha24_0_0_contains (j : Fin 7) : (ha24_0_0 j).Contains (fullFactor false 24 0 ((j.val:ℝ)/6)) := by
  rw [ha24_0_0_eq]
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @direct_factor_zero_full ((atomPoints j).direct.powBin 7 24) ((j.val:ℝ)/6) 24 (@direct_power_bin_contains (atomPoints j) ((j.val:ℝ)/6) (atomPoints_contains j) 24 (by norm_num))
noncomputable def hk24_0_1 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_1 j i k)
lemma hk24_0_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_0_1 j i k).Contains (fullFactor false 24 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_0_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power24 j i k) (mpower0_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 1 (power24_contains j i k) (mpower0_1_contains j i k)
noncomputable def ha24_0_1 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-18886947928),9015574933⟩,⟨523598775598298873062897157894,523598775598298873092102842122⟩⟩,⟨⟨(-95354044194),55868552078⟩,⟨1047197551196597746077455971779,1047197551196597746232544028239⟩⟩,⟨⟨(-167571923396),78729566172⟩,⟨1570796326794896619106849255254,1570796326794896619358150744784⟩⟩,⟨⟨(-493437620016),335495651418⟩,⟨2094395102393195491892589042502,2094395102393195492727410957379⟩⟩,⟨⟨(-774909673452),528125347749⟩,⟨2617993877991494364731333198011,2617993877991494366043666801802⟩⟩,⟨⟨(-671784187123),316414757627⟩,⟨3141592653589793237965900527776,3141592653589793238964099472526⟩⟩]
lemma ha24_0_1_eq (j : Fin 7) : ha24_0_1 j = ((ha24_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha24_0_1_contains (j : Fin 7) : (ha24_0_1 j).Contains (fullFactor false 24 1 ((j.val:ℝ)/6)) := by
  rw [ha24_0_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_0_0 j) false 24 0 j (ha24_0_0_contains j)
noncomputable def hk24_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_2 j i k)
lemma hk24_0_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_0_2 j i k).Contains (fullFactor false 24 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_0_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power24 j i k) (mpower0_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 2 (power24_contains j i k) (mpower0_2_contains j i k)
noncomputable def ha24_0_2 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-137077838904018869710281432111),(-137077838904018869702199069544)⟩,⟨(-4944591405),2360271999⟩⟩,⟨⟨(-548311355616075478866435626170),(-548311355616075478783486380443)⟩,⟨(-49927260789),29252705463⟩⟩,⟨⟨(-1233700550136169827456811617020),(-1233700550136169827255512897867)⟩,⟨(-131610680873),61834056677⟩⟩,⟨⟨(-2193245422464301915740446404123),(-2193245422464301914859241622165)⟩,⟨(-516726667350),351330224603⟩⟩,⟨⟨(-3426945972600471743520380759581),(-3426945972600471741791631781446)⟩,⟨(-1014354390547),691314463610⟩⟩,⟨⟨(-4934802200544679310216486629498),(-4934802200544679308632811430405)⟩,⟨(-1055236133532),497023139025⟩⟩]
lemma ha24_0_2_eq (j : Fin 7) : ha24_0_2 j = ((ha24_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha24_0_2_contains (j : Fin 7) : (ha24_0_2 j).Contains (fullFactor false 24 2 ((j.val:ℝ)/6)) := by
  rw [ha24_0_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_0_1 j) false 24 1 j (ha24_0_1_contains j)
noncomputable def hk24_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_3 j i k)
lemma hk24_0_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_0_3 j i k).Contains (fullFactor false 24 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_0_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power24 j i k) (mpower0_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 3 (power24_contains j i k) (mpower0_3_contains j i k)
noncomputable def ha24_0_3 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-411945177),862994002⟩,⟨(-23924596203935046432491923909),(-23924596203935046431005131171)⟩⟩,⟨⟨(-10211120509),17427901746⟩,⟨(-191396769631480371468770212239),(-191396769631480371439206228398)⟩⟩,⟨⟨(-32376236367),68911191361⟩,⟨(-645964097506246253710938208809),(-645964097506246253603482278347)⟩⟩,⟨⟨(-245274767244),360743267125⟩,⟨(-1531174157051842971941941198443),(-1531174157051842971321870326543)⟩⟩,⟨⟨(-603285677833),885191194856⟩,⟨(-2990574525491880804727634629760),(-2990574525491880803209497254939)⟩⟩,⟨⟨(-520481414076),1105040694969⟩,⟨(-5167712780049970030095117014335),(-5167712780049970028420246883285)⟩⟩]
lemma ha24_0_3_eq (j : Fin 7) : ha24_0_3 j = ((ha24_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha24_0_3_contains (j : Fin 7) : (ha24_0_3 j).Contains (fullFactor false 24 3 ((j.val:ℝ)/6)) := by
  rw [ha24_0_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_0_2 j) false 24 2 j (ha24_0_2_contains j)
noncomputable def hk24_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_4 j i k)
lemma hk24_0_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_0_4 j i k).Contains (fullFactor false 24 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_0_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power24 j i k) (mpower0_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 4 (power24_contains j i k) (mpower0_4_contains j i k)
noncomputable def ha24_0_4 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨3131722319766024859617761046,3131722319766024859822350343⟩,⟨(-53923498),112965651⟩⟩,⟨⟨50107557116256397751571226026,50107557116256397759470556206⟩,⟨(-2673265098),4562614008⟩⟩,⟨⟨253669507901048013615821861107,253669507901048013658827161446⟩,⟨(-12714118291),27061361567⟩⟩,⟨⟨801720913860102363924724104707,801720913860102364251944410949⟩,⟨(-128425567815),188884732972⟩⟩,⟨⟨1957326449853765536825110333186,1957326449853765537824959285093⟩,⟨(-394849552812),579356282247⟩⟩,⟨⟨4058712126416768217533012577165,4058712126416768218861371783972⟩,⟨(-408785146698),867896932309⟩⟩]
lemma ha24_0_4_eq (j : Fin 7) : ha24_0_4 j = ((ha24_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha24_0_4_contains (j : Fin 7) : (ha24_0_4 j).Contains (fullFactor false 24 4 ((j.val:ℝ)/6)) := by
  rw [ha24_0_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_0_3 j) false 24 3 j (ha24_0_3_contains j)
noncomputable def hk24_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_5 j i k)
lemma hk24_0_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_0_5 j i k).Contains (fullFactor false 24 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_0_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power24 j i k) (mpower0_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 5 (power24_contains j i k) (mpower0_5_contains j i k)
noncomputable def ha24_0_5 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-11829736),5646856⟩,⟨327953194428670967564092732,327953194428670967586561181⟩⟩,⟨⟨(-955591644),559887333⟩,⟨10494502221717470961566544162,10494502221717470963254381045⟩⟩,⟨⟨(-8501577470),3994258062⟩,⟨79692626246167045113922358858,79692626246167045127686541928⟩⟩,⟨⟨(-79119851931),53794776051⟩,⟨335824071094959070728067462000,335824071094959070866202144579⟩⟩,⟨⟨(-303350240020),206742742398⟩,⟨1024853732589596773409505789673,1024853732589596773936287687426⟩⟩,⟨⟨(-545315725324),256847282753⟩,⟨2550164039877345443444367348008,2550164039877345444287117477349⟩⟩]
lemma ha24_0_5_eq (j : Fin 7) : ha24_0_5 j = ((ha24_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha24_0_5_contains (j : Fin 7) : (ha24_0_5 j).Contains (fullFactor false 24 5 ((j.val:ℝ)/6)) := by
  rw [ha24_0_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_0_4 j) false 24 4 j (ha24_0_4_contains j)
noncomputable def hk24_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_6 j i k)
lemma hk24_0_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_0_6 j i k).Contains (fullFactor false 24 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_0_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power24 j i k) (mpower0_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 6 (power24_contains j i k) (mpower0_6_contains j i k)
noncomputable def ha24_0_6 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-28619315176067161692583588),(-28619315176067161690531747)⟩,⟨(-1032340),492782⟩⟩,⟨⟨(-1831636171268298348409897424),(-1831636171268298348109484036)⟩,⟨(-166782205),97718775⟩⟩,⟨⟨(-20863480763352960874980472332),(-20863480763352960871310607108)⟩,⟨(-2225707777),1045694316⟩⟩,⟨⟨(-117224714961171094312915825858),(-117224714961171094264324587556)⟩,⟨(-27618038398),18777919250⟩⟩,⟨⟨(-447176799626049401546226243007),(-447176799626049401314950871151)⟩,⟨(-132361511877),90208538987⟩⟩,⟨⟨(-1335262768854589496104071146761),(-1335262768854589495658557937502)⟩,⟨(-285526646095),134484922766⟩⟩]
lemma ha24_0_6_eq (j : Fin 7) : ha24_0_6 j = ((ha24_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha24_0_6_contains (j : Fin 7) : (ha24_0_6 j).Contains (fullFactor false 24 6 ((j.val:ℝ)/6)) := by
  rw [ha24_0_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_0_5 j) false 24 5 j (ha24_0_5_contains j)
noncomputable def hk24_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_7 j i k)
lemma hk24_0_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_0_7 j i k).Contains (fullFactor false 24 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_0_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power24 j i k) (mpower0_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 7 (power24_contains j i k) (mpower0_7_contains j i k)
noncomputable def ha24_0_7 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-36861),77219⟩,⟨(-2140719769235797028296903),(-2140719769235797028136611)⟩⟩,⟨⟨(-14618695),24950560⟩,⟨(-274012130462182019634651869),(-274012130462182019588837922)⟩⟩,⟨⟨(-234653256),499447658⟩,⟨(-4681754135318688101129256707),(-4681754135318688100290838389)⟩⟩,⟨⟨(-5618340302),8263297766⟩,⟨(-35073552699159298517628400147),(-35073552699159298502978293058)⟩⟩,⟨⟨(-33737914688),49503089683⟩,⟨(-167243731971546642872948710288),(-167243731971546642785919570147)⟩⟩,⟨⟨(-60356692198),128144059111⟩,⟨(-599264529320792076991812775641),(-599264529320792076789959396644)⟩⟩]
lemma ha24_0_7_eq (j : Fin 7) : ha24_0_7 j = ((ha24_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha24_0_7_contains (j : Fin 7) : (ha24_0_7 j).Contains (fullFactor false 24 7 ((j.val:ℝ)/6)) := by
  rw [ha24_0_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_0_6 j) false 24 6 j (ha24_0_6_contains j)
noncomputable def hk24_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_8 j i k)
lemma hk24_0_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_0_8 j i k).Contains (fullFactor false 24 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_0_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power24 j i k) (mpower0_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 8 (power24_contains j i k) (mpower0_8_contains j i k)
noncomputable def ha24_0_8 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨140109781258867029448461,140109781258867029459399⟩,⟨(-2413),5054⟩⟩,⟨⟨35868104002269959537150401,35868104002269959543261606⟩,⟨(-1913583),3266021⟩⟩,⟨⟨919260274839426580163458197,919260274839426580331007346⟩,⟨(-46074060),98066319⟩⟩,⟨⟨9182234624581109640360428406,9182234624581109644225045434⟩,⟨(-1470878052),2163326297⟩⟩,⟨⟨54730383304244933366114073796,54730383304244933394768505530⟩,⟨(-11040706764),16199848217⟩⟩,⟨⟨235330630358893204503283230980,235330630358893204583299948213⟩,⟨(-23702017601),50322054339⟩⟩]
lemma ha24_0_8_eq (j : Fin 7) : ha24_0_8 j = ((ha24_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha24_0_8_contains (j : Fin 7) : (ha24_0_8 j).Contains (fullFactor false 24 8 ((j.val:ℝ)/6)) := by
  rw [ha24_0_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_0_7 j) false 24 7 j (ha24_0_7_contains j)
noncomputable def hk24_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_9 j i k)
lemma hk24_0_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_0_9 j i k).Contains (fullFactor false 24 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_0_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power24 j i k) (mpower0_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 9 (power24_contains j i k) (mpower0_9_contains j i k)
noncomputable def ha24_0_9 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-295),141⟩,⟨8151256657387584304589,8151256657387584305252⟩⟩,⟨⟨(-380019),222656⟩,⟨4173443408582443163756958,4173443408582443164481314⟩⟩,⟨⟨(-17115802),8041441⟩,⟨160441184787359821858867270,160441184787359821888620814⟩⟩,⟨⟨(-503428890),342288866⟩,⟨2136803025194210899575928083,2136803025194210900482066959⟩⟩,⟨⟨(-4712344829),3211611413⟩,⟨15920423158960125591354284084,15920423158960125599740196683⟩⟩,⟨⟨(-17565710692),8273564931⟩,⟨82145886611128228785260658663,82145886611128228813453240589⟩⟩]
lemma ha24_0_9_eq (j : Fin 7) : ha24_0_9 j = ((ha24_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha24_0_9_contains (j : Fin 7) : (ha24_0_9 j).Contains (fullFactor false 24 9 ((j.val:ℝ)/6)) := by
  rw [ha24_0_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_0_8 j) false 24 8 j (ha24_0_8_contains j)
noncomputable def hk24_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_10 j i k)
lemma hk24_0_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_0_10 j i k).Contains (fullFactor false 24 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_0_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power24 j i k) (mpower0_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 10 (power24_contains j i k) (mpower0_10_contains j i k)
noncomputable def ha24_0_10 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-426798800539562151473),(-426798800539562151436)⟩,⟨(-16),8⟩⟩,⟨⟨(-437041971752511643128123),(-437041971752511643050877)⟩,⟨(-39796),23317⟩⟩,⟨⟨(-25202042373060605483619020),(-25202042373060605478865122)⟩,⟨(-2688544),1263147⟩⟩,⟨⟨(-447530979074571922619250825),(-447530979074571922428045006)⟩,⟨(-105437901),71688813⟩⟩,⟨⟨(-4167957036519161636403075057),(-4167957036519161634194381253)⟩,⟨(-1233688992),840797902⟩⟩,⟨⟨(-25806891390014060017261433981),(-25806891390014060008322327267)⟩,⟨(-5518430767),2599217081⟩⟩]
lemma ha24_0_10_eq (j : Fin 7) : ha24_0_10 j = ((ha24_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha24_0_10_contains (j : Fin 7) : (ha24_0_10 j).Contains (fullFactor false 24 10 ((j.val:ℝ)/6)) := by
  rw [ha24_0_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_0_9 j) false 24 9 j (ha24_0_9_contains j)
noncomputable def hk24_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_11 j i k)
lemma hk24_0_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_0_11 j i k).Contains (fullFactor false 24 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_0_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power24 j i k) (mpower0_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 11 (power24_contains j i k) (mpower0_11_contains j i k)
noncomputable def ha24_0_11 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-20315575399030665722),(-20315575399030665720)⟩⟩,⟨⟨(-2220),3789⟩,⟨(-41606298417214803400470),(-41606298417214803392983)⟩⟩,⟨⟨(-180377),383924⟩,⟨(-3598843235212085340833392),(-3598843235212085340143080)⟩⟩,⟨⟨(-13649519),20075330⟩,⟨(-85209699158455917374834212),(-85209699158455917338157477)⟩⟩,⟨⟨(-200109433),293617294⟩,⟨(-991971455030794224925440784),(-991971455030794224396615344)⟩⟩,⟨⟨(-742334663),1576060142⟩,⟨(-7370430945714350778608138769),(-7370430945714350776031675050)⟩⟩]
lemma ha24_0_11_eq (j : Fin 7) : ha24_0_11 j = ((ha24_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha24_0_11_contains (j : Fin 7) : (ha24_0_11 j).Contains (fullFactor false 24 11 ((j.val:ℝ)/6)) := by
  rw [ha24_0_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_0_10 j) false 24 10 j (ha24_0_10_contains j)
noncomputable def hk24_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_12 j i k)
lemma hk24_0_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_0_12 j i k).Contains (fullFactor false 24 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_0_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power24 j i k) (mpower0_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 12 (power24_contains j i k) (mpower0_12_contains j i k)
noncomputable def ha24_0_12 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨886434200375614885,886434200375614886⟩,⟨(-1),1⟩⟩,⟨⟨3630834484738518570723,3630834484738518571389⟩,⟨(-194),331⟩⟩,⟨⟨471087477881817150325337,471087477881817150417199⟩,⟨(-23612),50256⟩⟩,⟨⟨14871898049488972063822161,14871898049488972070270798⟩,⟨(-2382291),3503807⟩⟩,⟨⟨216414599701077852850120174,216414599701077852966180857⟩,⟨(-43657106),64057357⟩⟩,⟨⟨1929574309403923047580385519,1929574309403923048261044170⟩,⟨(-194342761),412611581⟩⟩]
lemma ha24_0_12_eq (j : Fin 7) : ha24_0_12 j = ((ha24_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha24_0_12_contains (j : Fin 7) : (ha24_0_12 j).Contains (fullFactor false 24 12 ((j.val:ℝ)/6)) := by
  rw [ha24_0_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_0_11 j) false 24 11 j (ha24_0_11_contains j)
noncomputable def hk24_0_13 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_13 j i k)
lemma hk24_0_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_0_13 j i k).Contains (fullFactor false 24 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_0_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power24 j i k) (mpower0_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 13 (power24_contains j i k) (mpower0_13_contains j i k)
noncomputable def ha24_0_13 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨35702758612702236,35702758612702237⟩⟩,⟨⟨(-27),16⟩,⟨292476998555256722998,292476998555256723054⟩⟩,⟨⟨(-6073),2854⟩,⟨56921729219679268112667,56921729219679268123949⟩⟩,⟨⟨(-564489),383805⟩,⟨2395971572164663074506718,2395971572164663075553268⟩⟩,⟨⟨(-12900137),8791849⟩,⟨43582469009646285019402301,43582469009646285042913811⟩⟩,⟨⟨(-99712117),46965061⟩,⟨466302805767612564342189721,466302805767612564508162642⟩⟩]
lemma ha24_0_13_eq (j : Fin 7) : ha24_0_13 j = ((ha24_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha24_0_13_contains (j : Fin 7) : (ha24_0_13 j).Contains (fullFactor false 24 13 ((j.val:ℝ)/6)) := by
  rw [ha24_0_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_0_12 j) false 24 12 j (ha24_0_12_contains j)
noncomputable def hk24_0_14 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_14 j i k)
lemma hk24_0_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_0_14 j i k).Contains (fullFactor false 24 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_0_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power24 j i k) (mpower0_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 14 (power24_contains j i k) (mpower0_14_contains j i k)
noncomputable def ha24_0_14 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1335280049649466),(-1335280049649465)⟩,⟨(-1),1⟩⟩,⟨⟨(-21877228333456835520),(-21877228333456835515)⟩,⟨(-3),2⟩⟩,⟨⟨(-6386603083791852241801),(-6386603083791852240513)⟩,⟨(-682),321⟩⟩,⟨⟨(-358436509015356793200362),(-358436509015356793042656)⟩,⟨(-84448),57418⟩⟩,⟨⟨(-8149902646786285759361876),(-8149902646786285754939291)⟩,⟨(-2412320),1644072⟩⟩,⟨⟨(-104638104924845707137904281),(-104638104924845707100326970)⟩,⟨(-22375347),10538936⟩⟩]
lemma ha24_0_14_eq (j : Fin 7) : ha24_0_14 j = ((ha24_0_13 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha24_0_14_contains (j : Fin 7) : (ha24_0_14 j).Contains (fullFactor false 24 14 ((j.val:ℝ)/6)) := by
  rw [ha24_0_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_0_13 j) false 24 13 j (ha24_0_13_contains j)
noncomputable def hk24_0_15 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_15 j i k)
lemma hk24_0_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_0_15 j i k).Contains (fullFactor false 24 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_0_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power24 j i k) (mpower0_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 15 (power24_contains j i k) (mpower0_15_contains j i k)
noncomputable def ha24_0_15 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-46610066605154),(-46610066605153)⟩⟩,⟨⟨(-1),1⟩,⟨(-1527318662517654887),(-1527318662517654886)⟩⟩,⟨⟨(-34),72⟩,⟨(-668803510981146723324),(-668803510981146723186)⟩⟩,⟨⟨(-8018),11792⟩,⟨(-50047177933378515339109),(-50047177933378515316929)⟩⟩,⟨⟨(-286945),421030⟩,⟨(-1422426349034211493224062),(-1422426349034211492447646)⟩⟩,⟨⟨(-2207270),4686282⟩,⟨(-21915353447830215831601211),(-21915353447830215823661277)⟩⟩]
lemma ha24_0_15_eq (j : Fin 7) : ha24_0_15 j = ((ha24_0_14 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha24_0_15_contains (j : Fin 7) : (ha24_0_15 j).Contains (fullFactor false 24 15 ((j.val:ℝ)/6)) := by
  rw [ha24_0_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_0_14 j) false 24 14 j (ha24_0_14_contains j)
noncomputable def hk24_0_16 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_16 j i k)
lemma hk24_0_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_0_16 j i k).Contains (fullFactor false 24 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_0_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power24 j i k) (mpower0_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 16 (power24_contains j i k) (mpower0_16_contains j i k)
noncomputable def ha24_0_16 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1525310862813,1525310862814⟩,⟨(-1),1⟩⟩,⟨⟨99962772705334443,99962772705334444⟩,⟨(-1),1⟩⟩,⟨⟨65659631149794723615,65659631149794723630⟩,⟨(-4),8⟩⟩,⟨⟨6551160272016798097367,6551160272016798100292⟩,⟨(-1050),1544⟩⟩,⟨⟨232743967104084891311948,232743967104084891439731⟩,⟨(-46952),68891⟩⟩,⟨⟨4303069587032947006563120,4303069587032947008135820⟩,⟨(-433397),920150⟩⟩]
lemma ha24_0_16_eq (j : Fin 7) : ha24_0_16 j = ((ha24_0_15 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha24_0_16_contains (j : Fin 7) : (ha24_0_16 j).Contains (fullFactor false 24 16 ((j.val:ℝ)/6)) := by
  rw [ha24_0_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_0_15 j) false 24 15 j (ha24_0_15_contains j)
noncomputable def hk24_0_17 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_17 j i k)
lemma hk24_0_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_0_17 j i k).Contains (fullFactor false 24 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_0_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power24 j i k) (mpower0_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 17 (power24_contains j i k) (mpower0_17_contains j i k)
noncomputable def ha24_0_17 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨46979464716,46979464717⟩⟩,⟨⟨(-1),1⟩,⟨6157692399285195,6157692399285196⟩⟩,⟨⟨(-1),1⟩,⟨6066935731106195666,6066935731106195668⟩⟩,⟨⟨(-191),130⟩,⟨807101058159109193246,807101058159109193610⟩⟩,⟨⟨(-10610),7231⟩,⟨35842487118702823476679,35842487118702823496473⟩⟩,⟨⟨(-170044),80092⟩,⟨795205400147551278341878,795205400147551278635045⟩⟩]
lemma ha24_0_17_eq (j : Fin 7) : ha24_0_17 j = ((ha24_0_16 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha24_0_17_contains (j : Fin 7) : (ha24_0_17 j).Contains (fullFactor false 24 17 ((j.val:ℝ)/6)) := by
  rw [ha24_0_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_0_16 j) false 24 16 j (ha24_0_16_contains j)
noncomputable def hk24_0_18 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_18 j i k)
lemma hk24_0_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_0_18 j i k).Contains (fullFactor false 24 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_0_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power24 j i k) (mpower0_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 18 (power24_contains j i k) (mpower0_18_contains j i k)
noncomputable def ha24_0_18 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1366577234),(-1366577233)⟩,⟨(-1),1⟩⟩,⟨⟨(-358240022308520),(-358240022308519)⟩,⟨(-1),1⟩⟩,⟨⟨(-529440020073462377),(-529440020073462376)⟩,⟨(-1),1⟩⟩,⟨⟨(-93910472408044662761),(-93910472408044662717)⟩,⟨(-23),16⟩⟩,⟨⟨(-5213078436041832673122),(-5213078436041832670226)⟩,⟨(-1544),1052⟩⟩,⟨⟨(-138789524622137721172360),(-138789524622137721120750)⟩,⟨(-29679),13979⟩⟩]
lemma ha24_0_18_eq (j : Fin 7) : ha24_0_18 j = ((ha24_0_17 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha24_0_18_contains (j : Fin 7) : (ha24_0_18 j).Contains (fullFactor false 24 18 ((j.val:ℝ)/6)) := by
  rw [ha24_0_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_0_17 j) false 24 17 j (ha24_0_17_contains j)
noncomputable def hk24_0_19 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_19 j i k)
lemma hk24_0_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_0_19 j i k).Contains (fullFactor false 24 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_0_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power24 j i k) (mpower0_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 19 (power24_contains j i k) (mpower0_19_contains j i k)
noncomputable def ha24_0_19 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-37659904),(-37659903)⟩⟩,⟨⟨(-1),1⟩,⟨(-19744635479058),(-19744635479057)⟩⟩,⟨⟨(-1),1⟩,⟨(-43770654673137423),(-43770654673137422)⟩⟩,⟨⟨(-2),3⟩,⟨(-10351875446044213764),(-10351875446044213759)⟩⟩,⟨⟨(-145),213⟩,⟨(-718305654265631155252),(-718305654265631154849)⟩⟩,⟨⟨(-2312),4908⟩,⟨(-22948428997269873114835),(-22948428997269873106227)⟩⟩]
lemma ha24_0_19_eq (j : Fin 7) : ha24_0_19 j = ((ha24_0_18 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha24_0_19_contains (j : Fin 7) : (ha24_0_19 j).Contains (fullFactor false 24 19 ((j.val:ℝ)/6)) := by
  rw [ha24_0_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_0_18 j) false 24 18 j (ha24_0_18_contains j)
noncomputable def hk24_0_20 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_20 j i k)
lemma hk24_0_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_0_20 j i k).Contains (fullFactor false 24 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_0_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power24 j i k) (mpower0_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 20 (power24_contains j i k) (mpower0_20_contains j i k)
noncomputable def ha24_0_20 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨985933,985934⟩,⟨(-1),1⟩⟩,⟨⟨1033826696146,1033826696147⟩,⟨(-1),1⟩⟩,⟨⟨3437739179098606,3437739179098608⟩,⟨(-1),1⟩⟩,⟨⟨1084045861738968866,1084045861738968868⟩,⟨(-1),1⟩⟩,⟨⟨94025990269704865188,94025990269704865242⟩,⟨(-19),28⟩⟩,⟨⟨3604730797462500933231,3604730797462500934596⟩,⟨(-364),771⟩⟩]
lemma ha24_0_20_eq (j : Fin 7) : ha24_0_20 j = ((ha24_0_19 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha24_0_20_contains (j : Fin 7) : (ha24_0_20 j).Contains (fullFactor false 24 20 ((j.val:ℝ)/6)) := by
  rw [ha24_0_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_0_19 j) false 24 19 j (ha24_0_19_contains j)
noncomputable def hk24_0_21 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_21 j i k)
lemma hk24_0_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_0_21 j i k).Contains (fullFactor false 24 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_0_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power24 j i k) (mpower0_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 21 (power24_contains j i k) (mpower0_21_contains j i k)
noncomputable def ha24_0_21 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨24582,24583⟩⟩,⟨⟨(-1),1⟩,⟨51553370693,51553370694⟩⟩,⟨⟨(-1),1⟩,⟨257142289286047,257142289286048⟩⟩,⟨⟨(-1),1⟩,⟨108115254456938454,108115254456938455⟩⟩,⟨⟨(-4),3⟩,⟨11721879376103578819,11721879376103578827⟩⟩,⟨⟨(-116),55⟩,⟨539266466260812848840,539266466260812849047⟩⟩]
lemma ha24_0_21_eq (j : Fin 7) : ha24_0_21 j = ((ha24_0_20 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha24_0_21_contains (j : Fin 7) : (ha24_0_21 j).Contains (fullFactor false 24 21 ((j.val:ℝ)/6)) := by
  rw [ha24_0_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_0_20 j) false 24 20 j (ha24_0_20_contains j)
noncomputable def hk24_0_22 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_22 j i k)
lemma hk24_0_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_0_22 j i k).Contains (fullFactor false 24 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_0_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power24 j i k) (mpower0_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 22 (power24_contains j i k) (mpower0_22_contains j i k)
noncomputable def ha24_0_22 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-586),(-585)⟩,⟨(-1),1⟩⟩,⟨⟨(-2453934707),(-2453934706)⟩,⟨(-1),1⟩⟩,⟨⟨(-18359916521553),(-18359916521552)⟩,⟨(-1),1⟩⟩,⟨⟨(-10292548155845728),(-10292548155845727)⟩,⟨(-1),1⟩⟩,⟨⟨(-1394900383872451221),(-1394900383872451219)⟩,⟨(-1),1⟩⟩,⟨⟨(-77007071306013533815),(-77007071306013533784)⟩,⟨(-17),8⟩⟩]
lemma ha24_0_22_eq (j : Fin 7) : ha24_0_22 j = ((ha24_0_21 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha24_0_22_contains (j : Fin 7) : (ha24_0_22 j).Contains (fullFactor false 24 22 ((j.val:ℝ)/6)) := by
  rw [ha24_0_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_0_21 j) false 24 21 j (ha24_0_21_contains j)
noncomputable def hk24_0_23 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_23 j i k)
lemma hk24_0_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_0_23 j i k).Contains (fullFactor false 24 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_0_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power24 j i k) (mpower0_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 23 (power24_contains j i k) (mpower0_23_contains j i k)
noncomputable def ha24_0_23 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-14),(-13)⟩⟩,⟨⟨(-1),1⟩,⟨(-111728453),(-111728452)⟩⟩,⟨⟨(-1),1⟩,⟨(-1253899540536),(-1253899540535)⟩⟩,⟨⟨(-1),1⟩,⟨(-937246193423888),(-937246193423887)⟩⟩,⟨⟨(-1),1⟩,⟨(-158775681103741858),(-158775681103741857)⟩⟩,⟨⟨(-2),3⟩,⟨(-10518471716932064458),(-10518471716932064453)⟩⟩]
lemma ha24_0_23_eq (j : Fin 7) : ha24_0_23 j = ((ha24_0_22 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha24_0_23_contains (j : Fin 7) : (ha24_0_23 j).Contains (fullFactor false 24 23 ((j.val:ℝ)/6)) := by
  rw [ha24_0_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_0_22 j) false 24 22 j (ha24_0_22_contains j)
noncomputable def hk24_0_24 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_24 j i k)
lemma hk24_0_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_0_24 j i k).Contains (fullFactor false 24 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_0_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power24 j i k) (mpower0_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 24 (power24_contains j i k) (mpower0_24_contains j i k)
noncomputable def ha24_0_24 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨(-1),1⟩⟩,⟨⟨4875073,4875074⟩,⟨(-1),1⟩⟩,⟨⟨82067533018,82067533019⟩,⟨(-1),1⟩⟩,⟨⟨81790159885152,81790159885153⟩,⟨(-1),1⟩⟩,⟨⟨17319740045980249,17319740045980250⟩,⟨(-1),1⟩⟩,⟨⟨1376864728037741370,1376864728037741371⟩,⟨(-1),1⟩⟩]
lemma ha24_0_24_eq (j : Fin 7) : ha24_0_24 j = ((ha24_0_23 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha24_0_24_contains (j : Fin 7) : (ha24_0_24 j).Contains (fullFactor false 24 24 ((j.val:ℝ)/6)) := by
  rw [ha24_0_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_0_23 j) false 24 23 j (ha24_0_23_contains j)
noncomputable def hk24_0_25 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_25 j i k)
lemma hk24_0_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_0_25 j i k).Contains (fullFactor false 24 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_0_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power24 j i k) (mpower0_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 25 (power24_contains j i k) (mpower0_25_contains j i k)
noncomputable def ha24_0_25 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨0,1⟩⟩,⟨⟨(-1),1⟩,⟨204206,204207⟩⟩,⟨⟨(-1),1⟩,⟨5156455176,5156455177⟩⟩,⟨⟨(-1),1⟩,⟨6852036411496,6852036411497⟩⟩,⟨⟨(-1),1⟩,⟨1813718936351216,1813718936351217⟩⟩,⟨⟨(-1),1⟩,⟨173021924583611076,173021924583611077⟩⟩]
lemma ha24_0_25_eq (j : Fin 7) : ha24_0_25 j = ((ha24_0_24 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha24_0_25_contains (j : Fin 7) : (ha24_0_25 j).Contains (fullFactor false 24 25 ((j.val:ℝ)/6)) := by
  rw [ha24_0_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_0_24 j) false 24 24 j (ha24_0_24_contains j)
noncomputable def hk24_0_26 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_26 j i k)
lemma hk24_0_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_0_26 j i k).Contains (fullFactor false 24 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_0_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power24 j i k) (mpower0_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 26 (power24_contains j i k) (mpower0_26_contains j i k)
noncomputable def ha24_0_26 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),1⟩⟩,⟨⟨(-8225),(-8224)⟩,⟨(-1),1⟩⟩,⟨⟨(-311528495),(-311528494)⟩,⟨(-1),1⟩⟩,⟨⟨(-551956596218),(-551956596217)⟩,⟨(-1),1⟩⟩,⟨⟨(-182627118144798),(-182627118144797)⟩,⟨(-1),1⟩⟩,⟨⟨(-20906323353147685),(-20906323353147684)⟩,⟨(-1),1⟩⟩]
lemma ha24_0_26_eq (j : Fin 7) : ha24_0_26 j = ((ha24_0_25 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha24_0_26_contains (j : Fin 7) : (ha24_0_26 j).Contains (fullFactor false 24 26 ((j.val:ℝ)/6)) := by
  rw [ha24_0_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_0_25 j) false 24 25 j (ha24_0_25_contains j)
noncomputable def hk24_0_27 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_27 j i k)
lemma hk24_0_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_0_27 j i k).Contains (fullFactor false 24 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_0_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power24 j i k) (mpower0_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 27 (power24_contains j i k) (mpower0_27_contains j i k)
noncomputable def ha24_0_27 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-1),0⟩⟩,⟨⟨(-1),1⟩,⟨(-320),(-318)⟩⟩,⟨⟨(-1),1⟩,⟨(-18123994),(-18123993)⟩⟩,⟨⟨(-1),1⟩,⟨(-42815377477),(-42815377475)⟩⟩,⟨⟨(-1),1⟩,⟨(-17708025083642),(-17708025083641)⟩⟩,⟨⟨(-1),1⟩,⟨(-2432561179993389),(-2432561179993388)⟩⟩]
lemma ha24_0_27_eq (j : Fin 7) : ha24_0_27 j = ((ha24_0_26 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha24_0_27_contains (j : Fin 7) : (ha24_0_27 j).Contains (fullFactor false 24 27 ((j.val:ℝ)/6)) := by
  rw [ha24_0_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_0_26 j) false 24 26 j (ha24_0_26_contains j)
noncomputable def hk24_0_28 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_28 j i k)
lemma hk24_0_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_0_28 j i k).Contains (fullFactor false 24 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_0_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power24 j i k) (mpower0_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 28 (power24_contains j i k) (mpower0_28_contains j i k)
noncomputable def ha24_0_28 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨(-1),1⟩⟩,⟨⟨11,12⟩,⟨(-1),1⟩⟩,⟨⟨1016753,1016754⟩,⟨(-1),1⟩⟩,⟨⟨3202582746,3202582747⟩,⟨(-1),1⟩⟩,⟨⟨1655696473581,1655696473582⟩,⟨(-1),1⟩⟩,⟨⟨272932726159819,272932726159820⟩,⟨(-1),1⟩⟩]
lemma ha24_0_28_eq (j : Fin 7) : ha24_0_28 j = ((ha24_0_27 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha24_0_28_contains (j : Fin 7) : (ha24_0_28 j).Contains (fullFactor false 24 28 ((j.val:ℝ)/6)) := by
  rw [ha24_0_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_0_27 j) false 24 27 j (ha24_0_27_contains j)
noncomputable def hk24_0_29 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_29 j i k)
lemma hk24_0_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_0_29 j i k).Contains (fullFactor false 24 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_0_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power24 j i k) (mpower0_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 29 (power24_contains j i k) (mpower0_29_contains j i k)
noncomputable def ha24_0_29 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨0,1⟩⟩,⟨⟨(-1),1⟩,⟨0,1⟩⟩,⟨⟨(-1),1⟩,⟨55072,55073⟩⟩,⟨⟨(-1),1⟩,⟨231292193,231292194⟩⟩,⟨⟨(-1),1⟩,⟨149469076953,149469076954⟩⟩,⟨⟨(-1),1⟩,⟨29567015428549,29567015428550⟩⟩]
lemma ha24_0_29_eq (j : Fin 7) : ha24_0_29 j = ((ha24_0_28 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha24_0_29_contains (j : Fin 7) : (ha24_0_29 j).Contains (fullFactor false 24 29 ((j.val:ℝ)/6)) := by
  rw [ha24_0_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_0_28 j) false 24 28 j (ha24_0_28_contains j)
noncomputable def hk24_0_30 (j : Fin 6) (i k : Fin 16) : CBox := (power24 j i k).conj.mul (mpower0_30 j i k)
lemma hk24_0_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_0_30 j i k).Contains (fullFactor false 24 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_0_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power24 j i k) (mpower0_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 30 (power24_contains j i k) (mpower0_30_contains j i k)
noncomputable def ha24_0_30 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),1⟩⟩,⟨⟨(-1),0⟩,⟨(-1),1⟩⟩,⟨⟨(-2884),(-2883)⟩,⟨(-1),1⟩⟩,⟨⟨(-16147242),(-16147241)⟩,⟨(-1),1⟩⟩,⟨⟨(-13043637614),(-13043637613)⟩,⟨(-1),1⟩⟩,⟨⟨(-3096250615297),(-3096250615296)⟩,⟨(-1),1⟩⟩]
lemma ha24_0_30_eq (j : Fin 7) : ha24_0_30 j = ((ha24_0_29 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha24_0_30_contains (j : Fin 7) : (ha24_0_30 j).Contains (fullFactor false 24 30 ((j.val:ℝ)/6)) := by
  rw [ha24_0_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_0_29 j) false 24 29 j (ha24_0_29_contains j)
noncomputable def hk24_1_0 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_0 j i k)
lemma hk24_1_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_1_0 j i k).Contains (fullFactor true 24 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_1_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel24_0 j i k) (mpower1_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 0 (kernel24_0_contains j i k) (mpower1_0_contains j i k)
noncomputable def ha24_1_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-3),4⟩,⟨(-4),2⟩⟩,⟨⟨(-4),0⟩,⟨(-2),2⟩⟩,⟨⟨(-6),(-3)⟩,⟨(-6),(-3)⟩⟩,⟨⟨(-236955311709037),(-236955311709034)⟩,⟨(-25302583633154),(-25302583633151)⟩⟩,⟨⟨(-50902692348634872196574),(-50902692348634872055211)⟩,⟨(-25572105302796923445599),(-25572105302796923304077)⟩⟩,⟨⟨(-9409877970793072962720468375),(-9409877970793072933272212257)⟩,⟨7173247941176577457230122546,7173247941176577486520048649⟩⟩]
lemma ha24_1_0_eq (j : Fin 7) : ha24_1_0 j = atomKernel24_0 j := by fin_cases j <;> decide +kernel
lemma ha24_1_0_contains (j : Fin 7) : (ha24_1_0 j).Contains (fullFactor true 24 0 ((j.val:ℝ)/6)) := by
  rw [ha24_1_0_eq]
  simpa only [fullFactor,ite_true] using atomKernel24_0_contains j
noncomputable def hk24_1_1 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_1 j i k)
lemma hk24_1_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_1_1 j i k).Contains (fullFactor true 24 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_1_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel24_0 j i k) (mpower1_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 1 (kernel24_0_contains j i k) (mpower1_1_contains j i k)
noncomputable def ha24_1_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),31⟩,⟨(-31),42⟩⟩,⟨⟨(-11),30⟩,⟨(-10),31⟩⟩,⟨⟨(-23),2⟩,⟨23,48⟩⟩,⟨⟨242174098457843,242174098457862⟩,⟨1133073413611544,1133073413611563⟩⟩,⟨⟨(-68618597869347544447143),(-68618597869347543768973)⟩,⟨225963129972071328187395,225963129972071328865300⟩⟩,⟨⟨27669709444365382060075635835,27669709444365382171459994905⟩,⟨32632369547623298580507136818,32632369547623298692457871091⟩⟩]
lemma ha24_1_1_eq (j : Fin 7) : ha24_1_1 j = ((ha24_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha24_1_1_contains (j : Fin 7) : (ha24_1_1 j).Contains (fullFactor true 24 1 ((j.val:ℝ)/6)) := by
  rw [ha24_1_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_1_0 j) true 24 0 j (ha24_1_0_contains j)
noncomputable def hk24_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_2 j i k)
lemma hk24_1_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_1_2 j i k).Contains (fullFactor true 24 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_1_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel24_0 j i k) (mpower1_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 2 (kernel24_0_contains j i k) (mpower1_2_contains j i k)
noncomputable def ha24_1_2 : Fin 7 → CBox := ![⟨⟨(-130),130⟩,⟨(-130),130⟩⟩,⟨⟨(-177),255⟩,⟨(-219),205⟩⟩,⟨⟨(-100),107⟩,⟨(-154),53⟩⟩,⟨⟨55,156⟩,⟨(-74),27⟩⟩,⟨⟨2433903422998170,2433903422998229⟩,⟨(-1417925915735287),(-1417925915735227)⟩⟩,⟨⟨485727351915311382835550,485727351915311384460638⟩,⟨60590157709179552859568,60590157709179554484257⟩⟩,⟨⟨56320350995595835814092500472,56320350995595836026874327530⟩,⟨(-53021765381761217058863982855),(-53021765381761216847078616456)⟩⟩]
lemma ha24_1_2_eq (j : Fin 7) : ha24_1_2 j = ((ha24_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha24_1_2_contains (j : Fin 7) : (ha24_1_2 j).Contains (fullFactor true 24 2 ((j.val:ℝ)/6)) := by
  rw [ha24_1_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_1_1 j) true 24 1 j (ha24_1_1_contains j)
noncomputable def hk24_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_3 j i k)
lemma hk24_1_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_1_3 j i k).Contains (fullFactor true 24 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_1_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel24_0 j i k) (mpower1_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 3 (kernel24_0_contains j i k) (mpower1_3_contains j i k)
noncomputable def ha24_1_3 : Fin 7 → CBox := ![⟨⟨(-400),400⟩,⟨(-400),400⟩⟩,⟨⟨(-924),707⟩,⟨(-840),779⟩⟩,⟨⟨(-440),256⟩,⟨(-271),425⟩⟩,⟨⟨(-274),(-5)⟩,⟨(-292),(-23)⟩⟩,⟨⟨(-3413011226152312),(-3413011226152189)⟩,⟨(-3031981442769580),(-3031981442769458)⟩⟩,⟨⟨(-31523829772962407256156),(-31523829772962404661565)⟩,⟨(-675671326609801028861767),(-675671326609801026265202)⟩⟩,⟨⟨(-67346145537295596620561162910),(-67346145537295596352107716802)⟩,⟨(-64472726409183884222733638545),(-64472726409183883953131165826)⟩⟩]
lemma ha24_1_3_eq (j : Fin 7) : ha24_1_3 j = ((ha24_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha24_1_3_contains (j : Fin 7) : (ha24_1_3 j).Contains (fullFactor true 24 3 ((j.val:ℝ)/6)) := by
  rw [ha24_1_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_1_2 j) true 24 2 j (ha24_1_2_contains j)
noncomputable def hk24_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_4 j i k)
lemma hk24_1_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_1_4 j i k).Contains (fullFactor true 24 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_1_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel24_0 j i k) (mpower1_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 4 (kernel24_0_contains j i k) (mpower1_4_contains j i k)
noncomputable def ha24_1_4 : Fin 7 → CBox := ![⟨⟨(-922),922⟩,⟨(-922),922⟩⟩,⟨⟨(-2136),2495⟩,⟨(-2151),2469⟩⟩,⟨⟨(-665),1089⟩,⟨(-853),901⟩⟩,⟨⟨(-370),165⟩,⟨22,557⟩⟩,⟨⟨(-2208948228001528),(-2208948228001339)⟩,⟨5090651911825972,5090651911826162⟩⟩,⟨⟨(-684528750454172925636989),(-684528750454172922525993)⟩,⟨151165723899910304199049,151165723899910307306643⟩⟩,⟨⟨(-55041720554162006471354930696),(-55041720554162006215172112765)⟩,⟨63823736303748481242903157957,63823736303748481498110451371⟩⟩]
lemma ha24_1_4_eq (j : Fin 7) : ha24_1_4 j = ((ha24_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha24_1_4_contains (j : Fin 7) : (ha24_1_4 j).Contains (fullFactor true 24 4 ((j.val:ℝ)/6)) := by
  rw [ha24_1_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_1_3 j) true 24 3 j (ha24_1_3_contains j)
noncomputable def hk24_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_5 j i k)
lemma hk24_1_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_1_5 j i k).Contains (fullFactor true 24 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_1_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel24_0 j i k) (mpower1_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 5 (kernel24_0_contains j i k) (mpower1_5_contains j i k)
noncomputable def ha24_1_5 : Fin 7 → CBox := ![⟨⟨(-1700),1700⟩,⟨(-1700),1700⟩⟩,⟨⟨(-5425),5111⟩,⟨(-5641),4887⟩⟩,⟨⟨(-1951),1583⟩,⟨(-2009),1525⟩⟩,⟨⟨(-71),779⟩,⟨(-484),366⟩⟩,⟨⟨5373220158957954,5373220158958188⟩,⟨498232941366912,498232941367145⟩⟩,⟨⟨219934755988246350646921,219934755988246353624929⟩,⟨538007162337074117955404,538007162337074120936860⟩⟩,⟨⟨48160908430591055774094996718,48160908430591055968181195396⟩,⟨37354537819972240089067473050,37354537819972240283802426375⟩⟩]
lemma ha24_1_5_eq (j : Fin 7) : ha24_1_5 j = ((ha24_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha24_1_5_contains (j : Fin 7) : (ha24_1_5 j).Contains (fullFactor true 24 5 ((j.val:ℝ)/6)) := by
  rw [ha24_1_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_1_4 j) true 24 4 j (ha24_1_4_contains j)
noncomputable def hk24_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_6 j i k)
lemma hk24_1_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_1_6 j i k).Contains (fullFactor true 24 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_1_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel24_0 j i k) (mpower1_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 6 (kernel24_0_contains j i k) (mpower1_6_contains j i k)
noncomputable def ha24_1_6 : Fin 7 → CBox := ![⟨⟨(-2612),2612⟩,⟨(-2612),2612⟩⟩,⟨⟨(-10026),9960⟩,⟨(-9412),10570⟩⟩,⟨⟨(-3024),2910⟩,⟨(-2611),3324⟩⟩,⟨⟨(-780),346⟩,⟨(-836),289⟩⟩,⟨⟨(-973418842217271),(-973418842217032)⟩,⟨(-4263203264845779),(-4263203264845538)⟩⟩,⟨⟨340502895417882883040621,340502895417882885421463⟩,⟨(-212903290292775536453211),(-212903290292775534074882)⟩⟩,⟨⟨20974145570009116620368578716,20974145570009116743717804035⟩,⟨(-30154080206631394217974316862),(-30154080206631394094975608027)⟩⟩]
lemma ha24_1_6_eq (j : Fin 7) : ha24_1_6 j = ((ha24_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha24_1_6_contains (j : Fin 7) : (ha24_1_6 j).Contains (fullFactor true 24 6 ((j.val:ℝ)/6)) := by
  rw [ha24_1_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_1_5 j) true 24 5 j (ha24_1_5_contains j)
noncomputable def hk24_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_7 j i k)
lemma hk24_1_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_1_7 j i k).Contains (fullFactor true 24 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_1_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel24_0 j i k) (mpower1_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 7 (kernel24_0_contains j i k) (mpower1_7_contains j i k)
noncomputable def ha24_1_7 : Fin 7 → CBox := ![⟨⟨(-3439),3439⟩,⟨(-3439),3439⟩⟩,⟨⟨(-15907),16595⟩,⟨(-16866),15633⟩⟩,⟨⟨(-3968),4573⟩,⟨(-4479),4062⟩⟩,⟨⟨(-750),527⟩,⟨(-370),908⟩⟩,⟨⟨(-2602982356930032),(-2602982356929820)⟩,⟨1565351018165400,1565351018165610⟩⟩,⟨⟨(-158512981825632089278155),(-158512981825632087650075)⟩,⟨(-177300895712402720637467),(-177300895712402719007977)⟩⟩,⟨⟨(-16117936351082083258592113647),(-16117936351082083191781774651)⟩,⟨(-10010864716208899387733946680),(-10010864716208899320766482418)⟩⟩]
lemma ha24_1_7_eq (j : Fin 7) : ha24_1_7 j = ((ha24_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha24_1_7_contains (j : Fin 7) : (ha24_1_7 j).Contains (fullFactor true 24 7 ((j.val:ℝ)/6)) := by
  rw [ha24_1_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_1_6 j) true 24 6 j (ha24_1_6_contains j)
noncomputable def hk24_1_8 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_8 j i k)
lemma hk24_1_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_1_8 j i k).Contains (fullFactor true 24 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_1_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel24_0 j i k) (mpower1_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 8 (kernel24_0_contains j i k) (mpower1_8_contains j i k)
noncomputable def ha24_1_8 : Fin 7 → CBox := ![⟨⟨(-3962),3962⟩,⟨(-3962),3962⟩⟩,⟨⟨(-23741),22509⟩,⟨(-22694),23555⟩⟩,⟨⟨(-5698),5058⟩,⟨(-5444),5312⟩⟩,⟨⟨(-423),846⟩,⟨(-658),610⟩⟩,⟨⟨1397043864143901,1397043864144063⟩,⟨1206710699451510,1206710699451673⟩⟩,⟨⟨(-76585644417188966778107),(-76585644417188965802322)⟩,⟨96555796327557180451627,96555796327557181426791⟩⟩,⟨⟨(-4140371773862156091503066007),(-4140371773862156059691671038)⟩,⟨7510257687084849820677899839,7510257687084849852430378125⟩⟩]
lemma ha24_1_8_eq (j : Fin 7) : ha24_1_8 j = ((ha24_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha24_1_8_contains (j : Fin 7) : (ha24_1_8 j).Contains (fullFactor true 24 8 ((j.val:ℝ)/6)) := by
  rw [ha24_1_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_1_7 j) true 24 7 j (ha24_1_7_contains j)
noncomputable def hk24_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_9 j i k)
lemma hk24_1_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_1_9 j i k).Contains (fullFactor true 24 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_1_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel24_0 j i k) (mpower1_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 9 (kernel24_0_contains j i k) (mpower1_9_contains j i k)
noncomputable def ha24_1_9 : Fin 7 → CBox := ![⟨⟨(-4057),4057⟩,⟨(-4057),4057⟩⟩,⟨⟨(-28549),29954⟩,⟨(-29363),29139⟩⟩,⟨⟨(-5883),6157⟩,⟨(-5801),6239⟩⟩,⟨⟨(-640),480⟩,⟨(-672),447⟩⟩,⟨⟨384218995028481,384218995028592⟩,⟨(-920324934309594),(-920324934309483)⟩⟩,⟨⟨49822074150731007470512,49822074150731007989681⟩,⟨27207810670394856586986,27207810670394857106364⟩⟩,⟨⟨3099687506615916050702759782,3099687506615916064116221751⟩,⟨1504529334396891991248610780,1504529334396892004680402367⟩⟩]
lemma ha24_1_9_eq (j : Fin 7) : ha24_1_9 j = ((ha24_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha24_1_9_contains (j : Fin 7) : (ha24_1_9 j).Contains (fullFactor true 24 9 ((j.val:ℝ)/6)) := by
  rw [ha24_1_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_1_8 j) true 24 8 j (ha24_1_8_contains j)
noncomputable def hk24_1_10 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_10 j i k)
lemma hk24_1_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_1_10 j i k).Contains (fullFactor true 24 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_1_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel24_0 j i k) (mpower1_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 10 (kernel24_0_contains j i k) (mpower1_10_contains j i k)
noncomputable def ha24_1_10 : Fin 7 → CBox := ![⟨⟨(-3739),3739⟩,⟨(-3739),3739⟩⟩,⟨⟨(-33881),32720⟩,⟨(-33476),33125⟩⟩,⟨⟨(-6020),6110⟩,⟨(-6243),5886⟩⟩,⟨⟨(-480),410⟩,⟨(-372),518⟩⟩,⟨⟨(-483411998854150),(-483411998854081)⟩,⟨(-38046727487889),(-38046727487820)⟩⟩,⟨⟨7606202336760695279757,7606202336760695528551⟩,⟨(-22270052025856935038732),(-22270052025856934789984)⟩⟩,⟨⟨485085588286525145578695256,485085588286525150682733860⟩,⟨(-1147556281726357429213719919),(-1147556281726357424114217833)⟩⟩]
lemma ha24_1_10_eq (j : Fin 7) : ha24_1_10 j = ((ha24_1_9 j).mul (piI.mul (atomPoints j).z)).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha24_1_10_contains (j : Fin 7) : (ha24_1_10 j).Contains (fullFactor true 24 10 ((j.val:ℝ)/6)) := by
  rw [ha24_1_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_1_9 j) true 24 9 j (ha24_1_9_contains j)
noncomputable def hk24_1_11 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_11 j i k)
lemma hk24_1_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_1_11 j i k).Contains (fullFactor true 24 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_1_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel24_0 j i k) (mpower1_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 11 (kernel24_0_contains j i k) (mpower1_11_contains j i k)
noncomputable def ha24_1_11 : Fin 7 → CBox := ![⟨⟨(-3133),3133⟩,⟨(-3133),3133⟩⟩,⟨⟨(-34119),34809⟩,⟨(-34145),34782⟩⟩,⟨⟨(-5658),5451⟩,⟨(-5496),5613⟩⟩,⟨⟨(-279),365⟩,⟨(-324),319⟩⟩,⟨⟨50615093057119,50615093057159⟩,⟨208273869662530,208273869662569⟩⟩,⟨⟨(-8757894721492374913241),(-8757894721492374804900)⟩,⟨(-1398970768856371193763),(-1398970768856371085422)⟩⟩,⟨⟨(-384994705634226914979853921),(-384994705634226913217461420)⟩,⟨(-139652381665842069633805132),(-139652381665842067870657085)⟩⟩]
lemma ha24_1_11_eq (j : Fin 7) : ha24_1_11 j = ((ha24_1_10 j).mul (piI.mul (atomPoints j).z)).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha24_1_11_contains (j : Fin 7) : (ha24_1_11 j).Contains (fullFactor true 24 11 ((j.val:ℝ)/6)) := by
  rw [ha24_1_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_1_10 j) true 24 10 j (ha24_1_10_contains j)
noncomputable def hk24_1_12 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_12 j i k)
lemma hk24_1_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_1_12 j i k).Contains (fullFactor true 24 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_1_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel24_0 j i k) (mpower1_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 12 (kernel24_0_contains j i k) (mpower1_12_contains j i k)
noncomputable def ha24_1_12 : Fin 7 → CBox := ![⟨⟨(-2406),2406⟩,⟨(-2406),2406⟩⟩,⟨⟨(-32817),32574⟩,⟨(-33006),32385⟩⟩,⟨⟨(-4596),4731⟩,⟨(-4643),4684⟩⟩,⟨⟨(-225),202⟩,⟨(-231),196⟩⟩,⟨⟨73793593307294,73793593307315⟩,⟨(-45787528016838),(-45787528016817)⟩⟩,⟨⟨37751635516807954659,37751635516807997906⟩,⟨3063657897524248189013,3063657897524248232266⟩⟩,⟨⟨(-35999719949748262495798076),(-35999719949748261937503144)⟩,⟨118037408572694834623061435,118037408572694835181363613⟩⟩]
lemma ha24_1_12_eq (j : Fin 7) : ha24_1_12 j = ((ha24_1_11 j).mul (piI.mul (atomPoints j).z)).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha24_1_12_contains (j : Fin 7) : (ha24_1_12 j).Contains (fullFactor true 24 12 ((j.val:ℝ)/6)) := by
  rw [ha24_1_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_1_11 j) true 24 11 j (ha24_1_11_contains j)
noncomputable def hk24_1_13 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_13 j i k)
lemma hk24_1_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_1_13 j i k).Contains (fullFactor true 24 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_1_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel24_0 j i k) (mpower1_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 13 (kernel24_0_contains j i k) (mpower1_13_contains j i k)
noncomputable def ha24_1_13 : Fin 7 → CBox := ![⟨⟨(-1706),1706⟩,⟨(-1706),1706⟩⟩,⟨⟨(-28649),28615⟩,⟨(-28414),28850⟩⟩,⟨⟨(-3632),3597⟩,⟨(-3649),3580⟩⟩,⟨⟨(-135),126⟩,⟨(-123),139⟩⟩,⟨⟨(-24873960217859),(-24873960217848)⟩,⟨(-20887782895603),(-20887782895593)⟩⟩,⟨⟨960720061919826514494,960720061919826530433⟩,⟨(-177844330461319642847),(-177844330461319626911)⟩⟩,⟨⟨33307380311094320553560194,33307380311094320716810570⟩,⟨8294742001161786167909795,8294742001161786331089500⟩⟩]
lemma ha24_1_13_eq (j : Fin 7) : ha24_1_13 j = ((ha24_1_12 j).mul (piI.mul (atomPoints j).z)).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha24_1_13_contains (j : Fin 7) : (ha24_1_13 j).Contains (fullFactor true 24 13 ((j.val:ℝ)/6)) := by
  rw [ha24_1_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_1_12 j) true 24 12 j (ha24_1_12_contains j)
noncomputable def hk24_1_14 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_14 j i k)
lemma hk24_1_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_1_14 j i k).Contains (fullFactor true 24 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_1_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel24_0 j i k) (mpower1_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 14 (kernel24_0_contains j i k) (mpower1_14_contains j i k)
noncomputable def ha24_1_14 : Fin 7 → CBox := ![⟨⟨(-1123),1123⟩,⟨(-1123),1123⟩⟩,⟨⟨(-23215),23350⟩,⟨(-23397),23168⟩⟩,⟨⟨(-2608),2595⟩,⟨(-2583),2620⟩⟩,⟨⟨(-71),79⟩,⟨(-75),75⟩⟩,⟨⟨(-4200601078737),(-4200601078732)⟩,⟨10469276010787,10469276010793⟩⟩,⟨⟨(-100227622677776329660),(-100227622677776324207)⟩,⟨(-271397800378277490821),(-271397800378277485366)⟩⟩,⟨⟨1692735059679679405072507,1692735059679679449359329⟩,⟨(-8702239221957094712344069),(-8702239221957094668020499)⟩⟩]
lemma ha24_1_14_eq (j : Fin 7) : ha24_1_14 j = ((ha24_1_13 j).mul (piI.mul (atomPoints j).z)).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha24_1_14_contains (j : Fin 7) : (ha24_1_14 j).Contains (fullFactor true 24 14 ((j.val:ℝ)/6)) := by
  rw [ha24_1_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_1_13 j) true 24 13 j (ha24_1_13_contains j)
noncomputable def hk24_1_15 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_15 j i k)
lemma hk24_1_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_1_15 j i k).Contains (fullFactor true 24 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_1_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel24_0 j i k) (mpower1_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 15 (kernel24_0_contains j i k) (mpower1_15_contains j i k)
noncomputable def ha24_1_15 : Fin 7 → CBox := ![⟨⟨(-690),690⟩,⟨(-690),690⟩⟩,⟨⟨(-17733),17608⟩,⟨(-17629),17712⟩⟩,⟨⟨(-1739),1756⟩,⟨(-1751),1744⟩⟩,⟨⟨(-41),39⟩,⟨(-42),39⟩⟩,⟨⟨3648890002008,3648890002011⟩,⟨236136440345,236136440348⟩⟩,⟨⟨(-69209969282348548312),(-69209969282348546569)⟩,⟨40040423181192667626,40040423181192669369⟩⟩,⟨⟨(-2116124197619576403353531),(-2116124197619576392122164)⟩,⟨(-298564115392377786482324),(-298564115392377775264436)⟩⟩]
lemma ha24_1_15_eq (j : Fin 7) : ha24_1_15 j = ((ha24_1_14 j).mul (piI.mul (atomPoints j).z)).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha24_1_15_contains (j : Fin 7) : (ha24_1_15 j).Contains (fullFactor true 24 15 ((j.val:ℝ)/6)) := by
  rw [ha24_1_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_1_14 j) true 24 14 j (ha24_1_14_contains j)
noncomputable def hk24_1_16 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_16 j i k)
lemma hk24_1_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_1_16 j i k).Contains (fullFactor true 24 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_1_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel24_0 j i k) (mpower1_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 16 (kernel24_0_contains j i k) (mpower1_16_contains j i k)
noncomputable def ha24_1_16 : Fin 7 → CBox := ![⟨⟨(-398),398⟩,⟨(-398),398⟩⟩,⟨⟨(-12534),12613⟩,⟨(-12579),12568⟩⟩,⟨⟨(-1104),1097⟩,⟨(-1102),1099⟩⟩,⟨⟨(-21),20⟩,⟨(-20),21⟩⟩,⟨⟨(-277401326256),(-277401326254)⟩,⟨(-1075978954240),(-1075978954238)⟩⟩,⟨⟨13270119511226416852,13270119511226417375⟩,⟨15908908850056780874,15908908850056781397⟩⟩,⟨⟨(-42548191049519827397379),(-42548191049519824733520)⟩,⟨481090122741771045329714,481090122741771047997695⟩⟩]
lemma ha24_1_16_eq (j : Fin 7) : ha24_1_16 j = ((ha24_1_15 j).mul (piI.mul (atomPoints j).z)).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha24_1_16_contains (j : Fin 7) : (ha24_1_16 j).Contains (fullFactor true 24 16 ((j.val:ℝ)/6)) := by
  rw [ha24_1_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_1_15 j) true 24 15 j (ha24_1_15_contains j)
noncomputable def hk24_1_17 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_17 j i k)
lemma hk24_1_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_1_17 j i k).Contains (fullFactor true 24 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_1_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel24_0 j i k) (mpower1_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 17 (kernel24_0_contains j i k) (mpower1_17_contains j i k)
noncomputable def ha24_1_17 : Fin 7 → CBox := ![⟨⟨(-216),216⟩,⟨(-216),216⟩⟩,⟨⟨(-8439),8401⟩,⟨(-8427),8414⟩⟩,⟨⟨(-652),653⟩,⟨(-651),654⟩⟩,⟨⟨(-10),10⟩,⟨(-10),10⟩⟩,⟨⟨(-267685250203),(-267685250201)⟩,⟨171298987392,171298987394⟩⟩,⟨⟨3273317075756093392,3273317075756093540⟩,⟨(-3848064194479459877),(-3848064194479459729)⟩⟩,⟨⟨102659904510496590294007,102659904510496590890473⟩,⟨3723924696961336319265,3723924696961336914620⟩⟩]
lemma ha24_1_17_eq (j : Fin 7) : ha24_1_17 j = ((ha24_1_16 j).mul (piI.mul (atomPoints j).z)).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha24_1_17_contains (j : Fin 7) : (ha24_1_17 j).Contains (fullFactor true 24 17 ((j.val:ℝ)/6)) := by
  rw [ha24_1_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_1_16 j) true 24 16 j (ha24_1_16_contains j)
noncomputable def hk24_1_18 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_18 j i k)
lemma hk24_1_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_1_18 j i k).Contains (fullFactor true 24 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_1_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel24_0 j i k) (mpower1_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 18 (kernel24_0_contains j i k) (mpower1_18_contains j i k)
noncomputable def ha24_1_18 : Fin 7 → CBox := ![⟨⟨(-111),111⟩,⟨(-111),111⟩⟩,⟨⟨(-5319),5333⟩,⟨(-5319),5333⟩⟩,⟨⟨(-365),366⟩,⟨(-366),365⟩⟩,⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨66502113516,66502113518⟩,⟨54284663191,54284663193⟩⟩,⟨⟨(-1001438617432239996),(-1001438617432239956)⟩,⟨(-592347682626051308),(-592347682626051268)⟩⟩,⟨⟨(-323866974749793663380),(-323866974749793537716)⟩,⟨(-20633713452162932706618),(-20633713452162932580682)⟩⟩]
lemma ha24_1_18_eq (j : Fin 7) : ha24_1_18 j = ((ha24_1_17 j).mul (piI.mul (atomPoints j).z)).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha24_1_18_contains (j : Fin 7) : (ha24_1_18 j).Contains (fullFactor true 24 18 ((j.val:ℝ)/6)) := by
  rw [ha24_1_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_1_17 j) true 24 17 j (ha24_1_17_contains j)
noncomputable def hk24_1_19 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_19 j i k)
lemma hk24_1_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_1_19 j i k).Contains (fullFactor true 24 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_1_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel24_0 j i k) (mpower1_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 19 (kernel24_0_contains j i k) (mpower1_19_contains j i k)
noncomputable def ha24_1_19 : Fin 7 → CBox := ![⟨⟨(-54),54⟩,⟨(-54),54⟩⟩,⟨⟨(-3193),3190⟩,⟨(-3196),3187⟩⟩,⟨⟨(-195),194⟩,⟨(-194),194⟩⟩,⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨7895797388,7895797390⟩,⟨(-20499982150),(-20499982149)⟩⟩,⟨⟨(-90241967299813062),(-90241967299813051)⟩,⟨237282456480201624,237282456480201635⟩⟩,⟨⟨(-3918319103202904857932),(-3918319103202904832742)⟩,⟨265471245232249509747,265471245232249534877⟩⟩]
lemma ha24_1_19_eq (j : Fin 7) : ha24_1_19 j = ((ha24_1_18 j).mul (piI.mul (atomPoints j).z)).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha24_1_19_contains (j : Fin 7) : (ha24_1_19 j).Contains (fullFactor true 24 19 ((j.val:ℝ)/6)) := by
  rw [ha24_1_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_1_18 j) true 24 18 j (ha24_1_18_contains j)
noncomputable def hk24_1_20 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_20 j i k)
lemma hk24_1_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_1_20 j i k).Contains (fullFactor true 24 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_1_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel24_0 j i k) (mpower1_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 20 (kernel24_0_contains j i k) (mpower1_20_contains j i k)
noncomputable def ha24_1_20 : Fin 7 → CBox := ![⟨⟨(-25),25⟩,⟨(-25),25⟩⟩,⟨⟨(-1817),1817⟩,⟨(-1815),1819⟩⟩,⟨⟨(-98),98⟩,⟨(-98),98⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-5333732181),(-5333732180)⟩,⟨(-270685917),(-270685916)⟩⟩,⟨⟨51646347579002299,51646347579002303⟩,⟨10077296110784366,10077296110784369⟩⟩,⟨⟨84718974955815787616,84718974955815792392⟩,⟨704965194156736913030,704965194156736917817⟩⟩]
lemma ha24_1_20_eq (j : Fin 7) : ha24_1_20 j = ((ha24_1_19 j).mul (piI.mul (atomPoints j).z)).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha24_1_20_contains (j : Fin 7) : (ha24_1_20 j).Contains (fullFactor true 24 20 ((j.val:ℝ)/6)) := by
  rw [ha24_1_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_1_19 j) true 24 19 j (ha24_1_19_contains j)
noncomputable def hk24_1_21 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_21 j i k)
lemma hk24_1_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_1_21 j i k).Contains (fullFactor true 24 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_1_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel24_0 j i k) (mpower1_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 21 (kernel24_0_contains j i k) (mpower1_21_contains j i k)
noncomputable def ha24_1_21 : Fin 7 → CBox := ![⟨⟨(-11),11⟩,⟨(-11),11⟩⟩,⟨⟨(-985),986⟩,⟨(-986),985⟩⟩,⟨⟨(-48),48⟩,⟨(-48),48⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨325330451,325330452⟩,⟨1192950985,1192950986⟩⟩,⟨⟨228283577889413,228283577889415⟩,⟨(-10385148075089297),(-10385148075089295)⟩⟩,⟨⟨120463795539878642340,120463795539878643208⟩,⟨(-20871243023580324702),(-20871243023580323836)⟩⟩]
lemma ha24_1_21_eq (j : Fin 7) : ha24_1_21 j = ((ha24_1_20 j).mul (piI.mul (atomPoints j).z)).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha24_1_21_contains (j : Fin 7) : (ha24_1_21 j).Contains (fullFactor true 24 21 ((j.val:ℝ)/6)) := by
  rw [ha24_1_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_1_20 j) true 24 20 j (ha24_1_20_contains j)
noncomputable def hk24_1_22 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_22 j i k)
lemma hk24_1_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_1_22 j i k).Contains (fullFactor true 24 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_1_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel24_0 j i k) (mpower1_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 22 (kernel24_0_contains j i k) (mpower1_22_contains j i k)
noncomputable def ha24_1_22 : Fin 7 → CBox := ![⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨(-511),510⟩,⟨(-510),511⟩⟩,⟨⟨(-22),22⟩,⟨(-22),22⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨228110411,228110413⟩,⟨(-150489507),(-150489506)⟩⟩,⟨⟨(-1935781161997826),(-1935781161997825)⟩,⟨290077550146567,290077550146568⟩⟩,⟨⟨(-4453931497331855040),(-4453931497331854889)⟩,⟨(-19594492686332756182),(-19594492686332756031)⟩⟩]
lemma ha24_1_22_eq (j : Fin 7) : ha24_1_22 j = ((ha24_1_21 j).mul (piI.mul (atomPoints j).z)).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha24_1_22_contains (j : Fin 7) : (ha24_1_22 j).Contains (fullFactor true 24 22 ((j.val:ℝ)/6)) := by
  rw [ha24_1_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_1_21 j) true 24 21 j (ha24_1_21_contains j)
noncomputable def hk24_1_23 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_23 j i k)
lemma hk24_1_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_1_23 j i k).Contains (fullFactor true 24 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_1_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel24_0 j i k) (mpower1_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 23 (kernel24_0_contains j i k) (mpower1_23_contains j i k)
noncomputable def ha24_1_23 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-253),253⟩,⟨(-253),253⟩⟩,⟨⟨(-10),10⟩,⟨(-10),10⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-45257761),(-45257759)⟩,⟨(-35905322),(-35905321)⟩⟩,⟨⟨110801438671964,110801438671965⟩,⟨334953740555303,334953740555304⟩⟩,⟨⟨(-3039995375995912174),(-3039995375995912148)⟩,⟨859242879253795247,859242879253795273⟩⟩]
lemma ha24_1_23_eq (j : Fin 7) : ha24_1_23 j = ((ha24_1_22 j).mul (piI.mul (atomPoints j).z)).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha24_1_23_contains (j : Fin 7) : (ha24_1_23 j).Contains (fullFactor true 24 23 ((j.val:ℝ)/6)) := by
  rw [ha24_1_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_1_22 j) true 24 22 j (ha24_1_22_contains j)
noncomputable def hk24_1_24 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_24 j i k)
lemma hk24_1_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_1_24 j i k).Contains (fullFactor true 24 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_1_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel24_0 j i k) (mpower1_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 24 (kernel24_0_contains j i k) (mpower1_24_contains j i k)
noncomputable def ha24_1_24 : Fin 7 → CBox := ![⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-121),121⟩,⟨(-121),121⟩⟩,⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-4054191),(-4054189)⟩,⟨10979154,10979156⟩⟩,⟨⟨53764465749867,53764465749868⟩,⟨(-28690261879610),(-28690261879609)⟩⟩,⟨⟨153065772433055615,153065772433055620⟩,⟨450673314276140780,450673314276140785⟩⟩]
lemma ha24_1_24_eq (j : Fin 7) : ha24_1_24 j = ((ha24_1_23 j).mul (piI.mul (atomPoints j).z)).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha24_1_24_contains (j : Fin 7) : (ha24_1_24 j).Contains (fullFactor true 24 24 ((j.val:ℝ)/6)) := by
  rw [ha24_1_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_1_23 j) true 24 23 j (ha24_1_23_contains j)
noncomputable def hk24_1_25 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_25 j i k)
lemma hk24_1_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_1_25 j i k).Contains (fullFactor true 24 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_1_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel24_0 j i k) (mpower1_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 25 (kernel24_0_contains j i k) (mpower1_25_contains j i k)
noncomputable def ha24_1_25 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-56),56⟩,⟨(-56),56⟩⟩,⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨2274684,2274686⟩,⟨83718,83720⟩⟩,⟨⟨(-6202991889630),(-6202991889629)⟩,⟨(-7977482519329),(-7977482519328)⟩⟩,⟨⟨63946055971352540,63946055971352542⟩,⟨(-25493957186357555),(-25493957186357553)⟩⟩]
lemma ha24_1_25_eq (j : Fin 7) : ha24_1_25 j = ((ha24_1_24 j).mul (piI.mul (atomPoints j).z)).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha24_1_25_contains (j : Fin 7) : (ha24_1_25 j).Contains (fullFactor true 24 25 ((j.val:ℝ)/6)) := by
  rw [ha24_1_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_1_24 j) true 24 24 j (ha24_1_24_contains j)
noncomputable def hk24_1_26 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_26 j i k)
lemma hk24_1_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_1_26 j i k).Contains (fullFactor true 24 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_1_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel24_0 j i k) (mpower1_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 26 (kernel24_0_contains j i k) (mpower1_26_contains j i k)
noncomputable def ha24_1_26 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-25),25⟩,⟨(-25),25⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-117700),(-117698)⟩,⟨(-409073),(-409072)⟩⟩,⟨⟨(-1085445357720),(-1085445357719)⟩,⟨1190755358254,1190755358255⟩⟩,⟨⟨(-4002565716631611),(-4002565716631610)⟩,⟨(-8697068743503449),(-8697068743503448)⟩⟩]
lemma ha24_1_26_eq (j : Fin 7) : ha24_1_26 j = ((ha24_1_25 j).mul (piI.mul (atomPoints j).z)).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha24_1_26_contains (j : Fin 7) : (ha24_1_26 j).Contains (fullFactor true 24 26 ((j.val:ℝ)/6)) := by
  rw [ha24_1_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_1_25 j) true 24 25 j (ha24_1_25_contains j)
noncomputable def hk24_1_27 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_27 j i k)
lemma hk24_1_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_1_27 j i k).Contains (fullFactor true 24 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_1_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel24_0 j i k) (mpower1_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 27 (kernel24_0_contains j i k) (mpower1_27_contains j i k)
noncomputable def ha24_1_27 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-11),11⟩,⟨(-11),11⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-63392),(-63390)⟩,⟨43098,43099⟩⟩,⟨⟨208484177064,208484177065⟩,⟨133174467525,133174467526⟩⟩,⟨⟨(-1135324685300557),(-1135324685300556)⟩,⟨595794325629746,595794325629747⟩⟩]
lemma ha24_1_27_eq (j : Fin 7) : ha24_1_27 j = ((ha24_1_26 j).mul (piI.mul (atomPoints j).z)).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha24_1_27_contains (j : Fin 7) : (ha24_1_27 j).Contains (fullFactor true 24 27 ((j.val:ℝ)/6)) := by
  rw [ha24_1_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_1_26 j) true 24 26 j (ha24_1_26_contains j)
noncomputable def hk24_1_28 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_28 j i k)
lemma hk24_1_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_1_28 j i k).Contains (fullFactor true 24 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_1_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel24_0 j i k) (mpower1_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 28 (kernel24_0_contains j i k) (mpower1_28_contains j i k)
noncomputable def ha24_1_28 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨10541,10543⟩,⟨8126,8128⟩⟩,⟨⟨14186452448,14186452449⟩,⟨(-33768393962),(-33768393961)⟩⟩,⟨⟨84450448126823,84450448126824⟩,⟨142421882216914,142421882216915⟩⟩]
lemma ha24_1_28_eq (j : Fin 7) : ha24_1_28 j = ((ha24_1_27 j).mul (piI.mul (atomPoints j).z)).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha24_1_28_contains (j : Fin 7) : (ha24_1_28 j).Contains (fullFactor true 24 28 ((j.val:ℝ)/6)) := by
  rw [ha24_1_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_1_27 j) true 24 27 j (ha24_1_27_contains j)
noncomputable def hk24_1_29 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_29 j i k)
lemma hk24_1_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_1_29 j i k).Contains (fullFactor true 24 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_1_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel24_0 j i k) (mpower1_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 29 (kernel24_0_contains j i k) (mpower1_29_contains j i k)
noncomputable def ha24_1_29 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨743,745⟩,⟨(-2105),(-2103)⟩⟩,⟨⟨(-5101568138),(-5101568137)⟩,⟨(-1178365795),(-1178365793)⟩⟩,⟨⟨17187295905543,17187295905544⟩,⟨(-11437786264349),(-11437786264348)⟩⟩]
lemma ha24_1_29_eq (j : Fin 7) : ha24_1_29 j = ((ha24_1_28 j).mul (piI.mul (atomPoints j).z)).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha24_1_29_contains (j : Fin 7) : (ha24_1_29 j).Contains (fullFactor true 24 29 ((j.val:ℝ)/6)) := by
  rw [ha24_1_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_1_28 j) true 24 28 j (ha24_1_28_contains j)
noncomputable def hk24_1_30 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_30 j i k)
lemma hk24_1_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk24_1_30 j i k).Contains (fullFactor true 24 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk24_1_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel24_0 j i k) (mpower1_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 24 30 (kernel24_0_contains j i k) (mpower1_30_contains j i k)
noncomputable def ha24_1_30 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-362),(-361)⟩,⟨(-9),(-8)⟩⟩,⟨⟨(-40697100),(-40697098)⟩,⟨722378168,722378169⟩⟩,⟨⟨(-1484315340771),(-1484315340770)⟩,⟨(-1997202051964),(-1997202051963)⟩⟩]
lemma ha24_1_30_eq (j : Fin 7) : ha24_1_30 j = ((ha24_1_29 j).mul (piI.mul (atomPoints j).z)).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha24_1_30_contains (j : Fin 7) : (ha24_1_30 j).Contains (fullFactor true 24 30 ((j.val:ℝ)/6)) := by
  rw [ha24_1_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha24_1_29 j) true 24 29 j (ha24_1_29_contains j)
end SharpPlanar.CachedData

end OAI
