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
noncomputable def hk1_0_0 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_0 j i k)
lemma hk1_0_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_0_0 j i k).Contains (fullFactor false 1 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_0_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power1 j i k) (mpower0_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 0 (power1_contains j i k) (mpower0_0_contains j i k)
noncomputable def ha1_0_0 : Fin 7 → CBox := ![⟨⟨999999999999999999999999999989,1000000000000000000000000000015⟩,⟨(-15),15⟩⟩,⟨⟨866025403784438646763098939526,866025403784438646763954632529⟩,⟨499999999999999999999469888220,500000000000000000001210408427⟩⟩,⟨⟨499999999999999999997708137538,500000000000000000000931269165⟩,⟨866025403784438646762180554973,866025403784438646766051325440⟩⟩,⟨⟨(-4444983321),2088366603⟩,⟨999999999999999999996733325039,1000000000000000000003266674962⟩⟩,⟨⟨(-500000000000000000006328835244),(-499999999999999999996392351351)⟩,⟨866025403784438646758206118258,866025403784438646767669145432⟩⟩,⟨⟨(-866025403784438646770926677365),(-866025403784438646758483511404)⟩,⟨499999999999999999992312631744,500000000000000000004285885012⟩⟩,⟨⟨(-1000000000000000000006553197785),(-999999999999999999993446802219)⟩,⟨(-8909814505),4196581061⟩⟩]
lemma ha1_0_0_eq (j : Fin 7) : ha1_0_0 j = ((atomPoints j).direct.powBin 7 1).conj := by fin_cases j <;> decide +kernel
lemma ha1_0_0_contains (j : Fin 7) : (ha1_0_0 j).Contains (fullFactor false 1 0 ((j.val:ℝ)/6)) := by
  rw [ha1_0_0_eq]
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @direct_factor_zero_full ((atomPoints j).direct.powBin 7 1) ((j.val:ℝ)/6) 1 (@direct_power_bin_contains (atomPoints j) ((j.val:ℝ)/6) (atomPoints_contains j) 1 (by norm_num))
noncomputable def hk1_0_1 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_1 j i k)
lemma hk1_0_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_0_1 j i k).Contains (fullFactor false 1 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_0_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power1 j i k) (mpower0_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 1 (power1_contains j i k) (mpower0_1_contains j i k)
noncomputable def ha1_0_1 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-261799387799149436539800435038),(-261799387799149436538055767453)⟩,⟨453449841058554462647811178190,453449841058554462649702593676⟩⟩,⟨⟨(-906899682117108925301600839033),(-906899682117108925294660626328)⟩,⟨523598775598298873074266633908,523598775598298873079308556124⟩⟩,⟨⟨(-1570796326794896619240131281032),(-1570796326794896619224868718970)⟩,⟨(-6982163474),3280398589⟩⟩,⟨⟨(-1813799364234217850606590032330),(-1813799364234217850580997211866)⟩,⟨(-1047197551196597746169921748207),(-1047197551196597746145777491670)⟩⟩,⟨⟨(-1308996938995747182707053754058),(-1308996938995747182671541183633)⟩,⟨(-2267249205292772313266765739071),(-2267249205292772313226972728393)⟩⟩,⟨⟨(-13183948232),27991007794⟩,⟨(-3141592653589793238490587478019),(-3141592653589793238439412521993)⟩⟩]
lemma ha1_0_1_eq (j : Fin 7) : ha1_0_1 j = ((ha1_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha1_0_1_contains (j : Fin 7) : (ha1_0_1 j).Contains (fullFactor false 1 1 ((j.val:ℝ)/6)) := by
  rw [ha1_0_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_0_0 j) false 1 0 j (ha1_0_0_contains j)
noncomputable def hk1_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_2 j i k)
lemma hk1_0_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_0_2 j i k).Contains (fullFactor false 1 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_0_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power1 j i k) (mpower0_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 2 (power1_contains j i k) (mpower0_2_contains j i k)
noncomputable def ha1_0_2 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-118712890786751174408525015863),(-118712890786751174407651969578)⟩,⟨(-68538919452009434853504211742),(-68538919452009434852829292678)⟩⟩,⟨⟨(-274155677808037739413863791737),(-274155677808037739410351182810)⟩,⟨(-474851563147004697635249703984),(-474851563147004697630104317636)⟩⟩,⟨⟨(-2576419028),5483778370⟩,⟨(-1233700550136169827364119346945),(-1233700550136169827348205167914)⟩⟩,⟨⟨1096622711232150957638518889210,1096622711232150957667293354039⟩,⟨(-1899406252588018790544547092218),(-1899406252588018790511700355414)⟩⟩,⟨⟨2967822269668779360175482416665,2967822269668779360237018217530⟩,⟨(-1713472986300235871348144785615),(-1713472986300235871296204785717)⟩⟩,⟨⟨4934802200544679309376602331615,4934802200544679309472695727833⟩,⟨(-20709297456),43968172227⟩⟩]
lemma ha1_0_2_eq (j : Fin 7) : ha1_0_2 j = ((ha1_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha1_0_2_contains (j : Fin 7) : (ha1_0_2 j).Contains (fullFactor false 1 2 ((j.val:ℝ)/6)) := by
  rw [ha1_0_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_0_1 j) false 1 1 j (ha1_0_1_contains j)
noncomputable def hk1_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_3 j i k)
lemma hk1_0_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_0_3 j i k).Contains (fullFactor false 1 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_0_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power1 j i k) (mpower0_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 3 (power1_contains j i k) (mpower0_3_contains j i k)
noncomputable def ha1_0_3 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨11962298101967523215804465293,11962298101967523215960338070⟩,⟨(-20719308087892496642566511763),(-20719308087892496642348184834)⟩⟩,⟨⟨165754464703139973138609702841,165754464703139973140933394351⟩,⟨(-95698384815740185727629278199),(-95698384815740185726098528956)⟩⟩,⟨⟨645964097506246253652015837451,645964097506246253662404649691⟩,⟨(-1349009849),2871299641⟩⟩,⟨⟨1326035717625119785102792067944,1326035717625119785129944318962⟩,⟨765587078525921485806773533848,765587078525921485829298839279⟩⟩,⟨⟨1495287262745940401954153852773,1495287262745940402004239700545⟩,⟨2589913510986562080279720322587,2589913510986562080341664389988⟩⟩,⟨⟨(-46043362287),21686725583⟩,⟨5167712780049970029199142893634,5167712780049970029316221003509⟩⟩]
lemma ha1_0_3_eq (j : Fin 7) : ha1_0_3 j = ((ha1_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha1_0_3_contains (j : Fin 7) : (ha1_0_3 j).Contains (fullFactor false 1 3 ((j.val:ℝ)/6)) := by
  rw [ha1_0_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_0_2 j) false 1 2 j (ha1_0_2_contains j)
noncomputable def hk1_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_4 j i k)
lemma hk1_0_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_0_4 j i k).Contains (fullFactor false 1 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_0_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power1 j i k) (mpower0_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 4 (power1_contains j i k) (mpower0_4_contains j i k)
noncomputable def ha1_0_4 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2712151086516110563384867168,2712151086516110563422079143⟩,⟨1565861159883012429848399102,1565861159883012429873787093⟩⟩,⟨⟨25053778558128198877486108620,25053778558128198877966606490⟩,⟨43394417384257769014111856697,43394417384257769014858326433⟩⟩,⟨⟨(-1127556733),529754929⟩,⟨253669507901048013634880945199,253669507901048013639768077348⟩⟩,⟨⟨(-400860456930051182051793045432),(-400860456930051182038722844623)⟩,⟨694310678148124304222603318122,694310678148124304239030263042⟩⟩,⟨⟨(-1695094429072569102152446031543),(-1695094429072569102106508081083)⟩,⟨978663224926882768641240351789,978663224926882768677136644299⟩⟩,⟨⟨(-4058712126416768218249628287592),(-4058712126416768218144756073171)⟩,⟨(-36162372177),17032714443⟩⟩]
lemma ha1_0_4_eq (j : Fin 7) : ha1_0_4 j = ((ha1_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha1_0_4_contains (j : Fin 7) : (ha1_0_4 j).Contains (fullFactor false 1 4 ((j.val:ℝ)/6)) := by
  rw [ha1_0_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_0_3 j) false 1 3 j (ha1_0_3_contains j)
noncomputable def hk1_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_5 j i k)
lemma hk1_0_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_0_5 j i k).Contains (fullFactor false 1 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_0_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power1 j i k) (mpower0_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 5 (power1_contains j i k) (mpower0_5_contains j i k)
noncomputable def ha1_0_5 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-163976597214335483789365320),(-163976597214335483786184741)⟩,⟨284015797627486289485824466,284015797627486289490625346⟩⟩,⟨⟨(-9088505524079561263722014810),(-9088505524079561263536744941)⟩,⟨5247251110858735481139423048,5247251110858735481256760806⟩⟩,⟨⟨(-79692626246167045121698954070),(-79692626246167045119909946715)⟩,⟨(-354232395),166427420⟩⟩,⟨⟨(-290832176770545960439647776797),(-290832176770545960431841126627)⟩,⟨(-167912035547479535402028978391),(-167912035547479535396019664868)⟩⟩,⟨⟨(-512426866294798386844918537985),(-512426866294798386824492177802)⟩,⟨(-887549367585894654665349531347),(-887549367585894654638471319349)⟩⟩,⟨⟨(-10701970113),22721488554⟩,⟨(-2550164039877345443902747702527),(-2550164039877345443828737122595)⟩⟩]
lemma ha1_0_5_eq (j : Fin 7) : ha1_0_5 j = ((ha1_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha1_0_5_contains (j : Fin 7) : (ha1_0_5 j).Contains (fullFactor false 1 5 ((j.val:ℝ)/6)) := by
  rw [ha1_0_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_0_4 j) false 1 4 j (ha1_0_4_contains j)
noncomputable def hk1_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_6 j i k)
lemma hk1_0_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_0_6 j i k).Contains (fullFactor false 1 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_0_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power1 j i k) (mpower0_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 6 (power1_contains j i k) (mpower0_6_contains j i k)
noncomputable def ha1_0_6 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-24785053981387676527259306),(-24785053981387676526761455)⟩,⟨(-14309657588033580845950123),(-14309657588033580845627015)⟩⟩,⟨⟨(-915818085634149174140296530),(-915818085634149174116902088)⟩,⟨(-1586243454808811297748435899),(-1586243454808811297711051036)⟩⟩,⟨⟨(-43570597),92737825⟩,⟨(-20863480763352960873412925496),(-20863480763352960872878153943)⟩⟩,⟨⟨58612357480585547143327490984,58612357480585547145611706049⟩,⟨(-101519581107763923056089545957),(-101519581107763923053041364113)⟩⟩,⟨⟨387266468459182445728583837304,387266468459182445741544377171⟩,⟨(-223588399813024700719345938835),(-223588399813024700709721553868)⟩⟩,⟨⟨1335262768854589495859813480852,1335262768854589495902815603287⟩,⟨(-5603538448),11896943587⟩⟩]
lemma ha1_0_6_eq (j : Fin 7) : ha1_0_6 j = ((ha1_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha1_0_6_contains (j : Fin 7) : (ha1_0_6 j).Contains (fullFactor false 1 6 ((j.val:ℝ)/6)) := by
  rw [ha1_0_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_0_5 j) false 1 5 j (ha1_0_5_contains j)
noncomputable def hk1_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_7 j i k)
lemma hk1_0_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_0_7 j i k).Contains (fullFactor false 1 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_0_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power1 j i k) (mpower0_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 7 (power1_contains j i k) (mpower0_7_contains j i k)
noncomputable def ha1_0_7 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1070359884617898514095318,1070359884617898514122895⟩,⟨(-1853917702541761442288448),(-1853917702541761442245307)⟩⟩,⟨⟨237301465925345464607147672,237301465925345464613495790⟩,⟨(-137006065231091009807653991),(-137006065231091009803718086)⟩⟩,⟨⟨4681754135318688100642595076,4681754135318688100777500019⟩,⟨(-9777220),20810320⟩⟩,⟨⟨30374587638444219469575504497,30374587638444219470584203689⟩,⟨17536776349579649254829765721,17536776349579649255569022564⟩⟩,⟨⟨83621865985773321412499787622,83621865985773321416365475850⟩,⟨144837320511075112674642723376,144837320511075112679950985462⟩⟩,⟨⟨(-5339335797),2514862175⟩,⟨599264529320792076880282673284,599264529320792076901489498945⟩⟩]
lemma ha1_0_7_eq (j : Fin 7) : ha1_0_7 j = ((ha1_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha1_0_7_contains (j : Fin 7) : (ha1_0_7 j).Contains (fullFactor false 1 7 ((j.val:ℝ)/6)) := by
  rw [ha1_0_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_0_6 j) false 1 6 j (ha1_0_6_contains j)
noncomputable def hk1_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_8 j i k)
lemma hk1_0_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_0_8 j i k).Contains (fullFactor false 1 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_0_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power1 j i k) (mpower0_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 8 (power1_contains j i k) (mpower0_8_contains j i k)
noncomputable def ha1_0_8 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨121338629888859693713686,121338629888859693716897⟩,⟨70054890629433514725998,70054890629433514728027⟩⟩,⟨⟨17934052001134979769792453,17934052001134979770364749⟩,⟨31062689251548081590670895,31062689251548081591600739⟩⟩,⟨⟨(-4086097),1919753⟩,⟨919260274839426580232525461,919260274839426580261940082⟩⟩,⟨⟨(-4591117312290554821262937232),(-4591117312290554821054786262)⟩,⟨7952048448396308887175255146,7952048448396308887464644134⟩⟩,⟨⟨(-47397902300335817858544323181),(-47397902300335817856656326266)⟩,⟨27365191652122466689451487779,27365191652122466690803637405⟩⟩,⟨⟨(-235330630358893204547830080398),(-235330630358893204538753098773)⟩,⟨(-2096752265),987584067⟩⟩]
lemma ha1_0_8_eq (j : Fin 7) : ha1_0_8 j = ((ha1_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha1_0_8_contains (j : Fin 7) : (ha1_0_8 j).Contains (fullFactor false 1 8 ((j.val:ℝ)/6)) := by
  rw [ha1_0_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_0_7 j) false 1 7 j (ha1_0_7_contains j)
noncomputable def hk1_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_9 j i k)
lemma hk1_0_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_0_9 j i k).Contains (fullFactor false 1 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_0_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power1 j i k) (mpower0_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 9 (power1_contains j i k) (mpower0_9_contains j i k)
noncomputable def ha1_0_9 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-4075628328693792152529),(-4075628328693792152397)⟩,⟨7059195338064676366503,7059195338064676366713⟩⟩,⟨⟨(-3614308013089114299765750),(-3614308013089114299646052)⟩,⟨2086721704291221582020112,2086721704291221582093345⟩⟩,⟨⟨(-160441184787359821876566303),(-160441184787359821870921782)⟩,⟨(-713159),335061⟩⟩,⟨⟨(-1850525702701626521483520556),(-1850525702701626521410286274)⟩,⟨(-1068401512597105450043325960),(-1068401512597105449991486201)⟩⟩,⟨⟨(-7960211579480062797955874928),(-7960211579480062797537212404)⟩,⟨(-13787490894657571028847107738),(-13787490894657571028254024750)⟩⟩,⟨⟨(-344731873),731904613⟩,⟨(-82145886611128228801071921017),(-82145886611128228797641978228)⟩⟩]
lemma ha1_0_9_eq (j : Fin 7) : ha1_0_9 j = ((ha1_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha1_0_9_contains (j : Fin 7) : (ha1_0_9 j).Contains (fullFactor false 1 9 ((j.val:ℝ)/6)) := by
  rw [ha1_0_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_0_8 j) false 1 8 j (ha1_0_8_contains j)
noncomputable def hk1_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_10 j i k)
lemma hk1_0_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_0_10 j i k).Contains (fullFactor false 1 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_0_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power1 j i k) (mpower0_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 10 (power1_contains j i k) (mpower0_10_contains j i k)
noncomputable def ha1_0_10 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-369618603571988403199),(-369618603571988403186)⟩,⟨(-213399400269781075732),(-213399400269781075723)⟩⟩,⟨⟨(-218520985876255821548635),(-218520985876255821540270)⟩,⟨(-378489450057716124876308),(-378489450057716124862567)⟩⟩,⟨⟨(-52632),112023⟩,⟨(-25202042373060605481725501),(-25202042373060605480758641)⟩⟩,⟨⟨223765489537285961256648084,223765489537285961268217647⟩,⟨(-387573196859101311874062639),(-387573196859101311857490802)⟩⟩,⟨⟨3609556675507699249848862591,3609556675507699250015620931⟩,⟨(-2083978518259580817700395011),(-2083978518259580817584155908)⟩⟩,⟨⟨25806891390014060012212033526,25806891390014060013371727720⟩,⟨(-108300712),229934616⟩⟩]
lemma ha1_0_10_eq (j : Fin 7) : ha1_0_10 j = ((ha1_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha1_0_10_contains (j : Fin 7) : (ha1_0_10 j).Contains (fullFactor false 1 10 ((j.val:ℝ)/6)) := by
  rw [ha1_0_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_0_9 j) false 1 9 j (ha1_0_9_contains j)
noncomputable def hk1_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_11 j i k)
lemma hk1_0_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_0_11 j i k).Contains (fullFactor false 1 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_0_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power1 j i k) (mpower0_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 11 (power1_contains j i k) (mpower0_11_contains j i k)
noncomputable def ha1_0_11 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨10157787699515332860,10157787699515332861⟩,⟨(-17593804388058740566),(-17593804388058740564)⟩⟩,⟨⟨36032111386744300675768,36032111386744300677192⟩,⟨(-20803149208607401698767),(-20803149208607401697903)⟩⟩,⟨⟨3598843235212085340413474,3598843235212085340562998⟩,⟨(-7516),15997⟩⟩,⟨⟨73793764120052327783635112,73793764120052327787025276⟩,⟨42604849579227958677194630,42604849579227958679533086⟩⟩,⟨⟨495985727515397112314205138,495985727515397112343448752⟩,⟨859072479885680691614499650,859072479885680691656922555⟩⟩,⟨⟨(-65669173),30930612⟩,⟨7370430945714350777142572560,7370430945714350777497241258⟩⟩]
lemma ha1_0_11_eq (j : Fin 7) : ha1_0_11 j = ((ha1_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha1_0_11_contains (j : Fin 7) : (ha1_0_11 j).Contains (fullFactor false 1 11 ((j.val:ℝ)/6)) := by
  rw [ha1_0_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_0_10 j) false 1 10 j (ha1_0_10_contains j)
noncomputable def hk1_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_12 j i k)
lemma hk1_0_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_0_12 j i k).Contains (fullFactor false 1 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_0_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power1 j i k) (mpower0_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 12 (power1_contains j i k) (mpower0_12_contains j i k)
noncomputable def ha1_0_12 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨767674536308627877,767674536308627878⟩,⟨443217100187807442,443217100187807443⟩⟩,⟨⟨1815417242369259285485,1815417242369259285567⟩,⟨3144394900720139784887,3144394900720139785022⟩⟩,⟨⟨(-2095),984⟩,⟨471087477881817150360732,471087477881817150381805⟩⟩,⟨⟨(-7435949024744486033759378),(-7435949024744486033327570)⟩,⟨12879441513349692558840825,12879441513349692559473518⟩⟩,⟨⟨(-187420541090973602833720545),(-187420541090973602823868724)⟩,⟨108207299850538926450344991,108207299850538926457069394⟩⟩,⟨⟨(-1929574309403923047970211882),(-1929574309403923047871217807)⟩,⟨(-17192150),8097616⟩⟩]
lemma ha1_0_12_eq (j : Fin 7) : ha1_0_12 j = ((ha1_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha1_0_12_contains (j : Fin 7) : (ha1_0_12 j).Contains (fullFactor false 1 12 ((j.val:ℝ)/6)) := by
  rw [ha1_0_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_0_11 j) false 1 11 j (ha1_0_11_contains j)
noncomputable def hk1_0_13 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_13 j i k)
lemma hk1_0_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_0_13 j i k).Contains (fullFactor false 1 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_0_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power1 j i k) (mpower0_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 13 (power1_contains j i k) (mpower0_13_contains j i k)
noncomputable def ha1_0_13 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-17851379306351119),(-17851379306351118)⟩,⟨30919495943783799,30919495943783800⟩⟩,⟨⟨(-253292510771476882290),(-253292510771476882277)⟩,⟨146238499277628361509,146238499277628361517⟩⟩,⟨⟨(-56921729219679268119672),(-56921729219679268116943)⟩,⟨(-254),119⟩⟩,⟨⟨(-2074972248239938619717654),(-2074972248239938619609117)⟩,⟨(-1197985786082331537554947),(-1197985786082331537481565)⟩⟩,⟨⟨(-21791234504823142516216682),(-21791234504823142514793129)⟩,⟨(-37743525322001707895205223),(-37743525322001707893101080)⟩⟩,⟨⟨(-1956878),4154672⟩,⟨(-466302805767612564437879828),(-466302805767612564412472535)⟩⟩]
lemma ha1_0_13_eq (j : Fin 7) : ha1_0_13 j = ((ha1_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha1_0_13_contains (j : Fin 7) : (ha1_0_13 j).Contains (fullFactor false 1 13 ((j.val:ℝ)/6)) := by
  rw [ha1_0_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_0_12 j) false 1 12 j (ha1_0_12_contains j)
noncomputable def hk1_0_14 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_14 j i k)
lemma hk1_0_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_0_14 j i k).Contains (fullFactor false 1 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_0_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power1 j i k) (mpower0_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 14 (power1_contains j i k) (mpower0_14_contains j i k)
noncomputable def ha1_0_14 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1156386444162984),(-1156386444162983)⟩,⟨(-667640024824733),(-667640024824732)⟩⟩,⟨⟨(-10938614166728417760),(-10938614166728417758)⟩,⟨(-18946235501166317752),(-18946235501166317750)⟩⟩,⟨⟨(-14),29⟩,⟨(-6386603083791852241321),(-6386603083791852240993)⟩⟩,⟨⟨179218254507678396555467,179218254507678396567017⟩,⟨(-310415122451108950042893),(-310415122451108950025667)⟩⟩,⟨⟨7058022730486958381010646,7058022730486958381426587⟩,⟨(-4074951323393142878701019),(-4074951323393142878421843)⟩⟩,⟨⟨104638104924845707116098397,104638104924845707122132854⟩,⟨(-439123),932307⟩⟩]
lemma ha1_0_14_eq (j : Fin 7) : ha1_0_14 j = ((ha1_0_13 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha1_0_14_contains (j : Fin 7) : (ha1_0_14 j).Contains (fullFactor false 1 14 ((j.val:ℝ)/6)) := by
  rw [ha1_0_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_0_13 j) false 1 13 j (ha1_0_13_contains j)
noncomputable def hk1_0_15 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_15 j i k)
lemma hk1_0_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_0_15 j i k).Contains (fullFactor false 1 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_0_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power1 j i k) (mpower0_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 15 (power1_contains j i k) (mpower0_15_contains j i k)
noncomputable def ha1_0_15 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨23305033302576,23305033302577⟩,⟨(-40365501752148),(-40365501752147)⟩⟩,⟨⟨1322696761414360852,1322696761414360853⟩,⟨(-763659331258827444),(-763659331258827443)⟩⟩,⟨⟨668803510981146723237,668803510981146723274⟩,⟨(-2),4⟩⟩,⟨⟨43342127478025776419581,43342127478025776422125⟩,⟨25023588966689257663231,25023588966689257664924⟩⟩,⟨⟨711213174517105746390013,711213174517105746441003⟩,⟨1231857353275977869191000,1231857353275977869267518⟩⟩,⟨⟨(-195262),91970⟩,⟨21915353447830215826964437,21915353447830215828298051⟩⟩]
lemma ha1_0_15_eq (j : Fin 7) : ha1_0_15 j = ((ha1_0_14 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha1_0_15_contains (j : Fin 7) : (ha1_0_15 j).Contains (fullFactor false 1 15 ((j.val:ℝ)/6)) := by
  rw [ha1_0_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_0_14 j) false 1 14 j (ha1_0_14_contains j)
noncomputable def hk1_0_16 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_16 j i k)
lemma hk1_0_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_0_16 j i k).Contains (fullFactor false 1 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_0_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power1 j i k) (mpower0_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 16 (power1_contains j i k) (mpower0_16_contains j i k)
noncomputable def ha1_0_16 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1320957955864,1320957955865⟩,⟨762655431406,762655431407⟩⟩,⟨⟨49981386352667221,49981386352667222⟩,⟨86570300595549323,86570300595549324⟩⟩,⟨⟨(-1),1⟩,⟨65659631149794723620,65659631149794723625⟩⟩,⟨⟨(-3275580136008399049540),(-3275580136008399049307)⟩,⟨5673471219829920494641,5673471219829920494993⟩⟩,⟨⟨(-201562188089707223604331),(-201562188089707223591168)⟩,⟨116371983552042445683167,116371983552042445691881⟩⟩,⟨⟨(-4303069587032947007487246),(-4303069587032947007211694)⟩,⟨(-38340),18059⟩⟩]
lemma ha1_0_16_eq (j : Fin 7) : ha1_0_16 j = ((ha1_0_15 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha1_0_16_contains (j : Fin 7) : (ha1_0_16 j).Contains (fullFactor false 1 16 ((j.val:ℝ)/6)) := by
  rw [ha1_0_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_0_15 j) false 1 15 j (ha1_0_15_contains j)
noncomputable def hk1_0_17 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_17 j i k)
lemma hk1_0_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_0_17 j i k).Contains (fullFactor false 1 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_0_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power1 j i k) (mpower0_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 17 (power1_contains j i k) (mpower0_17_contains j i k)
noncomputable def ha1_0_17 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-23489732359),(-23489732358)⟩,⟨40685409900,40685409901⟩⟩,⟨⟨(-5332718046471331),(-5332718046471330)⟩,⟨3078846199642597,3078846199642598⟩⟩,⟨⟨(-6066935731106195668),(-6066935731106195666)⟩,⟨(-1),1⟩⟩,⟨⟨(-698970019787090239246),(-698970019787090239199)⟩,⟨(-403550529079554596730),(-403550529079554596699)⟩⟩,⟨⟨(-17921243559351411743927),(-17921243559351411742527)⟩,⟨(-31040504379613153640340),(-31040504379613153638213)⟩⟩,⟨⟨(-3338),7086⟩,⟨(-795205400147551278515188),(-795205400147551278461734)⟩⟩]
lemma ha1_0_17_eq (j : Fin 7) : ha1_0_17 j = ((ha1_0_16 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha1_0_17_contains (j : Fin 7) : (ha1_0_17 j).Contains (fullFactor false 1 17 ((j.val:ℝ)/6)) := by
  rw [ha1_0_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_0_16 j) false 1 16 j (ha1_0_16_contains j)
noncomputable def hk1_0_18 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_18 j i k)
lemma hk1_0_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_0_18 j i k).Contains (fullFactor false 1 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_0_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power1 j i k) (mpower0_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 18 (power1_contains j i k) (mpower0_18_contains j i k)
noncomputable def ha1_0_18 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1183490601),(-1183490600)⟩,⟨(-683288617),(-683288616)⟩⟩,⟨⟨(-179120011154260),(-179120011154259)⟩,⟨(-310244959971483),(-310244959971482)⟩⟩,⟨⟨(-1),1⟩,⟨(-529440020073462377),(-529440020073462376)⟩⟩,⟨⟨46955236204022331367,46955236204022331372⟩,⟨(-81328854786764263387),(-81328854786764263380)⟩⟩,⟨⟨4514658357533078058030,4514658357533078058355⟩,⟨(-2606539218020916335935),(-2606539218020916335722)⟩⟩,⟨⟨138789524622137721141669,138789524622137721151441⟩,⟨(-583),1237⟩⟩]
lemma ha1_0_18_eq (j : Fin 7) : ha1_0_18 j = ((ha1_0_17 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha1_0_18_contains (j : Fin 7) : (ha1_0_18 j).Contains (fullFactor false 1 18 ((j.val:ℝ)/6)) := by
  rw [ha1_0_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_0_17 j) false 1 17 j (ha1_0_17_contains j)
noncomputable def hk1_0_19 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_19 j i k)
lemma hk1_0_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_0_19 j i k).Contains (fullFactor false 1 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_0_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power1 j i k) (mpower0_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 19 (power1_contains j i k) (mpower0_19_contains j i k)
noncomputable def ha1_0_19 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨18829951,18829952⟩,⟨(-32614434),(-32614433)⟩⟩,⟨⟨17099355913327,17099355913328⟩,⟨(-9872317739529),(-9872317739528)⟩⟩,⟨⟨43770654673137422,43770654673137423⟩,⟨(-1),1⟩⟩,⟨⟨8964987113086656144,8964987113086656146⟩,⟨5175937723022106880,5175937723022106882⟩⟩,⟨⟨359152827132815577508,359152827132815577540⟩,⟨622070944276038605474,622070944276038605521⟩⟩,⟨⟨(-205),97⟩,⟨22948428997269873109686,22948428997269873111376⟩⟩]
lemma ha1_0_19_eq (j : Fin 7) : ha1_0_19 j = ((ha1_0_18 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha1_0_19_contains (j : Fin 7) : (ha1_0_19 j).Contains (fullFactor false 1 19 ((j.val:ℝ)/6)) := by
  rw [ha1_0_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_0_18 j) false 1 18 j (ha1_0_18_contains j)
noncomputable def hk1_0_20 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_20 j i k)
lemma hk1_0_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_0_20 j i k).Contains (fullFactor false 1 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_0_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power1 j i k) (mpower0_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 20 (power1_contains j i k) (mpower0_20_contains j i k)
noncomputable def ha1_0_20 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨853843,853844⟩,⟨492966,492967⟩⟩,⟨⟨516913348073,516913348074⟩,⟨895320181973,895320181974⟩⟩,⟨⟨(-1),1⟩,⟨3437739179098606,3437739179098608⟩⟩,⟨⟨(-542022930869484434),(-542022930869484433)⟩,⟨938811255133340262,938811255133340263⟩⟩,⟨⟨(-81428896189552855160),(-81428896189552855153)⟩,⟨47012995134852432604,47012995134852432610⟩⟩,⟨⟨(-3604730797462500934052),(-3604730797462500933775)⟩,⟨(-33),16⟩⟩]
lemma ha1_0_20_eq (j : Fin 7) : ha1_0_20 j = ((ha1_0_19 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha1_0_20_contains (j : Fin 7) : (ha1_0_20 j).Contains (fullFactor false 1 20 ((j.val:ℝ)/6)) := by
  rw [ha1_0_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_0_19 j) false 1 19 j (ha1_0_19_contains j)
noncomputable def hk1_0_21 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_21 j i k)
lemma hk1_0_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_0_21 j i k).Contains (fullFactor false 1 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_0_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power1 j i k) (mpower0_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 21 (power1_contains j i k) (mpower0_21_contains j i k)
noncomputable def ha1_0_21 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-12292),(-12291)⟩,⟨21289,21290⟩⟩,⟨⟨(-44646528672),(-44646528671)⟩,⟨25776685346,25776685347⟩⟩,⟨⟨(-257142289286048),(-257142289286047)⟩,⟨(-1),1⟩⟩,⟨⟨(-93630556896327456),(-93630556896327455)⟩,⟨(-54057627228469228),(-54057627228469227)⟩⟩,⟨⟨(-5860939688051789412),(-5860939688051789411)⟩,⟨(-10151445319802585616),(-10151445319802585614)⟩⟩,⟨⟨(-3),5⟩,⟨(-539266466260812848966),(-539266466260812848922)⟩⟩]
lemma ha1_0_21_eq (j : Fin 7) : ha1_0_21 j = ((ha1_0_20 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha1_0_21_contains (j : Fin 7) : (ha1_0_21 j).Contains (fullFactor false 1 21 ((j.val:ℝ)/6)) := by
  rw [ha1_0_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_0_20 j) false 1 20 j (ha1_0_20_contains j)
noncomputable def hk1_0_22 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_22 j i k)
lemma hk1_0_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_0_22 j i k).Contains (fullFactor false 1 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_0_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power1 j i k) (mpower0_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 22 (power1_contains j i k) (mpower0_22_contains j i k)
noncomputable def ha1_0_22 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-507),(-506)⟩,⟨(-293),(-292)⟩⟩,⟨⟨(-1226967354),(-1226967353)⟩,⟨(-2125169796),(-2125169795)⟩⟩,⟨⟨(-1),1⟩,⟨(-18359916521553),(-18359916521552)⟩⟩,⟨⟨5146274077922863,5146274077922864⟩,⟨(-8913608172637076),(-8913608172637075)⟩⟩,⟨⟨1208019168182208037,1208019168182208038⟩,⟨(-697450191936225610),(-697450191936225609)⟩⟩,⟨⟨77007071306013533795,77007071306013533803⟩,⟨(-1),1⟩⟩]
lemma ha1_0_22_eq (j : Fin 7) : ha1_0_22 j = ((ha1_0_21 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha1_0_22_contains (j : Fin 7) : (ha1_0_22 j).Contains (fullFactor false 1 22 ((j.val:ℝ)/6)) := by
  rw [ha1_0_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_0_21 j) false 1 21 j (ha1_0_21_contains j)
noncomputable def hk1_0_23 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_23 j i k)
lemma hk1_0_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_0_23 j i k).Contains (fullFactor false 1 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_0_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power1 j i k) (mpower0_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 23 (power1_contains j i k) (mpower0_23_contains j i k)
noncomputable def ha1_0_23 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨6,7⟩,⟨(-12),(-11)⟩⟩,⟨⟨96759678,96759679⟩,⟨(-55864227),(-55864226)⟩⟩,⟨⟨1253899540535,1253899540536⟩,⟨(-1),1⟩⟩,⟨⟨811679013105350,811679013105351⟩,⟨468623096711943,468623096711944⟩⟩,⟨⟨79387840551870928,79387840551870929⟩,⟨137503773339017306,137503773339017308⟩⟩,⟨⟨(-1),1⟩,⟨10518471716932064454,10518471716932064456⟩⟩]
lemma ha1_0_23_eq (j : Fin 7) : ha1_0_23 j = ((ha1_0_22 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha1_0_23_contains (j : Fin 7) : (ha1_0_23 j).Contains (fullFactor false 1 23 ((j.val:ℝ)/6)) := by
  rw [ha1_0_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_0_22 j) false 1 22 j (ha1_0_22_contains j)
noncomputable def hk1_0_24 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_24 j i k)
lemma hk1_0_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_0_24 j i k).Contains (fullFactor false 1 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_0_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power1 j i k) (mpower0_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 24 (power1_contains j i k) (mpower0_24_contains j i k)
noncomputable def ha1_0_24 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨0,1⟩⟩,⟨⟨2437536,2437537⟩,⟨4221937,4221938⟩⟩,⟨⟨(-1),1⟩,⟨82067533018,82067533019⟩⟩,⟨⟨(-40895079942577),(-40895079942576)⟩,⟨70832356240132,70832356240133⟩⟩,⟨⟨(-14999334866761558),(-14999334866761557)⟩,⟨8659870022990124,8659870022990125⟩⟩,⟨⟨(-1376864728037741371),(-1376864728037741370)⟩,⟨(-1),1⟩⟩]
lemma ha1_0_24_eq (j : Fin 7) : ha1_0_24 j = ((ha1_0_23 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha1_0_24_contains (j : Fin 7) : (ha1_0_24 j).Contains (fullFactor false 1 24 ((j.val:ℝ)/6)) := by
  rw [ha1_0_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_0_23 j) false 1 23 j (ha1_0_23_contains j)
noncomputable def hk1_0_25 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_25 j i k)
lemma hk1_0_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_0_25 j i k).Contains (fullFactor false 1 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_0_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power1 j i k) (mpower0_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 25 (power1_contains j i k) (mpower0_25_contains j i k)
noncomputable def ha1_0_25 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨0,1⟩⟩,⟨⟨(-176849),(-176848)⟩,⟨102103,102104⟩⟩,⟨⟨(-5156455177),(-5156455176)⟩,⟨(-1),1⟩⟩,⟨⟨(-5934037600013),(-5934037600012)⟩,⟨(-3426018205749),(-3426018205748)⟩⟩,⟨⟨(-906859468175609),(-906859468175608)⟩,⟨(-1570726674205046),(-1570726674205044)⟩⟩,⟨⟨(-1),1⟩,⟨(-173021924583611077),(-173021924583611076)⟩⟩]
lemma ha1_0_25_eq (j : Fin 7) : ha1_0_25 j = ((ha1_0_24 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha1_0_25_contains (j : Fin 7) : (ha1_0_25 j).Contains (fullFactor false 1 25 ((j.val:ℝ)/6)) := by
  rw [ha1_0_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_0_24 j) false 1 24 j (ha1_0_24_contains j)
noncomputable def hk1_0_26 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_26 j i k)
lemma hk1_0_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_0_26 j i k).Contains (fullFactor false 1 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_0_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power1 j i k) (mpower0_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 26 (power1_contains j i k) (mpower0_26_contains j i k)
noncomputable def ha1_0_26 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),0⟩⟩,⟨⟨(-4113),(-4112)⟩,⟨(-7123),(-7122)⟩⟩,⟨⟨(-1),1⟩,⟨(-311528495),(-311528494)⟩⟩,⟨⟨275978298108,275978298109⟩,⟨(-478008434111),(-478008434110)⟩⟩,⟨⟨158159723733336,158159723733337⟩,⟨(-91313559072399),(-91313559072398)⟩⟩,⟨⟨20906323353147684,20906323353147685⟩,⟨(-1),1⟩⟩]
lemma ha1_0_26_eq (j : Fin 7) : ha1_0_26 j = ((ha1_0_25 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha1_0_26_contains (j : Fin 7) : (ha1_0_26 j).Contains (fullFactor false 1 26 ((j.val:ℝ)/6)) := by
  rw [ha1_0_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_0_25 j) false 1 25 j (ha1_0_25_contains j)
noncomputable def hk1_0_27 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_27 j i k)
lemma hk1_0_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_0_27 j i k).Contains (fullFactor false 1 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_0_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power1 j i k) (mpower0_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 27 (power1_contains j i k) (mpower0_27_contains j i k)
noncomputable def ha1_0_27 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨(-1),0⟩⟩,⟨⟨276,277⟩,⟨(-160),(-159)⟩⟩,⟨⟨18123993,18123994⟩,⟨(-1),1⟩⟩,⟨⟨37079204566,37079204567⟩,⟨21407688737,21407688739⟩⟩,⟨⟨8854012541820,8854012541821⟩,⟨15335599573285,15335599573286⟩⟩,⟨⟨(-1),1⟩,⟨2432561179993388,2432561179993389⟩⟩]
lemma ha1_0_27_eq (j : Fin 7) : ha1_0_27 j = ((ha1_0_26 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha1_0_27_contains (j : Fin 7) : (ha1_0_27 j).Contains (fullFactor false 1 27 ((j.val:ℝ)/6)) := by
  rw [ha1_0_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_0_26 j) false 1 26 j (ha1_0_26_contains j)
noncomputable def hk1_0_28 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_28 j i k)
lemma hk1_0_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_0_28 j i k).Contains (fullFactor false 1 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_0_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power1 j i k) (mpower0_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 28 (power1_contains j i k) (mpower0_28_contains j i k)
noncomputable def ha1_0_28 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨0,1⟩⟩,⟨⟨5,6⟩,⟨10,11⟩⟩,⟨⟨(-1),1⟩,⟨1016753,1016754⟩⟩,⟨⟨(-1601291374),(-1601291373)⟩,⟨2773518015,2773518016⟩⟩,⟨⟨(-1433875207079),(-1433875207078)⟩,⟨827848236790,827848236791⟩⟩,⟨⟨(-272932726159820),(-272932726159819)⟩,⟨(-1),1⟩⟩]
lemma ha1_0_28_eq (j : Fin 7) : ha1_0_28 j = ((ha1_0_27 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha1_0_28_contains (j : Fin 7) : (ha1_0_28 j).Contains (fullFactor false 1 28 ((j.val:ℝ)/6)) := by
  rw [ha1_0_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_0_27 j) false 1 27 j (ha1_0_27_contains j)
noncomputable def hk1_0_29 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_29 j i k)
lemma hk1_0_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_0_29 j i k).Contains (fullFactor false 1 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_0_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power1 j i k) (mpower0_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 29 (power1_contains j i k) (mpower0_29_contains j i k)
noncomputable def ha1_0_29 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨0,1⟩⟩,⟨⟨(-1),0⟩,⟨0,1⟩⟩,⟨⟨(-55073),(-55072)⟩,⟨(-1),1⟩⟩,⟨⟨(-200304916),(-200304915)⟩,⟨(-115646097),(-115646096)⟩⟩,⟨⟨(-74734538477),(-74734538476)⟩,⟨(-129444017722),(-129444017721)⟩⟩,⟨⟨(-1),1⟩,⟨(-29567015428550),(-29567015428549)⟩⟩]
lemma ha1_0_29_eq (j : Fin 7) : ha1_0_29 j = ((ha1_0_28 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha1_0_29_contains (j : Fin 7) : (ha1_0_29 j).Contains (fullFactor false 1 29 ((j.val:ℝ)/6)) := by
  rw [ha1_0_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_0_28 j) false 1 28 j (ha1_0_28_contains j)
noncomputable def hk1_0_30 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_30 j i k)
lemma hk1_0_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_0_30 j i k).Contains (fullFactor false 1 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_0_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power1 j i k) (mpower0_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 30 (power1_contains j i k) (mpower0_30_contains j i k)
noncomputable def ha1_0_30 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),0⟩⟩,⟨⟨(-1),1⟩,⟨(-2884),(-2883)⟩⟩,⟨⟨8073620,8073621⟩,⟨(-13983922),(-13983921)⟩⟩,⟨⟨11296121531,11296121532⟩,⟨(-6521818807),(-6521818806)⟩⟩,⟨⟨3096250615296,3096250615297⟩,⟨(-1),1⟩⟩]
lemma ha1_0_30_eq (j : Fin 7) : ha1_0_30 j = ((ha1_0_29 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha1_0_30_contains (j : Fin 7) : (ha1_0_30 j).Contains (fullFactor false 1 30 ((j.val:ℝ)/6)) := by
  rw [ha1_0_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_0_29 j) false 1 29 j (ha1_0_29_contains j)
noncomputable def hk1_1_0 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_0 j i k)
lemma hk1_1_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_1_0 j i k).Contains (fullFactor true 1 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_1_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel1_0 j i k) (mpower1_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 0 (kernel1_0_contains j i k) (mpower1_0_contains j i k)
noncomputable def ha1_1_0 : Fin 7 → CBox := ![⟨⟨287235913262267589131245569,287235913262267589152589145⟩,⟨(-3),3⟩⟩,⟨⟨(-1227594407139841125053370123),(-1227594407139841124878361402)⟩,⟨225258927663398569617556379,225258927663398569785347626⟩⟩,⟨⟨(-4099475087999640329578559768),(-4099475087999640327343491894)⟩,⟨15600083655785914278280280272,15600083655785914280549783452⟩⟩,⟨⟨(-51036477369635067913459257139),(-51036477369635067901487188489)⟩,⟨93385323635182926762172010361,93385323635182926773837146635⟩⟩,⟨⟨(-294139142057855203281176399137),(-294139142057855203251857742481)⟩,⟨141367692329865808421293419379,141367692329865808447103276276⟩⟩,⟨⟨(-607731118347857408150380104706),(-607731118347857408104316711950)⟩,⟨(-110320451301813891842385438936),(-110320451301813891798653618696)⟩⟩,⟨⟨(-667529588463563842466349351680),(-667529588463563842419653782517)⟩,⟨(-586481159748591935787351906668),(-586481159748591935733302259315)⟩⟩]
lemma ha1_1_0_eq (j : Fin 7) : ha1_1_0 j = atomKernel1_0 j := by fin_cases j <;> decide +kernel
lemma ha1_1_0_contains (j : Fin 7) : (ha1_1_0 j).Contains (fullFactor true 1 0 ((j.val:ℝ)/6)) := by
  rw [ha1_1_0_eq]
  simpa only [fullFactor,ite_true] using atomKernel1_0_contains j
noncomputable def hk1_1_1 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_1 j i k)
lemma hk1_1_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_1_1 j i k).Contains (fullFactor true 1 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_1_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel1_0 j i k) (mpower1_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 1 (kernel1_0_contains j i k) (mpower1_1_contains j i k)
noncomputable def ha1_1_1 : Fin 7 → CBox := ![⟨⟨(-2646976155858891764422936308),(-2646976155858891764217822444)⟩,⟨(-28),28⟩⟩,⟨⟨10248502049497462764170562060,10248502049497462766168665657⟩,⟨2837138858378663619951611366,2837138858378663621908620316⟩⟩,⟨⟨100526751266157010641267391192,100526751266157010664280121597⟩,⟨(-55694797749507294492877899648),(-55694797749507294469881268035)⟩⟩,⟨⟨621471044354675043360749079671,621471044354675043456196879347⟩,⟨(-3570646982377401830921203437),(-3570646982377401735081237023)⟩⟩,⟨⟨1098842859300173353297675724200,1098842859300173353464842925351⟩,⟨1144697213258281395037408564524,1144697213258281395216979041672⟩⟩,⟨⟨(-22663614851943702239959505301),(-22663614851943702026062341800)⟩,⟨2560460779786166905954461002828,2560460779786166906181594339863⟩⟩,⟨⟨(-1992454469280585019061246880751),(-1992454469280585018850163867175)⟩,⟨2520592259912149515844324457216,2520592259912149516031115751282⟩⟩]
lemma ha1_1_1_eq (j : Fin 7) : ha1_1_1 j = ((ha1_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha1_1_1_contains (j : Fin 7) : (ha1_1_1 j).Contains (fullFactor true 1 1 ((j.val:ℝ)/6)) := by
  rw [ha1_1_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_1_0 j) true 1 0 j (ha1_1_0_contains j)
noncomputable def hk1_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_2 j i k)
lemma hk1_1_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_1_2 j i k).Contains (fullFactor true 1 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_1_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel1_0 j i k) (mpower1_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 2 (kernel1_0_contains j i k) (mpower1_2_contains j i k)
noncomputable def ha1_1_2 : Fin 7 → CBox := ![⟨⟨12196390573361347335076360578,12196390573361347336060279735⟩,⟨(-130),130⟩⟩,⟨⟨(-34009640985647258686134702127),(-34009640985647258674695966201)⟩,⟨(-29926332711991384080832120016),(-29926332711991384069521085676)⟩⟩,⟨⟨(-390892336210065946434368050320),(-390892336210065946317253619215)⟩,⟨(-121756091788458023867561267047),(-121756091788458023750428842993)⟩⟩,⟨⟨(-888497586055070015111484179785),(-888497586055070014728809235609)⟩,⟨(-1582271839194707634054197981546),(-1582271839194707633669729255890)⟩⟩,⟨⟨1811675068507691695296714654735,1811675068507691695849247477462⟩,⟨(-3405633225673014004949345343088),(-3405633225673014004416292903187)⟩⟩,⟨⟨5238101189218518216233101047695,5238101189218518216789052327499⟩,⟨(-855378924179136656114289373347),(-855378924179136655594369708218)⟩⟩,⟨⟨4738027070831674426430075107891,4738027070831674426802228712530⟩,⟨3360752453292758894601793870823,3360752453292758895012648382098⟩⟩]
lemma ha1_1_2_eq (j : Fin 7) : ha1_1_2 j = ((ha1_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha1_1_2_contains (j : Fin 7) : (ha1_1_2 j).Contains (fullFactor true 1 2 ((j.val:ℝ)/6)) := by
  rw [ha1_1_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_1_1 j) true 1 1 j (ha1_1_1_contains j)
noncomputable def hk1_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_3 j i k)
lemma hk1_1_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_1_3 j i k).Contains (fullFactor true 1 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_1_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel1_0 j i k) (mpower1_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 3 (kernel1_0_contains j i k) (mpower1_3_contains j i k)
noncomputable def ha1_1_3 : Fin 7 → CBox := ![⟨⟨(-37464622336126396887965735586),(-37464622336126396884824099308)⟩,⟨(-400),400⟩⟩,⟨⟨49821256299583075567372271902,49821256299583075611015240203⟩,⟨118621753759090402050217381969,118621753759090402093675172892⟩⟩,⟨⟨432504574126370630636910636051,432504574126370631032907332316⟩,⟨870875508940356452212502387702,870875508940356452608562435214⟩⟩,⟨⟨(-1856083889996852295561614781199),(-1856083889996852294534724379791)⟩,⟨3005501558658382000443723818508,3005501558658382001467574875380⟩⟩,⟨⟨(-6159774073909780147087354235313),(-6159774073909780145967753500819)⟩,⟨(-1069723649070674514368451779461),(-1069723649070674513233941919231)⟩⟩,⟨⟨(-2394565727468471308003710582934),(-2394565727468471307157560098460)⟩,⟨(-6932248784196985862276325625828),(-6932248784196985861373845292200)⟩⟩,⟨⟨3748696461229969194790660635331,3748696461229969195322310012555⟩,⟨(-5913399628183859166641986241106),(-5913399628183859166149495343359)⟩⟩]
lemma ha1_1_3_eq (j : Fin 7) : ha1_1_3 j = ((ha1_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha1_1_3_contains (j : Fin 7) : (ha1_1_3 j).Contains (fullFactor true 1 3 ((j.val:ℝ)/6)) := by
  rw [ha1_1_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_1_2 j) true 1 2 j (ha1_1_2_contains j)
noncomputable def hk1_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_4 j i k)
lemma hk1_1_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_1_4 j i k).Contains (fullFactor true 1 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_1_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel1_0 j i k) (mpower1_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 4 (kernel1_0_contains j i k) (mpower1_4_contains j i k)
noncomputable def ha1_1_4 : Fin 7 → CBox := ![⟨⟨86312293687173228303222231626,86312293687173228310734782588⟩,⟨(-922),922⟩⟩,⟨⟨14769503800638230741352708750,14769503800638230866044362099⟩,⟨(-273652529403738708553243509167),(-273652529403738708428518470973)⟩⟩,⟨⟨588921331491213552857984591529,588921331491213553860617580309⟩,⟨(-1628814797274688215164792342915),(-1628814797274688214162241993586)⟩⟩,⟨⟨5151409994869979770237062172670,5151409994869979772287511035262⟩,⟨243966413586880668556205949827,243966413586880670606302038345⟩⟩,⟨⟨1098035427798879984112440752731,1098035427798879985858305897955⟩,⟨7519775578073350750253021663420,7519775578073350751999890387386⟩⟩,⟨⟨(-6658445948115395215178764130656),(-6658445948115395214084173638250)⟩,⟨3666231904245789672956063938847,3666231904245789673990833084238⟩⟩,⟨⟨(-5514336335438565913976223418805),(-5514336335438565913489113980508)⟩,⟨(-3106565412642726723968033368582),(-3106565412642726723453308537794)⟩⟩]
lemma ha1_1_4_eq (j : Fin 7) : ha1_1_4 j = ((ha1_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha1_1_4_contains (j : Fin 7) : (ha1_1_4 j).Contains (fullFactor true 1 4 ((j.val:ℝ)/6)) := by
  rw [ha1_1_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_1_3 j) true 1 3 j (ha1_1_3_contains j)
noncomputable def hk1_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_5 j i k)
lemma hk1_1_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_1_5 j i k).Contains (fullFactor true 1 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_1_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel1_0 j i k) (mpower1_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 5 (kernel1_0_contains j i k) (mpower1_5_contains j i k)
noncomputable def ha1_1_5 : Fin 7 → CBox := ![⟨⟨(-159079399753770086279525542603),(-159079399753770086265173037197)⟩,⟨(-1700),1700⟩⟩,⟨⟨(-226125701939186556349820942897),(-226125701939186556065176118251)⟩,⟨408594433963913454764777754126,408594433963913455050099672730⟩⟩,⟨⟨(-2257644881598426108315853630384),(-2257644881598426106288708238550)⟩,⟨997301796121189057750877925182,997301796121189059777877044926⟩⟩,⟨⟨(-2666435421810330547830228225564),(-2666435421810330544565111710923)⟩,⟨(-5401054071167189622238074926813),(-5401054071167189618965679879530)⟩⟩,⟨⟨6615473371111462706601380531648,6615473371111462708767781330380⟩,⟨(-3293610457390052365309166813778),(-3293610457390052363156081544278)⟩⟩,⟨⟨3933443938926397284084516859589,3933443938926397285096690178097⟩,⟨4923915451432749411741058434824,4923915451432749412800123299162⟩⟩,⟨⟨(-2036488633372645452773995261431),(-2036488633372645452376164358762)⟩,⟨4099148459978458920646320388630,4099148459978458921030491678082⟩⟩]
lemma ha1_1_5_eq (j : Fin 7) : ha1_1_5 j = ((ha1_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha1_1_5_contains (j : Fin 7) : (ha1_1_5 j).Contains (fullFactor true 1 5 ((j.val:ℝ)/6)) := by
  rw [ha1_1_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_1_4 j) true 1 4 j (ha1_1_4_contains j)
noncomputable def hk1_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_6 j i k)
lemma hk1_1_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_1_6 j i k).Contains (fullFactor true 1 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_1_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel1_0 j i k) (mpower1_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 6 (kernel1_0_contains j i k) (mpower1_6_contains j i k)
noncomputable def ha1_1_6 : Fin 7 → CBox := ![⟨⟨244328418206359943580614262277,244328418206359943603435849610⟩,⟨(-2612),2612⟩⟩,⟨⟨542104820585143372412522600647,542104820585143372954738151199⟩,⟨(-381945800975115803165120644407),(-381945800975115802622077311833)⟩⟩,⟨⟨2708645394883852982987387389408,2708645394883852986399358497113⟩,⟨1119492262887064207479030672730,1119492262887064210891158821464⟩⟩,⟨⟨(-3340686914106598561045545560344),(-3340686914106598556700813357652)⟩,⟨4817636060972483549340646137688,4817636060972483553679309311237⟩⟩,⟨⟨(-4206874169296466836866172315851),(-4206874169296466834647764732475)⟩,⟨(-4262070272063111759726689541891),(-4262070272063111757495920683551)⟩⟩,⟨⟨2890884651410802741649829576483,2890884651410802742501883018401⟩,⟨(-3256203565940719660623354668845),(-3256203565940719659799501123137)⟩⟩,⟨⟨2530755021032148929044250002463,2530755021032148929295964741302⟩,⟨1097350437922380124861218908538,1097350437922380125116981052064⟩⟩]
lemma ha1_1_6_eq (j : Fin 7) : ha1_1_6 j = ((ha1_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha1_1_6_contains (j : Fin 7) : (ha1_1_6 j).Contains (fullFactor true 1 6 ((j.val:ℝ)/6)) := by
  rw [ha1_1_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_1_5 j) true 1 5 j (ha1_1_5_contains j)
noncomputable def hk1_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_7 j i k)
lemma hk1_1_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_1_7 j i k).Contains (fullFactor true 1 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_1_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel1_0 j i k) (mpower1_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 7 (kernel1_0_contains j i k) (mpower1_7_contains j i k)
noncomputable def ha1_1_7 : Fin 7 → CBox := ![⟨⟨(-321652723836322512112172550720),(-321652723836322512081104605264)⟩,⟨(-3439),3439⟩⟩,⟨⟨(-796560213426525364539448415581),(-796560213426525363654668796240)⟩,⟨130373397563733933558416608595,130373397563733934443375585412⟩⟩,⟨⟨(-1081511837017671519563840575844),(-1081511837017671514644872745393)⟩,⟨(-2780257995586590279692675111801),(-2780257995586590274773548611656)⟩⟩,⟨⟨4866277113520346705113761855105,4866277113520346710051915619809⟩,⟨490188091944792565916858522290,490188091944792570855457450514⟩⟩,⟨⟨(-1902257811086116291148644196151),(-1902257811086116289184247658248)⟩,⟨3699181273936940160055725789841,3699181273936940162014561943983⟩⟩,⟨⟨(-2191231449984051785903869019778),(-2191231449984051785330352519489)⟩,⟨(-1359537005858171990513425535763),(-1359537005858171989926850175086)⟩⟩,⟨⟨498193235192244269606603448315,498193235192244269747311296797⟩,⟨(-1334953635791130924319782322136),(-1334953635791130924178822491052)⟩⟩]
lemma ha1_1_7_eq (j : Fin 7) : ha1_1_7 j = ((ha1_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha1_1_7_contains (j : Fin 7) : (ha1_1_7 j).Contains (fullFactor true 1 7 ((j.val:ℝ)/6)) := by
  rw [ha1_1_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_1_6 j) true 1 6 j (ha1_1_6_contains j)
noncomputable def hk1_1_8 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_8 j i k)
lemma hk1_1_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_1_8 j i k).Contains (fullFactor true 1 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_1_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel1_0 j i k) (mpower1_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 8 (kernel1_0_contains j i k) (mpower1_8_contains j i k)
noncomputable def ha1_1_8 : Fin 7 → CBox := ![⟨⟨370517339210823706052582441046,370517339210823706089549538410⟩,⟨(-3962),3962⟩⟩,⟨⟨823915463846596816021602633372,823915463846596817283360028888⟩,⟨245253481054223121162495933631,245253481054223122423295266894⟩⟩,⟨⟨(-1124234818917947214011401503976),(-1124234818917947207809459412415)⟩,⟨2407334520456433060390453793746,2407334520456433066592238225216⟩⟩,⟨⟨(-1408435644264619567851741256486),(-1408435644264619562944932514072)⟩,⟨(-3280691978677604981015022891045),(-3280691978677604976104373982773)⟩⟩,⟨⟨2496597022144665665829461652895,2496597022144665667340728923865⟩,⟨397854038637289394317985958996,397854038637289395829191369664⟩⟩,⟨⟨(-501351974583334850041146718955),(-501351974583334849688289680977)⟩,⟨1238669740408552015657883416307,1238669740408552016006340308030⟩⟩,⟨⟨(-614262469236681305725290677289),(-614262469236681305656406568484)⟩,⟨(-193540002862600254328008895327),(-193540002862600254260372336910)⟩⟩]
lemma ha1_1_8_eq (j : Fin 7) : ha1_1_8 j = ((ha1_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha1_1_8_contains (j : Fin 7) : (ha1_1_8 j).Contains (fullFactor true 1 8 ((j.val:ℝ)/6)) := by
  rw [ha1_1_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_1_7 j) true 1 7 j (ha1_1_7_contains j)
noncomputable def hk1_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_9 j i k)
lemma hk1_1_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_1_9 j i k).Contains (fullFactor true 1 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_1_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel1_0 j i k) (mpower1_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 9 (kernel1_0_contains j i k) (mpower1_9_contains j i k)
noncomputable def ha1_1_9 : Fin 7 → CBox := ![⟨⟨(-379382520290843648588076847231),(-379382520290843648549017644746)⟩,⟨(-4057),4057⟩⟩,⟨⟨(-600500752411898582609787047422),(-600500752411898581011630749608)⟩,⟨(-549263642632947803742446898086),(-549263642632947802145518981831)⟩⟩,⟨⟨1992595487597180966959768292692,1992595487597180973907852485905⟩,⟨(-673626695925647692002221345814),(-673626695925647685054236017904)⟩⟩,⟨⟨(-1419204481376796484371063016621),(-1419204481376796480033594935534)⟩,⟨1831000228500242791227515810120,1831000228500242795562503148139⟩⟩,⟨⟨(-216128117373209165886749693970),(-216128117373209164854554750492)⟩,⟨(-1348571328486694070220927731456),(-1348571328486694069186406946596)⟩⟩,⟨⟨601493033833309103272705758317,601493033833309103460405764397⟩,⟨130641099806405113287852746192,130641099806405113476324065604⟩⟩,⟨⟨(-64837318417744383891357131091),(-64837318417744383862494495881)⟩,⟨250495491825117084238672215067,250495491825117084268518750758⟩⟩]
lemma ha1_1_9_eq (j : Fin 7) : ha1_1_9 j = ((ha1_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha1_1_9_contains (j : Fin 7) : (ha1_1_9 j).Contains (fullFactor true 1 9 ((j.val:ℝ)/6)) := by
  rw [ha1_1_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_1_8 j) true 1 8 j (ha1_1_8_contains j)
noncomputable def hk1_1_10 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_10 j i k)
lemma hk1_1_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_1_10 j i k).Contains (fullFactor true 1 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_1_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel1_0 j i k) (mpower1_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 10 (kernel1_0_contains j i k) (mpower1_10_contains j i k)
noncomputable def ha1_1_10 : Fin 7 → CBox := ![⟨⟨349613832669521221915156642034,349613832669521221952263874479⟩,⟨(-3739),3739⟩⟩,⟨⟨256149072492868162565622962831,256149072492868164386637284518⟩,⟨644335962619595055802001189934,644335962619595057622466106271⟩⟩,⟨⟨(-1327991376622188701502492091431),(-1327991376622188694499026322594)⟩,⟨(-694553792805492225667046301609),(-694553792805492218663483153684)⟩⟩,⟨⟨1336959418051612477372430781885,1336959418051612480818617745038⟩,⟨206798710333507061792735994575,206798710333507065239189508122⟩⟩,⟨⟨(-590287383017911433390815763387),(-590287383017911432754366508071)⟩,⟨304207583690322321215901766252,304207583690322321850509812886⟩⟩,⟨⟨11007299403209770664214298582,11007299403209770754734949482⟩,⟨(-254928829292876404316513992295),(-254928829292876404225747389540)⟩⟩,⟨⟨91672046427881796967513744065,91672046427881796979125170389⟩,⟨18709286641625305320617205800,18709286641625305331689514739⟩⟩]
lemma ha1_1_10_eq (j : Fin 7) : ha1_1_10 j = ((ha1_1_9 j).mul (piI.mul (atomPoints j).z)).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha1_1_10_contains (j : Fin 7) : (ha1_1_10 j).Contains (fullFactor true 1 10 ((j.val:ℝ)/6)) := by
  rw [ha1_1_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_1_9 j) true 1 9 j (ha1_1_9_contains j)
noncomputable def hk1_1_11 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_11 j i k)
lemma hk1_1_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_1_11 j i k).Contains (fullFactor true 1 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_1_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel1_0 j i k) (mpower1_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 11 (kernel1_0_contains j i k) (mpower1_11_contains j i k)
noncomputable def ha1_1_11 : Fin 7 → CBox := ![⟨⟨(-292891799548783765999168029745),(-292891799548783765967148843831)⟩,⟨(-3133),3133⟩⟩,⟨⟨39259455957372622295812825565,39259455957372624181487884667⟩,⟨(-535632194452509245351707172780),(-535632194452509243465785795822)⟩⟩,⟨⟨269215277183579806287411651987,269215277183579812704092824609⟩,⟨932638572538822193791126540209,932638572538822200207847243653⟩⟩,⟨⟨(-247926600980377252169877607399),(-247926600980377249681375397574)⟩,⟨(-674072892116899856404029363771),(-674072892116899853914837273742)⟩⟩,⟨⟨209084686103535579934805450663,209084686103535580289682788590⟩,⟨206012582391311559129521325413,206012582391311559485175337731⟩⟩,⟨⟨(-95382930256173682262883287464),(-95382930256173682223073983889)⟩,⟨12234507446344396621811530569,12234507446344396661306593099⟩⟩,⟨⟨4576923054563444836563540049,4576923054563444840421044969⟩,⟨(-30413022924312660188944679285),(-30413022924312660184847121863)⟩⟩]
lemma ha1_1_11_eq (j : Fin 7) : ha1_1_11 j = ((ha1_1_10 j).mul (piI.mul (atomPoints j).z)).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha1_1_11_contains (j : Fin 7) : (ha1_1_11 j).Contains (fullFactor true 1 11 ((j.val:ℝ)/6)) := by
  rw [ha1_1_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_1_10 j) true 1 10 j (ha1_1_10_contains j)
noncomputable def hk1_1_12 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_12 j i k)
lemma hk1_1_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_1_12 j i k).Contains (fullFactor true 1 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_1_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel1_0 j i k) (mpower1_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 12 (kernel1_0_contains j i k) (mpower1_12_contains j i k)
noncomputable def ha1_1_12 : Fin 7 → CBox := ![⟨⟨224924755185570830432122811187,224924755185570830457427738512⟩,⟨(-2406),2406⟩⟩,⟨⟨(-191031510009805371564735295276),(-191031510009805369775159571301)⟩,⟨330026516980086659906719279505,330026516980086661696895919293⟩⟩,⟨⟨289811393352166711620245415276,289811393352166717008529951782⟩,⟨(-498198978621180652190091696624),(-498198978621180646801847784518)⟩⟩,⟨⟨(-228477031809919704135298820085),(-228477031809919702487705810572)⟩,⟨264508046514232780040132344395,264508046514232781687336839230⟩⟩,⟨⟨52911506329382344544784603420,52911506329382344726861393655⟩,⟨(-106512623981388505866688356800),(-106512623981388505684809977326)⟩⟩,⟨⟨9763355252478050948759550238,9763355252478050964572870924⟩,⟨31754223491159149826804115845,31754223491159149842780544185⟩⟩,⟨⟨(-9223470157124546158166184612),(-9223470157124546156843431795)⟩,⟨(-901386083894002516930556987),(-901386083894002515699744567)⟩⟩]
lemma ha1_1_12_eq (j : Fin 7) : ha1_1_12 j = ((ha1_1_11 j).mul (piI.mul (atomPoints j).z)).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha1_1_12_contains (j : Fin 7) : (ha1_1_12 j).Contains (fullFactor true 1 12 ((j.val:ℝ)/6)) := by
  rw [ha1_1_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_1_11 j) true 1 11 j (ha1_1_11_contains j)
noncomputable def hk1_1_13 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_13 j i k)
lemma hk1_1_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_1_13 j i k).Contains (fullFactor true 1 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_1_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel1_0 j i k) (mpower1_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 13 (kernel1_0_contains j i k) (mpower1_13_contains j i k)
noncomputable def ha1_1_13 : Fin 7 → CBox := ![⟨⟨(-159442903456742416324932655252),(-159442903456742416306487173513)⟩,⟨(-1706),1706⟩⟩,⟨⟨207037244954061604250711567196,207037244954061605818672634363⟩,⟨(-139986957182931470441399154411),(-139986957182931468873121200097)⟩⟩,⟨⟨(-307130762218868813231359735916),(-307130762218868809055017717375)⟩,⟨73871730633658541951744449537,73871730633658546128075613724⟩⟩,⟨⟨153674500732897821277018915973,153674500732897822283435051017⟩,⟨32197719055108401617717247516,32197719055108402624181371196⟩⟩,⟨⟨(-44020535755093054101581714217),(-44020535755093054015581024199)⟩,⟨(-6388153474434469595086100728),(-6388153474434469509078773220)⟩⟩,⟨⟨9449924857747458835832653629,9449924857747458841743473461⟩,⟨(-4788527391316955811108433174),(-4788527391316955805258238870)⟩⟩,⟨⟨(-117154360983701017496599997),(-117154360983701017134388683)⟩,⟨2575034399379846388717241539,2575034399379846389110638794⟩⟩]
lemma ha1_1_13_eq (j : Fin 7) : ha1_1_13 j = ((ha1_1_12 j).mul (piI.mul (atomPoints j).z)).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha1_1_13_contains (j : Fin 7) : (ha1_1_13 j).Contains (fullFactor true 1 13 ((j.val:ℝ)/6)) := by
  rw [ha1_1_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_1_12 j) true 1 12 j (ha1_1_12_contains j)
noncomputable def hk1_1_14 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_14 j i k)
lemma hk1_1_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_1_14 j i k).Contains (fullFactor true 1 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_1_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel1_0 j i k) (mpower1_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 14 (kernel1_0_contains j i k) (mpower1_14_contains j i k)
noncomputable def ha1_1_14 : Fin 7 → CBox := ![⟨⟨104951451349219330902335088125,104951451349219330914810684479⟩,⟨(-1123),1123⟩⟩,⟨⟨(-150546223707535979131377220794),(-150546223707535977855827355601)⟩,⟨21674031155625376977087008885,21674031155625378252666052366⟩⟩,⟨⟨135187344696563867682505329922,135187344696563870688017685697⟩,⟨87004233607412107611386008003,87004233607412110616910557499⟩⟩,⟨⟨(-19315852321128066572196336370),(-19315852321128066001385317310)⟩,⟨(-62580831094351540442229059333),(-62580831094351539871362924460)⟩⟩,⟨⟨2656685931080540525193063473,2656685931080540562905985085⟩,⟨15218194944493848875734050718,15218194944493848913472064439⟩⟩,⟨⟨(-1872727261342353100947768032),(-1872727261342353098937321541)⟩,⟨(-2516654044542493522172506536),(-2516654044542493520143835726)⟩⟩,⟨⟨665751052412352704693120601,665751052412352704801566994⟩,⟨(-4319671271995090020646311),(-4319671271995089921738473)⟩⟩]
lemma ha1_1_14_eq (j : Fin 7) : ha1_1_14 j = ((ha1_1_13 j).mul (piI.mul (atomPoints j).z)).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha1_1_14_contains (j : Fin 7) : (ha1_1_14 j).Contains (fullFactor true 1 14 ((j.val:ℝ)/6)) := by
  rw [ha1_1_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_1_13 j) true 1 13 j (ha1_1_13_contains j)
noncomputable def hk1_1_15 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_15 j i k)
lemma hk1_1_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_1_15 j i k).Contains (fullFactor true 1 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_1_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel1_0 j i k) (mpower1_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 15 (kernel1_0_contains j i k) (mpower1_15_contains j i k)
noncomputable def ha1_1_15 : Fin 7 → CBox := ![⟨⟨(-64477543003826390760359201576),(-64477543003826390752489506997)⟩,⟨(-690),690⟩⟩,⟨⟨82313530757326829579989120715,82313530757326830548323395146⟩,⟨26236790196739006436750319631,26236790196739007404984296383⟩⟩,⟨⟨(-14501065660182567137796166574),(-14501065660182565119114241788)⟩,⟨(-74973642426171908905723779610),(-74973642426171906887039722034)⟩⟩,⟨⟨(-17667788856382034339759006867),(-17667788856382034037577398879)⟩,⟨18384917857845495510330503996,18384917857845495812482823384⟩⟩,⟨⟨4418804670315139951886236070,4418804670315139967335192506⟩,⟨(-2355656684295322145931493840),(-2355656684295322130496006674)⟩⟩,⟨⟨(-597487037015741051501885196),(-597487037015741050852510985)⟩,⟨628209158796972077017257631,628209158796972077662062095⟩⟩,⟨⟨(-9373916899133741481151209),(-9373916899133741455953228)⟩,⟨(-160215551088624634111824925),(-160215551088624634083969598)⟩⟩]
lemma ha1_1_15_eq (j : Fin 7) : ha1_1_15 j = ((ha1_1_14 j).mul (piI.mul (atomPoints j).z)).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha1_1_15_contains (j : Fin 7) : (ha1_1_15 j).Contains (fullFactor true 1 15 ((j.val:ℝ)/6)) := by
  rw [ha1_1_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_1_14 j) true 1 14 j (ha1_1_14_contains j)
noncomputable def hk1_1_16 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_16 j i k)
lemma hk1_1_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_1_16 j i k).Contains (fullFactor true 1 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_1_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel1_0 j i k) (mpower1_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 16 (kernel1_0_contains j i k) (mpower1_16_contains j i k)
noncomputable def ha1_1_16 : Fin 7 → CBox := ![⟨⟨37136398827429175811478124299,37136398827429175816128951819⟩,⟨(-398),398⟩⟩,⟨⟨(-33343105464407602900457886606),(-33343105464407602211360916115)⟩,⟨(-31697970950057856971018560835),(-31697970950057856281990389552)⟩⟩,⟨⟨(-19670562124073366963156965662),(-19670562124073365692090867378)⟩,⟨27738675538810406724655092391,27738675538810407995718434245⟩⟩,⟨⟨8994683992253732315266512632,8994683992253732465210709533⟩,⟨2388933577376688140618494985,2388933577376688290566537348⟩⟩,⟨⟨(-1098698288681292028236420925),(-1098698288681292022312769919)⟩,⟨(-1052823142025405981131791624),(-1052823142025405975204252750)⟩⟩,⟨⟨186702094843846215422183614,186702094843846215616001322⟩,⟨124903784406946674497212374,124903784406946674691975060⟩⟩,⟨⟨(-36048897184672988701502315),(-36048897184672988694804503)⟩,⟨3995854337414128684020325,3995854337414128690046861⟩⟩]
lemma ha1_1_16_eq (j : Fin 7) : ha1_1_16 j = ((ha1_1_15 j).mul (piI.mul (atomPoints j).z)).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha1_1_16_contains (j : Fin 7) : (ha1_1_16 j).Contains (fullFactor true 1 16 ((j.val:ℝ)/6)) := by
  rw [ha1_1_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_1_15 j) true 1 15 j (ha1_1_15_contains j)
noncomputable def hk1_1_17 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_17 j i k)
lemma hk1_1_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_1_17 j i k).Contains (fullFactor true 1 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_1_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel1_0 j i k) (mpower1_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 17 (kernel1_0_contains j i k) (mpower1_17_contains j i k)
noncomputable def ha1_1_17 : Fin 7 → CBox := ![⟨⟨(-20130852001683972016701624161),(-20130852001683972014116430982)⟩,⟨(-216),216⟩⟩,⟨⟨8103955857998026332942995720,8103955857998026794453316539⟩,⟨21586409432734185162963960602,21586409432734185624457086082⟩⟩,⟨⟨14100429068633123910108060666,14100429068633124663348277313⟩,⟨(-2074484723546142233559511388),(-2074484723546141480319600330)⟩⟩,⟨⟨(-779500008540357537190986054),(-779500008540357467165293501)⟩,⟨(-3100471953444549428658545041),(-3100471953444549358630549898)⟩⟩,⟨⟨(-188183058617990689768062830),(-188183058617990687627922203)⟩,⟨392433915860396545317532542,392433915860396547456989814⟩⟩,⟨⟨22280806459140456098155534,22280806459140456153109230⟩,⟨(-50041393702561073095714125),(-50041393702561073040909245)⟩⟩,⟨⟨1246950375972618290063044,1246950375972618291421112⟩,⟨7613128907407587163650380,7613128907407587165164166⟩⟩]
lemma ha1_1_17_eq (j : Fin 7) : ha1_1_17 j = ((ha1_1_16 j).mul (piI.mul (atomPoints j).z)).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha1_1_17_contains (j : Fin 7) : (ha1_1_17 j).Contains (fullFactor true 1 17 ((j.val:ℝ)/6)) := by
  rw [ha1_1_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_1_16 j) true 1 16 j (ha1_1_16_contains j)
noncomputable def hk1_1_18 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_18 j i k)
lemma hk1_1_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_1_18 j i k).Contains (fullFactor true 1 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_1_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel1_0 j i k) (mpower1_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 18 (kernel1_0_contains j i k) (mpower1_18_contains j i k)
noncomputable def ha1_1_18 : Fin 7 → CBox := ![⟨⟨10306256360724907489286185273,10306256360724907490642515002⟩,⟨(-111),111⟩⟩,⟨⟨1007138104310771300777464328,1007138104310771592681057235⟩,⟨(-10867541913154431564115649374),(-10867541913154431272206414546)⟩⟩,⟨⟨(-4450445077366248593194671481),(-4450445077366248171629826857)⟩,⟨(-3466974006336426536380375190),(-3466974006336426114815044805)⟩⟩,⟨⟨(-757339214131383486066507591),(-757339214131383455180289185)⟩,⟨708677879975736577257968164,708677879975736608142960030⟩⟩,⟨⟨116566936914816941000104172,116566936914816941729772184⟩,⟨15262579424833824412798828,15262579424833825142472566⟩⟩,⟨⟨(-12229243981741613510096767),(-12229243981741613495469044)⟩,⟨(-3098849150929427543655597),(-3098849150929427529016518)⟩⟩,⟨⟨1514281259197659095382418,1514281259197659095705174⟩,⟨(-329572945884832952584932),(-329572945884832952295645)⟩⟩]
lemma ha1_1_18_eq (j : Fin 7) : ha1_1_18 j = ((ha1_1_17 j).mul (piI.mul (atomPoints j).z)).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha1_1_18_contains (j : Fin 7) : (ha1_1_18 j).Contains (fullFactor true 1 18 ((j.val:ℝ)/6)) := by
  rw [ha1_1_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_1_17 j) true 1 17 j (ha1_1_17_contains j)
noncomputable def hk1_1_19 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_19 j i k)
lemma hk1_1_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_1_19 j i k).Contains (fullFactor true 1 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_1_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel1_0 j i k) (mpower1_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 19 (kernel1_0_contains j i k) (mpower1_19_contains j i k)
noncomputable def ha1_1_19 : Fin 7 → CBox := ![⟨⟨(-4998717922210960306866145712),(-4998717922210960306192390218)⟩,⟨(-54),54⟩⟩,⟨⟨(-2532892822906867717759010249),(-2532892822906867542852106999)⟩,⟨4187824862916710257790470582,4187824862916710432705068696⟩⟩,⟨⟨213501305186712006350190677,213501305186712229868382135⟩,⟨2104751125602955054006051150,2104751125602955277524274151⟩⟩,⟨⟨303336110227108911472939372,303336110227108924377948181⟩,⟨98060618800453425863498120,98060618800453438768672577⟩⟩,⟨⟨(-5585658337274997360227159),(-5585658337274997124565125)⟩,⟨(-29561380920193906210722332),(-29561380920193905975008542)⟩⟩,⟨⟨(-212978843404191120029389),(-212978843404191116335963)⟩,⟨2744348266221071331157658,2744348266221071334854234⟩⟩,⟨⟨(-77602008429562564101521),(-77602008429562564043103)⟩,⟨(-284538107331648698016458),(-284538107331648697951330)⟩⟩]
lemma ha1_1_19_eq (j : Fin 7) : ha1_1_19 j = ((ha1_1_18 j).mul (piI.mul (atomPoints j).z)).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha1_1_19_contains (j : Fin 7) : (ha1_1_19 j).Contains (fullFactor true 1 19 ((j.val:ℝ)/6)) := by
  rw [ha1_1_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_1_18 j) true 1 18 j (ha1_1_18_contains j)
noncomputable def hk1_1_20 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_20 j i k)
lemma hk1_1_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_1_20 j i k).Contains (fullFactor true 1 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_1_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel1_0 j i k) (mpower1_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 20 (kernel1_0_contains j i k) (mpower1_20_contains j i k)
noncomputable def ha1_1_20 : Fin 7 → CBox := ![⟨⟨2303243873595219638672964929,2303243873595219638990740628⟩,⟨(-25),25⟩⟩,⟨⟨1749374466122183260863873710,1749374466122183360428675758⟩,⟨(-1134394167575409556158974334),(-1134394167575409456591613216)⟩⟩,⟨⟨489430233092341487472737366,489430233092341600057365840⟩,⟨(-573120073449755735186389687),(-573120073449755622601829779)⟩⟩,⟨⟨(-17875811939329458591039091),(-17875811939329453468609337)⟩,⟨(-91351816856341021725632693),(-91351816856341016603147376)⟩⟩,⟨⟨(-6405449852938034163290558),(-6405449852938034090962116)⟩,⟨3530085530596229852995443,3530085530596229925304004⟩⟩,⟨⟨568073858619441900146990,568073858619441901033944⟩,⟨(-53138834101762526538662),(-53138834101762525653602)⟩⟩,⟨⟨(-50645146257527185861232),(-50645146257527185848758)⟩,⟨16682577392207956558510,16682577392207956569724⟩⟩]
lemma ha1_1_20_eq (j : Fin 7) : ha1_1_20 j = ((ha1_1_19 j).mul (piI.mul (atomPoints j).z)).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha1_1_20_contains (j : Fin 7) : (ha1_1_20 j).Contains (fullFactor true 1 20 ((j.val:ℝ)/6)) := by
  rw [ha1_1_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_1_19 j) true 1 19 j (ha1_1_19_contains j)
noncomputable def hk1_1_21 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_21 j i k)
lemma hk1_1_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_1_21 j i k).Contains (fullFactor true 1 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_1_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel1_0 j i k) (mpower1_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 21 (kernel1_0_contains j i k) (mpower1_21_contains j i k)
noncomputable def ha1_1_21 : Fin 7 → CBox := ![⟨⟨(-1010722468061420243132112827),(-1010722468061420242989447471)⟩,⟨(-11),11⟩⟩,⟨⟨(-839458398852362150323854489),(-839458398852362096346693894)⟩,⟨104409279620573312388568883,104409279620573366365842576⟩⟩,⟨⟨(-255304157565512851574705762),(-255304157565512797567079192)⟩,⟨14340121459990032042875112,14340121459990086050499548⟩⟩,⟨⟨(-19812495311192135078510529),(-19812495311192133142074727)⟩,⟨16659008010285762172593022,16659008010285764108997421⟩⟩,⟨⟨1238833181188313052412662,1238833181188313073543660⟩,⟨1154465296116492549077555,1154465296116492570212846⟩⟩,⟨⟨(-29389768975147703289887),(-29389768975147703087868)⟩,⟨(-108729711221957448416771),(-108729711221957448214183)⟩⟩,⟨⟨3321477634826510347330,3321477634826510349381⟩,⟨8559447540698206135836,8559447540698206138111⟩⟩]
lemma ha1_1_21_eq (j : Fin 7) : ha1_1_21 j = ((ha1_1_20 j).mul (piI.mul (atomPoints j).z)).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha1_1_21_contains (j : Fin 7) : (ha1_1_21 j).Contains (fullFactor true 1 21 ((j.val:ℝ)/6)) := by
  rw [ha1_1_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_1_20 j) true 1 20 j (ha1_1_20_contains j)
noncomputable def hk1_1_22 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_22 j i k)
lemma hk1_1_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_1_22 j i k).Contains (fullFactor true 1 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_1_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel1_0 j i k) (mpower1_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 22 (kernel1_0_contains j i k) (mpower1_22_contains j i k)
noncomputable def ha1_1_22 : Fin 7 → CBox := ![⟨⟨423370437397320302099113585,423370437397320302160220741⟩,⟨(-5),5⟩⟩,⟨⟨310166366674967495148700530,310166366674967523080656753⟩,⟨105480192511169377960087113,105480192511169405891643719⟩⟩,⟨⟨60493425690918870049816320,60493425690918894779847974⟩,⟨56556861527465619298696835,56556861527465644028736411⟩⟩,⟨⟨6416727471211444887855522,6416727471211445586593515⟩,⟨2457409238768263077566364,2457409238768263776308648⟩⟩,⟨⟨157106515280838876924007,157106515280838882818952⟩,⟨(-339673743341080839769214),(-339673743341080833874837)⟩⟩,⟨⟨(-19249713463340800775227),(-19249713463340800731072)⟩,⟨8938399547945541847444,8938399547945541891473⟩⟩,⟨⟨1376577406809809367429,1376577406809809367825⟩,⟨(-618235381781154214591),(-618235381781154214232)⟩⟩]
lemma ha1_1_22_eq (j : Fin 7) : ha1_1_22 j = ((ha1_1_21 j).mul (piI.mul (atomPoints j).z)).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha1_1_22_contains (j : Fin 7) : (ha1_1_22 j).Contains (fullFactor true 1 22 ((j.val:ℝ)/6)) := by
  rw [ha1_1_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_1_21 j) true 1 21 j (ha1_1_21_contains j)
noncomputable def hk1_1_23 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_23 j i k)
lemma hk1_1_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_1_23 j i k).Contains (fullFactor true 1 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_1_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel1_0 j i k) (mpower1_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 23 (kernel1_0_contains j i k) (mpower1_23_contains j i k)
noncomputable def ha1_1_23 : Fin 7 → CBox := ![⟨⟨(-169630516111532848341941681),(-169630516111532848316918115)⟩,⟨(-3),3⟩⟩,⟨⟨(-86332429918969983143844405),(-86332429918969969318311511)⟩,⟨(-85295254653495969421963823),(-85295254653495955596611379)⟩⟩,⟨⟨(-285464731267465599057936),(-285464731267454767546450)⟩,⟨(-25652634577029348917593689),(-25652634577029338086082157)⟩⟩,⟨⟨(-243744453882053748005569),(-243744453882053506836467)⟩,⟨(-1727516645114820514365808),(-1727516645114820273195883)⟩⟩,⟨⟨(-78580930297157535361684),(-78580930297157533789046)⟩,⟨(-9178417532003549300934),(-9178417532003547728298)⟩⟩,⟨⟨2177116452923626296715,2177116452923626305895⟩,⟨3145452970825682444490,3145452970825682453694⟩⟩,⟨⟨(-108302113840389166381),(-108302113840389166320)⟩,⟨(-211076901258598283640),(-211076901258598283573)⟩⟩]
lemma ha1_1_23_eq (j : Fin 7) : ha1_1_23 j = ((ha1_1_22 j).mul (piI.mul (atomPoints j).z)).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha1_1_23_contains (j : Fin 7) : (ha1_1_23 j).Contains (fullFactor true 1 23 ((j.val:ℝ)/6)) := by
  rw [ha1_1_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_1_22 j) true 1 22 j (ha1_1_22_contains j)
noncomputable def hk1_1_24 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_24 j i k)
lemma hk1_1_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_1_24 j i k).Contains (fullFactor true 1 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_1_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel1_0 j i k) (mpower1_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 24 (kernel1_0_contains j i k) (mpower1_24_contains j i k)
noncomputable def ha1_1_24 : Fin 7 → CBox := ![⟨⟨65133442396077813545291231,65133442396077813555106918⟩,⟨(-2),2⟩⟩,⟨⟨14363680084106971048784808,14363680084106977606850089⟩,⟨40619374804049278167288194,40619374804049284725323246⟩⟩,⟨⟨(-5446227748738038470139601),(-5446227748738033923731639)⟩,⟨5323837198661289014762850,5323837198661293561170050⟩⟩,⟨⟨(-338951926557324941945088),(-338951926557324862174273)⟩,⟨255581902490504445758957,255581902490504525529245⟩⟩,⟨⟨3194747093343434527650,3194747093343434929701⟩,⟨15706317636970696521616,15706317636970696923695⟩⟩,⟨⟨471531353205455306582,471531353205455308421⟩,⟨(-462896816314156866386),(-462896816314156864551)⟩⟩,⟨⟨(-30911163976323348768),(-30911163976323348757)⟩,⟨17946515450704531734,17946515450704531745⟩⟩]
lemma ha1_1_24_eq (j : Fin 7) : ha1_1_24 j = ((ha1_1_23 j).mul (piI.mul (atomPoints j).z)).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha1_1_24_contains (j : Fin 7) : (ha1_1_24 j).Contains (fullFactor true 1 24 ((j.val:ℝ)/6)) := by
  rw [ha1_1_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_1_23 j) true 1 23 j (ha1_1_23_contains j)
noncomputable def hk1_1_25 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_25 j i k)
lemma hk1_1_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_1_25 j i k).Contains (fullFactor true 1 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_1_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel1_0 j i k) (mpower1_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 25 (kernel1_0_contains j i k) (mpower1_25_contains j i k)
noncomputable def ha1_1_25 : Fin 7 → CBox := ![⟨⟨(-24009068645118425909862464),(-24009068645118425906167845)⟩,⟨(-1),1⟩⟩,⟨⟨1636076981908468244512203,1636076981908471230845376⟩,⟨(-14591984928472993258459042),(-14591984928472990272117444)⟩⟩,⟨⟨2169332750012151823855577,2169332750012153655827794⟩,⟨73469880498864665227130,73469880498866497199358⟩⟩,⟨⟨90592553372368874884816,90592553372368900214683⟩,⟨40326720032098256487827,40326720032098281817766⟩⟩,⟨⟨2708873486572865580600,2708873486572865679285⟩,⟨(-1542414675787805987054),(-1542414675787805888378)⟩⟩,⟨⟨(-88926897483773123616),(-88926897483773123263)⟩,⟨(-64012984396465745721),(-64012984396465745367)⟩⟩,⟨⟨2824385101236288391,2824385101236288394⟩,⟨4330045624131425382,4330045624131425384⟩⟩]
lemma ha1_1_25_eq (j : Fin 7) : ha1_1_25 j = ((ha1_1_24 j).mul (piI.mul (atomPoints j).z)).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha1_1_25_contains (j : Fin 7) : (ha1_1_25 j).Contains (fullFactor true 1 25 ((j.val:ℝ)/6)) := by
  rw [ha1_1_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_1_24 j) true 1 24 j (ha1_1_24_contains j)
noncomputable def hk1_1_26 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_26 j i k)
lemma hk1_1_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_1_26 j i k).Contains (fullFactor true 1 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_1_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel1_0 j i k) (mpower1_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 26 (kernel1_0_contains j i k) (mpower1_26_contains j i k)
noncomputable def ha1_1_26 : Fin 7 → CBox := ![⟨⟨8509680517183672537373340,8509680517183672538709935⟩,⟨(-1),1⟩⟩,⟨⟨(-2568981362184987329053891),(-2568981362184986021479588)⟩,⟨4068569248181913455580988,4068569248181914763162834⟩⟩,⟨⟨(-396247185450621400472223),(-396247185450620690673434)⟩,⟨(-443620209347069897788859),(-443620209347069187990013)⟩⟩,⟨⟨(-1937522656903222641460),(-1937522656903214907724)⟩,⟨(-22188319619892245593053),(-22188319619892237859309)⟩⟩,⟨⟨(-431955694851713849049),(-431955694851713825762)⟩,⟨(-391448392502796075550),(-391448392502796052261)⟩⟩,⟨⟨(-7649243451556011185),(-7649243451556011119)⟩,⟨15706821898100367399,15706821898100367465⟩⟩,⟨⟨580983201293651323,580983201293651324⟩,⟨(-423538282056646497),(-423538282056646496)⟩⟩]
lemma ha1_1_26_eq (j : Fin 7) : ha1_1_26 j = ((ha1_1_25 j).mul (piI.mul (atomPoints j).z)).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha1_1_26_contains (j : Fin 7) : (ha1_1_26 j).Contains (fullFactor true 1 26 ((j.val:ℝ)/6)) := by
  rw [ha1_1_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_1_25 j) true 1 25 j (ha1_1_25_contains j)
noncomputable def hk1_1_27 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_27 j i k)
lemma hk1_1_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_1_27 j i k).Contains (fullFactor true 1 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_1_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel1_0 j i k) (mpower1_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 27 (kernel1_0_contains j i k) (mpower1_27_contains j i k)
noncomputable def ha1_1_27 : Fin 7 → CBox := ![⟨⟨(-2904429113767749108416612),(-2904429113767749107951174)⟩,⟨(-1),1⟩⟩,⟨⟨1289658390288705565261199,1289658390288706116582809⟩,⟨(-801461860921930737422728),(-801461860921930186099317)⟩⟩,⟨⟨(-12361871445742553441818),(-12361871445742288615455)⟩,⟨156478420273017451886139,156478420273017716712500⟩⟩,⟨⟨(-3994851879902161037345),(-3994851879902158763534)⟩,⟨2692225091544112662324,2692225091544114936129⟩⟩,⟨⟨(-42737796046087404040),(-42737796046087398746)⟩,⟨95882018240872054649,95882018240872059942⟩⟩,⟨⟨2576089554437808966,2576089554437808979⟩,⟨747667784865743001,747667784865743014⟩⟩,⟨⟨(-60685219599380569),(-60685219599380568)⟩,⟨(-74756157929383080),(-74756157929383079)⟩⟩]
lemma ha1_1_27_eq (j : Fin 7) : ha1_1_27 j = ((ha1_1_26 j).mul (piI.mul (atomPoints j).z)).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha1_1_27_contains (j : Fin 7) : (ha1_1_27 j).Contains (fullFactor true 1 27 ((j.val:ℝ)/6)) := by
  rw [ha1_1_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_1_26 j) true 1 26 j (ha1_1_26_contains j)
noncomputable def hk1_1_28 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_28 j i k)
lemma hk1_1_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_1_28 j i k).Contains (fullFactor true 1 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_1_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel1_0 j i k) (mpower1_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 28 (kernel1_0_contains j i k) (mpower1_28_contains j i k)
noncomputable def ha1_1_28 : Fin 7 → CBox := ![⟨⟨955903474605103032252441,955903474605103032408669⟩,⟨(-1),1⟩⟩,⟨⟨(-459519331600635937794161),(-459519331600635713639056)⟩,⟨48193567172068358283137,48193567172068582438276⟩⟩,⟨⟨30955423750280815422529,30955423750280910700506⟩,⟨(-25241537881216690712536),(-25241537881216595434563)⟩⟩,⟨⟨894929377678363021798,894929377678363666448⟩,⟨456709338364086615692,456709338364087260343⟩⟩,⟨⟨18133460127840363494,18133460127840364655⟩,⟨1862597164846029741,1862597164846030902⟩⟩,⟨⟨44288978234625539,44288978234625542⟩,⟨(-394666951372099371),(-394666951372099368)⟩⟩,⟨⟨(-9233977343089228),(-9233977343089227)⟩,⟨8327611522828318,8327611522828319⟩⟩]
lemma ha1_1_28_eq (j : Fin 7) : ha1_1_28 j = ((ha1_1_27 j).mul (piI.mul (atomPoints j).z)).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha1_1_28_contains (j : Fin 7) : (ha1_1_28 j).Contains (fullFactor true 1 28 ((j.val:ℝ)/6)) := by
  rw [ha1_1_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_1_27 j) true 1 27 j (ha1_1_27_contains j)
noncomputable def hk1_1_29 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_29 j i k)
lemma hk1_1_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_1_29 j i k).Contains (fullFactor true 1 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_1_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel1_0 j i k) (mpower1_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 29 (kernel1_0_contains j i k) (mpower1_29_contains j i k)
noncomputable def ha1_1_29 : Fin 7 → CBox := ![⟨⟨(-303757725673230720529902),(-303757725673230720479290)⟩,⟨(-1),1⟩⟩,⟨⟨127653714252159796058816,127653714252159884052402⟩,⟨46171245079579513772993,46171245079579601766406⟩⟩,⟨⟨(-9738213183408938343873),(-9738213183408905247239)⟩,⟨(-1211975216987692450646),(-1211975216987659354012)⟩⟩,⟨⟨(-6884119378801936284),(-6884119378801759820)⟩,⟨(-202208008042148252582),(-202208008042148076118)⟩⟩,⟨⟨(-650809555287453391),(-650809555287453145)⟩,⟨(-2986168569809377889),(-2986168569809377642)⟩⟩,⟨⟨(-56673251152222625),(-56673251152222623)⟩,⟨3345942567997232,3345942567997233⟩⟩,⟨⟨1096728170513645,1096728170513646⟩,⟨1095876864803655,1095876864803656⟩⟩]
lemma ha1_1_29_eq (j : Fin 7) : ha1_1_29 j = ((ha1_1_28 j).mul (piI.mul (atomPoints j).z)).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha1_1_29_contains (j : Fin 7) : (ha1_1_29 j).Contains (fullFactor true 1 29 ((j.val:ℝ)/6)) := by
  rw [ha1_1_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_1_28 j) true 1 28 j (ha1_1_28_contains j)
noncomputable def hk1_1_30 (j : Fin 6) (i k : Fin 16) : CBox := (kernel1_0 j i k).mul (mpower1_30 j i k)
lemma hk1_1_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_1_30 j i k).Contains (fullFactor true 1 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_1_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel1_0 j i k) (mpower1_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 30 (kernel1_0_contains j i k) (mpower1_30_contains j i k)
noncomputable def ha1_1_30 : Fin 7 → CBox := ![⟨⟨93307674968069502156449,93307674968069502172294⟩,⟨(-1),1⟩⟩,⟨⟨(-26898813713713992561041),(-26898813713713959170040)⟩,⟨(-27618604999837585076998),(-27618604999837551686054)⟩⟩,⟨⟨1390155879903790051627,1390155879903801165149⟩,⟨1870683060482900456998,1870683060482911570520⟩⟩,⟨⟨(-33781776682384171208),(-33781776682384124513)⟩,⟨20247071845331095770,20247071845331142465⟩⟩,⟨⟨(-426995268993283891),(-426995268993283840)⟩,⟨251061431221641959,251061431221642010⟩⟩,⟨⟨1786147405653289,1786147405653290⟩,⟨7639014807186454,7639014807186455⟩⟩,⟨⟨125043452230103,125043452230104⟩,⟨(-138869681849478),(-138869681849477)⟩⟩]
lemma ha1_1_30_eq (j : Fin 7) : ha1_1_30 j = ((ha1_1_29 j).mul (piI.mul (atomPoints j).z)).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha1_1_30_contains (j : Fin 7) : (ha1_1_30 j).Contains (fullFactor true 1 30 ((j.val:ℝ)/6)) := by
  rw [ha1_1_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_1_29 j) true 1 29 j (ha1_1_29_contains j)
end SharpPlanar.CachedData

end OAI
