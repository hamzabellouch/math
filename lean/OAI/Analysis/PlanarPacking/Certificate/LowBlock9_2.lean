import OAI.Analysis.PlanarPacking.Certificate.TableDensityValues
import OAI.Analysis.PlanarPacking.Certificate.HighHeaders9

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm9_0_0_14
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk9_0_14 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-93293582617901),(-93293582617883)⟩,⟨133825314956149,133825314956165⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-181537578376026),(-181537578376009)⟩,⟨323444665884535,323444665884552⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-111365475294832),(-111365475294813)⟩,⟨335467623050296,335467623050313⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-9338867863019),(-9338867863001)⟩,⟨211506819581215,211506819581231⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨25784716477888,25784716477904⟩,⟨81808900354584,81808900354602⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨15514957150763,15514957150783⟩,⟨17944480066549,17944480066567⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨4032881006181,4032881006202⟩,⟨1739318448920,1739318448937⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨522083445548,522083445571⟩,⟨(-37489642265),(-37489642249)⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨31954301320,31954301339⟩,⟨(-20158224738),(-20158224719)⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨750875054,750875072⟩,⟨(-1306615097),(-1306615075)⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨1647550,1647570⟩,⟨(-28839897),(-28839878)⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-76859),(-76840)⟩,⟨(-198911),(-198891)⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-290),(-271)⟩,⟨(-316),(-298)⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),0⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),0⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),0⟩⟩
lemma c0_15 : chunk 0 15 = s0_15 := by decide +kernel
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
lemma s0_eq (i : Fin 16) : chunk 0 i = s0 i := by
  fin_cases i
  · exact c0_0
  · exact c0_1
  · exact c0_2
  · exact c0_3
  · exact c0_4
  · exact c0_5
  · exact c0_6
  · exact c0_7
  · exact c0_8
  · exact c0_9
  · exact c0_10
  · exact c0_11
  · exact c0_12
  · exact c0_13
  · exact c0_14
  · exact c0_15
noncomputable def s1_0 : CBox := ⟨⟨1389515042892103580,1389515042892104787⟩,⟨1902659989993567032,1902659989993568239⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨4048002647388836776,4048002647388841063⟩,⟨4583110805467805440,4583110805467809725⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨6002504820697241299,6002504820697250645⟩,⟨4710095711368144951,4710095711368154300⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨6387090502015857113,6387090502015873728⟩,⟨2705791674273850425,2705791674273867039⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨5031961452074534867,5031961452074557802⟩,⟨316541315577130270,316541315577153206⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨2880539021027100761,2880539021027122939⟩,⟨(-1007750220598295832),(-1007750220598273654)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨1119634456527110012,1119634456527125878⟩,⟨(-1114296793036305519),(-1114296793036289653)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨218981047465950223,218981047465961399⟩,⟨(-681061461028561839),(-681061461028550660)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-51199611264195747),(-51199611264191013)⟩,⟨(-285560989691523339),(-285560989691518607)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-66204466952220414),(-66204466952219178)⟩,⟨(-85482139538216797),(-85482139538215562)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-34295260622896993),(-34295260622896669)⟩,⟨(-16788144751308464),(-16788144751308137)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-13228123379756216),(-13228123379756129)⟩,⟨(-537319810425246),(-537319810425156)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-4441936756137064),(-4441936756137033)⟩,⟨1452482269241556,1452482269241587⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-1419809757159072),(-1419809757159056)⟩,⟨970234388539774,970234388539794⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-446099819895959),(-446099819895941)⟩,⟨456121442279819,456121442279836⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-102929007993184),(-102929007993168)⟩,⟨129050279878070,129050279878086⟩⟩
lemma c1_15 : chunk 1 15 = s1_15 := by decide +kernel
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
lemma s1_eq (i : Fin 16) : chunk 1 i = s1 i := by
  fin_cases i
  · exact c1_0
  · exact c1_1
  · exact c1_2
  · exact c1_3
  · exact c1_4
  · exact c1_5
  · exact c1_6
  · exact c1_7
  · exact c1_8
  · exact c1_9
  · exact c1_10
  · exact c1_11
  · exact c1_12
  · exact c1_13
  · exact c1_14
  · exact c1_15
noncomputable def s2_0 : CBox := ⟨⟨497168676128034399944,497168676128034400127⟩,⟨(-3194874333648415031),(-3194874333648414924)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨1344730032032089909137,1344730032032089909631⟩,⟨(-146073563707915176955),(-146073563707915176655)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨1770660490049839656112,1770660490049839656828⟩,⟨(-562613841684622619936),(-562613841684622619418)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨1620360209948181730703,1620360209948181731500⟩,⟨(-1099017707190108301587),(-1099017707190108300896)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨998269458449041669383,998269458449041670100⟩,⟨(-1425376834797722494876),(-1425376834797722494131)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨253032604145613119805,253032604145613120328⟩,⟨(-1333393390960766010712),(-1333393390960766010063)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-261982141365020971751),(-261982141365020971374)⟩,⟨(-913751980585416575640),(-913751980585416575141)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-425391672529819630658),(-425391672529819630261)⟩,⟨(-436148382533995715738),(-436148382533995715311)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-348334648038450229138),(-348334648038450228594)⟩,⟨(-105675960130966933703),(-105675960130966933171)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-202499664938488705629),(-202499664938488704483)⟩,⟨41099492466832453620,41099492466832454746⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-89164829560143035197),(-89164829560143031445)⟩,⟨70331502991530080010,70331502991530083755⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-28436164169276607438),(-28436164169276598169)⟩,⟨54466787836574035719,54466787836574044988⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-4046028367192922925),(-4046028367192908338)⟩,⟨32760501908965438796,32760501908965453387⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨2729006232967623545,2729006232967638899⟩,⟨17199768912059920423,17199768912059935779⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨2883171691323622813,2883171691323633701⟩,⟨7913783042365123314,7913783042365134204⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨1084219935162580333,1084219935162584144⟩,⟨2262314920597695393,2262314920597699206⟩⟩
lemma c2_15 : chunk 2 15 = s2_15 := by decide +kernel
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
lemma s2_eq (i : Fin 16) : chunk 2 i = s2 i := by
  fin_cases i
  · exact c2_0
  · exact c2_1
  · exact c2_2
  · exact c2_3
  · exact c2_4
  · exact c2_5
  · exact c2_6
  · exact c2_7
  · exact c2_8
  · exact c2_9
  · exact c2_10
  · exact c2_11
  · exact c2_12
  · exact c2_13
  · exact c2_14
  · exact c2_15
noncomputable def s3_0 : CBox := ⟨⟨5187020910404091130446,5187020910404117031216⟩,⟨(-15202836800576747937081),(-15202836800576722033252)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨10319094452771676681489,10319094452771738010320⟩,⟨(-43653893467992106100749),(-43653893467992044764227)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨2790992850789363422031,2790992850789423662815⟩,⟨(-64724671265758438171207),(-64724671265758377921941)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-16731545798731951189266),(-16731545798731916852475)⟩,⟨(-71354512081476802572401),(-71354512081476768230745)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-38877697034204142313742),(-38877697034204130738897)⟩,⟨(-59620432118234076741621),(-59620432118234065168197)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-51515508769836673686116),(-51515508769836671419519)⟩,⟨(-34002521077570823978189),(-34002521077570821718823)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-48616278834520965468929),(-48616278834520965162650)⟩,⟨(-6196797488680616503075),(-6196797488680616204803)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-34001794038592061856428),(-34001794038592061791686)⟩,⟨12738726713833111863131,12738726713833111925539⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-16773583083374007716114),(-16773583083374007695006)⟩,⟨19174111151748292553241,19174111151748292575783⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-4015800313926631669516),(-4015800313926631660632)⟩,⟨16652790904136702925606,16652790904136702937196⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨2384806202180714328253,2384806202180714333747⟩,⟨10888999806109042470293,10888999806109042477135⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨4116020352592618614823,4116020352592618618504⟩,⟨5744892520817087141961,5744892520817087145816⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨3593758409479995230753,3593758409479995232980⟩,⟨2477958974696391472982,2477958974696391474941⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨2438934112383988665386,2438934112383988666619⟩,⟨840008968454679499857,840008968454679500769⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨1338514773939307438048,1338514773939307438657⟩,⟨193953311199989463095,193953311199989463476⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨419724483666010116891,419724483666010117079⟩,⟨20158314008724280099,20158314008724280215⟩⟩
lemma c3_15 : chunk 3 15 = s3_15 := by decide +kernel
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
lemma s3_eq (i : Fin 16) : chunk 3 i = s3 i := by
  fin_cases i
  · exact c3_0
  · exact c3_1
  · exact c3_2
  · exact c3_3
  · exact c3_4
  · exact c3_5
  · exact c3_6
  · exact c3_7
  · exact c3_8
  · exact c3_9
  · exact c3_10
  · exact c3_11
  · exact c3_12
  · exact c3_13
  · exact c3_14
  · exact c3_15
noncomputable def s4_0 : CBox := ⟨⟨(-17825927109561532432287),(-17825927109559776002607)⟩,⟨(-226600675271277532752738),(-226600675271275776350521)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-121045940295718233736315),(-121045940295711381490402)⟩,⟨(-624576067048011264397907),(-624576067048004412221809)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-372733002055260570454817),(-372733002055242837580786)⟩,⟨(-847882409129953637426085),(-847882409129935904631563)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-719895912568585877037938),(-719895912568545403870825)⟩,⟨(-790616891314716724351143),(-790616891314676251231556)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-985871860485503070758766),(-985871860485425639380438)⟩,⟨(-441634184414899788523780),(-441634184414822357129352)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-993689120713058343788594),(-993689120712946908793283)⟩,⟨55726605831752391350250,55726605831863826430509⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-714774249226214498333052),(-714774249226084419729853)⟩,⟨466704321181494753973860,466704321181624832678619⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-296907631462352836870685),(-296907631462196498033009)⟩,⟨623957970237388200639382,623957970237544539509134⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨59027710724630486818212,59027710724749628221304⟩,⟨530760386036208553174384,530760386036327694554023⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨241855441108072709312742,241855441108130749748260⟩,⟨316288845651533045150547,316288845651591085536938⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨265018383541538365190452,265018383541567574947992⟩,⟨114787199512406724379455,114787199512435934109593⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨204322493258302237416668,204322493258315043946058⟩,⟨(-9613222247278943926878),(-9613222247266137401317)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨127628434438619246674920,127628434438623733592388⟩,⟨(-58484950390210169654015),(-58484950390205682729657)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨67898838005873907075824,67898838005875333061532⟩,⟨(-60140049230203566506243),(-60140049230202140511581)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨30515612456183162036523,30515612456183601496149⟩,⟨(-40468716872008427071287),(-40468716872007987605126)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨8441351385723556141207,8441351385723656173471⟩,⟨(-13912583482030843131503),(-13912583482030743096918)⟩⟩
lemma c4_15 : chunk 4 15 = s4_15 := by decide +kernel
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
lemma s4_eq (i : Fin 16) : chunk 4 i = s4 i := by
  fin_cases i
  · exact c4_0
  · exact c4_1
  · exact c4_2
  · exact c4_3
  · exact c4_4
  · exact c4_5
  · exact c4_6
  · exact c4_7
  · exact c4_8
  · exact c4_9
  · exact c4_10
  · exact c4_11
  · exact c4_12
  · exact c4_13
  · exact c4_14
  · exact c4_15
noncomputable def s5_0 : CBox := ⟨⟨(-27457961698962248754748),(-27457961698962248460517)⟩,⟨(-781206420072944378792292),(-781206420072944378381663)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-383769895194548842859172),(-383769895194548841883441)⟩,⟨(-2185950549280729122099037),(-2185950549280729120828541)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-1434945014352504430106511),(-1434945014352504428238834)⟩,⟨(-3029535892210191987658269),(-3029535892210191985470700)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-3016101503565613022361419),(-3016101503565613019459128)⟩,⟨(-2834124725372496054641129),(-2834124725372496051560139)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-4356075068967916397448102),(-4356075068967916393647241)⟩,⟨(-1397339958517602325325596),(-1397339958517602321574517)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-4546652645908180922672567),(-4546652645908180918426799)⟩,⟨815069906977382739835208,815069906977382743844888⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-3281838438028730276980285),(-3281838438028730272321632)⟩,⟨2767760943332916237088422,2767760943332916241503377⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-1167390850288873403495174),(-1167390850288873395690174)⟩,⟨3543794411450382878641646,3543794411450382886385146⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨754850325132436049328684,754850325132436073094681⟩,⟨2996954476750942242171368,2996954476750942265958261⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨1779576450515471806561259,1779576450515471900042291⟩,⟨1722515367474624773431937,1722515367474624866921355⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨1874828613860528506321507,1874828613860528970264429⟩,⟨479157593464016283192403,479157593464016747119840⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨1439265593964759350511206,1439265593964760912836045⟩,⟨(-302799523755758553661626),(-302799523755756991341162)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨893008404151465964765962,893008404151469171953791⟩,⟨(-590799845423478022533067),(-590799845423474815332229)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨464774647682684853365917,464774647682689046244861⟩,⟨(-552463196101668217295804),(-552463196101664024396174)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨200895586081196193884294,200895586081199667952173⟩,⟨(-362332391446169990863727),(-362332391446166516778847)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨53559298076374753875555,53559298076376071502325⟩,⟨(-123593400051790690088694),(-123593400051789372455547)⟩⟩
lemma c5_15 : chunk 5 15 = s5_15 := by decide +kernel
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
lemma s5_eq (i : Fin 16) : chunk 5 i = s5 i := by
  fin_cases i
  · exact c5_0
  · exact c5_1
  · exact c5_2
  · exact c5_3
  · exact c5_4
  · exact c5_5
  · exact c5_6
  · exact c5_7
  · exact c5_8
  · exact c5_9
  · exact c5_10
  · exact c5_11
  · exact c5_12
  · exact c5_13
  · exact c5_14
  · exact c5_15
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma sums_eq (j : Fin 6) (i : Fin 16) : chunk j i = sums j i := by
  fin_cases j
  · exact s0_eq i
  · exact s1_eq i
  · exact s2_eq i
  · exact s3_eq i
  · exact s4_eq i
  · exact s5_eq i
noncomputable def ans : CBox := ⟨⟨(-2357382201600325632619526),(-2357382201600195248100303)⟩,⟨(-178734978152584750146943),(-178734978152454365573391)⟩⟩
lemma checked : cachedMomentRuleBox density0 hk9_0_14 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false false 9 14) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk9_0_14 (tableDensity false) (fullFactor false 9 14) density0_contains hk9_0_14_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-3092268153396314434352744),(-3092268153396314433679622)⟩,⟨219635173470286306377905,219635173470286306918881⟩⟩
lemma atomChecked : tableAtomBox false ha9_0_14 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false false 9 14) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false false ha9_0_14 9 14 ha9_0_14_contains
 def realAnswer : RBox := ⟨(-5449650354996640166972270),(-5449650354996509581779925)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false false 9 14) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm9_0_0_14
namespace hm9_1_0_14
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk9_0_14 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-18833528413506),(-18833528413490)⟩,⟨20581086614975,20581086614991⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-38620780425207),(-38620780425191)⟩,⟨50670167681769,50670167681787⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-27849409933669),(-27849409933653)⟩,⟨54102517790687,54102517790704⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-7754950218960),(-7754950218944)⟩,⟨35218766014786,35218766014802⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨1781840003414,1781840003432⟩,⟨14070151709198,14070151709214⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨1983974279351,1983974279367⟩,⟨3201545888623,3201545888639⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨590776145715,590776145731⟩,⟨331971137056,331971137072⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨80894537799,80894537816⟩,⟨(-2885148505),(-2885148489)⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨5027635874,5027635890⟩,⟨(-3339988429),(-3339988412)⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨112404309,112404326⟩,⟨(-225880021),(-225880004)⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-79511),(-79495)⟩,⟨(-5049177),(-5049160)⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-16357),(-16341)⟩,⟨(-34673),(-34657)⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-66),(-49)⟩,⟨(-63),(-46)⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),0⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),0⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),0⟩⟩
lemma c0_15 : chunk 0 15 = s0_15 := by decide +kernel
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
lemma s0_eq (i : Fin 16) : chunk 0 i = s0 i := by
  fin_cases i
  · exact c0_0
  · exact c0_1
  · exact c0_2
  · exact c0_3
  · exact c0_4
  · exact c0_5
  · exact c0_6
  · exact c0_7
  · exact c0_8
  · exact c0_9
  · exact c0_10
  · exact c0_11
  · exact c0_12
  · exact c0_13
  · exact c0_14
  · exact c0_15
noncomputable def s1_0 : CBox := ⟨⟨49492485129703804,49492485129704800⟩,⟨364119241165616822,364119241165617821⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨223454659778065625,223454659778069157⟩,⟨914366898672557496,914366898672561027⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨496139462663148648,496139462663156355⟩,⟨1034778086129744778,1034778086129752479⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨694367801880503038,694367801880516746⟩,⟨741597272994340761,741597272994354464⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨659149211770497927,659149211770516864⟩,⟨298656886197434187,298656886197453124⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨435360334634589013,435360334634607338⟩,⟨(-15497546549970227),(-15497546549951900)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨195367899379868718,195367899379881839⟩,⟨(-117166509634047460),(-117166509634034336)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨50898622817916415,50898622817925667⟩,⟨(-92230117965883737),(-92230117965874488)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-1132153149623321),(-1132153149619403)⟩,⟨(-43908644480521169),(-43908644480517251)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-8736845148554388),(-8736845148553362)⟩,⟨(-14524289672377677),(-14524289672376653)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-5328545780773381),(-5328545780773110)⟩,⟨(-3255350010152763),(-3255350010152494)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-2249411306157850),(-2249411306157773)⟩,⟨(-279624613806410),(-279624613806334)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-812245445068075),(-812245445068050)⟩,⟨189126781830010,189126781830037⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-277587323631837),(-277587323631817)⟩,⟨151627506036844,151627506036865⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-92558970714289),(-92558970714273)⟩,⟨75560470242266,75560470242283⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-22189061271201),(-22189061271185)⟩,⟨21881835390251,21881835390267⟩⟩
lemma c1_15 : chunk 1 15 = s1_15 := by decide +kernel
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
lemma s1_eq (i : Fin 16) : chunk 1 i = s1 i := by
  fin_cases i
  · exact c1_0
  · exact c1_1
  · exact c1_2
  · exact c1_3
  · exact c1_4
  · exact c1_5
  · exact c1_6
  · exact c1_7
  · exact c1_8
  · exact c1_9
  · exact c1_10
  · exact c1_11
  · exact c1_12
  · exact c1_13
  · exact c1_14
  · exact c1_15
noncomputable def s2_0 : CBox := ⟨⟨95974605164323748243,95974605164323748313⟩,⟨58207994748996206300,58207994748996206370⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨275631318059123171101,275631318059123171283⟩,⟨132394343843152103732,132394343843152103901⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨405075037146729196973,405075037146729197245⟩,⟨107444256126987348378,107444256126987348644⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨435307015025975758164,435307015025975758491⟩,⟨(-5238175900975164077),(-5238175900975163757)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨349968926324721324518,349968926324721324833⟩,⟨(-132045572831954111990),(-132045572831954111679)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨196290339695994705920,196290339695994706159⟩,⟨(-195752417417526499696),(-195752417417526499447)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨53876252181918259680,53876252181918259854⟩,⟨(-175708667148264517125),(-175708667148264516941)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-26490986077293292410),(-26490986077293292217)⟩,⟨(-109658114465914573420),(-109658114465914573219)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-46579252423501735043),(-46579252423501734701)⟩,⟨(-46529196247532589576),(-46529196247532589236)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-35899748599430317195),(-35899748599430316328)⟩,⟨(-9333137733565504111),(-9333137733565503246)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-19765735434814625792),(-19765735434814622768)⟩,⟨4666459621530313318,4666459621530316338⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-8574480634100006998),(-8574480634099999458)⟩,⟨6638522405674561511,6638522405674569052⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-2964783539539972362),(-2964783539539960469)⟩,⟨4833028300910231644,4833028300910243535⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-741996765187703852),(-741996765187691320)⟩,⟨2795760852091196942,2795760852091209475⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-70184987236387595),(-70184987236378700)⟩,⟨1358541139570805827,1358541139570814722⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨22961102871829380,22961102871832497⟩,⟨398512184104985002,398512184104988116⟩⟩
lemma c2_15 : chunk 2 15 = s2_15 := by decide +kernel
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
lemma s2_eq (i : Fin 16) : chunk 2 i = s2 i := by
  fin_cases i
  · exact c2_0
  · exact c2_1
  · exact c2_2
  · exact c2_3
  · exact c2_4
  · exact c2_5
  · exact c2_6
  · exact c2_7
  · exact c2_8
  · exact c2_9
  · exact c2_10
  · exact c2_11
  · exact c2_12
  · exact c2_13
  · exact c2_14
  · exact c2_15
noncomputable def s3_0 : CBox := ⟨⟨4427926742698245333526,4427926742698267092141⟩,⟨(-3037625241928485890890),(-3037625241928464132615)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨11344581366996901098450,11344581366996952582619⟩,⟨(-9462901042132741064612),(-9462901042132689581293)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨13182821091628809280977,13182821091628859776180⟩,⟨(-16010107155532062097757),(-16010107155532011603470)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨9054388156679731815346,9054388156679760524469⟩,⟨(-20708818390091685538264),(-20708818390091656829646)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨1119326165635710504357,1119326165635720136816⟩,⟨(-21111803686483985074912),(-21111803686483975442318)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-6484290060163832572043),(-6484290060163830711885)⟩,⟨(-16590862018351084292679),(-16590862018351082431877)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-10345840634182271369146),(-10345840634182271134808)⟩,⟨(-9250260514523635293658),(-9250260514523635058655)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-9841958502277466414565),(-9841958502277466373772)⟩,⟨(-2403844377801538912586),(-2403844377801538871617)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-6774056542496290105301),(-6774056542496290094697)⟩,⟨1766350319056688460506,1766350319056688471013⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-3423415076747970816214),(-3423415076747970811829)⟩,⟨3125001988025309289511,3125001988025309293735⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-1082596444248380638994),(-1082596444248380636439)⟩,⟨2777885161206903684192,2777885161206903686682⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨83342160124096340889,83342160124096342429⟩,⟨1880462936115432354049,1880462936115432355581⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨452633733664925504293,452633733664925505137⟩,⟨1075017157656757494131,1075017157656757494991⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨434408864496789105329,434408864496789105764⟩,⟨541621121896179987180,541621121896179987623⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨279400234858289354003,279400234858289354205⟩,⟨237542823683265583104,237542823683265583314⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨93935317579070889218,93935317579070889286⟩,⟨65380710760163504587,65380710760163504658⟩⟩
lemma c3_15 : chunk 3 15 = s3_15 := by decide +kernel
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
lemma s3_eq (i : Fin 16) : chunk 3 i = s3 i := by
  fin_cases i
  · exact c3_0
  · exact c3_1
  · exact c3_2
  · exact c3_3
  · exact c3_4
  · exact c3_5
  · exact c3_6
  · exact c3_7
  · exact c3_8
  · exact c3_9
  · exact c3_10
  · exact c3_11
  · exact c3_12
  · exact c3_13
  · exact c3_14
  · exact c3_15
noncomputable def s4_0 : CBox := ⟨⟨(-9661605146226296342391),(-9661605146224852917007)⟩,⟨(-74053838261314118748427),(-74053838261312675313534)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-49466633051966910393308),(-49466633051961278753029)⟩,⟨(-207510827494942284035143),(-207510827494936652370356)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-135247781087273321850205),(-135247781087258745576247)⟩,⟨(-291111475782760490848110),(-291111475782745914546224)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-253023519025782782847801),(-253023519025749508578978)⟩,⟨(-286995183261864338640328),(-286995183261831064354751)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-349262450793817403887483),(-349262450793753737010647)⟩,⟨(-182276777352355108840190),(-182276777352291441968609)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-365128254908088406556244),(-365128254907996780297976)⟩,⟨(-15233755374843353200911),(-15233755374751726970251)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-283643829866785059844356),(-283643829866678127180704)⟩,⟨138164239955060029231404,138164239955166961862662⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-145291758487468090217976),(-145291758487339631806209)⟩,⟨214955052815159667772032,214955052815288126173861⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-15174069457200196976978),(-15174069457102378333064)⟩,⟨204818593866217618571222,204818593866315437221573⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨63528993224725962288896,63528993224773565203463⟩,⟨143206690254019559227558,143206690254067162154604⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨87076431190726932730151,87076431190750858208708⟩,⟨74714915132651045147466,74714915132674970632444⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨76105058835411978193190,76105058835422453961621⟩,⟨25432989356783113420680,25432989356793589189993⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨53250487673912570066923,53250487673916235695340⟩,⟨(-132796274582633446097),(-132796274578967819132)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨31868021169491326586374,31868021169492490301406⟩,⟨(-8525612836462679527256),(-8525612836461515814036)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨16065575890637444518618,16065575890637802873050⟩,⟨(-7655134116205503172135),(-7655134116205144818978)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨4806914220988270657092,4806914220988352194466⟩,⟨(-2883311714380931150541),(-2883311714380849613604)⟩⟩
lemma c4_15 : chunk 4 15 = s4_15 := by decide +kernel
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
lemma s4_eq (i : Fin 16) : chunk 4 i = s4 i := by
  fin_cases i
  · exact c4_0
  · exact c4_1
  · exact c4_2
  · exact c4_3
  · exact c4_4
  · exact c4_5
  · exact c4_6
  · exact c4_7
  · exact c4_8
  · exact c4_9
  · exact c4_10
  · exact c4_11
  · exact c4_12
  · exact c4_13
  · exact c4_14
  · exact c4_15
noncomputable def s5_0 : CBox := ⟨⟨(-1916844818089785288982),(-1916844818089785152969)⟩,⟨(-23160890738959350246828),(-23160890738959350050198)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-26554883068580292412102),(-26554883068580291959516)⟩,⟨(-58951722693234360971346),(-58951722693234360361823)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-94942223871022837637856),(-94942223871022836774269)⟩,⟨(-34707111571642308811070),(-34707111571642307772413)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-171750117039790166425212),(-171750117039790165093317)⟩,⟨134359473865933396310637,134359473865933397743361⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-149186434946633311886512),(-149186434946633310107287)⟩,⟨478859352211141602110052,478859352211141603857013⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨87301013057530825262696,87301013057530827321687⟩,⟨874210277971207606406582,874210277971207608307170⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨532259743632128270889339,532259743632128273386690⟩,⟨1081549766885087930078706,1081549766885087932397078⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨1005891249966900989126596,1005891249966900994360661⟩,⟨937309328235067540013053,937309328235067545197048⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨1271814462887273283601994,1271814462887273302146028⟩,⟨498104232627140227944469,498104232627140246513673⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨1220904501817385773446194,1220904501817385849154851⟩,⟨(-11870698656173744316410),(-11870698656173668574262)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨930122948899152061025084,930122948899152439390064⟩,⟨(-379754199223757954354411),(-379754199223757575980913)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨567381205516725660109076,567381205516726935538242⟩,⟨(-526467215122699044151264),(-526467215122697768721860)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨268531623541588388274691,268531623541591008043356⟩,⟨(-495245727299570265569674),(-495245727299567645800381)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨86356457684136282383293,86356457684139709136293⟩,⟨(-371513228766858444982816),(-371513228766855018227596)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨8654810005547667055954,8654810005550507474713⟩,⟨(-220996702880789075368690),(-220996702880786234947564)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-4196640439333598259612),(-4196640439332520734031)⟩,⟨(-72406463153658825816609),(-72406463153657748289989)⟩⟩
lemma c5_15 : chunk 5 15 = s5_15 := by decide +kernel
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
lemma s5_eq (i : Fin 16) : chunk 5 i = s5 i := by
  fin_cases i
  · exact c5_0
  · exact c5_1
  · exact c5_2
  · exact c5_3
  · exact c5_4
  · exact c5_5
  · exact c5_6
  · exact c5_7
  · exact c5_8
  · exact c5_9
  · exact c5_10
  · exact c5_11
  · exact c5_12
  · exact c5_13
  · exact c5_14
  · exact c5_15
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma sums_eq (j : Fin 6) (i : Fin 16) : chunk j i = sums j i := by
  fin_cases j
  · exact s0_eq i
  · exact s1_eq i
  · exact s2_eq i
  · exact s3_eq i
  · exact s4_eq i
  · exact s5_eq i
noncomputable def ans : CBox := ⟨⟨710277817426169660178329,710277817426276759028828⟩,⟨241128803300019310698383,241128803300126409577351⟩⟩
lemma checked : cachedMomentRuleBox density1 hk9_0_14 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true false 9 14) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk9_0_14 (tableDensity true) (fullFactor false 9 14) density1_contains hk9_0_14_contains
noncomputable def atomAnswer : CBox := ⟨⟨4043735277518257336350275,4043735277518257337230511⟩,⟨(-287215226845759016740075),(-287215226845759016032645)⟩⟩
lemma atomChecked : tableAtomBox true ha9_0_14 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true false 9 14) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true false ha9_0_14 9 14 ha9_0_14_contains
 def realAnswer : RBox := ⟨4754013094944426896528604,4754013094944534196259339⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true false 9 14) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm9_1_0_14
namespace hm9_0_0_15
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk9_0_15 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-4649347975795),(-4649347975779)⟩,⟨(-3241481306787),(-3241481306770)⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-11029913792645),(-11029913792629)⟩,⟨(-6195983893885),(-6195983893869)⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-11020887911911),(-11020887911893)⟩,⟨(-3670648242971),(-3670648242953)⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-6567550221354),(-6567550221336)⟩,⟨(-302018364351),(-302018364333)⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-2353982114203),(-2353982114184)⟩,⟨734683357286,734683357302⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-468713426536),(-468713426516)⟩,⟨402149933696,402149933715⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-40462586159),(-40462586141)⟩,⟨92616153205,92616153225⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨686083007,686083027⟩,⟨10336921807,10336921825⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨329386086,329386104⟩,⟨528858949,528858966⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨17227163,17227184⟩,⟨10029815,10029832⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨291721,291742⟩,⟨18129,18148⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨1438,1457⟩,⟨(-561),(-544)⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨0,16⟩,⟨(-16),12⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨0,16⟩,⟨(-16),16⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨0,16⟩,⟨(-16),16⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨0,16⟩,⟨(-16),16⟩⟩
lemma c0_15 : chunk 0 15 = s0_15 := by decide +kernel
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
lemma s0_eq (i : Fin 16) : chunk 0 i = s0 i := by
  fin_cases i
  · exact c0_0
  · exact c0_1
  · exact c0_2
  · exact c0_3
  · exact c0_4
  · exact c0_5
  · exact c0_6
  · exact c0_7
  · exact c0_8
  · exact c0_9
  · exact c0_10
  · exact c0_11
  · exact c0_12
  · exact c0_13
  · exact c0_14
  · exact c0_15
noncomputable def s1_0 : CBox := ⟨⟨(-132517560560353345),(-132517560560353242)⟩,⟨96773875466932348,96773875466932450⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-316272644900366060),(-316272644900365748)⟩,⟨279250597402820990,279250597402821303⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-319165121788038881),(-319165121788038231)⟩,⟨406362167868308944,406362167868309593⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-178582827859741194),(-178582827859740085)⟩,⟨420565191067818669,420565191067819780⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-20514506438768972),(-20514506438767503)⟩,⟨319538340674351200,319538340674352670⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨60886882927816445,60886882927817806⟩,⟨175019336811846154,175019336811847514⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨64064300965065341,64064300965066268⟩,⟨64649775630719680,64649775630720608⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨36959058207660363,36959058207660985⟩,⟨11983929546793981,11983929546794607⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨14547813581414329,14547813581414587⟩,⟨(-2569152420319900),(-2569152420319640)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨4075197365428756,4075197365428832⟩,⟨(-3139415338768532),(-3139415338768454)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨749115654209041,749115654209073⟩,⟨(-1521263056450228),(-1521263056450196)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨23385148645970,23385148645991⟩,⟨(-549391651846328),(-549391651846307)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-56507351817429),(-56507351817410)⟩,⟨(-173637041258930),(-173637041258911)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-35973509278127),(-35973509278111)⟩,⟨(-52736515295418),(-52736515295401)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-16310231853588),(-16310231853570)⟩,⟨(-15962443029355),(-15962443029338)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-4526646245223),(-4526646245207)⟩,⟨(-3610686599035),(-3610686599019)⟩⟩
lemma c1_15 : chunk 1 15 = s1_15 := by decide +kernel
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
lemma s1_eq (i : Fin 16) : chunk 1 i = s1 i := by
  fin_cases i
  · exact c1_0
  · exact c1_1
  · exact c1_2
  · exact c1_3
  · exact c1_4
  · exact c1_5
  · exact c1_6
  · exact c1_7
  · exact c1_8
  · exact c1_9
  · exact c1_10
  · exact c1_11
  · exact c1_12
  · exact c1_13
  · exact c1_14
  · exact c1_15
noncomputable def s2_0 : CBox := ⟨⟨333317071018252067,333317071018252092⟩,⟨51980744602519666769,51980744602519666801⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨15159742061607642830,15159742061607642876⟩,⟨139717402223341823222,139717402223341823287⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨57672257279612874130,57672257279612874199⟩,⟨181711300114471927700,181711300114471927788⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨110622511805840556753,110622511805840556838⟩,⟨163307838298909371174,163307838298909371269⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨140116402610602658658,140116402610602658745⟩,⟨98317856533980317949,98317856533980318039⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨127388318969301163985,127388318969301164065⟩,⟨24329815593728056003,24329815593728056067⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨84498008398199299584,84498008398199299646⟩,⟨(-24096419302342056744),(-24096419302342056691)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨38926526567606408737,38926526567606408789⟩,⟨(-37846194629736165159),(-37846194629736165104)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨9106992271882344228,9106992271882344288⟩,⟨(-29842276111151373997),(-29842276111151373932)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-3358960547851666949),(-3358960547851666841)⟩,⟨(-16685015082289227937),(-16685015082289227829)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-5560807654418768395),(-5560807654418768084)⟩,⟨(-7070150267522860604),(-7070150267522860289)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-4156036064151786872),(-4156036064151786151)⟩,⟨(-2175672883952321045),(-2175672883952320327)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-2421084049294279629),(-2421084049294278537)⟩,⟨(-300903124090896386),(-300903124090895297)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-1238252611833711415),(-1238252611833710298)⟩,⟨195917382665709966,195917382665711085⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-559222732202846916),(-559222732202846133)⟩,⟨203632034295960761,203632034295961546⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-158323530915413397),(-158323530915413113)⟩,⟨75873226480809227,75873226480809508⟩⟩
lemma c2_15 : chunk 2 15 = s2_15 := by decide +kernel
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
lemma s2_eq (i : Fin 16) : chunk 2 i = s2 i := by
  fin_cases i
  · exact c2_0
  · exact c2_1
  · exact c2_2
  · exact c2_3
  · exact c2_4
  · exact c2_5
  · exact c2_6
  · exact c2_7
  · exact c2_8
  · exact c2_9
  · exact c2_10
  · exact c2_11
  · exact c2_12
  · exact c2_13
  · exact c2_14
  · exact c2_15
noncomputable def s3_0 : CBox := ⟨⟨2120176633373679857146,2120176633373683469764⟩,⟨723401411455306157468,723401411455309769655⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨6059121231487948374851,6059121231487956889868⟩,⟨1432834928347192847766,1432834928347201361706⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨8900274124945958717708,8900274124945967007007⟩,⟨385834591105212677125,385834591105220965244⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨9679204415865406739081,9679204415865411402505⟩,⟨(-2265342264028278857118),(-2265342264028274194365)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨7947570714537180173576,7947570714537181718943⟩,⟨(-5175334331325771184984),(-5175334331325769639425)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨4440805685922214354932,4440805685922214650590⟩,⟨(-6715712617769920167636),(-6715712617769919871022)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨795184396368576179496,795184396368576217606⟩,⟨(-6188303611962398682396),(-6188303611962398643252)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-1574540253099072495883),(-1574540253099072488103)⟩,⟨(-4217166757430263981568),(-4217166757430263973494)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-2309556139410830272458),(-2309556139410830269709)⟩,⟨(-2025105952606696569341),(-2025105952606696566771)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-1951675673531482883818),(-1951675673531482882435)⟩,⟨(-472889260071347294185),(-472889260071347293126)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-1242375709838047167508),(-1242375709838047166705)⟩,⟨270865827394565978251,270865827394565978893⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-639297733725707171179),(-639297733725707170734)⟩,⟨457318717825160194398,457318717825160194826⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-269784789643592650295),(-269784789643592650063)⟩,⟨390839404619824147207,390839404619824147468⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-89855835936575659380),(-89855835936575659270)⟩,⟨260649998496748140320,260649998496748140470⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-20489617927664369088),(-20489617927664369036)⟩,⟨141293524978363124028,141293524978363124108⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-2114927783248892812),(-2114927783248892786)⟩,⟨44024175611170130829,44024175611170130865⟩⟩
lemma c3_15 : chunk 3 15 = s3_15 := by decide +kernel
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
lemma s3_eq (i : Fin 16) : chunk 3 i = s3 i := by
  fin_cases i
  · exact c3_0
  · exact c3_1
  · exact c3_2
  · exact c3_3
  · exact c3_4
  · exact c3_5
  · exact c3_6
  · exact c3_7
  · exact c3_8
  · exact c3_9
  · exact c3_10
  · exact c3_11
  · exact c3_12
  · exact c3_13
  · exact c3_14
  · exact c3_15
noncomputable def s4_0 : CBox := ⟨⟨39511550101767068034932,39511550101767374284048⟩,⟨(-3107880511065036828649),(-3107880511064730574859)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨108495655543417490840837,108495655543418680854905⟩,⟨(-21017877169343905355944),(-21017877169342715330036)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨146202327884184915474080,146202327884187971348358⟩,⟨(-64233465874758535637478),(-64233465874755479749792)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨134878362159205893146568,134878362159212790311966⟩,⟨(-122715765960356468383405),(-122715765960349571210058)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨74355612167704361287774,74355612167717371089780⟩,⟨(-165723729695293166208452),(-165723729695280156409101)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-9086636736271050290417),(-9086636736252635733550)⟩,⟨(-164288194804361076865212),(-164288194804342662322170)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-75588883457011889654262),(-75588883456990811429292)⟩,⟨(-115997290391748987431833),(-115997290391727909223159)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-99072416713753741284091),(-99072416713728914037481)⟩,⟨(-47263873414182718644762),(-47263873414157891403222)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-82516714684385453530841),(-82516714684366925752171)⟩,⟨9092831477783839637140,9092831477802367419427⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-48144472121479712127212),(-48144472121470874705365)⟩,⟨36742235680409375526757,36742235680418212956070⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-17129822807699600988079),(-17129822807695247785849)⟩,⟨39460519463855005411429,39460519463859358617757⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨1385628208804799166382,1385628208806671938161⟩,⟨29853355617172972721811,29853355617174845494153⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨8395434099905768091016,8395434099906413350000⟩,⟨18341508287539296463055,18341508287539941721036⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨8524246178782355775812,8524246178782558075180⟩,⟨9628503903677147782611,9628503903677350080697⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨5684029748761435448520,5684029748761497195055⟩,⟨4286851410849883182128,4286851410849944927733⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨1944890429615250364561,1944890429615264349357⟩,⟨1180073561209384502153,1180073561209398486618⟩⟩
lemma c4_15 : chunk 4 15 = s4_15 := by decide +kernel
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
lemma s4_eq (i : Fin 16) : chunk 4 i = s4 i := by
  fin_cases i
  · exact c4_0
  · exact c4_1
  · exact c4_2
  · exact c4_3
  · exact c4_4
  · exact c4_5
  · exact c4_6
  · exact c4_7
  · exact c4_8
  · exact c4_9
  · exact c4_10
  · exact c4_11
  · exact c4_12
  · exact c4_13
  · exact c4_14
  · exact c4_15
noncomputable def s5_0 : CBox := ⟨⟨163485234473799000688407,163485234473799000774875⟩,⟨(-5744672564069228366264),(-5744672564069228304661)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨456023687454945650483121,456023687454945650749650⟩,⟨(-80021751148865110606920),(-80021751148865110403121)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨628133069566607245232092,628133069566607245687827⟩,⟨(-297352344804510500236087),(-297352344804510499847972)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨582439245161972675845908,582439245161972676481508⟩,⟨(-619380863652821689629630),(-619380863652821689031459)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨284152370727604301733891,284152370727604302498231⟩,⟨(-884263185773302837030288),(-884263185773302836255716)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-162602459115257579017353),(-162602459115257578212217)⟩,⟨(-910385204096376903350913),(-910385204096376902497759)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-544970981055575900180696),(-544970981055575899309116)⟩,⟨(-647177520595889340307819),(-647177520595889339387478)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-686396412580588888444629),(-686396412580588886943892)⟩,⟨(-226740213123696824731182),(-226740213123696823218368)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-570555012144597272359846),(-570555012144597267840295)⟩,⟨143195745108760905492931,143195745108760910008557⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-322361177603452335067380),(-322361177603452317625010)⟩,⟨332513612588354251811609,332513612588354269252694⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-88319129863370713831619),(-88319129863370628742229)⟩,⟨344605496069602169553911,344605496069602254646431⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨54672934580663683115825,54672934580663965458989⟩,⟨260530227065686301619821,260530227065686583963837⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨105451223098291092279882,105451223098291664529590⟩,⟨159508418314739967964100,159508418314740540211355⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨97593878887308369323694,97593878887309109837635⟩,⟨82133791343489084021535,82133791343489824531625⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨63539547722047502577330,63539547722048111753770⟩,⟨35235235207296702288720,35235235207297311462028⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨21591803688029783494916,21591803688030013684133⟩,⟨9357023152697818806807,9357023152698048994854⟩⟩
lemma c5_15 : chunk 5 15 = s5_15 := by decide +kernel
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
lemma s5_eq (i : Fin 16) : chunk 5 i = s5 i := by
  fin_cases i
  · exact c5_0
  · exact c5_1
  · exact c5_2
  · exact c5_3
  · exact c5_4
  · exact c5_5
  · exact c5_6
  · exact c5_7
  · exact c5_8
  · exact c5_9
  · exact c5_10
  · exact c5_11
  · exact c5_12
  · exact c5_13
  · exact c5_14
  · exact c5_15
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma sums_eq (j : Fin 6) (i : Fin 16) : chunk j i = sums j i := by
  fin_cases j
  · exact s0_eq i
  · exact s1_eq i
  · exact s2_eq i
  · exact s3_eq i
  · exact s4_eq i
  · exact s5_eq i
noncomputable def ans : CBox := ⟨⟨52020807502511498321518,52020807502532476236987⟩,⟨(-480359601281399089656461),(-480359601281378111753414)⟩⟩
lemma checked : cachedMomentRuleBox density0 hk9_0_15 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false false 9 15) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk9_0_15 (tableDensity false) (fullFactor false 9 15) density0_contains hk9_0_15_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-38075133827727417595610),(-38075133827727417490012)⟩,⟨(-634506425035256600853606),(-634506425035256600718803)⟩⟩
lemma atomChecked : tableAtomBox false ha9_0_15 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false false 9 15) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false false ha9_0_15 9 15 ha9_0_15_contains
 def realAnswer : RBox := ⟨13945673674783980725908,13945673674805158746975⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false false 9 15) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm9_0_0_15
namespace hm9_1_0_15
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk9_0_15 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-715020328714),(-715020328698)⟩,⟨(-654357165354),(-654357165338)⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-1727812909105),(-1727812909089)⟩,⟨(-1317857269695),(-1317857269679)⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-1777159698057),(-1777159698041)⟩,⟨(-916841055733),(-916841055717)⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-1093383980998),(-1093383980982)⟩,⟨(-242752899577),(-242752899560)⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-404759435737),(-404759435721)⟩,⟨50091183583,50091183599⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-83594136514),(-83594136498)⟩,⟨51325374603,51325374619⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-7713664881),(-7713664865)⟩,⟨13556390501,13556390517⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨47207947,47207964⟩,⟨1601125900,1601125917⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨54525657,54525674⟩,⟨83221602,83221618⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨2977381,2977399⟩,⟨1503861,1503880⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨51065,51081⟩,⟨(-550),(-534)⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨245,262⟩,⟨(-126),(-110)⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨0,16⟩,⟨(-16),12⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨0,16⟩,⟨(-16),16⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨0,16⟩,⟨(-16),16⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨0,16⟩,⟨(-16),16⟩⟩
lemma c0_15 : chunk 0 15 = s0_15 := by decide +kernel
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
lemma s0_eq (i : Fin 16) : chunk 0 i = s0 i := by
  fin_cases i
  · exact c0_0
  · exact c0_1
  · exact c0_2
  · exact c0_3
  · exact c0_4
  · exact c0_5
  · exact c0_6
  · exact c0_7
  · exact c0_8
  · exact c0_9
  · exact c0_10
  · exact c0_11
  · exact c0_12
  · exact c0_13
  · exact c0_14
  · exact c0_15
noncomputable def s1_0 : CBox := ⟨⟨(-25360178147130145),(-25360178147130058)⟩,⟨3446498949068016,3446498949068098⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-63093885153769782),(-63093885153769524)⟩,⟨15406187364996120,15406187364996379⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-70099261864459930),(-70099261864459397)⟩,⟨33565333600962391,33565333600962927⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-48896708244290029),(-48896708244289111)⟩,⟨45693297816902506,45693297816903422⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-19030394337598472),(-19030394337597255)⟩,⟨41834204198374884,41834204198376096⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨888159561173354,888159561174480⟩,⟨26437672219272435,26437672219273561⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨6723284802500049,6723284802500820⟩,⟨11272223250085761,11272223250086529⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨5000967509054215,5000967509054733⟩,⟨2777485471770606,2777485471771124⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨2235672226799033,2235672226799250⟩,⟨(-51331246215222),(-51331246215009)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨692038910974165,692038910974229⟩,⟨(-413698877063137),(-413698877063071)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨145111233148095,145111233148123⟩,⟨(-236223367144354),(-236223367144327)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨11794842572181,11794842572199⟩,⟨(-93386188231041),(-93386188231025)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-7344960812567),(-7344960812550)⟩,⟨(-31741398411478),(-31741398411462)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-5620193412556),(-5620193412540)⟩,⟨(-10308248516585),(-10308248516569)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-2701709216816),(-2701709216800)⟩,⟨(-3311586415670),(-3311586415654)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-767534125235),(-767534125219)⟩,⟨(-778366201777),(-778366201761)⟩⟩
lemma c1_15 : chunk 1 15 = s1_15 := by decide +kernel
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
lemma s1_eq (i : Fin 16) : chunk 1 i = s1 i := by
  fin_cases i
  · exact c1_0
  · exact c1_1
  · exact c1_2
  · exact c1_3
  · exact c1_4
  · exact c1_5
  · exact c1_6
  · exact c1_7
  · exact c1_8
  · exact c1_9
  · exact c1_10
  · exact c1_11
  · exact c1_12
  · exact c1_13
  · exact c1_14
  · exact c1_15
noncomputable def s2_0 : CBox := ⟨⟨(-6085983125989253689),(-6085983125989253669)⟩,⟨10034399825660926101,10034399825660926125⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-13758912797881650185),(-13758912797881650153)⟩,⟨28636081343883445467,28636081343883445502⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-11037991189501175075),(-11037991189501175031)⟩,⟨41562889463778215150,41562889463778215195⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨503061020984060072,503061020984060119⟩,⟨43856833355643310106,43856833355643310153⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨12959671904072122646,12959671904072122693⟩,⟨34438668943552143766,34438668943552143812⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨18685870306341793151,18685870306341793191⟩,⟨18782553663440058144,18782553663440058182⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨16236711730413589265,16236711730413589298⟩,⟨5005537827302714645,5005537827302714677⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨9777089981201941636,9777089981201941668⟩,⟨(-2344048725203726417),(-2344048725203726385)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨3995513902692031481,3995513902692031526⟩,⟨(-3985585716864384039),(-3985585716864383995)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨773703882183465236,773703882183465321⟩,⟨(-2955778785535183869),(-2955778785535183782)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-367386061681839291),(-367386061681839038)⟩,⟨(-1566125645463765193),(-1566125645463764938)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-506140062157264688),(-506140062157264097)⟩,⟨(-655251944417578949),(-655251944417578359)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-357063513812800229),(-357063513812799336)⟩,⟨(-219423109356416655),(-219423109356415763)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-201247316470076796),(-201247316470075878)⟩,⟨(-53510162135795247),(-53510162135794332)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-95996220286035140),(-95996220286034498)⟩,⟨(-4977087805322117),(-4977087805321475)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-27888931321438643),(-27888931321438411)⟩,⟨1606274189542861,1606274189543093⟩⟩
lemma c2_15 : chunk 2 15 = s2_15 := by decide +kernel
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
lemma s2_eq (i : Fin 16) : chunk 2 i = s2 i := by
  fin_cases i
  · exact c2_0
  · exact c2_1
  · exact c2_2
  · exact c2_3
  · exact c2_4
  · exact c2_5
  · exact c2_6
  · exact c2_7
  · exact c2_8
  · exact c2_9
  · exact c2_10
  · exact c2_11
  · exact c2_12
  · exact c2_13
  · exact c2_14
  · exact c2_15
noncomputable def s3_0 : CBox := ⟨⟨423621222744012905637,423621222744015940105⟩,⟨617522494543456431091,617522494543459465605⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨1313353173791759337447,1313353173791766484592⟩,⟨1574782189419517886699,1574782189419525033965⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨2201226198667265366333,2201226198667272313506⟩,⟨1813350230386619243066,1813350230386626190367⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨2808485141938251188459,2808485141938255086943⟩,⟨1229374436948675623696,1229374436948679522252⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨2813163073134149534638,2813163073134150820852⟩,⟨151008756227653413889,151008756227654700085⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨2164874173044704678022,2164874173044704921529⟩,⟨(-843932213759841129178),(-843932213759840885752)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨1179009671759835670703,1179009671759835700735⟩,⟨(-1315906170017311888815),(-1315906170017311858870)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨299406766091701218139,299406766091701223251⟩,⟨(-1219865776465617029622),(-1219865776465617024530)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-212040922659153132566),(-212040922659153131280)⟩,⟨(-817045810585665072941),(-817045810585665071641)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-365912172306131967991),(-365912172306131967481)⟩,⟨(-401738341927556840568),(-401738341927556840038)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-316763055519829349037),(-316763055519829348739)⟩,⟨(-123800108422260178620),(-123800108422260178315)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-209155982442356793532),(-209155982442356793348)⟩,⟨9110493515284226208,9110493515284226395⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-116979244092567435600),(-116979244092567435492)⟩,⟨49181986016878093755,49181986016878093861⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-57901993579049234221),(-57901993579049234157)⟩,⟨46412711640073565130,46412711640073565191⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-25078567063854257995),(-25078567063854257958)⟩,⟨29491003259312685038,29491003259312685073⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-6857794631185977779),(-6857794631185977754)⟩,⟨9852625976755095163,9852625976755095186⟩⟩
lemma c3_15 : chunk 3 15 = s3_15 := by decide +kernel
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
lemma s3_eq (i : Fin 16) : chunk 3 i = s3 i := by
  fin_cases i
  · exact c3_0
  · exact c3_1
  · exact c3_2
  · exact c3_3
  · exact c3_4
  · exact c3_5
  · exact c3_6
  · exact c3_7
  · exact c3_8
  · exact c3_9
  · exact c3_10
  · exact c3_11
  · exact c3_12
  · exact c3_13
  · exact c3_14
  · exact c3_15
noncomputable def s4_0 : CBox := ⟨⟨12912485754360860625585,12912485754361112305156⟩,⟨(-1684545710887926323185),(-1684545710887674645311)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨36046462042914509883587,36046462042915487931831⟩,⟨(-8589972613769189387928),(-8589972613768211344034)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨50195369100642604233769,50195369100645116152360⟩,⟨(-23308551978757632950196),(-23308551978755121036525)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨48957143243251284269165,48957143243256954654950⟩,⟨(-43131592277997976490711),(-43131592277992306107848)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨30679475584301567144584,30679475584312264269311⟩,⟨(-58708821683898676854337),(-58708821683887979728711)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨2561940508937265871038,2561940508952407033272⟩,⟨(-60362387993334670548507),(-60362387993319529381621)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-22368370343681129496209),(-22368370343663801899459)⟩,⟨(-46022503007292195975650),(-46022503007274868373545)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-34123763933099424673972),(-34123763933079024935684)⟩,⟨(-23111712975484135214918),(-23111712975463735475017)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-31835642852183630727465),(-31835642852168418839145)⟩,⟨(-2388339038119481092425),(-2388339038104269205117)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-21790075104716442717267),(-21790075104709194522390)⟩,⟨9644520026959288268522,9644520026966536461473⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-11137862173562509606309),(-11137862173558943921096)⟩,⟨12962245002207273926416,12962245002210839610652⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-3721946568690381814633),(-3721946568688849879817)⟩,⟨11117717048776522465655,11117717048778054400345⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨16282754839314332576,16282754839841482515⟩,⟨7651536380259831082195,7651536380260358232342⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨1207838388764522144427,1207838388764687235228⟩,⟨4518587235339333399079,4518587235339498490142⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨1075104162522019606681,1075104162522069956555⟩,⟨2256763975287295982150,2256763975287346332206⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨403065372046070363681,403065372046081762509⟩,⟨671985145658405404855,671985145658416803748⟩⟩
lemma c4_15 : chunk 4 15 = s4_15 := by decide +kernel
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
lemma s4_eq (i : Fin 16) : chunk 4 i = s4 i := by
  fin_cases i
  · exact c4_0
  · exact c4_1
  · exact c4_2
  · exact c4_3
  · exact c4_4
  · exact c4_5
  · exact c4_6
  · exact c4_7
  · exact c4_8
  · exact c4_9
  · exact c4_10
  · exact c4_11
  · exact c4_12
  · exact c4_13
  · exact c4_14
  · exact c4_15
noncomputable def s5_0 : CBox := ⟨⟨4846952677610040878680,4846952677610040919855⟩,⟨(-401036583045800519263),(-401036583045800490788)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨12299361426976075750358,12299361426976075877562⟩,⟨(-5537123871156067218713),(-5537123871156067124272)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨7207651921152204950472,7207651921152205165852⟩,⟨(-19675072639710851275290),(-19675072639710851096209)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-27557405221539211598586),(-27557405221539211304177)⟩,⟨(-35277846386997378331250),(-35277846386997378057537)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-97138154827122865645821),(-97138154827122865290832)⟩,⟨(-30316249613345982232944),(-30316249613345981871462)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-174930533166872555010789),(-174930533166872554629679)⟩,⟨17387676096680443609140,17387676096680444021729⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-213101741613099846425303),(-213101741613099845967997)⟩,⟨104741538550106496438877,104741538550106496931046⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-181642869807310356444378),(-181642869807310355440764)⟩,⟨194720136157177910146350,194720136157177911159477⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-94925954265304502450009),(-94925954265304498923266)⟩,⟨241967736163521191760759,241967736163521195282980⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨2091732014896995290380,2091732014897009420520⟩,⟨228275079996153917838530,228275079996153931963087⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨69723415437458954758507,69723415437459024155553⟩,⟨171020278670869031598789,171020278670869100994714⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨95245098513034382393660,95245098513034612889150⟩,⟨102733799842948582515626,102733799842948813011138⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨88426059262701096057879,88426059262701563493656⟩,⟨47981105765587009326521,47981105765587476762048⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨65635577855997608703551,65635577855998213907250⟩,⟨15268823789970187295321,15268823789970792498440⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨38755710511008333474086,38755710511008831538229⟩,⟨1520407743772082585435,1520407743772580649020⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨12649468480374489248999,12649468480374677491815⟩,⟨(-733058345652674714817),(-733058345652486472234)⟩⟩
lemma c5_15 : chunk 5 15 = s5_15 := by decide +kernel
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
lemma s5_eq (i : Fin 16) : chunk 5 i = s5 i := by
  fin_cases i
  · exact c5_0
  · exact c5_1
  · exact c5_2
  · exact c5_3
  · exact c5_4
  · exact c5_5
  · exact c5_6
  · exact c5_7
  · exact c5_8
  · exact c5_9
  · exact c5_10
  · exact c5_11
  · exact c5_12
  · exact c5_13
  · exact c5_14
  · exact c5_15
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma sums_eq (j : Fin 6) (i : Fin 16) : chunk j i = sums j i := by
  fin_cases j
  · exact s0_eq i
  · exact s1_eq i
  · exact s2_eq i
  · exact s3_eq i
  · exact s4_eq i
  · exact s5_eq i
noncomputable def ans : CBox := ⟨⟨(-53569232161108119232471),(-53569232161090887345371)⟩,⟨136028272472868208410703,136028272472885440291574⟩⟩
lemma checked : cachedMomentRuleBox density1 hk9_0_15 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true false 9 15) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk9_0_15 (tableDensity true) (fullFactor false 9 15) density1_contains hk9_0_15_contains
noncomputable def atomAnswer : CBox := ⟨⟨49790559620874315179246,49790559620874315317336⟩,⟨829739171199950939401512,829739171199950939577792⟩⟩
lemma atomChecked : tableAtomBox true ha9_0_15 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true false 9 15) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true false ha9_0_15 9 15 ha9_0_15_contains
 def realAnswer : RBox := ⟨(-3778672540233904053225),(-3778672540216472028035)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true false 9 15) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm9_1_0_15
end SharpPlanar.CachedData

end OAI
