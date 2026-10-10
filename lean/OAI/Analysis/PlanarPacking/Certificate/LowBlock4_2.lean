import OAI.Analysis.PlanarPacking.Certificate.TableDensityValues
import OAI.Analysis.PlanarPacking.Certificate.HighHeaders4

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm4_0_0_14
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk4_0_14 j i k))
noncomputable def s0_0 : CBox := ⟨⟨148558193710465,148558193710481⟩,⟨(-67436408595701),(-67436408595685)⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨329928374654461,329928374654478⟩,⟨(-170041130744998),(-170041130744982)⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨297479953756500,297479953756519⟩,⟨(-192105281899348),(-192105281899331)⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨160504375847529,160504375847546⟩,⟨(-139101476033480),(-139101476033463)⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨54192277796307,54192277796324⟩,⟨(-66991346777297),(-66991346777281)⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨10934459402480,10934459402498⟩,⟨(-21200092263556),(-21200092263537)⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨1102737478891,1102737478910⟩,⟨(-4278935454446),(-4278935454424)⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨7852018406,7852018423⟩,⟨(-526521050446),(-526521050426)⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-8608046513),(-8608046493)⟩,⟨(-36995018644),(-36995018626)⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-685821108),(-685821089)⟩,⟨(-1349020148),(-1349020128)⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-18701003),(-18700983)⟩,⟨(-22125098),(-22125077)⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-169163),(-169142)⟩,⟨(-130404),(-130387)⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-380),(-362)⟩,⟨(-198),(-182)⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-979747106866841777),(-979747106866840163)⟩,⟨2142843199585854310,2142843199585855921⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-2297151328409020882),(-2297151328409015531)⟩,⟨5671205566155302484,5671205566155307830⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-2247763333290743462),(-2247763333290732923)⟩,⟨7304816479855556109,7304816479855566646⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-1197005045687913706),(-1197005045687896569)⟩,⟨6854101786141773407,6854101786141790547⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-61911562712144369),(-61911562712121437)⟩,⟨5064409692424358503,5064409692424381437⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨544300997905933804,544300997905957632⟩,⟨3021078007105323392,3021078007105347224⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨607502768550626909,607502768550644816⟩,⟨1469970252681418714,1469970252681436622⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨419038143805416802,419038143805425927⟩,⟨586385713929357255,586385713929366378⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨220489471264879616,220489471264883333⟩,⟨191834462279250276,191834462279253992⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨96297450883938610,96297450883939941⟩,⟨50762579965921906,50762579965923239⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨37052081252928530,37052081252928884⟩,⟨10104063228784658,10104063228785012⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨13268545283938853,13268545283938940⟩,⟨891403303053550,891403303053637⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨4661968160339114,4661968160339148⟩,⟨(-490597354476454),(-490597354476421)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨1672399626071755,1672399626071774⟩,⟨(-412879964345000),(-412879964344979)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨602374676195601,602374676195619⟩,⟨(-211504363027263),(-211504363027247)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨152889412664162,152889412664178⟩,⟨(-62267945028532),(-62267945028516)⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨3003612878427064555,3003612878427064645⟩,⟨(-497210747813432506390),(-497210747813432506227)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-63075025363497941908),(-63075025363497941676)⟩,⟨(-1352148666927139113412),(-1352148666927139112983)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-277491750451602832079),(-277491750451602831719)⟩,⟨(-1840624630590391918663),(-1840624630590391918053)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-576457957546972758158),(-576457957546972757712)⟩,⟨(-1878095660662666519777),(-1878095660662666519106)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-812294157773232261089),(-812294157773232260616)⟩,⟨(-1548739843302501486232),(-1548739843302501485605)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-875828634423688187442),(-875828634423688186995)⟩,⟨(-1048042134461317278234),(-1048042134461317277723)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-766875730766002503206),(-766875730766002502831)⟩,⟨(-573491357845536030697),(-573491357845536030313)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-566166084502731984754),(-566166084502731984429)⟩,⟨(-237814849405667294781),(-237814849405667294473)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-362811910939620695960),(-362811910939620695501)⟩,⟨(-54552647534825119684),(-54552647534825119252)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-207205411611523295176),(-207205411611523294010)⟩,⟨19674262859174110295,19674262859174111441⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-108283894720374347828),(-108283894720374344787)⟩,⟨36495056632557350618,36495056632557353643⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-53185364062444956145),(-53185364062444948659)⟩,⟨31344930843359742303,31344930843359749783⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-25157068335334099714),(-25157068335334086431)⟩,⟨21533071986590512846,21533071986590526126⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-11591691809733286039),(-11591691809733269790)⟩,⟨13037123428412582398,13037123428412598644⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-4994630071318267580),(-4994630071318254301)⟩,⟨6788745519683194551,6788745519683207833⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-1390837076761921418),(-1390837076761916344)⟩,⟨2088086320657625661,2088086320657630738⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨10421403332421564822286,10421403332421599349297⟩,⟨12225598438608650098593,12225598438608684624418⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨30703146459618782973087,30703146459618858016485⟩,⟨32743927261828361124288,32743927261828436163926⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨48562277402960342799909,48562277402960406939214⟩,⟨43053041805735911986297,43053041805735976118911⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨60988452328071680952662,60988452328071712428173⟩,⟨41060256864846658927609,41060256864846690393577⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨65174122473429063202590,65174122473429072590821⟩,⟨29431089374236681898424,29431089374236691275127⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨60531511855498631399363,60531511855498633204346⟩,⟨13888476331669176943942,13888476331669178737775⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨49363919953116145381493,49363919953116145691449⟩,⟨182552006722446038104,182552006722446340975⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨35613982297324763187132,35613982297324763240357⟩,⟨(-8406579997369763963097),(-8406579997369763913390)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨22885738130656338679765,22885738130656338696173⟩,⟨(-11632393805953165767653),(-11632393805953165752374)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨13177710518310721283404,13177710518310721291563⟩,⟨(-11133614347131541364065),(-11133614347131541355756)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨6820789153210379573685,6820789153210379578085⟩,⟨(-8900564706592887192780),(-8900564706592887187724)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨3160996734776743442920,3160996734776743445243⟩,⟨(-6356874253655888225902),(-6356874253655888222865)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨1286218250017694372991,1286218250017694374175⟩,⟨(-4185461238864072738320),(-4185461238864072736537)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨436131826055187660597,436131826055187661182⟩,⟨(-2546837863270864542005),(-2546837863270864541001)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨109180332988545136369,109180332988545136637⟩,⟨(-1348953402989649354742),(-1348953402989649354233)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨14851147673339459003,14851147673339459092⟩,⟨(-419976532874524892761),(-419976532874524892597)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-126398824113664896837156),(-126398824113662544525625)⟩,⟨(-188940717708380288868868),(-188940717708377936567141)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-386941816098107567742515),(-386941816098099014010254)⟩,⟨(-505659753928876008171430),(-505659753928867454462494)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-652138335046288221640372),(-652138335046268264866139)⟩,⟨(-660541548366165129933070),(-660541548366145173180835)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-880970138122788566060134),(-880970138122746877105933)⟩,⟨(-613442077731826363813427),(-613442077731784674863143)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-1010328281951735468945870),(-1010328281951658013880767)⟩,⟨(-399802876030707135078228),(-399802876030629679987901)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-996462964248522275962369),(-996462964248401853404893)⟩,⟨(-111099132967606468442514),(-111099132967486045829553)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-847634684590258028671932),(-847634684590113129789860)⟩,⟨150927585359058392848069,150927585359203291807221⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-620299823089700666890877),(-620299823089574742828539)⟩,⟨318554867222229359385858,318554867222355283534191⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-385353062229762533827637),(-385353062229667775625130)⟩,⟨376674313256010602525001,376674313256105360795839⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-194440948430233904066130),(-194440948430170175131167)⟩,⟨351247397689992246016290,351247397690055974989588⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-67175580696054916395177),(-67175580696023152818823)⟩,⟨282971893780639059823003,282971893780670823417093⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨1907729469892973805125,1907729469905789700150⟩,⟨205626705184639815835488,205626705184652631735977⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨29405382368618637926521,29405382368623250396472⟩,⟨137777896772030677187183,137777896772035289656619⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨32233051819398635078370,32233051819400236207503⟩,⟨84964724142612091283262,84964724142613692409915⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨22696174207945928437995,22696174207946476293188⟩,⟨45358369162558056622648,45358369162558604475646⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨8007868939907197278871,8007868939907331216081⟩,⟨14167986768481176711360,14167986768481310647736⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨17685006992194595369242,17685006992194595606086⟩,⟨781583103965376759163557,781583103965376759518318⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨247832043559718538607420,247832043559718539351169⟩,⟨2207863922015310368083406,2207863922015310369144158⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨938731402184200588548691,938731402184200589872351⟩,⟨3227524700146170855051003,3227524700146170856782884⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨2050335019276076388745061,2050335019276076390696411⟩,⟨3616908276678138190411610,3616908276678138192741364⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨3235711073359208406680968,3235711073359208409225110⟩,⟨3273645229294978079631411,3273645229294978082437539⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨4050279866473218036539326,4050279866473218039597985⟩,⟨2291761718928048563107470,2291761718928048566294196⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨4219242495713273472193104,4219242495713273475919035⟩,⟨973393403334860449370348,973393403334860453115801⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨3755205956581621798205525,3755205956581621804479705⟩,⟨(-283171091586827960517588),(-283171091586827954279521)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨2891214782686691877926212,2891214782686691899463655⟩,⟨(-1171205586727839719812591),(-1171205586727839698312691)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨1928182748837425351809810,1928182748837425450577309⟩,⟨(-1588066945253404158981537),(-1588066945253404060221808)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨1099725771623411347317521,1099725771623411722045796⟩,⟨(-1609021329331176066919279),(-1609021329331175692166356)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨514017982659652192092738,514017982659653457144938⟩,⟨(-1386329203478489367774970),(-1386329203478488102689354)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨170354322913930553574915,170354322913933483029583⟩,⟨(-1060798015299772304872963),(-1060798015299769375391666)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨10728091692591601417431,10728091692596051639147⟩,⟨(-723184513295188116228594),(-723184513295183665990120)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-33158263381069998369647),(-33158263381065753861941)⟩,⟨(-413247230562158055601167),(-413247230562153811084949)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-17098622361183428113211),(-17098622361181671759077)⟩,⟨(-133619924295198248330799),(-133619924295196491974138)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨3234938535853762321380250,3234938535853890086675900⟩,⟨1266934740062624884416694,1266934740062752650032155⟩⟩
lemma checked : cachedMomentRuleBox density0 hk4_0_14 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false false 4 14) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk4_0_14 (tableDensity false) (fullFactor false 4 14) density0_contains hk4_0_14_contains
noncomputable def atomAnswer : CBox := ⟨⟨2503702050025207529197179,2503702050025207529537816⟩,⟨358945403537214847293683,358945403537214847508857⟩⟩
lemma atomChecked : tableAtomBox false ha4_0_14 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false false 4 14) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false false ha4_0_14 4 14 ha4_0_14_contains
 def realAnswer : RBox := ⟨5738640585878969750577429,5738640585879097716213716⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false false 4 14) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm4_0_0_14
namespace hm4_1_0_14
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk4_0_14 j i k))
noncomputable def s0_0 : CBox := ⟨⟨26704043214233,26704043214249⟩,⟨(-8080235329618),(-8080235329602)⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨60185154464368,60185154464384⟩,⟨(-21021677111016),(-21021677111000)⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨55688111181887,55688111181903⟩,⟨(-24773278068548),(-24773278068532)⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨30991714543433,30991714543449⟩,⟨(-18651013141307),(-18651013141289)⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨10787921140145,10787921140161⟩,⟨(-9307748695921),(-9307748695905)⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨2244000355968,2244000355985⟩,⟨(-3054191522823),(-3054191522807)⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨238347641760,238347641777⟩,⟨(-639594237031),(-639594237015)⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨4173889919,4173889935⟩,⟨(-81417812684),(-81417812668)⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-1511942739),(-1511942722)⟩,⟨(-5881407248),(-5881407232)⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-128044068),(-128044052)⟩,⟨(-218715111),(-218715095)⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-3540979),(-3540963)⟩,⟨(-3620906),(-3620889)⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-32019),(-32000)⟩,⟨(-21201),(-21185)⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-80),(-63)⟩,⟨(-42),(-26)⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-293382677280401812),(-293382677280400482)⟩,⟨221319052926227634,221319052926228966⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-719100511159808249),(-719100511159803842)⟩,⟨608476872584918385,608476872584922795⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-789378440172765535),(-789378440172756851)⟩,⟨836163846077257655,836163846077266341⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-567431890658320407),(-567431890658306268)⟩,⟨847260100673018614,847260100673032755⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-266245915730032191),(-266245915730013253)⟩,⟨677197565848774938,677197565848793875⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-53713175202510794),(-53713175202491102)⟩,⟨435403204584448082,435403204584467779⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨34043028723256801,34043028723271615⟩,⟨227095166035259015,227095166035273829⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨43973533812904866,43973533812912419⟩,⟨96697399632057828,96697399632065379⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨28613893556875198,28613893556878271⟩,⟨33797087706082781,33797087706085856⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨14060904294369896,14060904294370998⟩,⟨9687983283927413,9687983283928513⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨5879321409270605,5879321409270901⟩,⟨2214436741916019,2214436741916315⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨2251147573630547,2251147573630623⟩,⟨342215123923291,342215123923364⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨836309947750895,836309947750921⟩,⟨(-14314372237231),(-14314372237206)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨313602085061971,313602085061989⟩,⟨(-44925760178951),(-44925760178932)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨116523374717783,116523374717800⟩,⟨(-26757735709522),(-26757735709505)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨30056026363572,30056026363588⟩,⟨(-8242369203424),(-8242369203408)⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨59404809802529746082,59404809802529746143⟩,⟨(-95248809599849472451),(-95248809599849472382)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨149210735590796890809,149210735590796890956⟩,⟨(-267140207201310097542),(-267140207201310097381)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨170121425294055478940,170121425294055479153⟩,⟨(-383803074239701122171),(-383803074239701121942)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨123128439112769301467,123128439112769301720⟩,⟨(-418996651798235153875),(-418996651798235153610)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨43227349313851395666,43227349313851395918⟩,⟨(-373356717724590668281),(-373356717724590668019)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-27284668886829046427),(-27284668886829046202)⟩,⟨(-277699058489440010720),(-277699058489440010495)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-64047610198804382421),(-64047610198804382235)⟩,⟨(-173843500974942549673),(-173843500974942549486)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-67785476741407098202),(-67785476741407098023)⟩,⟨(-91429248845055324831),(-91429248845055324658)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-53302609217601309433),(-53302609217601309113)⟩,⟨(-39623570446235393359),(-39623570446235393041)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-34989932894100412975),(-34989932894100412054)⟩,⟨(-13163920443732057565),(-13163920443732056647)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-20313433518335258287),(-20313433518335255825)⟩,⟨(-2260097262807046312),(-2260097262807043852)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-10839076602092899171),(-10839076602092893071)⟩,⟨1110297347342678624,1110297347342684719⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-5465272919788390965),(-5465272919788380129)⟩,⟨1577532913768070537,1577532913768081368⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-2637090487269415858),(-2637090487269402591)⟩,⟨1201683101591803694,1201683101591816959⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-1170699099690363413),(-1170699099690352564)⟩,⟨694829315315142442,694829315315153292⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-330859370553452403),(-330859370553448253)⟩,⟨223380939070073843,223380939070077991⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨349887064498984793455,349887064499013802074⟩,⟨5358684586020686449210,5358684586020715457960⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨1621661107496905609227,1621661107496968615437⟩,⟨14693564227293860943591,14693564227293923950215⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨4128484105959733502626,4128484105959787277035⟩,⟨20361238392325942134910,20361238392325995910042⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨7482609511878309250967,7482609511878335577876⟩,⟨21405614897073582619656,21405614897073608947550⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨10490214971194066272943,10490214971194074093333⟩,⟨18475900497787809426331,18475900497787817247840⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨11967105643915614855688,11967105643915616343352⟩,⟨13348459633607739485493,13348459633607740974155⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨11490197286923960461332,11490197286923960707249⟩,⟨7964899899253799373216,7964899899253799619715⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨9534661581387118701444,9534661581387118737562⟩,⟨3653230111013140589432,3653230111013140625811⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨6998483704636044478533,6998483704636044487026⟩,⟨889478552716914116805,889478552716914125374⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨4641518924306014864104,4641518924306014867909⟩,⟨(-500895467267905648467),(-500895467267905644671)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨2837934792791903768595,2837934792791903770676⟩,⟨(-971617130394136677196),(-971617130394136675147)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨1629869086431421020040,1629869086431421021197⟩,⟨(-959234657014478439167),(-959234657014478438037)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨891968637143300696753,891968637143300697388⟩,⟨(-757335040126479321712),(-757335040126479321099)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨465260880112507353567,465260880112507353906⟩,⟨(-516981090762483850026),(-516981090762483849699)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨219594515569545817336,219594515569545817507⟩,⟨(-294014857063474599467),(-294014857063474599304)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨64193035836357621925,64193035836357621988⟩,⟨(-94761094171882786923),(-94761094171882786864)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-44651942408137879297652),(-44651942408135946078450)⟩,⟨(-59870439802037190774918),(-59870439802035257552260)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-136804911945760949355485),(-136804911945753919056881)⟩,⟨(-163886875345916471515306),(-163886875345909441208341)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-230565150702118069539680),(-230565150702101664900065)⟩,⟨(-224202528094359485278116),(-224202528094343080630553)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-311406602106308037887012),(-311406602106273763715312)⟩,⟨(-224512840315082578553652),(-224512840315048304380310)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-358791746626688547522752),(-358791746626624860754901)⟩,⟨(-167531540111031262051465),(-167531540110967575291915)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-359939783076932773859411),(-359939783076833757347834)⟩,⟨(-76282544004488580640373),(-76282544004389564146766)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-317640082034797928963848),(-317640082034678811584445)⟩,⟨16159739968243248884250,16159739968362366239217⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-248074495515744007129384),(-248074495515640537726578)⟩,⟨83239132584016604831529,83239132584120074208261⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-172193487453261497848412),(-172193487453183699969706)⟩,⟨114983037528301058436771,114983037528378856296228⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-106534546604832836050532),(-106534546604780569031188)⟩,⟨116382148759214455230313,116382148759266722239832⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-58680748166958723292645),(-58680748166932705392926)⟩,⟨99356817267047537417528,99356817267073555313084⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-28376027647023191425873),(-28376027647012707886843)⟩,⟨75419659881147114372522,75419659881157597910319⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-11465353517170328436023),(-11465353517166560201740)⟩,⟨52156875308367833742575,52156875308371601976956⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-3314053737027561605219),(-3314053737026254931825)⟩,⟨32875581612237864789083,32875581612239171462974⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-283490337319323211938),(-283490337318876446994)⟩,⟨17805263307535558218388,17805263307536004983755⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨164349850187069767252,164349850187178948208⟩,⟨5603352023960586788806,5603352023960695969920⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨1627589659748063621749,1627589659748063753735⟩,⟨23190465566186608954690,23190465566186609148093⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨22929415343486174642587,22929415343486175056408⟩,⟨60667992474288570817932,60667992474288571400646⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨88999547474235405521597,88999547474235406256486⟩,⟨50032856088024936883341,50032856088024937842098⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨206665929894467156376846,206665929894467157465328⟩,⟨(-76046168871642901645965),(-76046168871642900341993)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨359695934847573139877378,359695934847573141342757⟩,⟨(-353866600209446398031648),(-353866600209446396406965)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨499555769316715079895084,499555769316715081765380⟩,⟨(-727846749854802663203541),(-727846749854802661248999)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨555806728403580266308185,555806728403580268813560⟩,⟨(-1076236270372575191462472),(-1076236270372575188943872)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨488708116599031050580238,488708116599031055346684⟩,⟨(-1292820913318638313042009),(-1292820913318638308307188)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨324063915232754510728042,324063915232754528199065⟩,⟨(-1334558847379231862286673),(-1334558847379231844857884)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨128189164558379929744477,128189164558380010482279⟩,⟨(-1220785070510229300308733),(-1220785070510229219600909)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-38075962064778584285641),(-38075962064778278201796)⟩,⟨(-1008853499985789070445527),(-1008853499985788764374109)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-143360534012634601569854),(-143360534012633568433142)⟩,⟨(-763838703315361101651521),(-763838703315360068516407)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-183217852230984235036632),(-183217852230981841774554)⟩,⟨(-534510186104538164729754),(-534510186104535771465931)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-168283674154107865625038),(-168283674154104228248923)⟩,⟨(-343017645383108020947448),(-343017645383104383569334)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-115131129083610426718859),(-115131129083606956186090)⟩,⟨(-189008060402623510089115),(-189008060402620039555048)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-40600326774926543412704),(-40600326774925107039113)⟩,⟨(-60105844535367541779806),(-60105844535366105405769)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-54319571181525720320719),(-54319571181420770420772)⟩,⟨(-1508329989290956347597210),(-1508329989290851397575504)⟩⟩
lemma checked : cachedMomentRuleBox density1 hk4_0_14 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true false 4 14) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk4_0_14 (tableDensity true) (fullFactor false 4 14) density1_contains hk4_0_14_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-3274071911571425230934067),(-3274071911571425230488618)⟩,⟨(-469390143087127108280813),(-469390143087127107999431)⟩⟩
lemma atomChecked : tableAtomBox true ha4_0_14 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true false 4 14) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true false ha4_0_14 4 14 ha4_0_14_contains
 def realAnswer : RBox := ⟨(-3328391482752951051254786),(-3328391482752845900909390)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true false 4 14) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm4_1_0_14
namespace hm4_0_0_15
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk4_0_15 j i k))
noncomputable def s0_0 : CBox := ⟨⟨2342828884043,2342828884059⟩,⟨5161393098505,5161393098521⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨5797723454434,5797723454450⟩,⟨11254397975315,11254397975331⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨6308224634919,6308224634937⟩,⟨9779202451301,9779202451317⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨4314912295821,4314912295840⟩,⟨4988160875233,4988160875251⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨1923626696786,1923626696806⟩,⟨1560590613847,1560590613865⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨551344576114,551344576131⟩,⟨285690398806,285690398824⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨98392502259,98392502280⟩,⟨25602066780,25602066797⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨10418097672,10418097690⟩,⟨183295536,183295556⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨610320072,610320091⟩,⟨(-140170641),(-140170621)⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨17865079,17865098⟩,⟨(-9019144),(-9019124)⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨224288,224306⟩,⟨(-188631),(-188613)⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨941,959⟩,⟨(-1236),(-1217)⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-149243286766751141),(-149243286766751014)⟩,⟨(-68238391111589167),(-68238391111589040)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-391289012081183086),(-391289012081182701)⟩,⟨(-158530168108448766),(-158530168108448380)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-494669524672243388),(-494669524672242661)⟩,⟨(-152330932696240391),(-152330932696239662)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-451443272675416155),(-451443272675415010)⟩,⟨(-79025797306551407),(-79025797306550264)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-321619021045700411),(-321619021045698943)⟩,⟨(-4128828946294012),(-4128828946292538)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-183470013588292909),(-183470013588291446)⟩,⟨32897519549602267,32897519549603725⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-84730313308463373),(-84730313308462326)⟩,⟨34914631230130521,34914631230131568⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-31872056726349644),(-31872056726349130)⟩,⟨22719459959160609,22719459959161121⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-9781952865390534),(-9781952865390327)⟩,⟨11214796674629782,11214796674629990⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-2420727047498483),(-2420727047498404)⟩,⟨4578481622048859,4578481622048940⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-450541679103577),(-450541679103546)⟩,⟨1644874981150071,1644874981150103⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-37538235976067),(-37538235976046)⟩,⟨551065508064749,551065508064770⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨19044626111231,19044626111249⟩,⟨182164852158506,182164852158524⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨15301969429314,15301969429330⟩,⟨62089182772827,62089182772843⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨7562064168417,7562064168433⟩,⟨21548210895368,21548210895384⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨2184114952759,2184114952775⟩,⟨5363048299645,5363048299662⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨51985136478180797774,51985136478180797804⟩,⟨314410078191727460,314410078191727484⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨140486734463169239042,140486734463169239101⟩,⟨(-6544517664265078438),(-6544517664265078399)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨188876390498771430677,188876390498771430756⟩,⟨(-28442514625243543568),(-28442514625243543516)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨189224583433151729790,189224583433151729874⟩,⟨(-58017108089188261464),(-58017108089188261403)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨152373807136741347312,152373807136741347390⟩,⟨(-79830451350916259590),(-79830451350916259527)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨100197675212484299708,100197675212484299773⟩,⟨(-83633034112656146270),(-83633034112656146214)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨53060496374455789472,53060496374455789522⟩,⟨(-70848730995409062342),(-70848730995409062291)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨21231437542946083084,21231437542946083129⟩,⟨(-50435314539483805042),(-50435314539483804997)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨4700980601328211145,4700980601328211201⟩,⟨(-31093776526843224369),(-31093776526843224315)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-1607266899521519160),(-1607266899521519050)⟩,⟨(-17068268768193449501),(-17068268768193449385)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-2884704688249264536),(-2884704688249264283)⟩,⟨(-8578595917792725728),(-8578595917792725472)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-2390904202350361584),(-2390904202350361000)⟩,⟨(-4061885365626620197),(-4061885365626619611)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-1590797429717367189),(-1590797429717366195)⟩,⟨(-1859937223879146638),(-1859937223879145641)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-938333444021268662),(-938333444021267479)⟩,⟨(-834651783310322701),(-834651783310321517)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-479665216045257999),(-479665216045257047)⟩,⟨(-352959378232654505),(-352959378232653552)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-146128273041748193),(-146128273041747822)⟩,⟨(-97335358988503437),(-97335358988503065)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-1704985825522708527077),(-1704985825522703711972)⟩,⟨1453358037299167841869,1453358037299172657140⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-4545100970958602044286),(-4545100970958591626174)⟩,⟨4261463832791227947137,4261463832791238365779⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-5921015738902392502197),(-5921015738902383677299)⟩,⟨6677190617782768952967,6677190617782777778795⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-5570930650564512254675),(-5570930650564507980986)⟩,⟨8271100165879386497993,8271100165879390772988⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-3924277751672261669464),(-3924277751672260417245)⟩,⟨8683084783526458551373,8683084783526459805146⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-1814769112762167244656),(-1814769112762167009999)⟩,⟨7894687878766986883459,7894687878766987119592⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-26338934056042569777),(-26338934056042531069)⟩,⟨6284235332312218232535,6284235332312218272155⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨1039799396336299666190,1039799396336299672395⟩,⟨4415793332454318756628,4415793332454318763278⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨1401019594477729398908,1401019594477729400776⟩,⟨2760160185990145154356,2760160185990145156364⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨1304371445010728601449,1304371445010728602448⟩,⟨1545472695402984128244,1545472695402984129224⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨1014943344838751229838,1014943344838751230434⟩,⟨778503605712836307104,778503605712836307624⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨706899034901372358609,706899034901372358965⟩,⟨351818588339988676610,351818588339988676885⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨455315787737979840517,455315787737979840728⟩,⟨140041340349271926082,140041340349271926228⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨272202164706691669176,272202164706691669302⟩,⟨46651109861824444401,46651109861824444478⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨142397089201157435501,142397089201157435570⟩,⟨11532688288772765673,11532688288772765719⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨44050629926540226957,44050629926540226991⟩,⟨1557975589300761014,1557975589300761040⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨32945007175969705197316,32945007175970115350848⟩,⟨(-22039526678733916028486),(-22039526678733505873287)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨87840284513391503515905,87840284513392989099940⟩,⟨(-67210934897790433993063),(-67210934897788948405075)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨113901598101502661749983,113901598101506101152154⟩,⟨(-112425068237006834457118),(-112425068237003395051237)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨104648302140471182632020,104648302140478287499171⟩,⟨(-150214836415048560165571),(-150214836415041455297760)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨67280073223389479549812,67280073223402493141740⟩,⟨(-169857253289202160124992),(-169857253289189146537224)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨18437239202748092645096,18437239202767987835069⟩,⟨(-164731417008786954712539),(-164731417008767059531601)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-24410608255102962665901),(-24410608255079470425048)⟩,⟨(-137488518662956861658551),(-137488518662933369430052)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-50551191904754276962723),(-50551191904734270012339)⟩,⟨(-98564752866192653744837),(-98564752866172646808000)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-58521901017001383980662),(-58521901016986655227272)⟩,⟨(-59935019862149694730086),(-59935019862134965987271)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-53411835886822310469020),(-53411835886812612463216)⟩,⟨(-29602664604636405507904),(-29602664604626707507927)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-42144178328805863508356),(-42144178328801128498276)⟩,⟨(-10024111531294194640733),(-10024111531289459633306)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-30043053428002402140154),(-30043053428000527962518)⟩,⟨268683647501962676462,268683647503836853295⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-19797144659233463708905),(-19797144659232800449606)⟩,⟨4220643587886017572551,4220643587886680831926⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-12046609872317406593859),(-12046609872317179470984)⟩,⟨4568478765607828968628,4568478765608056091857⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-6371368489481632390153),(-6371368489481555419070)⟩,⟨3187718531111927270239,3187718531112004241629⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-1980611695904896609833),(-1980611695904877885729)⟩,⟨1119445922385538249198,1119445922385556973420⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-163564032722149798553056),(-163564032722149798478280)⟩,⟨3700004099647985795923,3700004099647985845514⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-460591228123305140317910),(-460591228123305140095129)⟩,⟨51676584678416614894805,51676584678416615050130⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-669141931213957174385164),(-669141931213957174023854)⟩,⟨194523289021176348630561,194523289021176348905583⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-743112125631871367862438),(-743112125631871367381030)⟩,⟨421031873918273082843363,421031873918273083245572⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-664837681748356138375354),(-664837681748356137802508)⟩,⟨656745416893528321845732,656745416893528322364406⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-459118025896471470134599),(-459118025896471469493441)⟩,⟨810738914961658130724013,810738914961658131339072⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-192171425751748158125644),(-192171425751748157384812)⟩,⟨831426505305376428240347,831426505305376428977254⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨54534329487071760352512,54534329487071761562001⟩,⟨727565059895086322887693,727565059895086324104228⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨222670563373967446471551,222670563373967450555950⟩,⟨550408557982289998048352,550408557982290002139851⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨296801182736447689198324,296801182736447707622520⟩,⟨360683456714583040374484,360683456714583058799884⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨295725516709081160836928,295725516709081229592024⟩,⟨202278131947979194407569,202278131947979263157706⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨250895808148521727369691,250895808148521955972317⟩,⟨93102710223803435546514,93102710223803664142701⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨189431511894108623846992,189431511894109146469819⟩,⟨30454172796233465226902,30454172796233987844697⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨127771534315594390875553,127771534315595176745044⟩,⟨1906928849829169521678,1906928849829955388052⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨72471036713361447139552,72471036713362191366048⟩,⟨(-5812535099611889861266),(-5812535099611145636336)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨23343529609295626047943,23343529609295932879315⟩,⟨(-2987057418159707845594),(-2987057418159401014687)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-284892313216316053625583),(-284892313216295456357943)⟩,⟨661974632540077014698408,661974632540097611901124⟩⟩
lemma checked : cachedMomentRuleBox density0 hk4_0_15 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false false 4 15) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk4_0_15 (tableDensity false) (fullFactor false 4 15) density0_contains hk4_0_15_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-62929618273591579401500),(-62929618273591579358805)⟩,⟨532130753182064536067187,532130753182064536137854⟩⟩
lemma atomChecked : tableAtomBox false ha4_0_15 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false false 4 15) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false false ha4_0_15 4 15 ha4_0_15_contains
 def realAnswer : RBox := ⟨(-347821931489907733027083),(-347821931489886935716748)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false false 4 15) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm4_0_0_15
namespace hm4_1_0_15
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk4_0_15 j i k))
noncomputable def s0_0 : CBox := ⟨⟨280713634117,280713634133⟩,⟨927778994280,927778994296⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨716682205564,716682205580⟩,⟨2052904373668,2052904373684⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨813347317242,813347317258⟩,⟨1830436937654,1830436937670⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨578429776843,578429776859⟩,⟨962989692423,962989692440⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨267197373940,267197373956⟩,⟨310598280856,310598280872⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨79403199350,79403199366⟩,⟨58613400784,58613400801⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨14701867370,14701867386⟩,⟨5528806660,5528806676⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨1610440999,1610441015⟩,⟨88095001,88095017⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨97001916,97001933⟩,⟨(-24581304),(-24581287)⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨2895985,2896002⟩,⟨(-1683395),(-1683377)⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨36700,36716⟩,⟨(-35722),(-35705)⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨148,164⟩,⟨(-240),(-224)⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-15414151582192164),(-15414151582192056)⟩,⟨(-20433634356076852),(-20433634356076744)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-41979538185112645),(-41979538185112327)⟩,⟨(-49621935903911875),(-49621935903911555)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-56615230895864656),(-56615230895864055)⟩,⟨(-53477612562411151),(-53477612562410548)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-55792320162141927),(-55792320162140981)⟩,⟨(-37408642242854811),(-37408642242853866)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-42994410497550347),(-42994410497549131)⟩,⟨(-16944322415976566),(-16944322415975347)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-26434234842323410),(-26434234842322201)⟩,⟨(-3290101024066581),(-3290101024065370)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-13085935061789130),(-13085935061788265)⟩,⟨1944526984950814,1944526984951682⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-5254142907215145),(-5254142907214720)⟩,⟨2380423147943245,2380423147943670⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-1722737075851393),(-1722737075851221)⟩,⟨1454239377946932,1454239377947106⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-461755040793237),(-461755040793168)⟩,⟨668179508483476,668179508483545⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-98632013588341),(-98632013588312)⟩,⟨260901316545396,260901316545425⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-14299030093924),(-14299030093904)⟩,⟨93465370911883,93465370911900⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨538301137297,538301137313⟩,⟨32671348472493,32671348472510⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨1663442442712,1663442442728⟩,⟨11641212536069,11641212536086⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨956523536597,956523536615⟩,⟨4168067433934,4168067433950⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨289105604657,289105604673⟩,⟨1054297479999,1054297480015⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨9958555106747358936,9958555106747358957⟩,⟨6211046916870713527,6211046916870713552⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨27754577850795473727,27754577850795473757⟩,⟨15504367345740413897,15504367345740413927⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨39380853668896805749,39380853668896805788⟩,⟨17462642734224882972,17462642734224883009⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨42209826574062539895,42209826574062539934⟩,⟨12416474374870799765,12416474374870799803⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨36726047211067415542,36726047211067415583⟩,⟨4268167836213304187,4268167836213304228⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨26541724794163935660,26541724794163935695⟩,⟨(-2591229106916566518),(-2591229106916566481)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨16076343835184307331,16076343835184307364⟩,⟨(-5908241855808794000),(-5908241855808793967)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨8153834809830420094,8153834809830420124⟩,⟨(-6033577799566791820),(-6033577799566791791)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨3400715756674228756,3400715756674228801⟩,⟨(-4565711561513799431),(-4565711561513799389)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨1086784645066850232,1086784645066850325⟩,⟨(-2881136254804891640),(-2881136254804891551)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨180168396393372950,180168396393373159⟩,⟨(-1608832269121164543),(-1608832269121164334)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-84318534445386373),(-84318534445385895)⟩,⟨(-827635009010988032),(-827635009010987552)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-116446137119824320),(-116446137119823507)⟩,⟨(-404011599253545832),(-404011599253545019)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-86466495781595953),(-86466495781594984)⟩,⟨(-189868986857567114),(-189868986857566147)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-49089902954688268),(-49089902954687489)⟩,⟨(-82728618532661441),(-82728618532660659)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-15632496955497007),(-15632496955496702)⟩,⟨(-23154562410203735),(-23154562410203432)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-747322140763908492400),(-747322140763904446730)⟩,⟨48791875744770360493,48791875744774406147⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-2039531464081414384981),(-2039531464081405637466)⟩,⟨225010148490898255300,225010148490907002755⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-2800053125371058665569),(-2800053125371051265893)⟩,⟨567419163222106929494,567419163222114329072⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-2903741619071560495083),(-2903741619071556919235)⟩,⟨1014345009472917356489,1014345009472920932202⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-2462469330499864429419),(-2462469330499863384884)⟩,⟨1397057659850474575626,1397057659850475620008⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-1741867187087840199090),(-1741867187087840004353)⟩,⟨1560237932007311081304,1560237932007311275909⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-1014747770018980676872),(-1014747770018980645371)⟩,⟨1462285654795128388720,1462285654795128420147⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-453570384976808518077),(-453570384976808513534)⟩,⟨1181846683780244029660,1181846683780244034173⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-107718342946757512102),(-107718342946757511049)⟩,⟨843794786323368818327,843794786323368819373⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨58433315417893706062,58433315417893706523⟩,⟨544164940089491717452,544164940089491717916⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨110683863609163340157,110683863609163340405⟩,⟨323781757213836506395,323781757213836506648⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨106620790773005122308,106620790773005122448⟩,⟨181316098294517791544,181316098294517791691⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨82367535228528232704,82367535228528232789⟩,⟨97059931615691238557,97059931615691238640⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨55247912186971391293,55247912186971391342⟩,⟨49734795636241217002,49734795636241217054⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨31035295132002967172,31035295132002967203⟩,⟨23182289516911621276,23182289516911621307⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨9939286554473006782,9939286554473006801⟩,⟨6733156508293898288,6733156508293898311⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨10439404038908969531887,10439404038909306613632⟩,⟨(-7785733554320521876717),(-7785733554320184795589)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨28469011864786057306525,28469011864787278310199⟩,⟨(-23762701732295604538540),(-23762701732294383536354)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨38658943824628108471510,38658943824630935693544⟩,⟨(-39748185158144800739884),(-39748185158141973519252)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨38296186170501917888349,38296186170507759086007⟩,⟨(-53098107376670728616461),(-53098107376664887419092)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨28185344077347127148444,28185344077357827457357⟩,⟨(-60319629220295629766877),(-60319629220284929456541)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨12633580903123556901845,12633580903139915558519⟩,⟨(-59501524844950454168748),(-59501524844934095509046)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-2597472340334057977177),(-2597472340314745656563)⟩,⟨(-51517763397883176473994),(-51517763397863864149350)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-13203314032522920157650),(-13203314032506480824558)⟩,⟨(-39412781123059697569415),(-39412781123043258232113)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-17860948555554424186616),(-17860948555542331654296)⟩,⟨(-26774642368214565119648),(-26774642368202472584286)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-17695328725796994175917),(-17695328725789040386584)⟩,⟨(-16211109732981069677616),(-16211109732973115886767)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-14796373324489157008911),(-14796373324485278503703)⟩,⟨(-8745191488284774845077),(-8745191488280896339237)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-11018561121837354143989),(-11018561121835821044592)⟩,⟨(-4148608317813998798839),(-4148608317812465699261)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-7494115575348789804397),(-7494115575348247942843)⟩,⟨(-1648660049346422264840),(-1648660049345880403299)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-4661142487297994462583),(-4661142487297809108267)⟩,⟨(-470319106567117741529),(-470319106566932387285)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-2501041569516838261112),(-2501041569516775492414)⟩,⟨(-39917572664809133012),(-39917572664746364375)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-783319208443805380023),(-783319208443790116670)⟩,⟨22971663275186049222,22971663275201312551⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-4853139415819205954465),(-4853139415819205913963)⟩,⟨340519400668178556142,340519400668178583777⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-12657094674747380588428),(-12657094674747380466814)⟩,⟨4781098995283432765510,4781098995283432851864⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-10382064822716977024638),(-10382064822716976825823)⟩,⟨18441974588983970661132,18441974588983970813541⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨15587510490835795405182,15587510490835795673105⟩,⟨42435376879507455548189,42435376879507455771921⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨71773473771206140447594,71773473771206140777653⟩,⟨72998076660384935682676,72998076660384935980481⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨145618777538845163746359,145618777538845164138093⟩,⟨99983633125463708879027,99983633125463709253974⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨211985786734646534566150,211985786734646535062961⟩,⟨109519814652255922184977,109519814652255922679193⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨250374974457225754060092,250374974457225754976900⟩,⟨94695621232362622868828,94695621232362623791597⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨253949985506755410120909,253949985506755413431015⟩,⟨61717015922488281452821,61717015922488284770557⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨228246404707767710132577,228246404707767725188607⟩,⟨24013763137824418621897,24013763137824433682930⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨185459016317282886340695,185459016317282942494702⟩,⟨(-6962521902779185568926),(-6962521902779129413302)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨138256177276209146756271,138256177276209333444825⟩,⟨(-25922699811726011057544),(-25922699811725824369180)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨95456993922518417588348,95456993922518844548914⟩,⟨(-32705570314847346866413),(-32705570314846919906441)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨60606195240365977632038,60606195240366619957777⟩,⟨(-29726956716882954254585),(-29726956716882311929353)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨33146681469971231806542,33146681469971840324087⟩,⟨(-20189261396513725882606),(-20189261396513117365356)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨10500562173843288141105,10500562173843539072227⟩,⟨(-7092867859558902813516),(-7092867859558651882489)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨287255876480720171488576,287255876480737091165728⟩,⟨3787074558002330351465,3787074558019250002228⟩⟩
lemma checked : cachedMomentRuleBox density1 hk4_0_15 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true false 4 15) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk4_0_15 (tableDensity true) (fullFactor false 4 15) density1_contains hk4_0_15_contains
noncomputable def atomAnswer : CBox := ⟨⟨82292577742388988392283,82292577742388988448115⟩,⟨(-695863292622699778026424),(-695863292622699777934014)⟩⟩
lemma atomChecked : tableAtomBox true ha4_0_15 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true false 4 15) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true false ha4_0_15 4 15 ha4_0_15_contains
 def realAnswer : RBox := ⟨369548454223109059880859,369548454223126179613843⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true false 4 15) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm4_1_0_15
namespace hm4_0_0_16
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk4_0_16 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-168117096775),(-168117096759)⟩,⟨76306463451,76306463467⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-359936914100),(-359936914082)⟩,⟨185337256642,185337256661⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-301442584059),(-301442584043)⟩,⟨194237002402,194237002421⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-145388486319),(-145388486301)⟩,⟨125531856708,125531856726⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-42158103823),(-42158103803)⟩,⟨51817887220,51817887241⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-7004086638),(-7004086621)⟩,⟨13455818533,13455818554⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-557828669),(-557828651)⟩,⟨2124036164,2124036184⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-3905242),(-3905221)⟩,⟨193610030,193610050⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨2145905,2145921⟩,⟨9461101,9461122⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨111542,111561⟩,⟨222402,222423⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨1781,1799⟩,⟨2129,2146⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-4),20⟩,⟨3,20⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-16),16⟩,⟨0,16⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨0,16⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨0,16⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨0,16⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨4455697266539871,4455697266539896⟩,⟨(-9744763985938187),(-9744763985938165)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨10256824377470461,10256824377470504⟩,⟨(-25310378945539268),(-25310378945539226)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨9678693704655013,9678693704655076⟩,⟨(-31405999837002719),(-31405999837002657)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨4891565258919014,4891565258919100⟩,⟨(-27878271127629776),(-27878271127629688)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨257555618907878,257555618907984⟩,⟨(-19150815463850778),(-19150815463850671)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-1864418939435374),(-1864418939435272)⟩,⟨(-10447826370173752),(-10447826370173651)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-1881711656974408),(-1881711656974333)⟩,⟨(-4579855700527463),(-4579855700527389)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-1155188208758789),(-1155188208758747)⟩,⟨(-1624581267927138),(-1624581267927094)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-534961652281154),(-534961652281128)⟩,⟨(-467782899518454),(-467782899518427)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-204156704927988),(-204156704927967)⟩,⟨(-108260971901904),(-108260971901884)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-68483168267453),(-68483168267431)⟩,⟨(-18840125093809),(-18840125093789)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-21463206644550),(-21463206644532)⟩,⟨(-1482062415591),(-1482062415573)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-6674806047782),(-6674806047766)⟩,⟨693256403117,693256403133⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-2161372645620),(-2161372645603)⟩,⟨531752765508,531752765525⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-722694116524),(-722694116508)⟩,⟨253489726828,253489726844⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-176368310838),(-176368310821)⟩,⟨71822580611,71822580627⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-30854605383952667),(-30854605383952650)⟩,⟨5095531782046161415,5095531782046161434⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨636607416065233138,636607416065233156⟩,⟨13684242361635534004,13684242361635534025⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨2733164009925733834,2733164009925733851⟩,⟨18170642102318999201,18170642102318999225⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨5474346722084002455,5474346722084002476⟩,⟨17874146090316783980,17874146090316784007⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨7355649778600235619,7355649778600235638⟩,⟨14055269438690588525,14055269438690588550⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨7487617179344107936,7487617179344107960⟩,⟨8981378024789423179,8981378024789423201⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨6136989218974024097,6136989218974024117⟩,⟨4602889080235152506,4602889080235152528⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨4212587882754221634,4212587882754221653⟩,⟨1777213876182186948,1777213876182186970⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨2498577053712715648,2498577053712715667⟩,⟨379813567993897684,379813567993897705⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨1318272126080767548,1318272126080767574⟩,⟨(-123107299656253551),(-123107299656253524)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨637222533401315118,637222533401315152⟩,⟨(-213792076003783468),(-213792076003783432)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨290855245385672856,290855245385672915⟩,⟨(-170990264634920618),(-170990264634920561)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨128925377812236045,128925377812236132⟩,⟨(-110185899373215431),(-110185899373215346)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨56344690865812783,56344690865812879⟩,⟨(-63317234152027512),(-63317234152027414)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨23384305948634355,23384305948634432⟩,⟨(-31773518436024553),(-31773518436024474)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨6386120516955149,6386120516955189⟩,⟨(-9587208128972936),(-9587208128972892)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-190016149324156920004),(-190016149324156290407)⟩,⟨(-222916852673892750795),(-222916852673892121222)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-554508043769236324222),(-554508043769234968135)⟩,⟨(-591465507986802701368),(-591465507986801345356)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-860725629268122147637),(-860725629268121009047)⟩,⟨(-763422228535120024999),(-763422228535118886530)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-1051621465545662334448),(-1051621465545661790085)⟩,⟨(-708621358111119907349),(-708621358111119363153)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-1084571858802481216522),(-1084571858802481059532)⟩,⟨(-490566840987436440853),(-490566840987436284060)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-965336856703219939380),(-965336856703219910406)⟩,⟨(-222319030515123014318),(-222319030515122985525)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-750049951556373787323),(-750049951556373782560)⟩,⟨(-3513225687112655680),(-3513225687112651029)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-513328192685670165430),(-513328192685670164636)⟩,⟨120580417271302127447,120580417271302128186⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-312106815989045435830),(-312106815989045435584)⟩,⟨158204605699729184039,158204605699729184268⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-169934506091964839185),(-169934506091964839062)⟩,⟨143273438982329016229,143273438982329016355⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-83307199837346027780),(-83307199837346027711)⟩,⟨108508172114467823602,108508172114467823684⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-36711707261056827446),(-36711707261056827400)⟩,⟨73699194464698802054,73699194464698802106⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-14294959948539094816),(-14294959948539094783)⟩,⟨46437376154353765105,46437376154353765142⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-4678269667615567956),(-4678269667615567937)⟩,⟨27274783872608093474,27274783872608093500⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-1142065296822398993),(-1142065296822398974)⟩,⟨14092230516694911586,14092230516694911608⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-153226157125873079),(-153226157125873061)⟩,⟨4331625141179387272,4331625141179387289⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨3602739840181325557184,3602739840181392603217⟩,⟨5385487985863714555566,5385487985863781601334⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨10944770536756973359800,10944770536757215247382⟩,⟨14305450244913470894914,14305450244913712781869⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨18170254737634531562542,18170254737635087276009⟩,⟨18413396612606826673055,18413396612607382385937⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨24012732170021703425003,24012732170022838613677⟩,⟨16736623028953581162017,16736623028954716350586⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨26772310719594188139647,26772310719596238000421⟩,⟨10614675788979122545845,10614675788981172407258⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨25531418243647366338172,25531418243650447901664⟩,⟨2868516581810275625399,2868516581813357190271⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨20907880190201952145490,20907880190205522976012⟩,⟨(-3701448775866945173891),(-3701448775863374341514)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨14683488389573752317824,14683488389576732480826⟩,⟨(-7520835585625165757163),(-7520835585622185592156)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨8739582492905417830181,8739582492907564191752⟩,⟨(-8524311851220491601297),(-8524311851218345238191)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨4225335058427180110327,4225335058428563725421⟩,⟨(-7614647777460944324205),(-7614647777459560708280)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨1402376008587488691521,1402376008588150446930⟩,⟨(-5884612896278991593596),(-5884612896278329837816)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-35428133531096953584),(-35428133530839999913)⟩,⟨(-4115206850765687332175),(-4115206850765430378393)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-567949427527227619873),(-567949427527138204438)⟩,⟨(-2666889606850240067426),(-2666889606850150652002)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-607040557260668102232),(-607040557260637897655)⟩,⟨(-1601278863769911224355),(-1601278863769881019827)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-419739996007116702226),(-419739996007106563895)⟩,⟨(-839036958704721528735),(-839036958704711390445)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-146710353571503038484),(-146710353571500584454)⟩,⟨(-259574495688398307935),(-259574495688395853923)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-725722373356242056301),(-725722373356242046556)⟩,⟨(-32090155795003060288624),(-32090155795003060273841)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-10101878713547557107533),(-10101878713547557077114)⟩,⟨(-90080567853172091446253),(-90080567853172091402379)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-37789855763073932100738),(-37789855763073932047154)⟩,⟨(-130058987995214619377067),(-130058987995214619306398)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-81055101925917663766314),(-81055101925917663688584)⟩,⟨(-143135210894443933653470),(-143135210894443933560204)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-124968833374295180857610),(-124968833374295180758462)⟩,⟨(-126583460360336419560352),(-126583460360336419450709)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-152144562998485180683372),(-152144562998485180567412)⟩,⟨(-86230008899757732303700),(-86230008899757732182754)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-153601137568284194228680),(-153601137568284194092034)⟩,⟨(-35568765715601350674972),(-35568765715601350537583)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-132157634553213043253760),(-132157634553213043032603)⟩,⟨9845974815625607528388,9845974815625607748255⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-98236461276833403347009),(-98236461276833402618291)⟩,⟨39689430721159396980653,39689430721159397708110⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-63253771488093369679744),(-63253771488093366457171)⟩,⟨52004951033750508691359,52004951033750511913761⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-34881426235953690684561),(-34881426235953678859282)⟩,⟨50956167583111856003294,50956167583111867829503⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-15809749825689112922568),(-15809749825689074196085)⟩,⟨42569583216215390621226,42569583216215429348869⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-5104068489941065651439),(-5104068489940978242057)⟩,⟨31713804628044823718350,31713804628044911128619⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-317764054004325302724),(-317764054004195198911)⟩,⟨21163786888519461426688,21163786888519591531045⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨955238382647937459483,955238382648059795285⟩,⟨11914928154611028576827,11914928154611150912894⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨489212369515196470586,489212369515246723082⟩,⟨3823254723748794119842,3823254723748844372417⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-126340165832091011750036),(-126340165832087893022870)⟩,⟨(-59448604121993614728831),(-59448604121990495989236)⟩⟩
lemma checked : cachedMomentRuleBox density0 hk4_0_16 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false false 4 16) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk4_0_16 (tableDensity false) (fullFactor false 4 16) density0_contains hk4_0_16_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-105739889332786839577479),(-105739889332786839563658)⟩,⟨(-10333719027224876916946),(-10333719027224876908954)⟩⟩
lemma atomChecked : tableAtomBox false ha4_0_16 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false false 4 16) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false false ha4_0_16 4 16 ha4_0_16_contains
 def realAnswer : RBox := ⟨(-232080055164877951327515),(-232080055164874632586528)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false false 4 16) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm4_0_0_16
namespace hm4_1_0_16
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk4_0_16 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-30219457770),(-30219457754)⟩,⟨9142766397,9142766413⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-65652249196),(-65652249180)⟩,⟨22908023572,22908023588⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-56416051205),(-56416051189)⟩,⟨25039503392,25039503408⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-28063009643),(-28063009627)⟩,⟨16824457966,16824457982⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-8388842834),(-8388842818)⟩,⟨7195778254,7195778270⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-1436585529),(-1436585512)⟩,⟨1937242351,1937242367⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-120362626),(-120362610)⟩,⟨317262165,317262182⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-1735538),(-1735521)⟩,⟨29918675,29918691⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨375741,375757⟩,⟨1503324,1503340⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨20807,20823⟩,⟨36037,36053⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨330,346⟩,⟨341,357⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-8),16⟩,⟨0,16⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-16),16⟩,⟨0,16⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨0,16⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨0,16⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨0,16⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨1334224393091722,1334224393091746⟩,⟨(-1006450816250357),(-1006450816250336)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨3210232727974682,3210232727974718⟩,⟨(-2715250946434894),(-2715250946434861)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨3396645140871694,3396645140871748⟩,⟨(-3593907018150795),(-3593907018150743)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨2312273355008542,2312273355008618⟩,⟨(-3444627148643070),(-3444627148642998)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨1011099029277006,1011099029277094⟩,⟨(-2559419753984101),(-2559419753984011)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨188950777971760,188950777971845⟩,⟨(-1504873569124052),(-1504873569123967)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-104152438564253),(-104152438564190)⟩,⟨(-707106808792148),(-707106808792083)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-120844819117377),(-120844819117339)⟩,⟨(-267728469023642),(-267728469023604)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-69314467623223),(-69314467623198)⟩,⟨(-82353098273965),(-82353098273943)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-29778978818852),(-29778978818834)⟩,⟨(-20640314144833),(-20640314144813)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-10858180842004),(-10858180841987)⟩,⟨(-4119923348395),(-4119923348377)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-3639232083201),(-3639232083185)⟩,⟨(-560265143738),(-560265143722)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-1196867550213),(-1196867550197)⟩,⟨18957501681,18957501698⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-405186988743),(-405186988725)⟩,⟨57750868806,57750868822⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-139783283835),(-139783283819)⟩,⟨32058334188,32058334204⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-34671236133),(-34671236117)⟩,⟨9506825290,9506825306⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-608807025574087408),(-608807025574087392)⟩,⟨976123460387146336,976123460387146352⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-1510367334469124613),(-1510367334469124594)⟩,⟨2703364217408025878,2703364217408025895⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-1680509531584223613),(-1680509531584223594)⟩,⟨3788279090489696174,3788279090489696193⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-1173884748327670412),(-1173884748327670396)⟩,⟨3986617008111435595,3986617008111435612⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-395105919650528162),(-395105919650528145)⟩,⟨3387049295973595024,3387049295973595045⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨230720937918205222,230720937918205239⟩,⟨2378431069126197395,2378431069126197413⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨511009874070805587,511009874070805603⟩,⟨1393899886818337362,1393899886818337380⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨503543203181347796,503543203181347814⟩,⟨681805918624696059,681805918624696078⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨366687529068705828,366687529068705847⟩,⟨273660566392275699,273660566392275716⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨222439559434526986,222439559434527006⟩,⟨84124877490086066,84124877490086087⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨119470596661787916,119470596661787947⟩,⟨13465707989781449,13465707989781481⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨59251493865507012,59251493865507061⟩,⟨(-6003609343873899),(-6003609343873854)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨28001272514095520,28001272514095593⟩,⟨(-8058863882636456),(-8058863882636384)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨12816582493086686,12816582493086765⟩,⟨(-5833041899492061),(-5833041899491981)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨5480808464294945,5480808464295009⟩,⟨(-3251506333165068),(-3251506333165001)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨1519154051897243,1519154051897280⟩,⟨(-1025611055390078),(-1025611055390046)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-6378794688818214829),(-6378794688817685858)⟩,⟨(-97707744317280088697),(-97707744317279559724)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-29269626918309890998),(-29269626918308752432)⟩,⟨(-265403584230256954814),(-265403584230255816243)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-73112819579843939117),(-73112819579842984519)⟩,⟨(-360997817764892363272),(-360997817764891408664)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-128913601546941575663),(-128913601546941120342)⟩,⟨(-369290970337352258681),(-369290970337351803344)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-174433418566616801555),(-174433418566616670783)⟩,⟨(-307695669091543888896),(-307695669091543758108)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-190714207408105248291),(-190714207408105224414)⟩,⟨(-213102802327861531418),(-213102802327861507522)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-174474506773496323736),(-174474506773496319959)⟩,⟨(-121207719259789027911),(-121207719259789024123)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-137345775837573437407),(-137345775837573436863)⟩,⟨(-52796971160713424548),(-52796971160713424003)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-95382677656738991446),(-95382677656738991313)⟩,⟨(-12230189081334260595),(-12230189081334260461)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-59813621988550077821),(-59813621988550077753)⟩,⟨6390945444311969208,6390945444311969273⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-34633673519588654716),(-34633673519588654675)⟩,⟨11821418127911596534,11821418127911596577⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-18910867217616441674),(-18910867217616441644)⟩,⟨11110933056515488399,11110933056515488427⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-9901839205448582093),(-9901839205448582072)⟩,⟨8398654028518070602,8398654028518070622⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-4984293064061416277),(-4984293064061416258)⟩,⟨5535241315811271264,5535241315811271280⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-2294381425922823346),(-2294381425922823328)⟩,⟨3071262574865958573,3071262574865958591⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-662096278954254283),(-662096278954254266)⟩,⟨977354236708136918,977354236708136934⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨1272711966068181676754,1272711966068236777729⟩,⟨1706516036376374246338,1706516036376429347415⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨3869567227480607949022,3869567227480806755986⟩,⟨4636316386634121531223,4636316386634320338432⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨6424145512201385764307,6424145512201842565381⟩,⟨6249336104024647237259,6249336104025104038569⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨8488039150327521877117,8488039150328455161160⟩,⟨6124165536696218250779,6124165536697151534871⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨9507253187100315992632,9507253187102001472759⟩,⟨4445596341453107594114,4445596341454793074015⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨9221670222872934401487,9221670222875468193690⟩,⟨1961594693885143000863,1961594693887676792587⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨7833657720751116371522,7833657720754051856196⟩,⟨(-391399475620199361121),(-391399475617263877074)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨5870562993790139329722,5870562993792588078386⟩,⟨(-1963475782521402619006),(-1963475782518953870979)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨3903183856374331369424,3903183856376093569912⟩,⟨(-2601139847892851486259),(-2601139847891089286222)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨2312718355570930574015,2312718355572065344924⟩,⟨(-2522428256162724406205),(-2522428256161589635520)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨1221880591960935028052,1221880591961477081648⟩,⟨(-2065850631985761521811),(-2065850631985219468305)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨568638180445809766962,568638180446019958610⟩,⟨(-1509205065299969949184),(-1509205065299759757563)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨222256208564297815171,222256208564370864803⟩,⟨(-1009505497538680783767),(-1009505497538607734133)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨62575041437412936993,62575041437437586830⟩,⟨(-619565527679754096339),(-619565527679729446491)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨5269390814789742103,5269390814798009712⟩,⟨(-329356695187387366150),(-329356695187379098531)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-3010142423176669122),(-3010142423174668682)⟩,⟨(-102659968883969309077),(-102659968883967308634)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-66789798943095609138),(-66789798943095603708)⟩,⟨(-952154525404447736183),(-952154525404447728221)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-934618755155212873248),(-934618755155212856345)⟩,⟨(-2475600243662429619778),(-2475600243662429595973)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-3582617218137054602641),(-3582617218137054572997)⟩,⟨(-2019692164463573507702),(-2019692164463573469039)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-8168879064633852620354),(-8168879064633852577229)⟩,⟨2995363682911979640135,2995363682911979691756⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-13888797283573358283318),(-13888797283573358226569)⟩,⟨13647886833553513455052,13647886833553513517925⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-18760882484186158671915),(-18760882484186158601436)⟩,⟨27313297309849239350531,27313297309849239424148⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-20232183976692157876224),(-20232183976692157784814)⟩,⟨39145966345727880055175,39145966345727880147064⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-17202537926953754487392),(-17202537926953754319898)⟩,⟨45459624289132233719894,45459624289132233886340⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-11019492940020273809585),(-11019492940020273218901)⟩,⟨45304510690761567359716,45304510690761567949111⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-4217446492187150481907),(-4217446492187147847908)⟩,⟨40008381751394111002894,40008381751394113636121⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨1193580598643537363551,1193580598643547022434⟩,⟨31963090380571443145288,31963090380571452804006⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨4394500657708827100645,4394500657708858727445⟩,⟨23460992625674919019445,23460992625674950646360⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨5473337456424933221443,5473337456425004631685⟩,⟨15982183459130857704800,15982183459130929115192⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨4923038020079145753809,4923038020079252093656⟩,⟨10039032393588244161644,10039032393588350501598⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨3319101471877572385447,3319101471877672413568⟩,⟨5449695235403614013535,5449695235403714041719⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨1161677606502241064439,1161677606502282161696⟩,⟨1719807372556531460331,1719807372556572557609⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-2995402248043707726154),(-2995402248041145761454)⟩,⟨51219637144977674717168,51219637144980236687162⟩⟩
lemma checked : cachedMomentRuleBox density1 hk4_0_16 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true false 4 16) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk4_0_16 (tableDensity true) (fullFactor false 4 16) density1_contains hk4_0_16_contains
noncomputable def atomAnswer : CBox := ⟨⟨138275239896721251737092,138275239896721251755164⟩,⟨13513324881755608265555,13513324881755608276007⟩⟩
lemma atomChecked : tableAtomBox true ha4_0_16 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true false 4 16) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true false ha4_0_16 4 16 ha4_0_16_contains
 def realAnswer : RBox := ⟨135279837648677444010938,135279837648680205993710⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true false 4 16) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm4_1_0_16
namespace hm4_0_0_17
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk4_0_17 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-2339141470),(-2339141453)⟩,⟨(-5153843533),(-5153843517)⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-5576599359),(-5576599342)⟩,⟨(-10835071199),(-10835071183)⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-5630063451),(-5630063433)⟩,⟨(-8747030358),(-8747030341)⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-3438557975),(-3438557959)⟩,⟨(-3989825740),(-3989825722)⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-1314594508),(-1314594491)⟩,⟨(-1072529879),(-1072529862)⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-309378615),(-309378596)⟩,⟨(-161754210),(-161754194)⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-43213355),(-43213334)⟩,⟨(-11450753),(-11450736)⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-3392367),(-3392348)⟩,⟨(-76824),(-76807)⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-138347),(-138329)⟩,⟨30994,31013⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-2622),(-2603)⟩,⟨1292,1311⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-31),(-13)⟩,⟨7,28⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-16),0⟩,⟨(-16),16⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-16),0⟩,⟨(-16),16⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-16),0⟩,⟨(-16),16⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-16),0⟩,⟨(-16),16⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-16),0⟩,⟨(-16),16⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨598852323324539,598852323324558⟩,⟨273825863633725,273825863633742⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨1540913134992977,1540913134992995⟩,⟨624586199861658,624586199861675⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨1876728648197892,1876728648197913⟩,⟨578810322916094,578810322916114⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨1620459663193229,1620459663193254⟩,⟨284991898647404,284991898647428⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨1073408626265699,1073408626265720⟩,⟨15090234445685,15090234445707⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨560072079981646,560072079981669⟩,⟨(-99467245186409),(-99467245186386)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨233048677320745,233048677320768⟩,⟨(-95473893414953),(-95473893414933)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨77960793511816,77960793511834⟩,⟨(-55298959629612),(-55298959629593)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨21061118895486,21061118895504⟩,⟨(-24025943820746),(-24025943820728)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨4558481807121,4558481807141⟩,⟨(-8571167222537),(-8571167222517)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨741721151196,741721151217⟩,⟨(-2684504358877),(-2684504358858)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨55074778512,55074778529⟩,⟨(-787039124706),(-787039124687)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-23756887611),(-23756887594)⟩,⟨(-230245279065),(-230245279046)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-17394453835),(-17394453818)⟩,⟨(-70824049252),(-70824049236)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-7997957844),(-7997957828)⟩,⟨(-22813733207),(-22813733190)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-2222904779),(-2222904763)⟩,⟨(-5458882406),(-5458882389)⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-470079455994715888),(-470079455994715870)⟩,⟨(-2849799834125454),(-2849799834125438)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-1254528545891245750),(-1254528545891245734)⟩,⟨58282660691665414,58282660691665431⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-1645291332849218805),(-1645291332849218788)⟩,⟨247196876637570753,247196876637570770⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-1589134720718354509),(-1589134720718354490)⟩,⟨486178893237845182,486178893237845199⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-1220294883369191902),(-1220294883369191882)⟩,⟨637926271509572446,637926271509572463⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-757764833026012931),(-757764833026012913)⟩,⟨630980935749538466,630980935749538484⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-375840981205977940),(-375840981205977920)⟩,⟨500373813371438418,500373813371438439⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-140029463950100399),(-140029463950100380)⟩,⟨331196896181447026,331196896181447045⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-28884270742092795),(-28884270742092777)⟩,⟨188990082008158459,188990082008158475⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨8875356028516924,8875356028516944⟩,⟨95840158682462541,95840158682462560⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨14914358104161882,14914358104161901⟩,⟨44554160175284296,44554160175284316⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨11510513392279926,11510513392279946⟩,⟨19603767286852038,19603767286852057⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨7183550876826294,7183550876826317⟩,⟨8411629597202510,8411629597202531⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨4021386089460536,4021386089460557⟩,⟨3580054317994100,3580054317994127⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨1980936534986142,1980936534986161⟩,⟨1458150615577606,1458150615577628⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨592000324113994,592000324114012⟩,⟨394344211171648,394344211171667⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨27430662794383844746,27430662794383922235⟩,⟨(-23381893489461246797),(-23381893489461169309)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨72441630119134617190,72441630119134783319⟩,⟨(-67909385364651110449),(-67909385364650944309)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨92642311161713137233,92642311161713275477⟩,⟨(-104426737769577546823),(-104426737769577408566)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨84836139471181323485,84836139471181388718⟩,⟨(-125844975764080701182),(-125844975764080635927)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨57719353378835380203,57719353378835398691⟩,⟨(-127505183767251109862),(-127505183767251091346)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨25634220922046365999,25634220922046369338⟩,⟨(-111099745122247513262),(-111099745122247509902)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨436148434709497296,436148434709497836⟩,⟨(-84260230356728120901),(-84260230356728120350)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-13161362132691458378),(-13161362132691458281)⟩,⟨(-56166766330261388725),(-56166766330261388622)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-16814874254711116939),(-16814874254711116900)⟩,⟨(-33217853352240109620),(-33217853352240109576)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-14812526956579058640),(-14812526956579058612)⟩,⟨(-17587350209672393643),(-17587350209672393614)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-10918909644831862107),(-10918909644831862082)⟩,⟨(-8390736672604799432),(-8390736672604799410)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-7232017173182636955),(-7232017173182636934)⟩,⟨(-3605630328359978608),(-3605630328359978588)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-4457670792597298765),(-4457670792597298747)⟩,⟨(-1373391904968473734),(-1373391904968473717)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-2572233023869009041),(-2572233023869009025)⟩,⟨(-441557605641204804),(-441557605641204786)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-1312600643963924123),(-1312600643963924107)⟩,⟨(-106445018192314326),(-106445018192314309)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-400886135223857299),(-400886135223857281)⟩,⟨(-14183276981276915),(-14183276981276899)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-828574780267502495137),(-828574780267492180167)⟩,⟨554287053534222478770,554287053534232793779⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-2192711861817947698575),(-2192711861817910630498)⟩,⟨1677434703237536298994,1677434703237573367161⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-2801639130872307159988),(-2801639130872222653080)⟩,⟨2763968463971423267141,2763968463971507774137⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-2519302320394357038494),(-2519302320394186329299)⟩,⟨3612827410982502450257,3612827410982673159467⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-1576182576529595977461),(-1576182576529292076745)⟩,⟨3971618936570111329674,3971618936570415230295⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-420044085411850287526),(-420044085411401048456)⟩,⟨3724401210289925646491,3724401210290374885365⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨528260165248560570057,528260165249071427958⟩,⟨2992534762463980015975,2992534762464490873613⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨1053144886501655776011,1053144886502073593919⟩,⟨2058847817954656212722,2058847817955074030354⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨1168660868138190028965,1168660868138484422680⟩,⟨1199468022882991413197,1199468022883285806699⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨1021762208166687716870,1021762208166873512737⟩,⟨567647243601441349557,567647243601627145314⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨773364093371912247220,773364093371999295455⟩,⟨184657491352626995397,184657491352714043584⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨530544840726216938625,530544840726250096129⟩,⟨(-4390267271450720851),(-4390267271417563360)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨338132394350794209966,338132394350805555398⟩,⟨(-71931577095749100806),(-71931577095737755373)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨200329455688772120162,200329455688775900760⟩,⟨(-75917081479112116870),(-75917081479108336265)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨103992572218936026540,103992572218937283378⟩,⟨(-52017994214181396139),(-52017994214180139294)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨32018130197065139059,32018130197065441781⟩,⟨(-18096295382430933855),(-18096295382430631134)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨5925527184733812711176,5925527184733812713939⟩,⟨(-133970735453646028560),(-133970735453646026746)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨16581294982081781898881,16581294982081781907024⟩,⟨(-1858584381063463784626),(-1858584381063463779008)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨23792262024004917008504,23792262024004917021523⟩,⟨(-6909585935817469489319),(-6909585935817469479484)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨25948585106905585449030,25948585106905585466046⟩,⟨(-14686582841479518713657),(-14686582841479518699508)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨22683778900747362164804,22683778900747362184563⟩,⟨(-22381207600558347605024),(-22381207600558347587177)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨15243036774751913623091,15243036774751913644576⟩,⟨(-26872685601443989204408),(-26872685601443989183823)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨6196238317614504202755,6196238317614504226748⟩,⟨(-26708282993027722287546),(-26708282993027722263685)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-1673072776293209020945),(-1673072776293208983319)⟩,⟨(-22594087559642928136763),(-22594087559642928098912)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-6658388259226155086595),(-6658388259226154964638)⟩,⟨(-16502233533012136460069),(-16502233533012136337899)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-8576414992898838987300),(-8576414992898838456826)⟩,⟨(-10440674955099255757820),(-10440674955099255227328)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-8263907732788723820496),(-8263907732788721905934)⟩,⟨(-5661350952879016404333),(-5661350952879014489936)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-6798046549946104029861),(-6798046549946097854816)⟩,⟨(-2526772328462559864916),(-2526772328462553690071)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-4997132274562937456410),(-4997132274562923696579)⟩,⟨(-805122557390940141512),(-805122557390926381827)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-3299337256195219349199),(-3299337256195199076689)⟩,⟨(-49834862849130776232),(-49834862849110503810)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-1843701454652467584447),(-1843701454652448657683)⟩,⟨147750884958779089467,147750884958798016185⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-589347082327936036281),(-589347082327928290080)⟩,⟨75408878404387651517,75408878404395397703⟩⟩
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
noncomputable def ans : CBox := ⟨⟨11560860332365298219379,11560860332365743478958⟩,⟨(-22597425938370081850881),(-22597425938369636593546)⟩⟩
lemma checked : cachedMomentRuleBox density0 hk4_0_17 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false false 4 17) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk4_0_17 (tableDensity false) (fullFactor false 4 17) density0_contains hk4_0_17_contains
noncomputable def atomAnswer : CBox := ⟨⟨1595932729921965584677,1595932729921965586094⟩,⟨(-19732628104434754804956),(-19732628104434754802399)⟩⟩
lemma atomChecked : tableAtomBox false ha4_0_17 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false false 4 17) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false false ha4_0_17 4 17 ha4_0_17_contains
 def realAnswer : RBox := ⟨13156793062287163804056,13156793062287809065052⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false false 4 17) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm4_0_0_17
namespace hm4_1_0_17
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk4_0_17 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-280263253),(-280263237)⟩,⟨(-926409940),(-926409924)⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-689207708),(-689207692)⟩,⟨(-1976204079),(-1976204062)⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-725658104),(-725658088)⟩,⟨(-1636837889),(-1636837873)⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-460757556),(-460757540)⟩,⟨(-769984205),(-769984189)⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-182506311),(-182506294)⟩,⟨(-213374544),(-213374528)⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-44527240),(-44527223)⟩,⟨(-33167857),(-33167840)⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-6452456),(-6452440)⟩,⟨(-2468747),(-2468730)⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-524067),(-524050)⟩,⟨(-32071),(-32055)⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-21984),(-21967)⟩,⟨5414,5430⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-433),(-417)⟩,⟨233,250⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-16),0⟩,⟨(-4),16⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-16),0⟩,⟨(-16),16⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-16),0⟩,⟨(-16),16⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-16),0⟩,⟨(-16),16⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-16),0⟩,⟨(-16),16⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-16),0⟩,⟨(-16),16⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨61849669135699,61849669135715⟩,⟨81994369047118,81994369047135⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨165295416321360,165295416321377⟩,⟨195468969202106,195468969202124⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨214729552521495,214729552521521⟩,⟨203057725931494,203057725931512⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨200179628341169,200179628341189⟩,⟨134528750244048,134528750244067⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨143417971816870,143417971816891⟩,⟨56792489181696,56792489181715⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨80647495449548,80647495449566⟩,⟨10214067660428,10214067660446⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨35970613894873,35970613894892⟩,⟨(-5251637782853),(-5251637782836)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨12843744948923,12843744948939⟩,⟨(-5775803518675),(-5775803518658)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨3706471263601,3706471263618⟩,⟨(-3110569649141),(-3110569649124)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨868651661896,868651661912⟩,⟨(-1249573908080),(-1249573908064)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨162022465672,162022465688⟩,⟨(-425469395079),(-425469395063)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨20666111432,20666111448⟩,⟨(-133407407253),(-133407407237)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-627624287),(-627624271)⟩,⟨(-41276571936),(-41276571920)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-1887328292),(-1887328276)⟩,⟨(-13275483265),(-13275483249)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-1011311641),(-1011311625)⟩,⟨(-4412394253),(-4412394236)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-294231296),(-294231280)⟩,⟨(-1073123785),(-1073123769)⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-90050183319662210),(-90050183319662194)⟩,⟨(-56165021783382629),(-56165021783382613)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-247827130267074043),(-247827130267074027)⟩,⟨(-138479491352511956),(-138479491352511940)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-342987863743250487),(-342987863743250471)⟩,⟨(-152213027457465133),(-152213027457465117)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-354391395403392350),(-354391395403392334)⟩,⟨(-104457498187931681),(-104457498187931665)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-294012444291486348),(-294012444291486331)⟩,⟨(-34425040250118661),(-34425040250118645)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-200612694832960017),(-200612694832960001)⟩,⟨19335799217993776,19335799217993792⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-113760377653683469),(-113760377653683452)⟩,⟨41602153858345259,41602153858345276⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-53663790865121615),(-53663790865121599)⟩,⟨39556864102709666,39556864102709682⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-20729023327962204),(-20729023327962186)⟩,⟨27721144950140592,27721144950140608⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-6129536388049194),(-6129536388049177)⟩,⟨16165437474724785,16165437474724802⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-947280281873358),(-947280281873342)⟩,⟨8350909941753284,8350909941753302⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨402353081085933,402353081085952⟩,⟨3992761213169724,3992761213169743⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨524957834608740,524957834608760⟩,⟨1826683866866585,1826683866866605⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨370366285817862,370366285817880⟩,⟨814290581473562,814290581473581⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨202700681654691,202700681654712⟩,⟨341752441010531,341752441010550⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨63329917119753,63329917119771⟩,⟨93807797529034,93807797529052⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨12023236618650754571,12023236618650819679⟩,⟨(-784875911370102193),(-784875911370037082)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨32505440998767646905,32505440998767786397⟩,⟨(-3583481181917147549),(-3583481181917008060)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨43804516212010342980,43804516212010458898⟩,⟨(-8866638557476447517),(-8866638557476331598)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨44203804143463480186,44203804143463534771⟩,⟨(-15420270921909921562),(-15420270921909866979)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨36187372175375070590,36187372175375086016⟩,⟨(-20498885882985847345),(-20498885882985831920)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨24538797694243369988,24538797694243372763⟩,⟨(-21941461400961673854),(-21941461400961671084)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨13626884778753367768,13626884778753368208⟩,⟨(-19594154807424414275),(-19594154807424413834)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨5784551568069240475,5784551568069240552⟩,⟨(-15023376135059023209),(-15023376135059023134)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨1306970267709941447,1306970267709941475⟩,⟨(-10148496928788725500),(-10148496928788725472)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-657901223520913857),(-657901223520913836)⟩,⟨(-6188259362124265453),(-6188259362124265430)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-1188367499398108884),(-1188367499398108867)⟩,⟨(-3486909807003011444),(-3486909807003011424)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-1089809373309590950),(-1089809373309590934)⟩,⟨(-1856426354708517729),(-1856426354708517712)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-806025340271947900),(-806025340271947884)⟩,⟨(-950773399256807572),(-950773399256807555)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-521959140470469060),(-521959140470469043)⟩,⟨(-470138713583421849),(-470138713583421833)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-286056792747673275),(-286056792747673259)⟩,⟨(-213721961835460047),(-213721961835460031)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-90452425329269067),(-90452425329269051)⟩,⟨(-61276649756632239),(-61276649756632223)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-262552546602596043850),(-262552546602587566567)⟩,⟨195808667354561177952,195808667354569655219⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-710633987320536990689),(-710633987320506524394)⟩,⟨593063524279823770260,593063524279854236519⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-950806152275850677266),(-950806152275781211788)⟩,⟨977209423344577531145,977209423344646996587⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-921754258021034704119),(-921754258020894357263)⟩,⟨1277063810987239225142,1277063810987379571988⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-659958175395157064340),(-659958175394907184774)⟩,⟨1410364658542528731234,1410364658542778610839⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-286664137977215788672),(-286664137976846405448)⟩,⟨1345160500619714809223,1345160500620084192519⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨55506218650083169168,55506218650503131771⟩,⟨1121134844302377743318,1121134844302797706011⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨274824303918578799644,274824303918922113499⟩,⟨823019076308941668530,823019076309284982474⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨356542342620914788015,356542342621156490595⟩,⟨535553029470794858511,535553029471036561154⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨338428334436164743944,338428334436317124490⟩,⟨310541919658755378062,310541919658907758636⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨271474074856444043363,271474074856515345957⟩,⟨160684408826940380006,160684408827011682612⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨194560402911945690999,194560402911972814332⟩,⟨73358782917015320251,73358782917042443592⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨127990062964062683087,127990062964071951965⟩,⟨28200420708629327606,28200420708638596488⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨77510016384880372304,77510016384883457644⟩,⟨7835828042421950460,7835828042425035796⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨40821122564062335745,40821122564063360680⟩,⟨654676738017166022,654676738018190953⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨12662945798684440153,12662945798684686925⟩,⟨(-371238411698864584),(-371238411698617814)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨175817968501711455506,175817968501711456989⟩,⟨(-12329615527806166692),(-12329615527806165676)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨455720823431588164659,455720823431588169055⟩,⟨(-171954297273404437891),(-171954297273404434765)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨369793617834665392932,369793617834665400017⟩,⟨(-655038087434735349273),(-655038087434735343838)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-541745771505332398436),(-541745771505332389066)⟩,⟨(-1480034647116101057588),(-1480034647116101049755)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-2442551355847832925374),(-2442551355847832914091)⟩,⟨(-2487109928331636619805),(-2487109928331636609616)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-4821808856653811885429),(-4821808856653811872397)⟩,⟨(-3313269882973060900473),(-3313269882973060887995)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-6803748277785456880728),(-6803748277785456864722)⟩,⟨(-3517821340031101939126),(-3517821340031101923203)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-7768602973801181757689),(-7768602973801181729239)⟩,⟨(-2941285691625739136016),(-2941285691625739107389)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-7607067464141728656658),(-7607067464141728557869)⟩,⟨(-1851827470851010255104),(-1851827470851010156112)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-6600549804235939068520),(-6600549804235938635050)⟩,⟨(-697138644236487852863),(-697138644236487419285)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-5184779840101812626506),(-5184779840101811062847)⟩,⟨192577764358029758989,192577764358031322654⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-3747028167012656741215),(-3747028167012651698376)⟩,⟨701160288144959399723,701160288144964442532⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-2518493552274929670907),(-2518493552274918429733)⟩,⟨862102828389527558362,862102828389538799507⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-1565095169337224623645),(-1565095169337208054049)⟩,⟨767343798609437632859,767343798609454202434⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-843289306127063816866),(-843289306127048341385)⟩,⟨513561957262724742119,513561957262740217590⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-265105205537451896422),(-265105205537445561469)⟩,⟨179069062429582704728,179069062429589039680⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-8590494065457652267736),(-8590494065457286488399)⟩,⟨(-863687665486935883120),(-863687665486570104765)⟩⟩
lemma checked : cachedMomentRuleBox density1 hk4_0_17 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true false 4 17) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk4_0_17 (tableDensity true) (fullFactor false 4 17) density1_contains hk4_0_17_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-2086988954513339612584),(-2086988954513339610731)⟩,⟨25804205982722371664676,25804205982722371668019⟩⟩
lemma atomChecked : tableAtomBox true ha4_0_17 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true false 4 17) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true false ha4_0_17 4 17 ha4_0_17_contains
 def realAnswer : RBox := ⟨(-10677483019971091880320),(-10677483019970526099130)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true false 4 17) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm4_1_0_17
namespace hm4_0_0_18
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk4_0_18 j i k))
noncomputable def s0_0 : CBox := ⟨⟨149221124,149221140⟩,⟨(-67722263),(-67722247)⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨308065954,308065972⟩,⟨(-158483109),(-158483093)⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨239759867,239759884⟩,⟨(-154154505),(-154154487)⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨103446552,103446570⟩,⟨(-88990446),(-88990428)⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨25785470,25785487⟩,⟨(-31518028),(-31518011)⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨3531042,3531060⟩,⟨(-6724514),(-6724495)⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨222201,222220⟩,⟨(-831428),(-831404)⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨1397,1416⟩,⟨(-56244),(-56223)⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-435),(-415)⟩,⟨(-1923),(-1902)⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-26),(-5)⟩,⟨(-40),(-23)⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),0⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),0⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),0⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-15893169101168),(-15893169101152)⟩,⟨34757249449849,34757249449865⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-35921599438032),(-35921599438014)⟩,⟨88601593847909,88601593847926⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-32692790098863),(-32692790098844)⟩,⟨105922219068008,105922219068025⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-15682961596159),(-15682961596139)⟩,⟨88966321492233,88966321492251⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-833464682129),(-833464682111)⟩,⟨56830349576153,56830349576171⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨5012776703013,5012776703034⟩,⟨28361160574587,28361160574607⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨4576223135485,4576223135505⟩,⟨11202837738019,11202837738038⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨2500894312524,2500894312542⟩,⟨3534425768418,3534425768437⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨1019457655430,1019457655447⟩,⟨895861495931,895861495951⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨339980967022,339980967042⟩,⟨181340374148,181340374166⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨99420941947,99420941965⟩,⟨27587309396,27587309412⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨27265456677,27265456695⟩,⟨1933030873,1933030890⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨7502838763,7502838779⟩,⟨(-769068432),(-769068413)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨2192170748,2192170765⟩,⟨(-537471846),(-537471829)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨680208484,680208501⟩,⟨(-238342750),(-238342733)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨159575636,159575652⟩,⟨(-64977121),(-64977105)⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨248590710708180,248590710708196⟩,⟨(-40957158030798377),(-40957158030798360)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-5039483538077430),(-5039483538077414)⟩,⟨(-108622562397558633),(-108622562397558616)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-21115686721405929),(-21115686721405913)⟩,⟨(-140702117151721586),(-140702117151721569)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-40780527606923508),(-40780527606923491)⟩,⟨(-133440954086696649),(-133440954086696633)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-52254328369587229),(-52254328369587211)⟩,⟨(-100067368866057056),(-100067368866057040)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-50222808682906862),(-50222808682906845)⟩,⟨(-60386148800003983),(-60386148800003964)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-38534968173093958),(-38534968173093941)⟩,⟨(-28986608024774741),(-28986608024774720)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-24595283614792012),(-24595283614791994)⟩,⟨(-10421343961149372),(-10421343961149356)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-13502602661473208),(-13502602661473189)⟩,⟨(-2074752765172400),(-2074752765172382)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-6581456882402207),(-6581456882402189)⟩,⟨604365136834096,604365136834114⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-2942475391623017),(-2942475391622999)⟩,⟨982755768947964,982755768947981⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-1248017946724258),(-1248017946724240)⟩,⟨731875858156732,731875858156751⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-518356762180470),(-518356762180452)⟩,⟨442343510580574,442343510580595⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-214842653093981),(-214842653093962)⟩,⟨241225961717410,241225961717427⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-85874412810128),(-85874412810112)⟩,⟨116643176311160,116643176311178⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-22998052932194),(-22998052932177)⟩,⟨34524625272008,34524625272025⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨2717349290753901596,2717349290753910614⟩,⟨3187911995472983010,3187911995472992031⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨7854707368297650030,7854707368297669265⟩,⟨8379638123689055557,8379638123689074792⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨11965753660616197804,11965753660616213673⟩,⟨10617818764540297973,10617818764540313842⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨14223220753888381177,14223220753888388579⟩,⟨9592528065320958040,9592528065320965438⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨14157543983190666373,14157543983190668450⟩,⟨6414087444125865980,6414087444125868051⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨12076548481437583967,12076548481437584349⟩,⟨2791625356593826513,2791625356593826890⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨8940362621108033417,8940362621108033492⟩,⟨50673037810848900,50673037810848975⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨5804528794080409837,5804528794080409863⟩,⟨(-1356835266052871708),(-1356835266052871683)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨3339216110203179772,3339216110203179791⟩,⟨(-1688002433431795086),(-1688002433431795068)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨1719187149890605103,1719187149890605122⟩,⟨(-1446428691209402972),(-1446428691209402955)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨798212643513800279,798212643513800296⟩,⟨(-1037761632953172469),(-1037761632953172451)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨334467520914802919,334467520914802936⟩,⟨(-670274738807714577),(-670274738807714560)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨124622429345030407,124622429345030423⟩,⟨(-404146677772244092),(-404146677772244076)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨39361684693523808,39361684693523826⟩,⟨(-229109924382408498),(-229109924382408481)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨9369989892944119,9369989892944135⟩,⟨(-115468916159750436),(-115468916159750420)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨1239929598184118,1239929598184134⟩,⟨(-35040314049918623),(-35040314049918607)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-80540276585523328692),(-80540276585521829887)⟩,⟨(-120396790089126894592),(-120396790089125395790)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-242807546120995670093),(-242807546120990305125)⟩,⟨(-317423585573192371503),(-317423585573187006547)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-397086130058487217462),(-397086130058475080380)⟩,⟨(-402596534707481683094),(-402596534707469546022)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-513375452736763754909),(-513375452736739509568)⟩,⟨(-358158196823237260908),(-358158196823213015570)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-556460828041970128905),(-556460828041927576495)⟩,⟨(-221050328609275826217),(-221050328609233273792)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-513128740989394596032),(-513128740989332741438)⟩,⟨(-58091657510734296716),(-58091657510672442096)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-404538053870757016173),(-404538053870687988758)⟩,⟨71205303275637841493,71205303275706868937⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-272654068294799009691),(-272654068294743684073)⟩,⟨139284519412443432296,139284519412498757949⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-155481939976963642244),(-155481939976925505187)⟩,⟨151325214177739131871,151325214177777268952⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-72025830074075024426),(-72025830074051460415)⟩,⟨129491989310616557344,129491989310640121367⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-22964584145606753420),(-22964584145595938755)⟩,⟨95993373410248635675,95993373410259450347⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨513005715568733843,513005715572774921⟩,⟨64601216542685500869,64601216542689541952⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨8604265248517271139,8604265248518630760⟩,⟨40490499191511956475,40490499191513316095⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨8966900580905426712,8966900580905873645⟩,⟨23670297662469667672,23670297662470114605⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨6088426479121411372,6088426479121558541⟩,⟨12173116128303469982,12173116128303617149⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨2108119435328378190,2108119435328413471⟩,⟨3729980285562512575,3729980285562547857⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨23357472609260517151,23357472609260517481⟩,⟨1033376718006151019993,1033376718006151020489⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨322953174867086346328,322953174867086347320⟩,⟨2882590880707943699993,2882590880707943701431⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨1193183735945086103153,1193183735945086104870⟩,⟨4110642340496247825327,4110642340496247827603⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨2513283850580366657641,2513283850580366660084⟩,⟨4442846427012876051705,4442846427012876054645⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨3785714050425828965352,3785714050425828968398⟩,⟨3839160812445482977762,3839160812445482981138⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨4482809420962861478017,4482809420962861481481⟩,⟨2544889270470500998517,2544889270470501002132⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨4386153528910138866455,4386153528910138870401⟩,⟨1019464491461582482672,1019464491461582486641⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨3648252060790278286359,3648252060790278292490⟩,⟨(-268499555671810971287),(-268499555671810965193)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨2618186519302663345349,2618186519302663364704⟩,⟨(-1054996238401637365026),(-1054996238401637345702)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨1627638743154925879256,1627638743154925961746⟩,⟨(-1335839469491766334175),(-1335839469491766251687)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨867824310256139019575,867824310256139312297⟩,⟨(-1265785921025284462444),(-1265785921025284169695)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨381409067465845773250,381409067465846703144⟩,⟨(-1025304744401272108962),(-1025304744401271179037)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨119946798179752233627,119946798179754279333⟩,⟨(-743661120495030630537),(-743661120495028584809)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨7381175159843467457,7381175159846450793⟩,⟨(-485779807999436498730),(-485779807999433515379)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-21583701314253113682),(-21583701314250348165)⟩,⟨(-269443269759534317340),(-269443269759531551816)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-10978021614933506701),(-10978021614932378985)⟩,⟨(-85799664639925903970),(-85799664639924776252)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨3804099607683176676121,3804099607683236822129⟩,⟨2104256448832117777357,2104256448832177923735⟩⟩
lemma checked : cachedMomentRuleBox density0 hk4_0_18 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false false 4 18) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk4_0_18 (tableDensity false) (fullFactor false 4 18) density0_contains hk4_0_18_contains
noncomputable def atomAnswer : CBox := ⟨⟨3471739243130349748474,3471739243130349748924⟩,⟨232647668234464728063,232647668234464728302⟩⟩
lemma atomChecked : tableAtomBox false ha4_0_18 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false false 4 18) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false false ha4_0_18 4 18 ha4_0_18_contains
 def realAnswer : RBox := ⟨7275838850813426424595,7275838850813686571053⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false false 4 18) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm4_0_0_18
namespace hm4_1_0_18
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk4_0_18 j i k))
noncomputable def s0_0 : CBox := ⟨⟨26822507,26822523⟩,⟨(-8113995),(-8113979)⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨56185017,56185033⟩,⟨(-19584823),(-19584807)⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨44860969,44860985⟩,⟨(-19865539),(-19865523)⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨19960343,19960360⟩,⟨(-11922003),(-11921987)⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨5128863,5128879⟩,⟨(-4374568),(-4374551)⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨723844,723861⟩,⟨(-967528),(-967512)⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨47862,47879⟩,⟨(-124110),(-124094)⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨552,568⟩,⟨(-8692),(-8676)⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-81),(-64)⟩,⟨(-310),(-294)⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-16),3⟩,⟨(-17),(-1)⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),0⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),0⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),0⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-4759007928416),(-4759007928400)⟩,⟨3589710731594,3589710731610⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-11240948783167),(-11240948783150)⟩,⟨9503761317631,9503761317647⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-11465298367553),(-11465298367537)⟩,⟨12117515114516,12117515114532⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-7392732490654),(-7392732490636)⟩,⟨10987849277599,10987849277615⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-3013150961598),(-3013150961581)⟩,⟨7591076481070,7591076481086⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-521512220691),(-521512220674)⟩,⟨4082670751613,4082670751631⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨250147204852,250147204868⟩,⟨1728613809003,1728613809019⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨260802792703,260802792720⟩,⟨582100031043,582100031059⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨131882909781,131882909798⟩,⟨157603239464,157603239480⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨49539754627,49539754644⟩,⟨34538504332,34538504348⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨15751222614,15751222631⟩,⟨6019771231,6019771247⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨4620252935,4620252951⟩,⟨720122070,720122087⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨1344758961,1344758978⟩,⟨(-19599382),(-19599364)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨410854354,410854370⟩,⟨(-58261271),(-58261255)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨131551936,131551952⟩,⟨(-30132367),(-30132351)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨31369667,31369683⟩,⟨(-8600473),(-8600457)⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨4893605924434731,4893605924434747⟩,⟨(-7845872335859911),(-7845872335859895)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨11991348633117627,11991348633117643⟩,⟨(-21457189737654523),(-21457189737654507)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨13021105227535105,13021105227535122⟩,⟨(-29329241891014247),(-29329241891014231)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨8779021273038292,8779021273038308⟩,⟨(-29754651724682470),(-29754651724682454)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨2832888797249147,2832888797249163⟩,⟨(-24105275337029820),(-24105275337029801)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-1530511491403408),(-1530511491403392)⟩,⟨(-15982251394376939),(-15982251394376923)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-3199066049006932),(-3199066049006916)⟩,⟨(-8769419661479008),(-8769419661478992)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-2935185598594425),(-2935185598594409)⟩,⟨(-3989595258577048),(-3989595258577031)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-1979514985371821),(-1979514985371805)⟩,⟨(-1483116693994336),(-1483116693994320)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-1109673802040382),(-1109673802040366)⟩,⟨(-421850076768147),(-421850076768131)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-551358792818829),(-551358792818812)⟩,⟨(-62940723038899),(-62940723038883)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-254136016297205),(-254136016297189)⟩,⟨25469078931667,25469078931683⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-112552724541788),(-112552724541772)⟩,⟨32298492097332,32298492097351⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-48863086044550),(-48863086044534)⟩,⟨22210700659075,22210700659092⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-20126215758605),(-20126215758589)⟩,⟨11934640513059,11934640513075⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-5470831038903),(-5470831038887)⟩,⟨3693281290091,3693281290107⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨91209483956605766,91209483956613346⟩,⟨1397302463901821585,1397302463901829167⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨414353761837758908,414353761837775059⟩,⟨3759963256404086439,3759963256404102591⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨1015560435511589260,1015560435511602568⟩,⟨5020125331889155897,5020125331889169208⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨1742091015614803582,1742091015614809775⟩,⟨4997308850127083730,4997308850127089922⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨2275209447521048268,2275209447521049996⟩,⟨4019603010569800321,4019603010569802052⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨2384205520301859399,2384205520301859715⟩,⟨2668779697135082981,2668779697135083296⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨2078362152696763045,2078362152696763107⟩,⟨1446979334168024700,1446979334168024762⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨1552112404444294531,1552112404444294556⟩,⟨598593555835655428,598593555835655453⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨1019855871240808942,1019855871240808958⟩,⟨131914503840195375,131914503840195392⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨604701563360196585,604701563360196602⟩,⟨(-63966515753244079),(-63966515753244061)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨331576820487672190,331576820487672207⟩,⟨(-112832247257059776),(-112832247257059759)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨172123645573049993,172123645573050009⟩,⟨(-100959519336489873),(-100959519336489856)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨86224122208450484,86224122208450501⟩,⟨(-73059792355006170),(-73059792355006154)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨41882541023693081,41882541023693097⟩,⟨(-46485881202491922),(-46485881202491906)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨18802356431255184,18802356431255200⟩,⟨(-25163276313004926),(-25163276313004910)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨5356062806928700,5356062806928716⟩,⟨(-7906153019321697),(-7906153019321681)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-28451832612247006901),(-28451832612245775122)⟩,⟨(-38150360429585934941),(-38150360429584703158)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-85845517951953712250),(-85845517951949302790)⟩,⟨(-102871832708248060663),(-102871832708243651195)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-140391071763607828721),(-140391071763597851940)⟩,⟨(-136624831904360124038),(-136624831904350147249)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-181468006499259819722),(-181468006499239886661)⟩,⟨(-131028440339992093887),(-131028440339972160822)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-197602796833345036139),(-197602796833310047796)⟩,⟨(-92531125990797503684),(-92531125990762515343)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-185322010088184538978),(-185322010088133679492)⟩,⟨(-39566174220373893701),(-39566174220323034229)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-151545177844285796293),(-151545177844229050628)⟩,⟨7433957076587695941,7433957076644441592⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-108976503478400049079),(-108976503478354588869)⟩,⟨36330977855149886601,36330977855195346800⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-69403189608577294397),(-69403189608545983096)⟩,⟨46158545072734369318,46158545072765680611⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-39383158116762973811),(-39383158116743647719)⟩,⟨42885222512991340655,42885222513010666742⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-19957658095570952126),(-19957658095562093634)⟩,⟨33693720035990970002,33693720035999828493⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-8938323672187326712),(-8938323672184021036)⟩,⟨23689115404112862613,23689115404116168286⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-3379414919204130347),(-3379414919203019573)⟩,⟨15325986256398328968,15325986256399439743⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-926721469847686123),(-926721469847321381)⟩,⟨9158186464627643593,9158186464628008337⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-76819059618091285),(-76819059617971266)⟩,⟨4778390151581238111,4778390151581358126⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨43240965355636935,43240965355665697⟩,⟨1475179913938921503,1475179913938950266⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨2149638391839405354,2149638391839405545⟩,⟨30661654655363497918,30661654655363498192⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨29879182911164120289,29879182911164120846⟩,⟨79230875244456749448,79230875244456750226⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨113112657968745002770,113112657968745003721⟩,⟨63945764256894385196,63945764256894386432⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨253257121845692950854,253257121845692952208⟩,⟨(-92537982520086582658),(-92537982520086581043)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨420637318828306812187,420637318828306813926⟩,⟨(-412861322962937287784),(-412861322962937285859)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨552643312259615340079,552643312259615342178⟩,⟨(-803952361105365567781),(-803952361105365565592)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨577685004012052858141,577685004012052860770⟩,⟨(-1116852338368658857791),(-1116852338368658855147)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨474973417748000901351,474973417748000905983⟩,⟨(-1253855609865944535198),(-1253855609865944530590)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨293918549577505613132,293918549577505628813⟩,⟨(-1206371356079116690230),(-1206371356079116674580)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨108836429417419487630,108836429417419555050⟩,⟨(-1028481959262847141433),(-1028481959262847074028)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-29345062510433081815),(-29345062510432842719)⟩,⟨(-794324530538985614104),(-794324530538985375011)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-105659590505084845328),(-105659590505084085910)⟩,⟨(-565212322494836917096),(-565212322494836157673)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-128247118909632523130),(-128247118909630851865)⟩,⟨(-374823923633142146926),(-374823923633140475659)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-112960394304846297764),(-112960394304843859346)⟩,⟨(-230445940077241495101),(-230445940077239056679)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-75048623727620106561),(-75048623727617845327)⟩,⟨(-123241944345970799863),(-123241944345968538626)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-26069460904179956368),(-26069460904179034102)⟩,⟨(-38595196210908580102),(-38595196210907657835)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨190333463681382326824,190333463681431737824⟩,⟨(-1360682472826096839541),(-1360682472826047428382)⟩⟩
lemma checked : cachedMomentRuleBox density1 hk4_0_18 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true false 4 18) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk4_0_18 (tableDensity true) (fullFactor false 4 18) density1_contains hk4_0_18_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-4539966702555072748592),(-4539966702555072748005)⟩,⟨(-304231566152761567780),(-304231566152761567467)⟩⟩
lemma atomChecked : tableAtomBox true ha4_0_18 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true false 4 18) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true false ha4_0_18 4 18 ha4_0_18_contains
 def realAnswer : RBox := ⟨(-4349633238873790421768),(-4349633238873541010181)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true false 4 18) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm4_1_0_18
namespace hm4_0_0_19
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk4_0_19 j i k))
noncomputable def s0_0 : CBox := ⟨⟨1857492,1857510⟩,⟨4093086,4093103⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨4267217,4267234⟩,⟨8298589,8298606⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨3999465,3999482⟩,⟨6227215,6227231⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨2182703,2182722⟩,⟨2541883,2541902⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨716331,716348⟩,⟨587638,587654⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨138588,138604⟩,⟨73075,73093⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨15165,15183⟩,⟨4081,4098⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨876,895⟩,⟨14,32⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨18,35⟩,⟨(-17),4⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨0,16⟩,⟨(-16),16⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨0,16⟩,⟨(-16),16⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨0,16⟩,⟨(-16),16⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨0,16⟩,⟨(-16),16⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-1911132504533),(-1911132504517)⟩,⟨(-873909133308),(-873909133292)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-4826488377570),(-4826488377553)⟩,⟨(-1957245246701),(-1957245246685)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-5663851447878),(-5663851447860)⟩,⟨(-1749469405352),(-1749469405334)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-4627756289523),(-4627756289505)⟩,⟨(-817667770465),(-817667770447)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-2850856168727),(-2850856168709)⟩,⟨(-43536877651),(-43536877632)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-1360843750626),(-1360843750608)⟩,⟨239376151419,239376151438⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-510314372279),(-510314372263)⟩,⟨207856164393,207856164410⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-151848576817),(-151848576800)⟩,⟨107183926164,107183926183⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-36113014059),(-36113014040)⟩,⟨40994944257,40994944277⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-6836528585),(-6836528566)⟩,⟨12780528044,12780528062⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-972368028),(-972368011)⟩,⟨3489525454,3489525473⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-64278817),(-64278798)⟩,⟨895128643,895128663⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨23591889,23591908⟩,⟨231678192,231678210⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨15735723,15735739⟩,⟨64291377,64291393⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨6729313,6729329⟩,⟨19214710,19214727⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨1799367,1799383⟩,⟨4419274,4419291⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨3380707752652543,3380707752652559⟩,⟨20543484205137,20543484205153⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨8910082636694784,8910082636694801⟩,⟨(-412813762879576),(-412813762879560)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨11399511091822234,11399511091822251⟩,⟨(-1708814346991650),(-1708814346991633)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨10615807666372003,10615807666372020⟩,⟨(-3240746147219992),(-3240746147219975)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨7774360860345096,7774360860345112⟩,⟨(-4055261567455230),(-4055261567455211)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨4559256675863684,4559256675863702⟩,⟨(-3787392936346947),(-3787392936346930)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨2118130184684439,2118130184684457⟩,⟨(-2811765334923131),(-2811765334923113)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨734843526238815,734843526238831⟩,⟨(-1730565651919736),(-1730565651919718)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨141197672501814,141197672501832⟩,⟨(-914051175635567),(-914051175635548)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-38991259555820),(-38991259555801)⟩,⟨(-428223943223635),(-428223943223619)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-61356021510724),(-61356021510706)⟩,⟨(-184122643268886),(-184122643268869)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-44090194022632),(-44090194022616)⟩,⟨(-75277148434575),(-75277148434556)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-25806549627020),(-25806549627001)⟩,⟨(-30264027742546),(-30264027742529)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-13709109233135),(-13709109233118)⟩,⟨(-12214850046910),(-12214850046892)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-6506899834506),(-6506899834489)⟩,⟨(-4791275610223),(-4791275610206)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-1907461277724),(-1907461277708)⟩,⟨(-1270651331307),(-1270651331291)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-350990577727436704),(-350990577727435692)⟩,⟨299178490838161331,299178490838162341⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-918296775546649497),(-918296775546647372)⟩,⟨860698345939360551,860698345939362673⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-1152882557712117956),(-1152882557712116218)⟩,⟨1298949485320455058,1298949485320456796⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-1027574366471043357),(-1027574366471042552)⟩,⟨1522958731822887976,1522958731822888785⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-675275378728523215),(-675275378728522980)⟩,⟨1489296080112933725,1489296080112933958⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-288024952344281582),(-288024952344281529)⟩,⟨1243685755175538140,1243685755175538196⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-5535307795504216),(-5535307795504196)⟩,⟨898731832815170301,898731832815170324⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨132525105556914186,132525105556914206⟩,⟨568329517066685908,568329517066685926⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨160546167217318131,160546167217318148⟩,⟨318027432810885867,318027432810885885⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨133817150715983168,133817150715983184⟩,⟨159218029410994419,159218029410994439⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨93445830849040071,93445830849040088⟩,⟨71941669287088925,71941669287088941⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨58855279029598403,58855279029598420⟩,⟨29394446913645443,29394446913645461⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨34713884616270658,34713884616270675⟩,⟨10713480848735513,10713480848735529⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨19333237210541189,19333237210541206⟩,⟨3324196246696068,3324196246696085⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨9623203173822841,9623203173822857⟩,⟨781402445385975,781402445385991⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨2901577763887518,2901577763887534⟩,⟨102692026984167,102692026984183⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨16573611072871089912,16573611072871296243⟩,⟨(-11086910339350161920),(-11086910339349955590)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨43532829930449287719,43532829930450023349⟩,⟨(-33296517866189115991),(-33296517866188380360)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨54808751340871889612,54808751340873541045⟩,⟨(-54045359031864427689),(-54045359031862776254)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨48238538683597376962,48238538683600639278⟩,⟨(-69111085592338135180),(-69111085592334872865)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨29369945273311200149,29369945273316844910⟩,⟨(-73863420810620019712),(-73863420810614374952)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨7611259538536528462,7611259538544597060⟩,⟨(-66977212190571945914),(-66977212190563877316)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-9093010457184695147),(-9093010457175858703)⟩,⟨(-51809930502424368668),(-51809930502415532227)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-17452304042303743453),(-17452304042296802775)⟩,⟨(-34208570132533911314),(-34208570132526970641)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-18563941894664192653),(-18563941894659512031)⟩,⟨(-19094442340797443279),(-19094442340792762660)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-15547891538251598807),(-15547891538248767415)⟩,⟨(-8658303963330620338),(-8658303963327788945)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-11288393195724221254),(-11288393195722948327)⟩,⟨(-2705714009831452392),(-2705714009830179464)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-7452293563234337823),(-7452293563233871212)⟩,⟨56692465793170377,56692465793636987⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-4593530212289451747),(-4593530212289297370)⟩,⟨975067731775392044,975067731775546422⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-2649635799376207369),(-2649635799376157305)⟩,⟨1003387643856216583,1003387643856266652⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-1349963147960271368),(-1349963147960255030)⟩,⟨675114186507556391,675114186507572729⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-411657675245681618),(-411657675245677711)⟩,⟨232659000716308304,232659000716312214⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-170729805961479774586),(-170729805961479774491)⟩,⟨3857986647879047141,3857986647879047208⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-474752534288122043570),(-474752534288122043318)⟩,⟨53163854859040834983,53163854859040835159⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-672829042603642225414),(-672829042603642225025)⟩,⟨195201715545858199560,195201715545858199855⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-720662339273561623915),(-720662339273561623421)⟩,⟨407460195640328434695,407460195640328435107⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-615576657787396264098),(-615576657787396263539)⟩,⟨606648430397869231110,606648430397869231613⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-402525214816609357403),(-402525214816609356815)⟩,⟨708461964473699200382,708461964473699200946⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-158907075808220192060),(-158907075808220191427)⟩,⟨682418036959859089094,682418036959859089724⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨40821346493219612801,40821346493219613749⟩,⟨558090752047974984318,558090752047974985270⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨158366293789132376106,158366293789132379018⟩,⟨393539881382578389651,393539881382578392569⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨197120881789247820151,197120881789247832315⟩,⟨240390463417458601174,240390463417458613336⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨183680751673140916077,183680751673140958498⟩,⟨126029413036724146065,126029413036724188476⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨146503629247472129197,146503629247472261884⟩,⟨54543396853858640098,54543396853858772776⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨104846400939330560677,104846400939330848828⟩,⟨16929298771457114413,16929298771457402562⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨67760111272936694681,67760111272937110625⟩,⟨1035676573400493904,1035676573400909845⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨37304750621005714480,37304750621006097318⟩,⟨(-2987044879389229039),(-2987044879388846203)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨11833659785141540658,11833659785141696207⟩,⟨(-1514065689355402685),(-1514065689355247140)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-359955988251939642410),(-359955988251931931401)⟩,⟨605018560002705160775,605018560002712871739⟩⟩
lemma checked : cachedMomentRuleBox density0 hk4_0_19 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false false 4 19) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk4_0_19 (tableDensity false) (fullFactor false 4 19) density0_contains hk4_0_19_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-32114598548245551008),(-32114598548245550968)⟩,⟨577846356976628256177,577846356976628256253⟩⟩
lemma atomChecked : tableAtomBox false ha4_0_19 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false false 4 19) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false false ha4_0_19 4 19 ha4_0_19_contains
 def realAnswer : RBox := ⟨(-392070586800285193418),(-392070586800077482369)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false false 4 19) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm4_0_0_19
namespace hm4_1_0_19
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk4_0_19 j i k))
noncomputable def s0_0 : CBox := ⟨⟨222540,222556⟩,⟨735721,735737⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨527268,527284⟩,⟨1513409,1513425⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨515308,515324⟩,⟨1165015,1165031⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨292349,292365⟩,⟨490374,490390⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨99393,99410⟩,⟨116855,116871⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨19925,19943⟩,⟨14972,14988⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨2255,2271⟩,⟨873,890⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨129,145⟩,⟨(-1),15⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨0,16⟩,⟨(-16),3⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨0,16⟩,⟨(-16),16⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨0,16⟩,⟨(-16),16⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨0,16⟩,⟨(-16),16⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨0,16⟩,⟨(-16),16⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-197379144518),(-197379144502)⟩,⟨(-261678814966),(-261678814950)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-517674282071),(-517674282055)⟩,⟨(-612427157987),(-612427157971)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-647850147761),(-647850147743)⟩,⟨(-613324289989),(-613324289973)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-571430069100),(-571430069084)⟩,⟨(-384902916596),(-384902916580)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-380700286538),(-380700286522)⟩,⟨(-151469723574),(-151469723558)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-195840518530),(-195840518514)⟩,⟨(-25228313026),(-25228313010)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-78718576684),(-78718576668)⟩,⟨11290545852,11290545868⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-25000798791),(-25000798775)⟩,⟨11160137486,11160137502⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-6350890078),(-6350890062)⟩,⟨5299211346,5299211362⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-1301460041),(-1301460025)⟩,⟨1861344814,1861344831⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-211955305),(-211955289)⟩,⟨552632221,552632237⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-23778093),(-23778076)⟩,⟨151638223,151638241⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨579022,579038⟩,⟨41515512,41515529⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨1704106,1704122⟩,⟨12047867,12047884⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨850597,850613⟩,⟨3715913,3715929⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨238157,238173⟩,⟨868736,868752⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨647615368757084,647615368757100⟩,⟨403934853812557,403934853812573⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨1760025780037061,1760025780037077⟩,⟨983722900126504,983722900126520⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨2376023348045855,2376023348045872⟩,⟨1055289299296937,1055289299296953⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨2366802929513070,2366802929513086⟩,⟨699016394045308,699016394045325⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨1872419361012048,1872419361012065⟩,⟨220862079835080,220862079835096⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨1206345267751503,1206345267751521⟩,⟨(-114776496777558),(-114776496777542)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨640491598616847,640491598616863⟩,⟨(-233074071249041),(-233074071249025)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨281025384926001,281025384926017⟩,⟨(-206357520586487),(-206357520586471)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨100541168945810,100541168945826⟩,⟨(-133931090743303),(-133931090743287)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨27507946911025,27507946911042⟩,⟨(-72173537358322),(-72173537358306)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨3962152753577,3962152753593⟩,⟨(-34490930155257),(-34490930155241)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-1527470212411),(-1527470212394)⟩,⟨(-15325700562998),(-15325700562982)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-1882737550342),(-1882737550326)⟩,⟨(-6570494558809),(-6570494558793)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-1261914747348),(-1261914747332)⟩,⟨(-2777916244478),(-2777916244462)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-665716757606),(-665716757590)⟩,⟨(-1122893599656),(-1122893599640)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-204049521301),(-204049521285)⟩,⟨(-302264673131),(-302264673115)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-153843292961633661),(-153843292961632811)⟩,⟨10041488761920471,10041488761921320⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-412032892078783312),(-412032892078781525)⟩,⟨45389787440367038,45389787440368823⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-545047155891497911),(-545047155891496451)⟩,⟨110198663321046232,110198663321047690⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-535230441985564862),(-535230441985564183)⟩,⟨186456592350794195,186456592350794874⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-423001790092796008),(-423001790092795812)⟩,⟨239246478248757265,239246478248757461⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-274985602632364753),(-274985602632364705)⟩,⟨245448252736188635,245448252736188681⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-145569353937601994),(-145569353937601973)⟩,⟨208861561282457205,208861561282457226⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-58686531465646691),(-58686531465646675)⟩,⟨151923393612015211,151923393612015227⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-12614095072000402),(-12614095072000385)⟩,⟨97100884861831080,97100884861831097⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨5892283878885111,5892283878885127⟩,⟨55983532798280796,55983532798280813⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨10149846933749741,10149846933749757⟩,⟨29872485383717560,29872485383717576⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨8861009864408732,8861009864408748⟩,⟨15119670951885424,15119670951885440⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨6273954840045216,6273954840045232⟩,⟨7408215748221803,7408215748221819⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨3922227020518593,3922227020518609⟩,⟨3534818153013565,3534818153013581⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨2097027856716288,2097027856716305⟩,⟨1567102822108766,1567102822108782⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨654680621420885,654680621420901⟩,⟨443522422014636,443522422014652⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨5251702215892400453,5251702215892570027⟩,⟨(-3916585531171683748),(-3916585531171514173)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨14108052277523087562,14108052277523692180⟩,⟨(-11772104750471650199),(-11772104750471045581)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨18598989191442784822,18598989191444142319⟩,⟨(-19107918800438919936),(-19107918800437562440)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨17645771985980659134,17645771985983341215⟩,⟨(-24429370259832830851),(-24429370259830148772)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨12290988332723450663,12290988332728092015⟩,⟨(-26229049753325988466),(-26229049753321347109)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨5173730725887755318,5173730725894389665⟩,⟨(-24188601381765993679),(-24188601381759359333)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-943186317534888412),(-943186317527624198)⟩,⟨(-19407066034324881506),(-19407066034317617287)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-4550235812885062804),(-4550235812879359749)⟩,⟨(-13670711839023107469),(-13670711839017404416)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-5661469668856454990),(-5661469668852612099)⟩,⟨(-8521034569083132769),(-8521034569079289880)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-5148540812068572860),(-5148540812066250681)⟩,⟨(-4731906255435176226),(-4731906255432854047)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-3961897197571612525),(-3961897197570569841)⟩,⟨(-2348436126417943978),(-2348436126416901297)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-2732586363775900172),(-2732586363775518472)⟩,⟨(-1031787753296390664),(-1031787753296008966)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-1738632166765648535),(-1738632166765522413)⟩,⟨(-383666754517751436),(-383666754517625313)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-1025143569065709946),(-1025143569065669083)⟩,⟨(-103833289256469654),(-103833289256428791)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-529906166567779347),(-529906166567766022)⟩,⟨(-8539434963978675),(-8539434963965350)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-162807475982840211),(-162807475982837026)⟩,⟨4771522297978133,4771522297981322⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-5065786872914261386),(-5065786872914261329)⟩,⟨355058775288031643,355058775288031687⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-13049976955391673622),(-13049976955391673477)⟩,⟨4918628589813150773,4918628589813150875⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-10475741641287384578),(-10475741641287384360)⟩,⟨18504479008955631509,18504479008955631677⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨14974955491904691541,14974955491904691816⟩,⟨41055780289663333757,41055780289663333988⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨66113385148005457202,66113385148005457523⟩,⟨67397779263721029564,67397779263721029858⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨126992361236680946515,126992361236680946873⟩,⟨87329318197339587325,87329318197339587673⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨173688902084535099999,173688902084535100423⟩,⟨89874646570820426397,89874646570820426819⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨191726494559799013731,191726494559799014451⟩,⟨72666005663242166304,72666005663242167022⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨181248815475915680691,181248815475915683051⟩,⟨44196055114339716741,44196055114339719106⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨151824957205667641353,151824957205667651295⟩,⟨16097462880443390468,16097462880443400411⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨115290683071251778767,115290683071251813413⟩,⟨(-4236243084828029448),(-4236243084827994801)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨80772376269616514013,80772376269616622372⟩,⟨(-15084359181539605031),(-15084359181539496671)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨52849146218448554723,52849146218448790136⟩,⟨(-18074252994247946840),(-18074252994247711429)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨32145432533531803675,32145432533532143648⟩,⟨(-15753763230554150146),(-15753763230553810177)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨17063202655030217558,17063202655030530584⟩,⟨(-10389931370686644153),(-10389931370686331124)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨5323132630668622647,5323132630668749856⟩,⟨(-3595527191168551514),(-3595527191168424301)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨204254213793446308391,204254213793452643248⟩,⟨36137738774070887060,36137738774077221903⟩⟩
lemma checked : cachedMomentRuleBox density1 hk4_0_19 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true false 4 19) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk4_0_19 (tableDensity true) (fullFactor false 4 19) density1_contains hk4_0_19_contains
noncomputable def atomAnswer : CBox := ⟨⟨41996013486167258959,41996013486167259010⟩,⟨(-755645236046360027408),(-755645236046360027309)⟩⟩
lemma atomChecked : tableAtomBox true ha4_0_19 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true false 4 19) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true false ha4_0_19 4 19 ha4_0_19_contains
 def realAnswer : RBox := ⟨246250227279513567350,246250227279719902258⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true false 4 19) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm4_1_0_19
end SharpPlanar.CachedData

end OAI
