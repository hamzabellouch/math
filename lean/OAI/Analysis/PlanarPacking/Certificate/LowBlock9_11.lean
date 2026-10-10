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
namespace hm9_0_1_8
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk9_1_8 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-527),250⟩,⟨(-262),513⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-1542),680⟩,⟨(-1209),1019⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-2554),637⟩,⟨(-1998),1191⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-1629),2366⟩,⟨(-3353),648⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-1211),4291⟩,⟨(-2301),3204⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-5211),2952⟩,⟨(-2645),5540⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-5301),5428⟩,⟨(-7507),3231⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-7115),8450⟩,⟨(-6508),9170⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-8279),5300⟩,⟨(-7729),6190⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-7985),7445⟩,⟨(-6756),7375⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-8887),7112⟩,⟨(-9588),6507⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-5622),8839⟩,⟨(-6635),8042⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-6463),4696⟩,⟨(-4326),6437⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-3699),2337⟩,⟨(-3835),2946⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-1882),2143⟩,⟨(-2129),991⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-627),682⟩,⟨(-682),290⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨1816113205228,1816113205366⟩,⟨(-1051422956898),(-1051422956760)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨3704649631808,3704649632190⟩,⟨(-2020608445066),(-2020608444682)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨2877115994761,2877115995370⟩,⟨(-1346656760450),(-1346656759842)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨1302464051538,1302464052468⟩,⟨(-431270623747),(-431270622823)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨377693896877,377693898288⟩,⟨(-44423857671),(-44423856252)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨71099098208,71099100284⟩,⟨14644029126,14644031205⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨7991682499,7991685218⟩,⟨6381461855,6381464577⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨284054160,284057391⟩,⟨1115963212,1115966443⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-62939934),(-62936509)⟩,⟨94645657,94649083⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-10892899),(-10889560)⟩,⟨(-303609),(-300265)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-439690),(-435771)⟩,⟨(-1040119),(-1036204)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨97385,101507⟩,⟨(-98434),(-94307)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨18048,22160⟩,⟨6172,10288⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-784),2292⟩,⟨2832,5907⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-1594),280⟩,⟨67,1936⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-595),114⟩,⟨(-253),451⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-35528793198154063426),(-35528793198154063195)⟩,⟨16713291841202353721,16713291841202353949⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-77728955097942381746),(-77728955097942381219)⟩,⟨47444024932070267324,47444024932070267849⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-66068652408492583874),(-66068652408492583270)⟩,⟨62488973957177005196,62488973957177005800⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-29422924361679345112),(-29422924361679344611)⟩,⟨51734120884397960714,51734120884397961215⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-4385027633663107956),(-4385027633663107584)⟩,⟨27824258803547471160,27824258803547471532⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨2425605118604642330,2425605118604642615⟩,⟨9812527875060385933,9812527875060386226⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨1726944771582802276,1726944771582802568⟩,⟨2270206274178005463,2270206274178005753⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨567864059728551172,567864059728551526⟩,⟨333814199471427042,333814199471427401⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨128434868207030531,128434868207031043⟩,⟨24381483469250817,24381483469251332⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨23569950680982030,23569950680982658⟩,⟨(-2119402218294391),(-2119402218293763)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨4014160070873755,4014160070874484⟩,⟨(-1187287220739763),(-1187287220739036)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨715706081386043,715706081386798⟩,⟨(-306211421271870),(-306211421271117)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨146606189085967,146606189086669⟩,⟨(-70824328838554),(-70824328837845)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨36115151504290,36115151504835⟩,⟨(-17280159767614),(-17280159767067)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨10330516380415,10330516380781⟩,⟨(-4626747440799),(-4626747440434)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨2353220598645,2353220598779⟩,⟨(-996720403583),(-996720403450)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-566578563696049729263838),(-566578563696048385577655)⟩,⟨208238502440490441967879,208238502440491785641730⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-1383944889367997199808598),(-1383944889367994453149002)⟩,⟨716067089613829823398566,716067089613832570069901⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-1441595454026988044630355),(-1441595454026986035168231)⟩,⟨1271480225195654533381842,1271480225195656542960897⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-811140794066177917397407),(-811140794066177198204195)⟩,⟨1511333573214187613732062,1511333573214188333148177⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-49007760431100555917544),(-49007760431100384495555)⟩,⟨1212415421831984750992254,1212415421831984922557795⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨334933267299117922615381,334933267299117953157547⟩,⟨624800128276457621970917,624800128276457652521274⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨311320028590433576873753,311320028590433580194687⟩,⟨164660371979671371005746,164660371979671374290236⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨151393511894392841858181,151393511894392842485104⟩,⟨(-21367163341160258665438),(-21367163341160258053152)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨42691115394372587015361,42691115394372587277054⟩,⟨(-41698706147358221164183),(-41698706147358220901237)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨3965567598102306436828,3965567598102306555919⟩,⟨(-21248215733791423793576),(-21248215733791423672058)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-2809689406525057710227),(-2809689406525057656818)⟩,⟨(-6985321076364548576991),(-6985321076364548523142)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-2024185981344157679726),(-2024185981344157656971)⟩,⟨(-1664088271470942855332),(-1664088271470942832648)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-909227914342311739323),(-909227914342311729848)⟩,⟨(-252467440758034603865),(-252467440758034594477)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-357243230154051168647),(-357243230154051164696)⟩,⟨18281510312246752246,18281510312246756163⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-131737068326231805692),(-131737068326231804080)⟩,⟨36411326393657184546,36411326393657186150⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-33445444173581627235),(-33445444173581626791)⟩,⟨13357533195753451493,13357533195753451938⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-108626265957434960121607704),(-108626265957433559079562917)⟩,⟨(-75227116533915313374042247),(-75227116533913912327908413)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-319007501522226675551253462),(-319007501522221890756892216)⟩,⟨(-163720056538136657084105043),(-163720056538131872270305792)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-479140604975181004679759476),(-479140604975171478378109243)⟩,⟨(-104158664711720509433332626),(-104158664711710983083419947)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-507341880050880396233781171),(-507341880050865060892818956)⟩,⟨85367098165968411444269011,85367098165983746859512528⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-362556297691759642679361203),(-362556297691729520624884382)⟩,⟨277324128733990981921265727,277324128734021104014854869⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-121298287228773958401595226),(-121298287228729506883187398)⟩,⟨335315563277496721569981563,335315563277541173081801482⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨70558363194674767643027378,70558363194714485472522864⟩,⟨240356456347829002833159301,240356456347868720632074655⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨131528645719305832686537479,131528645719340250276843797⟩,⟨92502893423145694119915055,92502893423180111696739708⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨95633550343030375690537609,95633550343051997570916120⟩,⟨(-7272065827097177823322500),(-7272065827075555939030687)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨39393705023729715879108077,39393705023737699207930094⟩,⟨(-37171128577642493080109123),(-37171128577634509744499632)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨4959090897646347395802737,4959090897649673589546393⟩,⟨(-29135246695164327220801123),(-29135246695161001025670295)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-6401393290197621541600526),(-6401393290196639815464632)⟩,⟨(-14528700325395424430008422),(-14528700325394442704701186)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-6692495156344455666464636),(-6692495156344233548044658)⟩,⟨(-5204301484014584053809083),(-5204301484014361936369859)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-4280826733877935364466682),(-4280826733877866080866370)⟩,⟨(-1210857356954907297754499),(-1210857356954838014541384)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-2141548710287412583284726),(-2141548710287389698062253)⟩,⟨(-27494141814874043067524),(-27494141814851157945057)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-631540073507686482936561),(-631540073507681127773362)⟩,⟨76322557166329383010152,76322557166334738157049⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-361244062157813583375332227),(-361244062157813581138805546)⟩,⟨(-1007048595183985823536410244),(-1007048595183985821208531619)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-1411050015102674482344651293),(-1411050015102674475397076390)⟩,⟨(-2672726827180548176089101919),(-2672726827180548168920829460)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-3112086264138897767186315894),(-3112086264138897754972820217)⟩,⟨(-3271426778866986646661252430),(-3271426778866986634257204680)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-4985541670143862801626149069),(-4985541670143862783799738919)⟩,⟨(-2257504047151281705043740373),(-2257504047151281687216580625)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-5879257534967032092199738928),(-5879257534967032068969889908)⟩,⟨213930458154408421966398923,213930458154408444955501993⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-4868702729369845294879497594),(-4868702729369845267782602921)⟩,⟨2985999120419577898345203450,2985999120419577925115026084⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-2244767138406757721089563384),(-2244767138406757691542423189)⟩,⟨4509486148910802965287408903,4509486148910802994717791685⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨554122485620115714568313596,554122485620115745560282125⟩,⟨4059237386060021273324420181,4059237386060021304359283699⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨2149113441001277120755741517,2149113441001277160590686543⟩,⟨2280635969779998075640122288,2280635969779998115547335358⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨2249140231739570556422678445,2249140231739570677981944100⟩,⟨449975319057549387253741025,449975319057549508828235360⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨1504823550983757841267380866,1504823550983758263053611441⟩,⟨(-615876035347401924859503903),(-615876035347401503075453865)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨684919371090030313265184032,684919371090031260640954652⟩,⟨(-886740724781112697316190676),(-886740724781111749935938896)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨161360967221537470937469723,161360967221539447376212991⟩,⟨(-726655689349487276097814612),(-726655689349485299651932487)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-55782358750247349320477943),(-55782358750244360530157671)⟩,⟨(-461097601802741973459108614),(-461097601802738984665291842)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-86626760644455528785689541),(-86626760644452823292259056)⟩,⟨(-236557060196744212693038138),(-236557060196741507198753246)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-35866512561321377754922367),(-35866512561320303743421622)⟩,⟨(-70958433915661872841336582),(-70958433915660798829797734)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-2886150787092593158920145906),(-2886150787092555755312009441)⟩,⟨481929250827157768440758344,481929250827195172066852620⟩⟩
lemma checked : cachedMomentRuleBox density0 hk9_1_8 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 9 8) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk9_1_8 (tableDensity false) (fullFactor true 9 8) density0_contains hk9_1_8_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-3592453078810636682648092548),(-3592453078810636677257342512)⟩,⟨1377289656134564278467060165,1377289656134564283773405174⟩⟩
lemma atomChecked : tableAtomBox false ha9_1_8 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 9 8) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha9_1_8 9 8 ha9_1_8_contains
 def realAnswer : RBox := ⟨(-6478603865903229841668238454),(-6478603865903192432469351953)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 9 8) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm9_0_1_8
namespace hm9_1_1_8
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk9_1_8 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-101),48⟩,⟨(-56),91⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-271),129⟩,⟨(-228),172⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-437),136⟩,⟨(-380),192⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-254),457⟩,⟨(-570),138⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-236),708⟩,⟨(-356),590⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-886),464⟩,⟨(-475),879⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-821),899⟩,⟨(-1190),528⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-1130),1329⟩,⟨(-1025),1453⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-1331),838⟩,⟨(-1235),993⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-1317),1231⟩,⟨(-1095),1213⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-1528),1180⟩,⟨(-1622),1102⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-949),1546⟩,⟨(-1162),1376⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-1117),823⟩,⟨(-727),1133⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-642),383⟩,⟨(-659),517⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-337),363⟩,⟨(-363),154⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-117),120⟩,⟨(-120),48⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨327199824074,327199824104⟩,⟨(-9517805503),(-9517805472)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨650102852594,650102852655⟩,⟨(-9880179796),(-9880179735)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨478778901372,478778901460⟩,⟨10399128103,10399128192⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨200671487524,200671487656⟩,⟨20210154896,20210155025⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨53111548605,53111548800⟩,⟨13564575471,13564575667⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨9075472502,9075472794⟩,⟨5079663248,5079663538⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨891552511,891552900⟩,⟨1179481700,1179482089⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨8319911,8320388⟩,⟨169603211,169603690⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-11680672),(-11680144)⟩,⟨12649142,12649667⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-1687430),(-1686893)⟩,⟨(-259297),(-258761)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-54517),(-53857)⟩,⟨(-176033),(-175373)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨17997,18722⟩,⟨(-15252),(-14526)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨3053,3806⟩,⟨1406,2159⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-235),349⟩,⟨520,1103⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-325),40⟩,⟨(-10),356⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-122),27⟩,⟨(-62),87⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-8808930312874535881),(-8808930312874535798)⟩,⟨(-989783901744464978),(-989783901744464896)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-20585278273229368960),(-20585278273229368781)⟩,⟨(-161101886183308445),(-161101886183308267)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-20144422977953010924),(-20144422977953010727)⟩,⟨3897576960231232593,3897576960231232793⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-11808070802812305677),(-11808070802812305520)⟩,⟨6006631377517926053,6006631377517926211⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-4158636295552596681),(-4158636295552596568)⟩,⟨4422047670539103399,4422047670539103510⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-725117444373755529),(-725117444373755446)⟩,⟨1941823731957041087,1941823731957041170⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨39524286417651141,39524286417651214⟩,⟨552469751300398646,552469751300398721⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨58690832951567558,58690832951567636⟩,⟨107411602417016568,107411602417016648⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨18402286349572085,18402286349572185⟩,⟨14923713048044614,14923713048044718⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨3968724236570321,3968724236570433⟩,⟨1526746628059217,1526746628059327⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨740943415956732,740943415956853⟩,⟨111326289740600,111326289740720⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨137572152824509,137572152824629⟩,⟨3599401240091,3599401240211⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨28024065907842,28024065907945⟩,⟨(-646421907031),(-646421906925)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨6660064098577,6660064098661⟩,⟨(-196239150641),(-196239150557)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨1829529537495,1829529537555⟩,⟨(-36424087187),(-36424087127)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨406655777958,406655777991⟩,⟨(-4576636176),(-4576636146)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-193449947470225968877135),(-193449947470224840409865)⟩,⟨(-57413756582986716639994),(-57413756582985588171416)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-506244554724309385052981),(-506244554724307080075384)⟩,⟨(-84836645902514388490335),(-84836645902512083513883)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-613878471949753460871584),(-613878471949751777325462)⟩,⟨47247084474654576023684,47247084474656259557812⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-480066535030587298014370),(-480066535030586697337054)⟩,⟨223204798752412686475445,223204798752413287129964⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-224579685223765663325567),(-224579685223765521111962)⟩,⟨282304784398128963537027,282304784398129105736221⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-25226103558779412076216),(-25226103558779387368115)⟩,⟨203163185421813138887365,203163185421813163594738⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨46168527570721951034472,46168527570721953345929⟩,⟨88464240823112187248863,88464240823112189563942⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨38289443415518253968231,38289443415518254256509⟩,⟨18877278709218528393811,18877278709218528683454⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨16157153673954834962938,16157153673954835060288⟩,⟨(-2880662397632971421711),(-2880662397632971324522)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨4112803237154732655716,4112803237154732698164⟩,⟨(-4164325454702435580198),(-4164325454702435537984)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨410674677099604815836,410674677099604834678⟩,⟨(-1972170464871173493582),(-1972170464871173474777)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-209481666599332360610),(-209481666599332352595)⟩,⟨(-665715549672324782576),(-665715549672324774551)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-168299988711004921029),(-168299988711004917662)⟩,⟨(-187663346451432302856),(-187663346451432299480)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-83909516708526875703),(-83909516708526874271)⟩,⟨(-47165211213810064678),(-47165211213810063245)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-35496775713984275419),(-35496775713984274820)⟩,⟨(-10633627592548502451),(-10633627592548501851)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-9650103000902023038),(-9650103000902022865)⟩,⟨(-1756866930553449622),(-1756866930553449447)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-36908763913075031718375004),(-36908763913073880467870762)⟩,⟨(-22855693522352549644618368),(-22855693522351398394718888)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-109205442585090042527889659),(-109205442585086110411321182)⟩,⟨(-50276443529198731119190216),(-50276443529194799006116191)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-166764109503750516850566238),(-166764109503742686870417061)⟩,⟨(-32585516840526241436736862),(-32585516840518411466299982)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-181987843008831724939644873),(-181987843008819117934358708)⟩,⟨27731569667375229453492143,27731569667387836442650769⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-137999940146009843432441308),(-137999940145985076550725734)⟩,⟨93149196561140506832222216,93149196561165273703708271⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-56287888363773447883844513),(-56287888363736898617567334)⟩,⟨118246791480384370770093549,118246791480420920036383192⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨14835535779804465278729373,14835535779837116003347785⟩,⟨91391182023780992850569497,91391182023813643581542328⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨43658620875887957354362090,43658620875916236987045073⟩,⟨41691558509817907767329882,41691558509846187403238191⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨36667743052389112858693122,36667743052406865273327565⟩,⟨3959378256996857581782061,3959378257014609995781403⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨18469525437918521036293143,18469525437925068646073179⟩,⟨(-10641426514531096795954414),(-10641426514524549187511515)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨5293506087254454466296741,5293506087257178981805563⟩,⟨(-10489923451452041221067168),(-10489923451449316705839228)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-291269871264163538181990),(-291269871263360476363257)⟩,⟨(-6228587387626406417466968),(-6228587387625603355505732)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-1495945968397182469508376),(-1495945968397001018862483)⟩,⟨(-2850745834837379813395462),(-2850745834837198362574483)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-1196874600824922215273767),(-1196874600824865682767494)⟩,⟨(-1090626695472486351679110),(-1090626695472429819104472)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-662683649205363217539503),(-662683649205344559363758)⟩,⟨(-355932844353261027169947),(-355932844353242368976654)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-204700336054699815139717),(-204700336054695451025993)⟩,⟨(-78192402603887829350093),(-78192402603883465233520)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-12147060204001635471040729),(-12147060204001635161863048)⟩,⟨(-29397096601090593539897160),(-29397096601090593178394788)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-59036266294535430558856452),(-59036266294535429572532213)⟩,⟨(-65312045057750031788834698),(-65312045057750030681420597)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-135976114912774414561341478),(-135976114912774412824857693)⟩,⟨(-4497772465306134762244846),(-4497772465306132937225925)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-157144014677032081443785881),(-157144014677032078849702750)⟩,⟨241103169989361773674222017,241103169989361776217607150⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨29611464801593078730249988,29611464801593082965940795⟩,⟨643184664273780997810382191,643184664273781001817197073⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨495210370265569643157652008,495210370265569649599470065⟩,⟨965172007009163144952788007,965172007009163151092012814⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨1077849966112057410772877877,1077849966112057420159823232⟩,⟨913641303034224917904599265,913641303034224927187979285⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨1444055937056047676459076742,1444055937056047689227314189⟩,⟨437361644287887759769352925,437361644287887772609738772⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨1371635507905880005067533377,1371635507905880027713893748⟩,⟨(-190104240374869580295393713),(-190104240374869557523885052)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨944147662128745256656745451,944147662128745348763504650⟩,⟨(-622719631211597077469244426),(-622719631211596985323746592)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨436599322937069247799833827,436599322937069587057112903⟩,⟨(-722914677481525426853439080),(-722914677481525087610869536)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨68520824379239302133290297,68520824379240072071810029⟩,⟨(-585868662120413847652072883),(-585868662120413077738876195)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-104923033213818568316193365),(-104923033213816956113399595)⟩,⟨(-377373440054613666891706449),(-377373440054612054701404230)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-136818808387128734917173052),(-136818808387126293541003165)⟩,⟨(-203686065736446258987034370),(-203686065736443817613478743)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-98154711508503771672019521),(-98154711508501560302107393)⟩,⟨(-91922810793899416049406151),(-91922810793897204679237985)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-34440626188251124484194146),(-34440626188250246380045658)⟩,⟨(-25427501362865193796232621),(-25427501362864315691775024)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨758828501640791150841303986,758828501640821861976817457⟩,⟨86777754913566293384599303,86777754913597004474314551⟩⟩
lemma checked : cachedMomentRuleBox density1 hk9_1_8 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 9 8) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk9_1_8 (tableDensity true) (fullFactor true 9 8) density1_contains hk9_1_8_contains
noncomputable def atomAnswer : CBox := ⟨⟨4697823256906217193336524824,4697823256906217200385967178⟩,⟨(-1801071088791353294165222150),(-1801071088791353287226155601)⟩⟩
lemma atomChecked : tableAtomBox true ha9_1_8 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 9 8) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha9_1_8 9 8 ha9_1_8_contains
 def realAnswer : RBox := ⟨5456651758547008344077828810,5456651758547039062462784635⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 9 8) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm9_1_1_8
namespace hm9_0_1_9
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk9_1_9 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-216),556⟩,⟨(-436),338⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-810),1472⟩,⟨(-884),1398⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-1071),2419⟩,⟨(-1015),2472⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-3240),1563⟩,⟨(-1342),3458⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-4033),1565⟩,⟨(-3761),1837⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-1807),4863⟩,⟨(-4336),2381⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-5707),4327⟩,⟨(-2983),7024⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-8468),7849⟩,⟨(-9651),6706⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-6443),9072⟩,⟨(-6807),8981⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-6950),7567⟩,⟨(-6776),6210⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-7150),8563⟩,⟨(-6199),9569⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-8979),5812⟩,⟨(-8391),6662⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-4830),6756⟩,⟨(-6649),4580⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-2474),3838⟩,⟨(-3035),3992⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-2214),1937⟩,⟨(-1038),2198⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-701),648⟩,⟨(-298),700⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-1597311128986),(-1597311128853)⟩,⟨(-462251626107),(-462251625973)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-3204051807012),(-3204051806632)⟩,⟨(-997393411210),(-997393410829)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-2387322393490),(-2387322392824)⟩,⟨(-878638056396),(-878638055733)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-997119002686),(-997119001728)⟩,⟨(-487660914672),(-487660913715)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-250604786705),(-250604785446)⟩,⟨(-185376777614),(-185376776352)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-36027943746),(-36027942207)⟩,⟨(-48510786400),(-48510784856)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-1695634211),(-1695632446)⟩,⟨(-8492679836),(-8492678073)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨403588922,403591499⟩,⟨(-907262577),(-907259999)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨93751371,93754754⟩,⟨(-34266116),(-34262730)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨7888700,7892582⟩,⟨5704347,5708227⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-169532),(-165910)⟩,⟨1007598,1011213⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-125394),(-122416)⟩,⟨28655,31645⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-14349),(-11092)⟩,⟨(-17357),(-14095)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-100),2620⟩,⟨(-5327),(-2606)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨93,1860⟩,⟨(-1456),316⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-99),590⟩,⟨(-329),364⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨20692048456412256169,20692048456412256298⟩,⟨14902359162638923978,14902359162638924110⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨51743504468017445345,51743504468017445635⟩,⟨29063877117366329645,29063877117366329930⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨57108633108278272234,57108633108278272552⟩,⟨17303077564161723503,17303077564161723814⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨39442781647265932265,39442781647265932539⟩,⟨(-542516057779143768),(-542516057779143498)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨17492877038581403216,17492877038581403457⟩,⟨(-7188163262507717963),(-7188163262507717724)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨4767072654030343393,4767072654030343615⟩,⟨(-4977579787513543046),(-4977579787513542822)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨650097651712574496,650097651712574765⟩,⟨(-1869308357633134365),(-1869308357633134095)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-36094684744827151),(-36094684744826842)⟩,⟨(-464329494876766505),(-464329494876766197)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-40656508605259420),(-40656508605259024)⟩,⟨(-85030968970965406),(-85030968970965009)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-11837962675908675),(-11837962675908246)⟩,⟨(-12747597662236339),(-12747597662235911)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-2587647380408776),(-2587647380408346)⟩,⟨(-1769556225577014),(-1769556225576580)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-531267066123078),(-531267066122616)⟩,⟨(-263191850320097),(-263191850319640)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-116180129259975),(-116180129259461)⟩,⟨(-48269746184092),(-48269746183585)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-29047708088703),(-29047708088256)⟩,⟨(-11633220960178),(-11633220959732)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-8231984848249),(-8231984847922)⟩,⟨(-3426080046879),(-3426080046552)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-1854695652353),(-1854695652228)⟩,⟨(-803326936996),(-803326936873)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨202656813660187959556839,202656813660188668415324⟩,⟨255827533300506113060995,255827533300506821901504⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨605288468189892812702964,605288468189894212115617⟩,⟨589810854967958934730699,589810854967960334073635⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨909847607551584922806319,909847607551585871088135⟩,⟨522098174774931949412926,522098174774932897556704⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨933036489349891490061277,933036489349891861812394⟩,⟨147159799574293343530471,147159799574293715150579⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨644340032607073090949316,644340032607073202091387⟩,⟨(-204605953681170824300164),(-204605953681170713191729)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨263121891227112110861348,263121891227112127581282⟩,⟨(-301946838217122380133483),(-301946838217122363387495)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨21915448538387032557067,21915448538387034307600⟩,⟨(-200938380615706532940587),(-200938380615706531164801)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-45544410716576769295775),(-45544410716576768850350)⟩,⟨(-76769409308065404975864),(-76769409308065404528843)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-32887280478533605646411),(-32887280478533605461586)⟩,⟨(-13277233950930344213885),(-13277233950930344032515)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-12679377398503616171990),(-12679377398503616089014)⟩,⟨3201652075257685722866,3201652075257685804826⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-3120176804020496249313),(-3120176804020496214409)⟩,⟨3426399329808160946196,3426399329808160981208⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-360423482315388215026),(-360423482315388201046)⟩,⟨1598361586472910630949,1598361586472910645100⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨124651117395045441528,124651117395045447124⟩,⟨585020940271027939855,585020940271027945507⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨118559298070782109183,118559298070782111441⟩,⟨196193002273491208887,196193002273491211158⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨61455951587753398396,61455951587753399295⟩,⟨63341240858372434485,63341240858372435381⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨18065309800394476020,18065309800394476275⟩,⟨14787951113123177363,14787951113123177612⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-25629603809267520338847354),(-25629603809266897764613129)⟩,⟨55249414063674192472203501,55249414063674815042185891⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-49022125562712661860183620),(-49022125562710575618316344)⟩,⟨158311273901159571865772843,158311273901161658092407186⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-8021101424421867739178928),(-8021101424417896405314696)⟩,⟨227707213057554749783607030,227707213057558721087180865⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨83263085544470210960145552,83263085544477850832067048⟩,⟨226113274799561091149638384,226113274799568730990066298⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨162033778602369195181738454,162033778602384343906752033⟩,⟨142782334586900582833162555,142782334586915731548913334⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨169088464172739142911218992,169088464172759649126488676⟩,⟨23904206625530764120809478,23904206625551270347055133⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨106454329084483860018144241,106454329084502551340464508⟩,⟨(-58820910164372298754951877),(-58820910164353607416148615)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨29395775353895416643491545,29395775353913591565093069⟩,⟨(-73587726680221984623495228),(-73587726680203809699070095)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-15234219532908068399897045),(-15234219532898061089819689)⟩,⟨(-45519946574702558761511515),(-45519946574692551455756329)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-23425799537581379719777846),(-23425799537577102566378152)⟩,⟨(-14464563605689687021302307),(-14464563605685409870803441)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-15163099425724864388043280),(-15163099425723092145214250)⟩,⟨1618325797965834997841567,1618325797967607240793622⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-6338831761182262361276368),(-6338831761181807241008959)⟩,⟨5366015405225771868038836,5366015405226226989163681⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-1591997229800963488558887),(-1591997229800838500593983)⟩,⟨4196078036019066744588555,4196078036019191732995909⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨74511465492471847422265,74511465492513502100516⟩,⟨2376332795431043892303512,2376332795431085547068883⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨340718399988062096500809,340718399988074858910708⟩,⟨1100628965426955643932721,1100628965426968406334416⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨145146136919384134196351,145146136919387010923996⟩,⟨311192116905530456319682,311192116905533333037435⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-396666024865940699149603461),(-396666024865940698195952824)⟩,⟨166258528475762751589354900,166258528475762752509418372⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-1044350244878667412346005887),(-1044350244878667409405717612)⟩,⟨626498042334841867960040863,626498042334841870821198421⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-1248095186871811572346332500),(-1248095186871811567244477068)⟩,⟨1335424460343291906013884518,1335424460343291911055022900⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-786597803785367891870454360),(-786597803785367884509899321)⟩,⟨2087375074029357112177949994,2087375074029357119559019434⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨263000858524817973533675054,263000858524817983067714051⟩,⟨2404709791907283348160406946,2404709791907283357812376683⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨1401771550806757660784703440,1401771550806757672042078466⟩,⟨1914887786023687603288421008,1914887786023687614676989018⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨1974731279285325049641992668,1974731279285325062087723256⟩,⟨765389612354968595437045708,765389612354968607917304459⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨1695039485338167212766793835,1695039485338167225839297831⟩,⟨(-412899426065268982586571435),(-412899426065268969542811616)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨871427832725691742659394696,871427832725691760008121777⟩,⟨(-1034056026925348873962447680),(-1034056026925348856645260369)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨71285706730073534546006701,71285706730073588661429399⟩,⟨(-1000523702474361719640379621),(-1000523702474361665529137988)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-361475227864215768966238524),(-361475227864215589728844455)⟩,⟨(-622923569415323990410732855),(-622923569415323811172517593)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-438168300434958246643458743),(-438168300434957828427061268)⟩,⟨(-245278315881880487182060062),(-245278315881880068968682431)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-336333056825396575034425135),(-336333056825395607946073625)⟩,⟨(-21051661758540523005571983),(-21051661758539555920671994)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-203529404656019261565366891),(-203529404656017860731017328)⟩,⟨59245927332455373670250934,59245927332456774503291193⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-100414647985088410024046698),(-100414647985087178172929023)⟩,⟨57317877914286810486434759,57317877914288042337494626⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-29395287484169603826726211),(-29395287484169122444951595)⟩,⟨21799561773885662082556120,21799561773886143464447663⟩⟩
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
noncomputable def ans : CBox := ⟨⟨290347781309170014476058837,290347781309188073078198429⟩,⟨1126590598920995699647681269,1126590598921013758248661290⟩⟩
lemma checked : cachedMomentRuleBox density0 hk9_1_9 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 9 9) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk9_1_9 (tableDensity false) (fullFactor true 9 9) density0_contains hk9_1_9_contains
noncomputable def atomAnswer : CBox := ⟨⟨642745902983122997798431837,642745902983123000172548751⟩,⟨1400715046897365558447037835,1400715046897365560855872758⟩⟩
lemma atomChecked : tableAtomBox false ha9_1_9 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 9 9) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha9_1_9 9 9 ha9_1_9_contains
 def realAnswer : RBox := ⟨933093684292293012174490674,933093684292311073350747180⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 9 9) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm9_0_1_9
namespace hm9_1_1_9
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk9_1_9 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-44),104⟩,⟨(-77),70⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-154),256⟩,⟨(-154),257⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-218),408⟩,⟨(-170),453⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-596),253⟩,⟨(-273),578⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-656),308⟩,⟨(-676),290⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-290),816⟩,⟨(-674),436⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-938),668⟩,⟨(-497),1107⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-1334),1247⟩,⟨(-1527),1058⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-1019),1454⟩,⟨(-1090),1435⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-1155),1251⟩,⟨(-1113),1003⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-1187),1473⟩,⟨(-1047),1624⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-1572),980⟩,⟨(-1437),1167⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-845),1167⟩,⟨(-1171),771⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-405),667⟩,⟨(-533),685⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-379),346⟩,⟨(-163),379⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-124),120⟩,⟨(-51),124⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-184869221626),(-184869221595)⟩,⟨(-181938839829),(-181938839797)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-365399071717),(-365399071659)⟩,⟨(-365777240027),(-365777239968)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-263807159771),(-263807159675)⟩,⟨(-278312476009),(-278312475914)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-104582151609),(-104582151474)⟩,⟨(-125225258410),(-125225258277)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-24122965128),(-24122964953)⟩,⟨(-37899855341),(-37899855165)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-2819290404),(-2819290184)⟩,⟨(-8184418046),(-8184417828)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨65732737,65732994⟩,⟨(-1250202640),(-1250202380)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨84914124,84914511⟩,⟨(-119278686),(-119278301)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨14842369,14842888⟩,⟨(-2881854),(-2881330)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨1115298,1115920⟩,⟨1040249,1040871⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-43947),(-43339)⟩,⟨160885,161494⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-21784),(-21257)⟩,⟨2999,3526⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-2301),(-1703)⟩,⟨(-3292),(-2690)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨45,562⟩,⟨(-960),(-443)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨20,367⟩,⟨(-259),87⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-26),119⟩,⟨(-62),81⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨2215600083597230035,2215600083597230087⟩,⟨5313565338036827976,5313565338036828027⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨6469363307222423994,6469363307222424099⟩,⟨11753177276109976574,11753177276109976676⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨8777516407745844076,8777516407745844186⟩,⟨10208986532043297632,10208986532043297741⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨7395280507560035492,7395280507560035585⟩,⟨4733893390423772131,4733893390423772222⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨3987211812626000820,3987211812626000898⟩,⟨843958661492803863,843958661492803936⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨1382996466704296344,1382996466704296412⟩,⟨(-290724404534858219),(-290724404534858152)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨304229742166299234,304229742166299302⟩,⟨(-234733957403301076),(-234733957403301007)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨38546849099572105,38546849099572176⟩,⟨(-77469441220085883),(-77469441220085813)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨815392230245882,815392230245964⟩,⟨(-17060693117897579),(-17060693117897497)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-898370153311807),(-898370153311729)⟩,⟨(-2993838326909524),(-2993838326909444)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-285720062820565),(-285720062820490)⟩,⟨(-482890917265171),(-482890917265092)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-65933640286529),(-65933640286452)⟩,⟨(-81473283598306),(-81473283598228)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-14763903502215),(-14763903502134)⟩,⟨(-15847445390816),(-15847445390736)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-3636244356306),(-3636244356234)⟩,⟨(-3727372527040),(-3727372526968)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-1008817453131),(-1008817453073)⟩,⟨(-1029553446334),(-1029553446279)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-224518610437),(-224518610406)⟩,⟨(-230310446187),(-230310446154)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨3187789384197386503691,3187789384197981837126⟩,⟨109056210493381571129826,109056210493382166465108⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨42930322269559834104846,42930322269561008479315⟩,⟨275068753029308364289117,275068753029309538670795⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨132034612620399851525166,132034612620400645910753⟩,⟨308965564744720191442871,308965564744720985842706⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨203225022216157009403848,203225022216157319794633⟩,⟨209024688144560905522425,209024688144561215926632⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨190506861102566620702816,190506861102566712999732⟩,⟨64011386712876125770269,64011386712876218070486⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨112384428682546316718324,112384428682546330265501⟩,⟨(-27308392233553116700082),(-27308392233553103155577)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨37413887007598812582680,37413887007598813778360⟩,⟨(-43358634423314439594669),(-43358634423314438401477)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨1564722663271631171235,1564722663271631375464⟩,⟨(-24873575775114211440075),(-24873575775114211235966)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-5425345900136912089070),(-5425345900136912022678)⟩,⟨(-8105336171783500862411),(-8105336171783500795669)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-3329521527568693694318),(-3329521527568693665359)⟩,⟨(-1205356122885511921740),(-1205356122885511892687)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-1203020171742236814053),(-1203020171742236801774)⟩,⟨300031673786563474583,300031673786563486847⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-312927414428336887125),(-312927414428336882153)⟩,⟨304140891538189527754,304140891538189532706⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-56131537338544825088),(-56131537338544823071)⟩,⟨149603563193179498096,149603563193179500108⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-1210664695169117258),(-1210664695169116427)⟩,⟨61672970290297021459,61672970290297022287⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨4977998642965901823,4977998642965902163⟩,⟨23403933564264305248,23403933564264305587⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨2028921431543236838,2028921431543236940⟩,⟨6026081514868360872,6026081514868360976⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-7479879075711973898940468),(-7479879075711462318654718)⟩,⟨18559957657757132724017274,18559957657757644305018371⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-14155198591942181856486719),(-14155198591940467389902891)⟩,⟨53734013841385118933114122,53734013841386833402541580⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-1115023707403779693591183),(-1115023707400515560879966)⟩,⟨78952835315858090395020487,78952835315861354533920880⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨28537113935220048015349859,28537113935226328672834568⟩,⟨81363810693822837569194684,81363810693829118233800116⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨55916773133351262765799772,55916773133363718260494511⟩,⟨55492170565913208242607187,55492170565925663740259919⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨60957642327030875243513622,60957642327047735972867543⟩,⟨14765833817513164079997374,14765833817530024807654534⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨41745828443560720121180795,41745828443576085435313623⟩,⟨(-16682015481490117405626822),(-16682015481474752094950986)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨15026711413190453496257971,15026711413205387246790072⟩,⟨(-25677105276570999653307968),(-25677105276556065903533346)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-2566355236533104094707097),(-2566355236524887622427020)⟩,⟨(-18280708577247956789801265),(-18280708577239740316675782)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-7650981589045573547524360),(-7650981589042065722711383)⟩,⟨(-7673723848139800229488601),(-7673723848136292404094470)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-5951106448201871357642017),(-5951106448200419676065408)⟩,⟨(-1159978115508420836373450),(-1159978115506969154812795)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-3081564577747227531911906),(-3081564577746855234725064)⟩,⟨1069654958245316757433083,1069654958245689054463598⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-1209777181031471450333378),(-1209777181031369348852356)⟩,⟨1200406359292848573602433,1200406359292950675002497⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-362329795935241287378618),(-362329795935207297561222)⟩,⟨785837027225181941992485,785837027225215931793940⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-72389807759271508075896),(-72389807759261102642951)⟩,⟨398133909045305795605296,398133909045316201039445⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-5761043046432018857015),(-5761043046429674452510)⟩,⟨118140860195759994681988,118140860195762339088124⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-11545283895417428489128136),(-11545283895417428341761737)⟩,⟨5496444835180042767803380,5496444835180042896404135⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-24975774666662838697591430),(-24975774666662838246716468)⟩,⟨25189216486870971287278948,25189216486870971696399308⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨1438980176875668282330752,1438980176875669023474160⟩,⟨55047036064105152558455285,55047036064105153275339672⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨102283673721826115134524957,102283673721826116164088602⟩,⟨57496103681380781328641388,57496103681380782393481505⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨263016560134213391761598597,263016560134213393389010003⟩,⟨(-31454244042247064614147506),(-31454244042247062878244350)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨383045370965154801608013949,383045370965154804200594068⟩,⟨(-238055380320231494497266995),(-238055380320231491784358949)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨340938936089415533041097948,340938936089415536983633454⟩,⟨(-486864067383372525912008062),(-486864067383372521940600709)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨121910301412141683229021276,121910301412141688614768668⟩,⟨(-631129019972950762245697270),(-631129019972950756902121718)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-149326110030405012367668791),(-149326110030405002358359154)⟩,⟨(-578811158860976600957366022),(-578811158860976591000831141)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-322213020764196724388908280),(-322213020764196683209367118)⟩,⟨(-375403283448769501607711772),(-375403283448769460438207617)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-343699974295886984557334286),(-343699974295886840374834929)⟩,⟨(-147783334090200233121992704),(-147783334090200088929483590)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-264245102416319105721736858),(-264245102416318765756562056)⟩,⟨8160659792318282478435948,8160659792318622454967328⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-161397660449110385703989857),(-161397660449109596657371482)⟩,⟨73467658604465262256942900,73467658604466051306648280⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-81606358599971162601651781),(-81606358599970018251859160)⟩,⟨76691729311622224167296167,76691729311623368516826275⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-34080540961076920886721038),(-34080540961075913979204795)⟩,⟨51458109008491107129805361,51458109008492114036523989⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-8851517788264497674604516),(-8851517788264104089574184)⟩,⟨17605071762810718150260040,17605071762811111734959370⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-5010143683958034729899572),(-5010143683943206168674588)⟩,⟨(-313509840407780370181181497),(-313509840407765541596393511)⟩⟩
lemma checked : cachedMomentRuleBox density1 hk9_1_9 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 9 9) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk9_1_9 (tableDensity true) (fullFactor true 9 9) density1_contains hk9_1_9_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-840513873131776230994871443),(-840513873131776227890257017)⟩,⟨(-1831704292096554964196141299),(-1831704292096554961046126400)⟩⟩
lemma atomChecked : tableAtomBox true ha9_1_9 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 9 9) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha9_1_9 9 9 ha9_1_9_contains
 def realAnswer : RBox := ⟨(-845524016815734265824771015),(-845524016815719433958931605)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 9 9) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm9_1_1_9
namespace hm9_0_1_10
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk9_1_10 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-428),135⟩,⟨(-310),258⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-1026),702⟩,⟨(-1183),543⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-1692),1155⟩,⟨(-2233),615⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-1135),3189⟩,⟨(-2719),1607⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-2144),3533⟩,⟨(-1654),4020⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-4755),1618⟩,⟨(-2847),3581⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-2718),4972⟩,⟨(-5366),2263⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-7275),7135⟩,⟨(-5821),8550⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-8564),6630⟩,⟨(-8921),6469⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-6995),6373⟩,⟨(-5826),6279⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-7274),6373⟩,⟨(-8456),5205⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-5366),8147⟩,⟨(-5968),7815⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-6339),4455⟩,⟨(-4350),6160⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-3584),2352⟩,⟨(-3737),2820⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-1792),2059⟩,⟨(-2041),976⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-593),651⟩,⟨(-650),279⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨550355095272,550355095358⟩,⟨1050430625205,1050430625291⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨1083203263014,1083203263246⟩,⟨2143496425953,2143496426179⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨760511105141,760511105504⟩,⟨1668228508193,1668228508553⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨270544005716,270544006281⟩,⟨761555584479,761555585044⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨41165823556,41165824455⟩,⟨226232543745,226232544636⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-4068781010),(-4068779664)⟩,⟨45084755307,45084756650⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-3180132496),(-3180130744)⟩,⟨5783359021,5783360775⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-681891956),(-681889968)⟩,⟨358928551,358930541⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-75751265),(-75749176)⟩,⟨(-22036520),(-22034431)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-2660566),(-2657651)⟩,⟨(-7368690),(-7365776)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨554964,558313⟩,⟨(-625872),(-622525)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨99616,102784⟩,⟨28859,32034⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨1605,4399⟩,⟨15281,18076⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-3412),(-1569)⟩,⟨1562,3408⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-1555),(-361)⟩,⟨(-540),663⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-429),63⟩,⟨(-354),145⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨1743000238420732003,1743000238420732094⟩,⟨(-14802562292616066016),(-14802562292616065927)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨26564003847659425,26564003847659624⟩,⟨(-34809276230778680264),(-34809276230778680062)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-7857625550168280943),(-7857625550168280704)⟩,⟨(-34352903561689254715),(-34352903561689254473)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-12191370873375955568),(-12191370873375955353)⟩,⟨(-20125622118893357467),(-20125622118893357250)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-9202573752066884414),(-9202573752066884235)⟩,⟨(-6775859379738563733),(-6775859379738563556)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-4145894073567538244),(-4145894073567538090)⟩,⟨(-836466792856814613),(-836466792856814459)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-1197090986194314532),(-1197090986194314369)⟩,⟨307152976664633784,307152976664633948⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-229188808860852699),(-229188808860852528)⟩,⟨187874150537816537,187874150537816702⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-28841118603985008),(-28841118603984796)⟩,⟨53927098803138490,53927098803138705⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-1874244496762333),(-1874244496762039)⟩,⟨11355688110961337,11355688110961630⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨176582411197254,176582411197626⟩,⟨2105413003604289,2105413003604662⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨99218112589077,99218112589486⟩,⟨394090811419218,394090811419626⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨28619494255418,28619494255819⟩,⟨82676240797485,82676240797884⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨7808709494814,7808709495133⟩,⟨20577823346164,20577823346480⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨2232459024199,2232459024417⟩,⟨5913997681724,5913997681942⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨496935066997,496935067081⟩,⟨1350137144181,1350137144262⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨87448192258701412357768,87448192258701714184114⟩,⟨(-132569924654258648060099),(-132569924654258346213868)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨180024459282651762099049,180024459282652331489320⟩,⟨(-371185814923966883906024),(-371185814923966314454262)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨99268022510228203253838,99268022510228639956509⟩,⟨(-505572750017640023450489),(-505572750017639586673752)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-83689226901124646296695),(-83689226901124426049503)⟩,⟨(-460607801743851000406516),(-460607801743850780125868)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-206600236075746586585477),(-206600236075746529466281)⟩,⟨(-268758950855642746006327),(-268758950855642688896976)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-190955647686678991344816),(-190955647686678983857212)⟩,⟨(-70753886886433697145931),(-70753886886433689683871)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-100645369899183836230822),(-100645369899183835162490)⟩,⟨27776626970655278417718,27776626970655279479447⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-28011640852800077180713),(-28011640852800076934655)⟩,⟨37618364786594603119397,37618364786594603368442⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨565106123178092477647,565106123178092575944⟩,⟨18961562659744491126187,18961562659744491226569⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨4473215636945372169737,4473215636945372212581⟩,⟨5540281257535716377109,5540281257535716419954⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨2460690915492703791440,2460690915492703808353⟩,⟨731344524961258528314,731344524961258544975⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨894634829142396114703,894634829142396121119⟩,⟨(-223239346540227795767),(-223239346540227789428)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨263022750791437966856,263022750791437969637⟩,⟨(-217408660910093315861),(-217408660910093313082)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨67379243459893527225,67379243459893528503⟩,⟨(-113752633475791960224),(-113752633475791958943)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨15150551715499371710,15150551715499372267⟩,⟨(-49000620609469374676),(-49000620609469374114)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨2453450526892658666,2453450526892658833⟩,⟨(-13397816015316125679),(-13397816015316125510)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨24397251159716555012136035,24397251159716796099740002⟩,⟨6568408311889756555797215,6568408311889997646075104⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨68388444758168663797052653,68388444758169453343756599⟩,⟨8691802530131018437931562,8691802530131807993359980⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨94308221579824556528463339,94308221579826120752870015⟩,⟨(-13640484572801646014869960),(-13640484572800081776202415)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨87169608440578296220311202,87169608440581878425657368⟩,⟨(-52129634012078915887846594),(-52129634012075333673012586)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨46237248885122474171942296,46237248885129060289331890⟩,⟨(-79494627080894130403595536),(-79494627080887544286290209)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-4872356082760299837719420),(-4872356082752176712947262)⟩,⟨(-73443620036689501958870561),(-73443620036681378841998808)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-35207244750373909225536603),(-35207244750365176772575311)⟩,⟨(-39812440240156558953241380),(-39812440240147826506401053)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-34765582131997839967780040),(-34765582131989675547436550)⟩,⟨(-5152070501039779539962446),(-5152070501031615119117642)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-18202789232893695265071081),(-18202789232889584484790462)⟩,⟨11668735152385233284143898,11668735152389344067081113⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-3624199432254951916540405),(-3624199432252752776708440)⟩,⟨12062674021276189423452541,12062674021278388563985891⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨2635017775789515801132035,2635017775790303303777279⟩,⟨6572866800563456926884055,6572866800564244429086380⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨3268822126500206268602646,3268822126500403830728594⟩,⟨2145511157546171175529917,2145511157546368737188396⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨2133785385897952428350178,2133785385898020629040037⟩,⟨137343493027383325549832,137343493027451526133931⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨1078682416780385286429964,1078682416780405677568523⟩,⟨(-379575157218216045749909),(-379575157218195654591642)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨456182049762437586492513,456182049762443383976264⟩,⟨(-321054714556837883626904),(-321054714556832086109475)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨121763092438115108982929,121763092438116361263920⟩,⟨(-114022472511210517476034),(-114022472511209265181604)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨67598720025045189157154227,67598720025045189496766714⟩,⟨140163492712458540304889462,140163492712458540655457121⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨247529920900150118280024199,247529920900150119337082658⟩,⟨365778481813570295019961623,365778481813570296101993479⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨512410308592008085183696113,512410308592008087049697364⟩,⟨425378550810799326811929047,425378550810799328693885832⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨782794381679493633652379819,782794381679493636391516212⟩,⟨238344395592621565809879580,238344395592621568533803222⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨880498922053926572031134554,880498922053926575622274853⟩,⟨(-161602419821117867750539739),(-161602419821117864209849691)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨670869387081038358346852519,670869387081038362635573167⟩,⟨(-580945192565899157179849460),(-580945192565899152936236016)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨219642647985159300919432244,219642647985159305625002365⟩,⟨(-770705546536675636456005348),(-770705546536675631757833965)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-224386156734046826779035660),(-224386156734046821890915508)⟩,⟨(-629851991316947052524399085),(-629851991316947047621343828)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-437743639103001000527989742),(-437743639103000993744234126)⟩,⟨(-290191005354180621636818875),(-290191005354180614841592749)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-394181577214426799486793619),(-394181577214426778158649733)⟩,⟨21791777474278803697440362,21791777474278825026239458⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-226256816843943945249580886),(-226256816843943878203134131)⟩,⟨176744062739190478226897421,176744062739190545273108451⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-71907159482826958155752644),(-71907159482826780305207240)⟩,⟨189346467687463788915604092,189346467687463966767721335⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨12820494930641387488840317,12820494930641801395606064⟩,⟨136709379364341796582358226,136709379364342210490584496⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨37570275786088838505711402,37570275786089413794021705⟩,⟨78548154350958845827260170,78548154350959421115923232⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨30265552327513261252172807,30265552327513751791835339⟩,⟨36945708569257978134657271,36945708569258468674168252⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨10961701981973259104095807,10961701981973447417106935⟩,⟨10472800543214532797982990,10472800543214721110881347⟩⟩
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
noncomputable def ans : CBox := ⟨⟨391962561187775121012308293,391962561187782977667710345⟩,⟨(-138572103357586060557698825),(-138572103357578203904336352)⟩⟩
lemma checked : cachedMomentRuleBox density0 hk9_1_10 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 9 10) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk9_1_10 (tableDensity false) (fullFactor true 9 10) density0_contains hk9_1_10_contains
noncomputable def atomAnswer : CBox := ⟨⟨487791341404278693459800407,487791341404278694438555045⟩,⟨(-263758757988586915475851842),(-263758757988586914509776897)⟩⟩
lemma atomChecked : tableAtomBox false ha9_1_10 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 9 10) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha9_1_10 9 10 ha9_1_10_contains
 def realAnswer : RBox := ⟨879753902592053814372108700,879753902592061672206265390⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 9 10) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm9_0_1_10
namespace hm9_1_1_10
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk9_1_10 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-80),31⟩,⟨(-63),47⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-176),139⟩,⟨(-214),98⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-280),232⟩,⟨(-401),112⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-195),570⟩,⟨(-447),319⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-410),568⟩,⟨(-276),702⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-786),274⟩,⟨(-511),554⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-421),815⟩,⟨(-838),384⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-1158),1123⟩,⟨(-921),1353⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-1373),1050⟩,⟨(-1426),1032⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-1160),1054⟩,⟨(-942),1035⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-1256),1057⟩,⟨(-1437),876⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-903),1427⟩,⟨(-1043),1342⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-1096),777⟩,⟨(-732),1086⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-625),386⟩,⟨(-642),494⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-320),348⟩,⟨(-347),154⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-111),115⟩,⟨(-115),46⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-2423545542),(-2423545519)⟩,⟨184962548428,184962548454⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-6002598068),(-6002598025)⟩,⟨369969528363,369969528406⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-8776571037),(-8776570975)⟩,⟨276218656065,276218656121⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-9346014997),(-9346014912)⟩,⟨118412573980,118412574065⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-6162137604),(-6162137472)⟩,⟨32558796721,32558796851⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-2506990748),(-2506990556)⟩,⟨5979915897,5979916090⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-651853165),(-651852908)⟩,⟨696587615,696587872⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-109049940),(-109049642)⟩,⟨31893449,31893749⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-10803224),(-10802896)⟩,⟨(-5107126),(-5106800)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-270429),(-269956)⟩,⟨(-1197183),(-1196715)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨100246,100813⟩,⟨(-92613),(-92050)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨16470,17028⟩,⟨6418,6976⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨8,522⟩,⟨2747,3263⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-678),(-323)⟩,⟨230,586⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-301),(-60)⟩,⟨(-128),112⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-85),21⟩,⟨(-78),32⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨2086460150136171948,2086460150136171987⟩,⟨(-2640057330516612034),(-2640057330516611995)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨4157284992933132992,4157284992933133067⟩,⟨(-6681190851551276345),(-6681190851551276270)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨2663647417069311564,2663647417069311652⟩,⟨(-7491672837730308370),(-7491672837730308282)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨201877043984534519,201877043984534597⟩,⟨(-5233840066320870942),(-5233840066320870869)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-815625034985173630),(-815625034985173570)⟩,⟨(-2323646990374960376),(-2323646990374960317)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-604804385861055207),(-604804385861055159)⟩,⟨(-621441192435523109),(-621441192435523059)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-227143844629660875),(-227143844629660822)⟩,⟨(-77251573335805314),(-77251573335805267)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-54456138878127479),(-54456138878127434)⟩,⟨8083865135200401,8083865135200448⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-9232894229464957),(-9232894229464908)⟩,⟨6127939550944973,6127939550945024⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-1202214710719665),(-1202214710719607)⟩,⟨1682429817701294,1682429817701353⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-130743413424644),(-130743413424574)⟩,⟨354827459519527,354827459519596⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-13133909027200),(-13133909027126)⟩,⟨70628368182500,70628368182570⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-1410581420383),(-1410581420317)⟩,⟨14995322008201,14995322008265⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-198366154050),(-198366153996)⟩,⟨3657237338763,3657237338820⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-41112605525),(-41112605483)⟩,⟨1021045721200,1021045721241⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-8404789151),(-8404789125)⟩,⟨228787272981,228787273003⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨49926735260329443661332,49926735260329697163912⟩,⟨(-18052488020974719180697),(-18052488020974465680172)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨120807496598717822809590,120807496598718300661374⟩,⟨(-62232732625939402264087),(-62232732625938924418678)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨122871115645078778284344,122871115645079144142983⟩,⟨(-110160079339990952674639),(-110160079339990586823666)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨64574029574328333447689,64574029574328517429149⟩,⟨(-129251046216572570311173),(-129251046216572386333151)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-2390601859551234944366),(-2390601859551187547709)⟩,⟨(-100740781267640762792822),(-100740781267640715395138)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-33218083017705301808166),(-33218083017705295817948)⟩,⟨(-48521935387827527613959),(-48521935387827521621173)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-27945913652121049715956),(-27945913652121048993411)⟩,⟨(-9698062446746075796772),(-9698062446746075073584)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-12378034248459700389241),(-12378034248459700278024)⟩,⟨4273665127373804533151,4273665127373804644064⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-2803955550197652502411),(-2803955550197652466403)⟩,⟨4399150900943331409024,4399150900943331444832⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨162798912824651162014,162798912824651177140⟩,⟨1921154030098884967719,1921154030098884982850⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨439379640632986811744,439379640632986817629⟩,⟨527863451508436352216,527863451508436358125⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨232054901101801481058,232054901101801483317⟩,⟨80341716213480909331,80341716213480911595⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨90481648028751919529,90481648028751920531⟩,⟨(-11082065222641092090),(-11082065222641091089)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨31673290607102453430,31673290607102453906⟩,⟨(-16202326382911776485),(-16202326382911776013)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨10543427561227781513,10543427561227781733⟩,⟨(-9066342364780098963),(-9066342364780098749)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨2504602621965982636,2504602621965982705⟩,⟨(-2736537957792016661),(-2736537957792016590)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨8115868262672783511857986,8115868262672981614461102⟩,⟨1744663274446961535234846,1744663274447159637362525⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨23034002255350309192379645,23034002255350958025356659⟩,⟨1932454382887755169339670,1932454382888404000651980⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨32576651361545603302297165,32576651361546888964371846⟩,⟨(-5415460782330038770137107),(-5415460782328753110988921)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨31479757225260620943304413,31479757225263565842432677⟩,⟨(-18168738218568064595046697),(-18168738218565119698190201)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨18555640217843037366009239,18555640217848452546643581⟩,⟨(-27948304084042920039735283),(-27948304084037504859487765)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨837934731229888051490849,837934731236567060070203⟩,⟨(-27021786903091883505497129),(-27021786903085204495488067)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-11083563395871831765821862),(-11083563395864653255430720)⟩,⟨(-16220109754660562099674398),(-16220109754653383587987497)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-12619830017033033138444270),(-12619830017026324653539447)⟩,⟨(-3856360238080774738282083),(-3856360238074066253434096)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-7702219647885400265435769),(-7702219647882025161124248)⟩,⟨3135014971808570585388123,3135014971811945689151316⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-2487697908133541283093843),(-2487697908131737665772039)⟩,⟨4288592621771541268404765,4288592621773344885581376⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨231662332312801485993030,231662332313446556050306⟩,⟨2806239141177580511460141,2806239141178225581599693⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨894214578500942780032489,894214578501104381715304⟩,⟨1248598934625556760072030,1248598934625718361842766⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨716045086398251789107428,716045086398307503353354⟩,⟨382863500140878678049928,382863500140934392316449⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨412954745046241607942088,412954745046258247395547⟩,⟨51913851776682479074383,51913851776699118524866⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨194185742454962816019195,194185742454967542961840⟩,⟨(-26015559439483723725276),(-26015559439478996788332)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨55419328453648158770916,55419328453649179347916⟩,⟨(-15184486799761335880314),(-15184486799760315305576)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨2205043195371115835691231,2205043195371115883652600⟩,⟨4067040364404954234696789,4067040364404954288607141⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨9615535969129783779059728,9615535969129783931229631⟩,⟨8544007911730799080234050,8544007911730799244946960⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨19985910899423965948137574,19985910899423966213509386⟩,⟨(-1709767617310996988331129),(-1709767617310996718370797)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨18594811125205005184001797,18594811125205005575760449⟩,⟨(-38832780211315104113768238),(-38832780211315103740252164)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-18721450584466142071890999),(-18721450584466141434914294)⟩,⟨(-96276906638799290194156599),(-96276906638799289602439462)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-100515607543472963723050007),(-100515607543472962695441191)⟩,⟨(-135542310915991586235426070),(-135542310915991585248828341)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-195426213603190021144469115),(-195426213603190019644758770)⟩,⟨(-111548698327179637170181888),(-111548698327179635675783605)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-245517709485680709179778715),(-245517709485680707189310206)⟩,⟨(-21540563369462038514196867),(-21540563369462036503393321)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-216749462298069948542922573),(-216749462298069944575687802)⟩,⟨83389383499458440390622697,83389383499458444376338395⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-130636689760978664337720604),(-130636689760978648046300732)⟩,⟨144446886994835911165918836,144446886994835927458530365⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-39617484662549319472508415),(-39617484662549265525911790)⟩,⟨143806720615676368214077613,143806720615676422155407180⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨18901872847452274594969679,18901872847452419269954076⟩,⟨104951649064351360792724876,104951649064351505463882546⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨39789184262518949177442990,39789184262519286953416390⟩,⟨60314554583055358785927646,60314554583055696561719710⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨36520628924699368287500933,36520628924699838252722538⟩,⟨27968593283455061101799359,27968593283455531067673411⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨23306884363724422894776822,23306884363724823847849174⟩,⟨10333274477393485637543251,10333274477393886591183306⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨7808529530565552546974736,7808529530565706508637726⟩,⟨2379325037323037907459974,2379325037323191869325300⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-114494128716723121448857116),(-114494128716716669605593958)⟩,⟨16866878385522736559863126,16866878385529188393096920⟩⟩
lemma checked : cachedMomentRuleBox density1 hk9_1_10 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 9 10) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk9_1_10 (tableDensity true) (fullFactor true 9 10) density1_contains hk9_1_10_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-637880984913287523496571982),(-637880984913287522216662070)⟩,⟨344915298908152118974323635,344915298908152120237652409⟩⟩
lemma atomChecked : tableAtomBox true ha9_1_10 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 9 10) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha9_1_10 9 10 ha9_1_10_contains
 def realAnswer : RBox := ⟨(-752375113630010645045429098),(-752375113630004191722256028)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 9 10) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm9_1_1_10
namespace hm9_0_1_11
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk9_1_11 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-126),315⟩,⟨(-157),291⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-607),621⟩,⟨(-332),893⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-952),813⟩,⟨(-219),1545⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-2412),582⟩,⟨(-1412),1583⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-2425),2086⟩,⟨(-3335),1176⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-1636),4224⟩,⟨(-2801),3086⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-4380),1876⟩,⟨(-2154),4033⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-5059),5746⟩,⟨(-6435),4283⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-5880),7019⟩,⟨(-5335),7669⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-5657),6221⟩,⟨(-5716),5396⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-5086),5499⟩,⟨(-3879),6682⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-6668),4474⟩,⟨(-6570),4816⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-3725),5387⟩,⟨(-5172),3744⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-2027),3037⟩,⟨(-2374),3177⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-1742),1504⟩,⟨(-835),1727⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-545),498⟩,⟨(-234),545⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨244675791796,244675791866⟩,⟨(-728856653373),(-728856653303)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨511035779869,511035780057⟩,⟨(-1476644413392),(-1476644413204)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨426139769020,426139769343⟩,⟨(-1123091406973),(-1123091406648)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨224556639404,224556639871⟩,⟨(-485524617934),(-485524617464)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨83714605496,83714606114⟩,⟨(-129500834584),(-129500833969)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨22513495768,22513496503⟩,⟨(-21060224474),(-21060223739)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨4265814894,4265815942⟩,⟨(-1646284006),(-1646282962)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨534528511,534530054⟩,⟨98981372,98982914⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨34495359,34497272⟩,⟨44971561,44973477⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-1427980),(-1426024)⟩,⟨5545306,5547262⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-598391),(-596353)⟩,⟨170136,172172⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-55318),(-52947)⟩,⟨(-59565),(-57196)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨2885,5332⟩,⟨(-13463),(-11016)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨1662,3491⟩,⟨(-1727),100⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨139,1228⟩,⟨(-258),835⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-112),294⟩,⟨(-72),342⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-7326062390567394783),(-7326062390567394720)⟩,⟨3009130364204545133,3009130364204545194⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-16196521690709298905),(-16196521690709298778)⟩,⟨9065075317149293818,9065075317149293943⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-13921043317924639158),(-13921043317924639014)⟩,⟨12812021693167009642,12812021693167009783⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-6063935408424526047),(-6063935408424525928)⟩,⟨11226936989487802787,11226936989487802909⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-554218410979997410),(-554218410979997316)⟩,⟨6253239717286749420,6253239717286749515⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨843713345784295683,843713345784295760⟩,⟨2203458092198950321,2203458092198950396⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨521050942719039868,521050942719039961⟩,⟨469793091123780335,469793091123780428⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨164985865308402727,164985865308402846⟩,⟨46548204353686439,46548204353686559⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨35706237842508937,35706237842509105⟩,⟨(-5127936263864070),(-5127936263863901)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨6090199102229345,6090199102229542⟩,⟨(-3290016136491273),(-3290016136491078)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨931840919092756,931840919092972⟩,⟨(-898551230609742),(-898551230609531)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨146619687501125,146619687501328⟩,⟨(-206462837653974),(-206462837653772)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨27024406317974,27024406318189⟩,⟨(-48258578456161),(-48258578455943)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨6304506246520,6304506246724⟩,⟨(-12582843244262),(-12582843244059)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨1788587868201,1788587868356⟩,⟨(-3660477350479),(-3660477350323)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨410548942250,410548942317⟩,⟨(-835543811618),(-835543811554)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-67795202912663277804360),(-67795202912663157773278)⟩,⟨(-18426714531005101166823),(-18426714531004981146568)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-181505721080293096622479),(-181505721080292826388344)⟩,⟨(-23858223033417439985014),(-23858223033417169774601)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-228014140203310641415091),(-228014140203310407632905)⟩,⟨30552986433040256650352,30552986433040490414896⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-183476766539319088138354),(-183476766539318983331197)⟩,⟨104059225883686243628561,104059225883686348436944⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-83061862181792140827453),(-83061862181792117245078)⟩,⟨130306262390342955996052,130306262390342979594640⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨673265980328622163936,673265980328625592085⟩,⟨94128797874725261404350,94128797874725264842759⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨29563427185201989218487,29563427185201989746781⟩,⟨39111848193555212499808,39111848193555213027333⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨21736124090781450087741,21736124090781450198269⟩,⟨5427801654998728522017,5427801654998728629842⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨8332292437885332903785,8332292437885332947235⟩,⟨(-3956838673477025027663),(-3956838673477024984609)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨1563584830524408905237,1563584830524408922962⟩,⟨(-3158985260931479479010),(-3158985260931479461014)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-207115811316052184259),(-207115811316052175644)⟩,⟨(-1276030137591784258179),(-1276030137591784249443)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-307804502756528158840),(-307804502756528154758)⟩,⟨(-357459213259137495385),(-357459213259137491301)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-163062373022202981843),(-163062373022202980010)⟩,⟨(-68793161400498974446),(-68793161400498972626)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-69258348303801531384),(-69258348303801530578)⟩,⟨(-2930500514377329152),(-2930500514377328354)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-26552764240976067194),(-26552764240976066848)⟩,⟨5403926186111497599,5403926186111497942⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-6848871687979015117),(-6848871687979015010)⟩,⟨2298086874531873442,2298086874531873547⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨871969768880981589413377,871969768881063370203096⟩,⟨(-9488624766080795243944975),(-9488624766080713464478365)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-1236839530796632933604774),(-1236839530796367905778549)⟩,⟨(-26040416947258275142765392),(-26040416947258010118975854)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-11482275424082386312112582),(-11482275424081729395294613)⟩,⟨(-34360935407310938484763710),(-34360935407310281572505838)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-25813245432603154559145326),(-25813245432601689493568315)⟩,⟨(-29129204275698428979219602),(-29129204275696963915713856)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-33664471118312539728052331),(-33664471118310035308279770)⟩,⟨(-11578928508348334519822171),(-11578928508345830098469179)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-27773402724688477894060474),(-27773402724685549159174938)⟩,⟨7774969319822496222244256,7774969319825424961090012⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-12393703363160510155936473),(-12393703363156688140459371)⟩,⟨17092097371904050492058284,17092097371907872509028098⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨1214834013140120862816081,1214834013143276708468051⟩,⟨14118404476204972191114370,14118404476208128035870455⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨6456484661122636567163716,6456484661124319200661228⟩,⟨6058520555153849091230807,6058520555155531723663092⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨5235931322612592418548224,5235931322613545974683779⟩,⟨159940206585414796640192,159940206586368352764117⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨2368507377411528476748217,2368507377411824840060113⟩,⟨(-1824052475786225987178009),(-1824052475785929623538445)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨483854762611676902337232,483854762611772835690783⟩,⟨(-1602021540636728110113804),(-1602021540636632176621817)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-214813013701299230446838),(-214813013701268545238335)⟩,⟨(-900843393331924940408789),(-900843393331894255204797)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-300751135789250328677039),(-300751135789242087776562)⟩,⟨(-399439463483600069953371),(-399439463483591829088171)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-196279605434233437385273),(-196279605434231300831188)⟩,⟨(-147509482915817783380813),(-147509482915815646853366)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-64581250280066743873416),(-64581250280066291084939)⟩,⟨(-35453706733784310932352),(-35453706733783858152671)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨44872130899501555754874340,44872130899501555871694099⟩,⟨(-24621897599280414180151220),(-24621897599280414066522338)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨115959887223003237154796404,115959887223003237515684178⟩,⟨(-88065994208634593288581887),(-88065994208634592934648998)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨130684053002921896937678967,130684053002921897566624392⟩,⟨(-177700665804264252608918331),(-177700665804264251983163959)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨62405432016489663001730972,62405432016489663914444406⟩,⟨(-265648981297655048281817940),(-265648981297655047361463504)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-75708310357184521427560100),(-75708310357184520236966991)⟩,⟨(-291497291008220021931967162),(-291497291008220020722409725)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-215473349383515651627294187),(-215473349383515650180105734)⟩,⟨(-211169699430643577992619308),(-211169699430643576531951067)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-270948244040513988959825928),(-270948244040513987360741693)⟩,⟨(-50837340567553088875768197),(-50837340567553087276124106)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-210216029332439045090976940),(-210216029332439043437347849)⟩,⟨100395647730084248911181035,100395647730084250558297220⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-84067395275340333202297656),(-84067395275340330790875997)⟩,⟨165280557206237456629018456,165280557206237459037000896⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨25512050493253032835932753,25512050493253040354481583⟩,⟨138930665715139221726058281,138930665715139229244727200⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨74678453128982508766221041,74678453128982531217638334⟩,⟨72452812347729519875364222,72452812347729542326822372⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨72549281881963776568549613,72549281881963847251021711⟩,⟨15884337179650435456436654,15884337179650506138256895⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨49286147337910906147583221,49286147337911063169225765⟩,⟨(-12560334263515044428537662),(-12560334263514887407339608)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨26667716786819654982200965,26667716786819864098941710⟩,⟨(-18600124012617533128073247),(-18600124012617324011352786)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨11782672595197075685462603,11782672595197247860716658⟩,⟨(-13520961420326174969800979),(-13520961420326002794419819)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨3188306006987427974031105,3188306006987492666579032⟩,⟨(-4736238483569974358226308),(-4736238483569909665613119)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-56003130973202487451874092),(-56003130973199376694348157)⟩,⟨(-122661078704801650146965710),(-122661078704798539387769136)⟩⟩
lemma checked : cachedMomentRuleBox density0 hk9_1_11 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 9 11) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk9_1_11 (tableDensity false) (fullFactor true 9 11) density0_contains hk9_1_11_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-96520384490866105229380419),(-96520384490866104867835080)⟩,⟨(-153079576043343779830126115),(-153079576043343779464424646)⟩⟩
lemma atomChecked : tableAtomBox false ha9_1_11 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 9 11) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha9_1_11 9 11 ha9_1_11_contains
 def realAnswer : RBox := ⟨(-152523515464068592781254511),(-152523515464065481462183237)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 9 11) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm9_0_1_11
namespace hm9_1_1_11
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk9_1_11 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-31),60⟩,⟨(-32),58⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-118),108⟩,⟨(-66),160⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-190),131⟩,⟨(-52),271⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-423),112⟩,⟨(-279),255⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-386),394⟩,⟨(-571),210⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-286),687⟩,⟨(-436),540⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-709),294⟩,⟨(-369),627⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-799),915⟩,⟨(-1018),679⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-934),1131⟩,⟨(-854),1227⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-934),1030⟩,⟨(-941),877⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-845),952⟩,⟨(-650),1141⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-1171),754⟩,⟨(-1130),840⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-650),933⟩,⟨(-913),630⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-336),529⟩,⟨(-417),547⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-297),270⟩,⟨(-132),296⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-97),96⟩,⟨(-41),97⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨87649503481,87649503507⟩,⟨(-81851646533),(-81851646509)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨175573758514,175573758548⟩,⟨(-164707891606),(-164707891568)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨132643790523,132643790577⟩,⟨(-123234550409),(-123234550356)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨59232003269,59232003344⟩,⟨(-51688383025),(-51688382951)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨17954403998,17954404092⟩,⟨(-13088885334),(-13088885243)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨3985011049,3985011162⟩,⟨(-1901290740),(-1901290629)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨656209736,656209894⟩,⟨(-78417022),(-78416863)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨74341729,74341964⟩,⟨29949663,29949899⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨4084987,4085288⟩,⟨7550399,7550698⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-329675),(-329356)⟩,⟨834346,834665⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-99964),(-99615)⟩,⟨17933,18283⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-8540),(-8120)⟩,⟨(-10949),(-10528)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨697,1152⟩,⟨(-2330),(-1876)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨312,660⟩,⟨(-278),74⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨10,231⟩,⟨(-45),176⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-31),59⟩,⟨(-20),72⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-1764689033916151952),(-1764689033916151923)⟩,⟨(-288153728429604894),(-288153728429604864)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-4191521382131787376),(-4191521382131787325)⟩,⟨(-191246782807322322),(-191246782807322272)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-4201724829646340975),(-4201724829646340920)⟩,⟨753512397307977465,753512397307977516⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-2502981057258349849),(-2502981057258349801)⟩,⟨1342539773745089242,1342539773745089290⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-857961536597705958),(-857961536597705919)⟩,⟨1045867073030656953,1045867073030656992⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-112290772566792861),(-112290772566792830)⟩,⟨470507974293513707,470507974293513736⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨34751230776244969,34751230776245001⟩,⟨131670740150774069,131670740150774102⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨21855777513454103,21855777513454139⟩,⟨23156128637159287,23156128637159324⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨6137126609098850,6137126609098893⟩,⟨2247641717666677,2247641717666714⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨1242659470293390,1242659470293436⟩,⟨(-47821879009399),(-47821879009357)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨219143000596552,219143000596598⟩,⟨(-75185525284669),(-75185525284625)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨38784594360827,38784594360866⟩,⟨(-22349100294674),(-22349100294634)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨7675374882678,7675374882716⟩,⟨(-5634293839489),(-5634293839448)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨1807078280208,1807078280248⟩,⟨(-1489687108318),(-1489687108280)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨497250426532,497250426567⟩,⟨(-431822638009),(-431822637975)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨110916900881,110916900903⟩,⟨(-98206414854),(-98206414832)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-14486133106720114170262),(-14486133106720013382285)⟩,⟨(-18485733500507763737587),(-18485733500507662948487)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-43114272595832161447843),(-43114272595831934708845)⟩,⟨(-42162955686707423381924),(-42162955686707196640460)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-64203707552903759272266),(-64203707552903563439839)⟩,⟨(-36151762765083219927582),(-36151762765083024093322)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-64570977974147695335766),(-64570977974147607807526)⟩,⟨(-8256256751551036373842),(-8256256751550948845722)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-42797275090563606431592),(-42797275090563586878242)⟩,⟨16679990765625432049383,16679990765625451601093⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-15536946736458758075142),(-15536946736458755331914)⟩,⟨22301190757431619120159,22301190757431621862363⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨609943868399371146982,609943868399371508358⟩,⟨13876711160060692236328,13876711160060692597785⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨4160832363566195348253,4160832363566195396303⟩,⟨4670303360177681309365,4670303360177681357682⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨2506586344599158193619,2506586344599158209533⟩,⟨388899382387414596132,388899382387414612079⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨829880122934945933462,829880122934945939805⟩,⟨(-471277144673293519675),(-471277144673293513362)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨143175048520746431486,143175048520746434546⟩,⟨(-314823989451371551374),(-314823989451371548328)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-16668002754850691864),(-16668002754850690414)⟩,⟨(-124518744002771756650),(-124518744002771755197)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-26800568952921045482),(-26800568952921044822)⟩,⟨(-38946861582915502428),(-38946861582915501765)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-15337638224651353376),(-15337638224651353077)⟩,⟨(-10616707798103391899),(-10616707798103391599)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-6875760733456699214),(-6875760733456699079)⟩,⟨(-2587540725689886457),(-2587540725689886318)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-1912863967838644472),(-1912863967838644421)⟩,⟨(-460655350010743600),(-460655350010743549)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨126425035716580758456322,126425035716647954014277⟩,⟨(-3128126587197408718799184),(-3128126587197341523000103)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-787237340483399792218548),(-787237340483182009997631)⟩,⟨(-8705733879681547411210313),(-8705733879681329628213596)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-4229714036667487281657425),(-4229714036666947355036760)⟩,⟨(-11822034981664514076249973),(-11822034981663974148675141)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-9074905958337635968224801),(-9074905958336431556457004)⟩,⟨(-10566758504162328966490401),(-10566758504161124554171829)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-12008979029701547805458103),(-12008979029699488650199252)⟩,⟨(-4944782376782282066003040),(-4944782376780222910942451)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-10430554918348253927230502),(-10430554918345845866994336)⟩,⟨1851536134780855840577804,1851536134783263900052623⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-5331462811625285406750653),(-5331462811622143501519824)⟩,⟨5699538230223604390735527,5699538230226746295643698⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-338282995586669633747914),(-338282995584076542689499)⟩,⟨5310145641983928124918684,5310145641986521216158872⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨2016418238185473426014762,2016418238186854880440707⟩,⟨2744396974026383127398543,2744396974027764582053531⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨1990529008598282889886006,1990529008599064958609986⟩,⟨538825009733362199978440,538825009734144268708339⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨1113742355603571784574913,1113742355603814548678236⟩,⟨(-415745048477387662935549),(-415745048477144898894604)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨403999723627706885794722,403999723627785357578799⟩,⟨(-518537522500527468932322),(-518537522500448997175561)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨67360107111580383903690,67360107111605451497446⟩,⟨(-345175238846307980607613),(-345175238846282913013847)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-32924381368624951749623),(-32924381368618227224144)⟩,⟨(-178980693843610697074957),(-178980693843603972543449)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-37214885960665363821026),(-37214885960663621968360)⟩,⟨(-77789918548603921372247),(-77789918548602179515003)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-13983570156651659096488),(-13983570156651290143721)⟩,⟨(-21177467980214421948718),(-21177467980214052994462)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨1297806939542774344748800,1297806939542774362627060⟩,⟨(-794448412693344272930311),(-794448412693344256726648)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨2639126402320711988572765,2639126402320712043112003⟩,⟨(-3319040213689176979393577),(-3319040213689176928119678)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-956865650694059289682110),(-956865650694059200592963)⟩,⟨(-6573352458106103521611985),(-6573352458106103432629766)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-13332314235026839089090315),(-13332314235026838966429958)⟩,⟨(-5341270305177974744051921),(-5341270305177974613566539)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-31861161225603254137425782),(-31861161225603253942059346)⟩,⟨8650100633870850787317487,8650100633870850999355978⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-43147792600147378792315298),(-43147792600147378451644016)⟩,⟨37853929487419987480792482,37853929487419987833600584⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-32031755457900817313352591),(-32031755457900816802665439)⟩,⟨70511231993855262280192889,70511231993855262790770701⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨1358585071100359118340980,1358585071100359793271609⟩,⟨85896923910701908874191747,85896923910701909540682899⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨38028891388210391967283425,38028891388210393409745297⟩,⟨72676100876536187668405807,72676100876536189105586507⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨57172371249999011857177565,57172371249999017622315936⟩,⟨39869692285900484405285015,39869692285900490170984248⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨53598382289724473574025536,53598382289724491642519843⟩,⟨7091518778370910810147220,7091518778370928880942823⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨37051639375332545682106759,37051639375332603205102806⟩,⟨(-12506144161327687598048045),(-12506144161327630074133863)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨19780570791451807561288304,19780570791451935688938947⟩,⟨(-18031183183803997080074304),(-18031183183803868952649089)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨8094195705129054892765263,8094195705129225709725848⟩,⟨(-15150619138396613786669725),(-15150619138396442970112452)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨2365418648932625606753802,2365418648932766328161300⟩,⟨(-9276952828857480831398480),(-9276952828857340110282236)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨385316831613801784234361,385316831613854672482798⟩,⟨(-3049930061538118146996537),(-3049930061538065258846852)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨10606515001255937156344201,10606515001258491853466862⟩,⟨37313009569859085915877950,37313009569861640616683955⟩⟩
lemma checked : cachedMomentRuleBox density1 hk9_1_11 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 9 11) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk9_1_11 (tableDensity true) (fullFactor true 9 11) density1_contains hk9_1_11_contains
noncomputable def atomAnswer : CBox := ⟨⟨126218964334209521750245873,126218964334209522223035932⟩,⟨200180984056680326991939922,200180984056680327470164919⟩⟩
lemma atomChecked : tableAtomBox true ha9_1_11 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 9 11) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha9_1_11 9 11 ha9_1_11_contains
 def realAnswer : RBox := ⟨136825479335465458806590074,136825479335468014176502794⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 9 11) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm9_1_1_11
namespace hm9_0_1_12
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk9_1_12 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-225),146⟩,⟨(-257),114⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-453),616⟩,⟨(-722),351⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-542),1025⟩,⟨(-1200),375⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-350),1613⟩,⟨(-776),1185⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-1598),1244⟩,⟨(-641),2198⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-3060),1321⟩,⟨(-2610),1774⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-1576),3784⟩,⟨(-3061),2265⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-4114),3196⟩,⟨(-2860),4300⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-5034),4561⟩,⟨(-5779),3856⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-5031),4571⟩,⟨(-4526),4719⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-3924),3879⟩,⟨(-4930),2747⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-3393),4960⟩,⟨(-3531),5024⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-4186),2844⟩,⟨(-2942),3968⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-2360),1604⟩,⟨(-2473),1831⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-1165),1352⟩,⟨(-1337),655⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-384),422⟩,⟨(-420),182⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-413307804133),(-413307804088)⟩,⟨194795699251,194795699295⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-844532468152),(-844532468051)⟩,⟨394020833507,394020833610⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-659382362837),(-659382362683)⟩,⟨292707021440,292707021594⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-303406201884),(-303406201644)⟩,⟨115271670759,115271670997⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-92001511756),(-92001511367)⟩,⟨22818624616,22818625008⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-19239294926),(-19239294336)⟩,⟨450139326,450139919⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-2745740455),(-2745739705)⟩,⟨(-944596674),(-944595923)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-231831892),(-231831083)⟩,⟨(-264242064),(-264241253)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-785583),(-784416)⟩,⟨(-37318600),(-37317427)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨2882717,2884281⟩,⟨(-2534119),(-2532557)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨405426,406999⟩,⟨117957,119532⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨11170,12491⟩,⟨53031,54346⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-7389),(-5865)⟩,⟨5350,6872⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-2524),(-1222)⟩,⟨(-980),324⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-769),81⟩,⟨(-822),28⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-186),151⟩,⟨(-282),54⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨3013883663743193355,3013883663743193390⟩,⟨2408033670097527291,2408033670097527326⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨7736487713456553239,7736487713456553304⟩,⟨4738159829970047927,4738159829970047986⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨8873309059044364386,8873309059044364451⟩,⟨2820578555902077225,2820578555902077288⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨6338729768072996946,6338729768072997007⟩,⟨(-226508971694034026),(-226508971694033965)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨2835468156807175740,2835468156807175795⟩,⟨(-1397493302242552438),(-1397493302242552381)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨720838923805933004,720838923805933059⟩,⟨(-967570447883073375),(-967570447883073319)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨53735434107492860,53735434107492924⟩,⟨(-361091097180948463),(-361091097180948398)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-29818430992773805),(-29818430992773735)⟩,⟨(-85867359697723680),(-85867359697723608)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-13667607679511106),(-13667607679511021)⟩,⟨(-13914099452776151),(-13914099452776065)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-3489787400608118),(-3489787400608022)⟩,⟨(-1544043544035342),(-1544043544035245)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-721790086092138),(-721790086092005)⟩,⟨(-87021786098580),(-87021786098446)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-144063595113209),(-144063595113052)⟩,⟨12883864781839,12883864781994⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-31303185826408),(-31303185826245)⟩,⟨6888789974301,6888789974463⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-7930058188799),(-7930058188665)⟩,⟨2273218705889,2273218706023⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-2298810270346),(-2298810270249)⟩,⟨713241348088,713241348187⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-526774900079),(-526774900037)⟩,⟨165671000049,165671000091⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨1490548184835528089010,1490548184835587127515⟩,⟨28449745112427665950735,28449745112427724991798⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨14077371304545849494976,14077371304545976416753⟩,⟨73124963956119568519908,73124963956119695446173⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨41827117352655549039164,41827117352655650491164⟩,⟨84359772888705225312871,84359772888705326764944⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨65572044352281722277617,65572044352281763048554⟩,⟨57357834224985346141358,57357834224985386905068⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨63021454379281249861120,63021454379281258518893⟩,⟨14061918654960103903669,14061918654960112552587⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨37197665537622884525599,37197665537622886213300⟩,⟨(-14392755572493388069444),(-14392755572493386383237)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨10950353330512114819410,10950353330512115027230⟩,⟨(-18040630623244442016003),(-18040630623244441806225)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-1472606748970288689169),(-1472606748970288646160)⟩,⟨(-9698484128995914819618),(-9698484128995914775691)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-3107618873279759500426),(-3107618873279759479652)⟩,⟨(-2691880561317765287307),(-2691880561317765266689)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-1598754136081253329602),(-1598754136081253319309)⟩,⟨(-44152539885544473174),(-44152539885544463061)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-488857953881395157903),(-488857953881395153155)⟩,⟨342225651727655966384,342225651727655971118⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-84820203802191741154),(-84820203802191739080)⟩,⟨204309273862881067368,204309273862881069456⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨6860514588772156358,6860514588772157238⟩,⟨83857847319595477814,83857847319595478704⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨14497781129644395485,14497781129644395861⟩,⟨29997268609515844240,29997268609515844617⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨8468247513095395253,8468247513095395414⟩,⟨10024889317493500234,10024889317493500394⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨2588472749406858112,2588472749406858166⟩,⟨2373992063210412911,2373992063210412964⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-3283618680647650616319371),(-3283618680647625106961605)⟩,⟨262306172527904217508002,262306172527929727393274⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-8816521000452404801805584),(-8816521000452305149243200)⟩,⟨1983972093624154177763292,1983972093624253831570669⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-11072213136100540507793429),(-11072213136100288520113360)⟩,⟨6068436603515399034207590,6068436603515651023016551⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-8377059234229080561220100),(-8377059234228551313887923)⟩,⟨10804565305736031119990397,10804565305736560367481626⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-1709286658466052097164753),(-1709286658465213483645177)⟩,⟨12516631166370535097853817,12516631166371373710287584⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨4780892280098947433536323,4780892280100012566182067⟩,⟨9190099224796985161974430,9190099224798050293199744⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨7056984135242318700968136,7056984135243773919590912⟩,⟨3050622956253948467887237,3050622956255403686335649⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨4973504140713366758815569,4973504140714428403809652⟩,⟨(-1641709936278698455088576),(-1641709936277636809533312)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨1612098355930075402392843,1612098355930776584847793⟩,⟨(-2906304335198269891294050),(-2906304335197568708570813)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-456900779272225154960730),(-456900779271871362622867)⟩,⟨(-1944107996368022981407007),(-1944107996367669189171813)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-928252373273071496579360),(-928252373272963002756393)⟩,⟨(-690436929012512920436005),(-690436929012404426752036)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-656557314018291295733408),(-656557314018250014150157)⟩,⟨(-3792505496110426453879),(-3792505496069144889942)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-316784739315890728114379),(-316784739315879162141818)⟩,⟨186660926566867331414861,186660926566878897409424⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-116181255797946223876084),(-116181255797943437190565)⟩,⟨163294542729372302723201,163294542729375089431484⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-32233768488049166350404),(-32233768488048253850270)⟩,⟨93672770190076458074727,93672770190077370584425⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-5512758611090143127353),(-5512758611089914629547)⟩,⟨29311858436796102785774,29311858436796331285835⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-8123092584164765003061930),(-8123092584164764968309857)⟩,⟨(-13121163074404233538174488),(-13121163074404233502589881)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-28487339923880216788738749),(-28487339923880216680432540)⟩,⟨(-33540123474244303130346350),(-33540123474244303020338441)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-56190096350770200990827954),(-56190096350770200799117106)⟩,⟨(-36441011421714026162396864),(-36441011421714025970365659)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-82272338587368598960055789),(-82272338587368598677712970)⟩,⟨(-13775285702743263406637882),(-13775285702743263127413302)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-87963986209500516669230513),(-87963986209500516296835279)⟩,⟨29807323974770020854201392,29807323974770021220351410⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-60099255093452360826486359),(-60099255093452360373355499)⟩,⟨72301892757391618195055118,72301892757391618644593407⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-8097901226626641174968838),(-8097901226626640680681435)⟩,⟨86551292999743531758830405,86551292999743532253572941⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨38819547908159283693503008,38819547908159284199750176⟩,⟨63472926226669559909377929,63472926226669560418033317⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨56259852264798903242064449,56259852264798904017235842⟩,⟨20896057548916276306368457,20896057548916277082414082⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨44148663338082516897269442,44148663338082519286372314⟩,⟨(-14045438173416573680205350),(-14045438173416571291256507)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨20444579692476808814094651,20444579692476816163339823⟩,⟨(-27871480214275471807940583),(-27871480214275464458698434)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨1699418540602447563045542,1699418540602472854238000⟩,⟨(-24905362539380945716013628),(-24905362539380920424611334)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-6813762862608276014217771),(-6813762862608222740180042)⟩,⟨(-15868899333482588331765041),(-15868899333482535057620791)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-7762855830564346031523382),(-7762855830564278308110798)⟩,⟨(-7974926657762740176820736),(-7974926657762672453439387)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-5265784486929118802360315),(-5265784486929065342013593)⟩,⟨(-3222336541196528115685649),(-3222336541196474655404501)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-1797746838584578470214316),(-1797746838584558931331793)⟩,⟨(-807990029523345561972757),(-807990029523326023119463)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-34770382533484816246812020),(-34770382533483686274471814)⟩,⟨19805310716132543248410650,19805310716133673219861773⟩⟩
lemma checked : cachedMomentRuleBox density0 hk9_1_12 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 9 12) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk9_1_12 (tableDensity false) (fullFactor true 9 12) density0_contains hk9_1_12_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-43593494103365930856950987),(-43593494103365930730120739)⟩,⟨31837625467524361590987814,31837625467524361716585418⟩⟩
lemma atomChecked : tableAtomBox false ha9_1_12 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 9 12) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha9_1_12 9 12 ha9_1_12_contains
 def realAnswer : RBox := ⟨(-78363876636850747203763007),(-78363876636849616904592553)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 9 12) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm9_0_1_12
namespace hm9_1_1_12
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk9_1_12 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-44),34⟩,⟨(-51),27⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-81),119⟩,⟨(-129),72⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-93),196⟩,⟨(-208),80⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-79),277⟩,⟨(-125),229⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-298),196⟩,⟨(-127),370⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-493),238⟩,⟨(-451),280⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-255),610⟩,⟨(-476),384⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-656),505⟩,⟨(-457),682⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-813),727⟩,⟨(-927),616⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-834),754⟩,⟨(-738),777⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-684),650⟩,⟨(-846),460⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-572),871⟩,⟨(-618),867⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-728),496⟩,⟨(-501),704⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-414),268⟩,⟨(-427),321⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-210),232⟩,⟨(-232),106⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-73),76⟩,⟨(-76),34⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-71162202721),(-71162202702)⟩,⟨(-3937937284),(-3937937265)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-143411523070),(-143411523043)⟩,⟨(-6833152027),(-6833151999)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-108637794412),(-108637794379)⟩,⟨(-4535830029),(-4535829994)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-47615497776),(-47615497733)⟩,⟨(-2717450182),(-2717450140)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-13551779411),(-13551779346)⟩,⟨(-1686813203),(-1686813138)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-2646002629),(-2646002539)⟩,⟨(-770656281),(-770656189)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-350876860),(-350876741)⟩,⟨(-230189081),(-230188962)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-25768470),(-25768339)⟩,⟨(-44963419),(-44963289)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨773304,773492⟩,⟨(-5600327),(-5600140)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨497270,497527⟩,⟨(-338034),(-337775)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨63915,64186⟩,⟨25730,26001⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨1089,1328⟩,⟨9187,9427⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-1417),(-1130)⟩,⟨832,1121⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-464),(-207)⟩,⟨(-222),31⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-142),31⟩,⟨(-169),8⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-40),38⟩,⟨(-60),18⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨294619492520366855,294619492520366875⟩,⟨819600436038038890,819600436038038913⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨920434411836592235,920434411836592266⟩,⟨1832718431403994174,1832718431403994206⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨1347772968393809600,1347772968393809631⟩,⟨1611483056698723694,1611483056698723726⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨1205446701109420855,1205446701109420885⟩,⟨735040757687110870,735040757687110900⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨674412729680718158,674412729680718185⟩,⟨95571863184972578,95571863184972604⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨233957170102095828,233957170102095856⟩,⟨(-80257840645780130),(-80257840645780101)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨47081718616971626,47081718616971652⟩,⟨(-52947712558722056),(-52947712558722026)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨3437553280526636,3437553280526665⟩,⟨(-16527731283845061),(-16527731283845033)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-985941256798438),(-985941256798410)⟩,⟨(-3393104680924727),(-3393104680924699)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-440292946020353),(-440292946020326)⟩,⟨(-525463453988819),(-525463453988791)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-110467694373575),(-110467694373542)⟩,⟨(-68749767206667),(-68749767206633)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-24091818262979),(-24091818262943)⟩,⟨(-8559145742428),(-8559145742393)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-5395625751601),(-5395625751566)⟩,⟨(-1152908429471),(-1152908429435)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-1359678670127),(-1359678670095)⟩,⟨(-188488359615),(-188488359584)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-387115337081),(-387115337057)⟩,⟨(-38982581597),(-38982581569)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-87559557947),(-87559557928)⟩,⟨(-7433172681),(-7433172661)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-5285694097752892591125),(-5285694097752843011386)⟩,⟨7922059975226378051646,7922059975226427631122⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-10744161696977727902971),(-10744161696977621398399)⟩,⟨22051951883894783731706,22051951883894890235805⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-5569785564667825323821),(-5569785564667740337233)⟩,⟨29638494110851494770144,29638494110851579756719⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨5578171097552039888762,5578171097552073927159⟩,⟨26299895100370430450248,26299895100370464489387⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨12649032958118679196080,12649032958118686358885⟩,⟨14434437286468267586731,14434437286468274750428⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨11167949714067980106783,11167949714067981462874⟩,⟨2809783975996854249380,2809783975996855605617⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨5454434031148624056034,5454434031148624199953⟩,⟨(-2448408470211191925101),(-2448408470211191781377)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨1185450185031247616736,1185450185031247636546⟩,⟨(-2468875683685603678461),(-2468875683685603658735)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-290282958342171079551),(-290282958342171071958)⟩,⟨(-1092683966925054870003),(-1092683966925054862396)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-351843706419295491850),(-351843706419295488268)⟩,⟨(-252429489117847937404),(-252429489117847933804)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-159603668465716282513),(-159603668465716280841)⟩,⟨3676269011006111138,3676269011006112812⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-48641207499747079044),(-48641207499747078301)⟩,⟨33239772749390219152,33239772749390219892⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-10522419592145652121),(-10522419592145651794)⟩,⟨19860737334042240885,19860737334042241211⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-1010701097455341815),(-1010701097455341671)⟩,⟨8908243943822434933,8908243943822435080⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨499001152016140625,499001152016140696⟩,⟨3522695924154174822,3522695924154174890⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨253802529094762855,253802529094762887⟩,⟨922309307183931635,922309307183931666⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-1073023447014912263443527),(-1073023447014891303985103)⟩,⟨141332066721133853955781,141332066721154813316944⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-2925132116173660219026493),(-2925132116173578329423062)⟩,⟨790899450862562362937316,790899450862644252298370⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-3792267859978224344713426),(-3792267859978017231215184)⟩,⟨2183700891471365394985937,2183700891471572508240595⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-3057818206306558054377520),(-3057818206306122967223455)⟩,⟨3819804430776614878006438,3819804430777049965088357⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-893373407452002811616574),(-893373407451313300162638)⟩,⟨4521340433351596742091793,4521340433352286253738151⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨1419862675106126691821252,1419862675107002459857500⟩,⟨3530377791739292369603912,3530377791740168137925112⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨2448280062599558112386902,2448280062600754386793144⟩,⟨1443390632039648434620803,1443390632040844709067929⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨1938592671066392820743569,1938592671067265157269626⟩,⟨(-331507671038387177027908),(-331507671037514840622982)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨813753981731784304218588,813753981732359982587505⟩,⟨(-986002220752026436829252),(-986002220751450758522389)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨2392606981195938795385,2392606981486109935473⟩,⟨(-786251611308861366250089),(-786251611308571195091278)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-271873256908644360852487),(-271873256908555493718875)⟩,⟨(-371162400102251599603020),(-371162400102162732442624)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-240039014270682338237820),(-240039014270648570292375)⟩,⟨(-94327121594905014259060),(-94327121594871246309359)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-138852779782674196022802),(-138852779782664747512233)⟩,⟨14714912363098561043070,14714912363108009549907⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-64395351843586707680811),(-64395351843584433869505)⟩,⟨34257532210531927257002,34257532210534201064340⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-25236321185219089624907),(-25236321185218345711410)⟩,⟨23950652563044339500930,23950652563045083412773⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-6388431555251516714725),(-6388431555251330513327)⟩,⟨8046148956022327746632,8046148956022513947644⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-259727622036238939219597),(-259727622036238934218178)⟩,⟨(-378187038711681538120197),(-378187038711681532700401)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-1045058788960505485045881),(-1045058788960505469261667)⟩,⟨(-741492286314830598301403),(-741492286314830581796369)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-1974719412679170976274921),(-1974719412679170949020507)⟩,⟨408049110142358892132425,408049110142358918990231⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-1362755226105447347984999),(-1362755226105447308310249)⟩,⟨4175028689788003620356868,4175028689788003657117585⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨3379541114770545750867277,3379541114770545815790798⟩,⟨9609941972185685066353134,9609941972185685125882430⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨12866192554526044596571424,12866192554526044706885624⟩,⟨12440963070855120622488277,12440963070855120729607446⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨23082346160790299353313149,23082346160790299511305645⟩,⟨8012697069647662063560684,8012697069647662222195317⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨27254485426321670235881414,27254485426321670440803763⟩,⟨(-3263290738238215184292111),(-3263290738238214976376097)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨21963846739695088441410484,21963846739695088913732737⟩,⟨(-14927417567221802146448386),(-14927417567221801672883959)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨10612780680224225529973907,10612780680224227369394665⟩,⟨(-20254448019180110483905751),(-20254448019180108644987948)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-103395690447114871486630),(-103395690447108958560865)⟩,⟨(-17963103078424016875598301),(-17963103078424010963496158)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-5986929363347414049377530),(-5986929363347393470574003)⟩,⟨(-11702567601014134742267178),(-11702567601014114163624739)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-7091874190254208889505834),(-7091874190254165424411317)⟩,⟨(-5683657860995306234856043),(-5683657860995262769595965)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-5566734485976111077672291),(-5566734485976055763398105)⟩,⟨(-1892927831925782840917070),(-1892927831925727526453685)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-3284455280563125324560544),(-3284455280563081634500345)⟩,⟨(-269923963649861142260975),(-269923963649817452075440)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-1060206359283472673986352),(-1060206359283456701691660)⟩,⟨47136153112279157079709,47136153112295129415757⟩⟩
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
noncomputable def ans : CBox := ⟨⟨10928566172008637564865376,10928566172009565603539737⟩,⟨(-4723944451041839959414767),(-4723944451040911921928503)⟩⟩
lemma checked : cachedMomentRuleBox density1 hk9_1_12 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 9 12) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk9_1_12 (tableDensity true) (fullFactor true 9 12) density1_contains hk9_1_12_contains
noncomputable def atomAnswer : CBox := ⟨⟨57006876904401601724004043,57006876904401601889858983⟩,⟨(-41633817919070319167842470),(-41633817919070319003599450)⟩⟩
lemma atomChecked : tableAtomBox true ha9_1_12 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 9 12) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha9_1_12 9 12 ha9_1_12_contains
 def realAnswer : RBox := ⟨67935443076410239188869419,67935443076411167593398720⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 9 12) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm9_1_1_12
namespace hm9_0_1_13
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk9_1_13 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-117),124⟩,⟨(-63),173⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-449),252⟩,⟨(-263),437⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-819),304⟩,⟨(-379),743⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-1132),466⟩,⟨(-1087),506⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-606),1212⟩,⟨(-1353),465⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-882),1809⟩,⟨(-873),1807⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-2746),1130⟩,⟨(-1898),1970⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-2174),3047⟩,⟨(-2972),2160⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-3126),3168⟩,⟨(-2446),3841⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-3309),3652⟩,⟨(-3481),3380⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-2868),2704⟩,⟨(-1925),3468⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-3376),2360⟩,⟨(-3522),2366⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-2002),2991⟩,⟨(-2806),2125⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-1168),1692⟩,⟨(-1309),1777⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-967),828⟩,⟨(-478),960⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-302),276⟩,⟨(-137),300⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨234046778551,234046778585⟩,⟨89716994212,89716994247⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨479336142418,479336142490⟩,⟨182912211516,182912211591⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨372507796461,372507796579⟩,⟨145582527207,145582527327⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨166607393641,166607393813⟩,⟨72688994980,72688995152⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨46922627153,46922627373⟩,⟨26285847293,26285847511⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨8443956358,8443956629⟩,⟨7187707448,7187707719⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨874904782,874905220⟩,⟨1459947893,1459948332⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨11053822,11054438⟩,⟨209523538,209524158⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-13038695),(-13037998)⟩,⟨18568748,18569441⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-2356998),(-2356190)⟩,⟨290475,291285⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-176566),(-175504)⟩,⟨(-200012),(-198950)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨10290,11352⟩,⟨(-33861),(-32800)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨5176,6101⟩,⟨(-1858),(-940)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨645,1322⟩,⟨412,1088⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-163),334⟩,⟨84,580⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-127),82⟩,⟨(-31),176⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨288617628330595516,288617628330595542⟩,⟨(-1710336518009493660),(-1710336518009493636)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨157506341876819303,157506341876819341⟩,⟨(-4090130215531820168),(-4090130215531820133)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-887220156142703658),(-887220156142703615)⟩,⟨(-4135558100459239662),(-4135558100459239616)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-1562415586425649362),(-1562415586425649320)⟩,⟨(-2455412959465746805),(-2455412959465746760)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-1239787718767141579),(-1239787718767141540)⟩,⟨(-788584520379140658),(-788584520379140622)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-567916405391472669),(-567916405391472636)⟩,⟨(-42912241148668225),(-42912241148668189)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-158773783005760314),(-158773783005760280)⟩,⟨74421407981571385,74421407981571419⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-26112399143251970),(-26112399143251931)⟩,⟨36019772182147370,36019772182147409⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-1555059804144823),(-1555059804144766)⟩,⟨9609123217832584,9609123217832643⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨466234431681376,466234431681447⟩,⟨1885135619006096,1885135619006163⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨201371672993538,201371672993616⟩,⟨318585644540954,318585644541033⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨54488389801536,54488389801615⟩,⟨53351108200102,53351108200180⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨13883550243782,13883550243858⟩,⟨10060142225448,10060142225521⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨3809957660286,3809957660360⟩,⟨2325184079419,2325184079494⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨1142601029289,1142601029349⟩,⟨646026189131,646026189191⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨264662620540,264662620573⟩,⟨146196396925,146196396957⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨9941790654372275637427,9941790654372299406237⟩,⟨(-3856944520805441177779),(-3856944520805417409145)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨24388786445561664871428,24388786445561714053451⟩,⟨(-13676349866543468347934),(-13676349866543419165480)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨25104814232509776455244,25104814232509812910756⟩,⟨(-25205574800872727479154),(-25205574800872691020952)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨12395310219862626032423,12395310219862639271437⟩,⟨(-30813993270665432153747),(-30813993270665418909987)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-3190532098927292472659),(-3190532098927288641478)⟩,⟨(-24701005378914390899214),(-24701005378914387065881)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-10417759455873876748101),(-10417759455873876079901)⟩,⟨(-11611622418917934631035),(-11611622418917933963447)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-8267982504329521738035),(-8267982504329521661340)⟩,⟨(-1397811787317966748068),(-1397811787317966672416)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-3388102583751161311428),(-3388102583751161289800)⟩,⟨2059298163613304174132,2059298163613304195697⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-500168320640901497905),(-500168320640901488188)⟩,⟨1615931865220740371226,1615931865220740381127⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨263603881091719599837,263603881091719604454⟩,⟨615838654253972930090,615838654253972934742⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨221898181339031871012,221898181339031872999⟩,⟨124161247915508431569,124161247915508433543⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨95505833796894234184,95505833796894235005⟩,⟨(-6977535468454082134),(-6977535468454081323)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨31233880106715018150,31233880106715018482⟩,⟨(-19691510240618485147),(-19691510240618484812)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨8685429261901355832,8685429261901355992⟩,⟨(-11960166234193795315),(-11960166234193795155)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨2114388340406620255,2114388340406620333⟩,⟨(-5472124635944708482),(-5472124635944708398)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨370620629849156441,370620629849156475⟩,⟨(-1532065628384445894),(-1532065628384445860)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨261152584815224649592131,261152584815233987338619⟩,⟨1018221971609899618344864,1018221971609908955956416⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨1113338637518134043023018,1113338637518169551424706⟩,⟨2668748538968646638411250,2668748538968682146514673⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨2554844774452090434297149,2554844774452176324690481⟩,⟨3157803060518202065919390,3157803060518287956107846⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨3945598067147278433007000,3945598067147448828024760⟩,⟨2020815734504359094477144,2020815734504529489627863⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨4130555055204913087674685,4130555055205161395430439⟩,⟨(-247519016496007706160341),(-247519016495759397892653)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨2656706990844826964493696,2656706990845213559295731⟩,⟨(-2176907155927883959712191),(-2176907155927497364549618)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨484593706180307639767874,484593706180794631320694⟩,⟨(-2538427095335455709143153),(-2538427095334968717658397)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-936806978292748820242764),(-936806978292405535183547)⟩,⟨(-1521607001466169942081433),(-1521607001465826657248414)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-1113086624856532390838341),(-1113086624856271595311149)⟩,⟨(-295182680292765299432662),(-295182680292504503939660)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-619363345445363673562975),(-619363345445250453475378)⟩,⟨332138884150090985658998,332138884150204205817140⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-147307824989969685323947),(-147307824989926608482384)⟩,⟨386104938546906664972659,386104938546949741849059⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨66120180313215028364072,66120180313230075871153⟩,⟨228400871789001839638793,228400871789016887139558⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨99517476620053921951972,99517476620057595343030⟩,⟨90855759335135560614665,90855759335139233991213⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨70582038516659415069706,70582038516660542501839⟩,⟨22714595136142310468019,22714595136143437893297⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨36888385857999830924630,36888385858000224206586⟩,⟨677161465492221004005,677161465492614284204⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨11051416106035354193500,11051416106035448149027⟩,⟨(-1447718415952840478313),(-1447718415952746523056)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-3528171589692117354759760),(-3528171589692117344781286)⟩,⟨2449203693347718517314284,2449203693347718527098406⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-8908961016732888977673758),(-8908961016732888946810119)⟩,⟨8445740455358135519094011,8445740455358135549597959⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-9270517094553075291022096),(-9270517094553075237079426)⟩,⟨16320630827412908813923531,16320630827412908867960975⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-2374539379524095523840908),(-2374539379524095445301770)⟩,⟨23418556568537333137874872,23418556568537333217512929⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨10279671103103967378794251,10279671103103967482484601⟩,⟨24358810683480215904535493,24358810683480216010055658⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨22142042329625720117207091,22142042329625720245285268⟩,⟨15530173164122142095143461,15530173164122142224072683⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨25302997084481838695762091,25302997084481838835831625⟩,⟨27493065040605533941152,27493065040605673694361⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨17431887541221744867726267,17431887541221745011542051⟩,⟨(-13314371655887749126686426),(-13314371655887748983639377)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨4274152513389298503630431,4274152513389298731150597⟩,⟨(-17412949594194613117325734),(-17412949594194612889992001)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-5903818650274162689390538),(-5903818650274161991463569)⟩,⟨(-12723386153338413292609074),(-12723386153338412594602518)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-9325114214142114334375890),(-9325114214142111987375187)⟩,⟨(-5039491341625764409281917),(-5039491341625762062282602)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-7721010612160269810807505),(-7721010612160261659207733)⟩,⟨613584460810858724820378,613584460810866876361951⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-4581421388971154577603270),(-4581421388971138302184498)⟩,⟨2882702454707022647878205,2882702454707038923279238⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-2088657518913618578200727),(-2088657518913598968164704)⟩,⟨2828997249650089046124211,2828997249650108656181865⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-730311879499221383511440),(-730311879499205761868242)⟩,⟨1820574049094243393024539,1820574049094259014693140⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-156782329128680288154927),(-156782329128673519683277)⟩,⟨608189092150481478888860,608189092150488247369238⟩⟩
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
noncomputable def ans : CBox := ⟨⟨6250419168352001770274384,6250419168352380812719353⟩,⟨8975490176771023224757988,8975490176771402267574515⟩⟩
lemma checked : cachedMomentRuleBox density0 hk9_1_13 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 9 13) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk9_1_13 (tableDensity false) (fullFactor true 9 13) density0_contains hk9_1_13_contains
noncomputable def atomAnswer : CBox := ⟨⟨9546046116894270244337023,9546046116894270285152503⟩,⟨11326141308834535463012452,11326141308834535504167704⟩⟩
lemma atomChecked : tableAtomBox false ha9_1_13 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 9 13) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha9_1_13 9 13 ha9_1_13_contains
 def realAnswer : RBox := ⟨15796465285246271914611407,15796465285246651197871856⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 9 13) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm9_0_1_13
namespace hm9_1_1_13
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk9_1_13 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-29),27⟩,⟨(-19),37⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-86),50⟩,⟨(-54),79⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-154),56⟩,⟨(-81),129⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-193),101⟩,⟨(-204),87⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-101),222⟩,⟨(-226),97⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-166),288⟩,⟨(-141),308⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-442),189⟩,⟨(-320),308⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-345),489⟩,⟨(-472),349⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-504),512⟩,⟨(-392),618⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-545),605⟩,⟨(-578),556⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-482),472⟩,⟨(-320),595⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-598),399⟩,⟨(-611),416⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-352),522⟩,⟨(-498),363⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-199),299⟩,⟨(-232),309⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-168),151⟩,⟨(-79),168⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-57),55⟩,⟨(-26),57⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨25456490752,25456490770⟩,⟨29675046999,29675047019⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨52242434287,52242434312⟩,⟨59312550885,59312550907⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨40585935133,40585935162⟩,⟨44563507248,44563507278⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨17995473878,17995473913⟩,⟨19735206248,19735206281⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨4951102644,4951102685⟩,⟨5959334973,5959335015⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨841905369,841905421⟩,⟨1346238449,1346238499⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨70502550,70502623⟩,⟨235637116,235637192⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-4528199),(-4528097)⟩,⟨30597071,30597175⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-2393018),(-2392903)⟩,⟨2466223,2466337⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-372064),(-371923)⟩,⟨(-509),(-367)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-25458),(-25270)⟩,⟨(-35340),(-35153)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨2242,2436⟩,⟨(-5604),(-5407)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨933,1113⟩,⟨(-247),(-67)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨96,236⟩,⟨85,223⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-44),65⟩,⟨13,117⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-33),21⟩,⟨(-16),38⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨257848890293099289,257848890293099306⟩,⟨(-294721438763948179),(-294721438763948159)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨518145179958792133,518145179958792156⟩,⟨(-766637177064818562),(-766637177064818540)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨331891999066349434,331891999066349453⟩,⟨(-894776184224028571),(-894776184224028544)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨10778786103949011,10778786103949036⟩,⟨(-647742518655693717),(-647742518655693695)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-124892751936309302),(-124892751936309281)⟩,⟨(-290918650123719744),(-290918650123719721)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-91102073615826903),(-91102073615826883)⟩,⟨(-73000474714678851),(-73000474714678832)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-33691046049321532),(-33691046049321512)⟩,⟨(-4776207166564280),(-4776207166564256)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-7595598136768412),(-7595598136768391)⟩,⟨3249237431733936,3249237431733954⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-1072860715294201),(-1072860715294177)⟩,⟨1399365409356077,1399365409356100⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-74192608774864),(-74192608774841)⟩,⟨340857006971588,340857006971610⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨8540953342014,8540953342038⟩,⟨66907380229235,66907380229255⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨4815947748223,4815947748251⟩,⟨12589771559509,12589771559534⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨1457652684530,1457652684555⟩,⟨2566142194726,2566142194748⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨422951982253,422951982275⟩,⟨610470392361,610470392384⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨129245208765,129245208787⟩,⟨168264700603,168264700626⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨30131322718,30131322735⟩,⟨37511351761,37511351779⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨3435018130247358070920,3435018130247378031642⟩,⟨953065868941396126150,953065868941416086891⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨9129942203063103345644,9129942203063144616205⟩,⟨1216816253980608361998,1216816253980649632517⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨11279994749002631200756,11279994749002661740133⟩,⟨(-1604836343596835598370),(-1604836343596805059270)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨8763489179625402155271,8763489179625413207995⟩,⟨(-5315170775146143075751),(-5315170775146132023511)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨3570081924393624149979,3570081924393627326510⟩,⟨(-6484667052243658991705),(-6484667052243655815387)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-519416818505637413505),(-519416818505636874691)⟩,⟨(-4473903265277423521962),(-4473903265277422983080)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-1704025045191186617846),(-1704025045191186566903)⟩,⟨(-1655067510233993959804),(-1655067510233993908758)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-1105398643087394516050),(-1105398643087394506389)⟩,⟨(-57776006229971069026),(-57776006229971059363)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-363639425773407662448),(-363639425773407658894)⟩,⟨290055259321182054315,290055259321182057852⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-34306831337327249205),(-34306831337327247564)⟩,⟨178092784133375239114,178092784133375240753⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨30984402963420935755,30984402963420936463⟩,⟨60557642217816829801,60557642217816830507⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨22320527443234968012,22320527443234968307⟩,⟨12335516240799461602,12335516240799461899⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨9863121027899151777,9863121027899151905⟩,⟨62287783097725359,62287783097725487⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨3694467179609319051,3694467179609319118⟩,⟨(-1473640891995631148),(-1473640891995631080)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨1274427982224137305,1274427982224137345⟩,⟨(-951591905917448925),(-951591905917448883)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨307188008721610503,307188008721610527⟩,⟨(-299898018131615988),(-299898018131615961)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨102827660226841767994980,102827660226849440264067⟩,⟨329709613808456905111762,329709613808464577406178⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨411199880136201034308877,411199880136230213382019⟩,⟨878100767124807478179610,878100767124836657311995⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨908392239339426469644356,908392239339497064507628⟩,⟨1075571445680882233078839,1075571445680952827988876⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨1400747250538750954104381,1400747250538891033309988⟩,⟨745151511532252511648346,745151511532392590836599⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨1509704064657162168624862,1509704064657366327678572⟩,⟨(-702465419988474287533),(-702465419784315334481)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨1049000509558448419301134,1049000509558766284932677⟩,⟨(-701031022571081520851693),(-701031022570763655296782)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨294471132725987371425669,294471132726387708692671⟩,⟨(-908855971004962953073231),(-908855971004562615793409)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-262787623140309986329269),(-262787623140027919522442)⟩,⟨(-617436500666946007547076),(-617436500666663940689572)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-400282967277865190803705),(-400282967277651071880340)⟩,⟨(-189813203538396027255703),(-189813203538181908322282)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-267540023347849893092973),(-267540023347757031950662)⟩,⟨70687219182144531708780,70687219182237392837506⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-101243309048296728177600),(-101243309048261444459620)⟩,⟨129477426518677018805165,129477426518712302516302⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-8111944127293867065548),(-8111944127281558226601)⟩,⟨93053359010409952150228,93053359010422260990138⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨20111633288582122614649,20111633288585123441030⟩,⟨47055409366685135645338,47055409366688136474292⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨19281726460131902036895,19281726460132821946202⟩,⟨18880677191462981269142,18880677191463901179659⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨11380889655242074326576,11380889655242394956914⟩,⟨6194993118621841252776,6194993118622161883421⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨3600066811178779384210,3600066811178855949249⟩,⟨1334151034692248116776,1334151034692324681860⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-101316046986135587430334),(-101316046986135585917863)⟩,⟨77707439599493603964299,77707439599493605384752⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-190588827453877065866632),(-190588827453877061269564)⟩,⟨302379484147473501303112,302379484147473505773944⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨146889187545810413093395,146889187545810420541453⟩,⟨545597750980389241397215,545597750980389249076295⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨1201121245011215490563528,1201121245011215500686263⟩,⟨306634616216383168972073,306634616216383180060846⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨2659551214101828863221113,2659551214101828880070858⟩,⟨(-1159834742438221774982632),(-1159834742438221756578663)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨3265106194854421571197177,3265106194854421602086913⟩,⟨(-3984293144060930749042561),(-3984293144060930717408614)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨1703926703206899080194577,1703926703206899125287920⟩,⟨(-6908613631649069421299642),(-6908613631649069376567783)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-1786858186417189811785905),(-1786858186417189752449949)⟩,⟨(-7896254595752450893510787),(-7896254595752450835091702)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-5184110558298756857447277),(-5184110558298756715823443)⟩,⟨(-6009483374409201101955630),(-6009483374409200960558121)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-6489685512781562533686337),(-6489685512781561997978186)⟩,⟨(-2415406344706804488784635),(-2415406344706803952832377)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-5453000890084944388456785),(-5453000890084942502459234)⟩,⟨785573856855880337400382,785573856855882223643173⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-3319043215909600255590222),(-3319043215909593624174313)⟩,⟨2370732157207112789716720,2370732157207119421138935⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-1414398395939784632851963),(-1414398395939771355917854)⟩,⟨2472679280416176101004452,2472679280416189377860988⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-304928240291272168735161),(-304928240291256153650373)⟩,⟨1832634856113511957393860,1832634856113527972404248⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨89593535484475977875891,89593535484488743744174⟩,⟨1043301005848631107477128,1043301005848643873301191⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨71994910556661163227331,71994910556666696315264⟩,⟨330427691918114323828897,330427691918119856905483⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-1730412442189426614981067),(-1730412442189115296162725)⟩,⟨(-2890954401886145117117223),(-2890954401885833797956446)⟩⟩
lemma checked : cachedMomentRuleBox density1 hk9_1_13 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 9 13) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk9_1_13 (tableDensity true) (fullFactor true 9 13) density1_contains hk9_1_13_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-12483291075938661142122504),(-12483291075938661088748415)⟩,⟨(-14811107865399007966988535),(-14811107865399007913170129)⟩⟩
lemma atomChecked : tableAtomBox true ha9_1_13 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 9 13) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha9_1_13 9 13 ha9_1_13_contains
 def realAnswer : RBox := ⟨(-14213703518128087857103571),(-14213703518127776284911140)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 9 13) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm9_1_1_13
end SharpPlanar.CachedData

end OAI
