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
namespace hm9_0_1_14
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk9_1_14 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-47),72⟩,⟨(-89),29⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-98),251⟩,⟨(-197),153⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-122),504⟩,⟨(-347),275⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-389),627⟩,⟨(-261),754⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-957),400⟩,⟨(-489),868⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-944),585⟩,⟨(-1135),383⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-690),1695⟩,⟨(-1064),1324⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-2215),1533⟩,⟨(-1676),2040⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-1785),1951⟩,⟨(-2296),1401⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-2394),2161⟩,⟨(-2280),2316⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-1784),2020⟩,⟨(-2327),1331⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-1515),2115⟩,⟨(-1456),2277⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-1981),1306⟩,⟨(-1425),1833⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-1127),794⟩,⟨(-1186),865⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-550),644⟩,⟨(-636),322⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-185),203⟩,⟨(-201),90⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-49516774380),(-49516774358)⟩,⟨(-117689130246),(-117689130221)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-103385416996),(-103385416957)⟩,⟨(-241034715181),(-241034715143)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-81671131724),(-81671131665)⟩,⟨(-188989781186),(-188989781133)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-35498293339),(-35498293257)⟩,⟨(-87611154138),(-87611154054)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-8548617638),(-8548617507)⟩,⟨(-27016245751),(-27016245619)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-810637119),(-810636924)⟩,⟨(-5877284391),(-5877284198)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨147229654,147229888⟩,⟨(-914593692),(-914593457)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨67056725,67057018⟩,⟨(-95000015),(-94999722)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨12133637,12134089⟩,⟨(-4095684),(-4095235)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨1212591,1213118⟩,⟨623679,624207⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨24451,24962⟩,⟨153060,153572⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-15820),(-15194)⟩,⟨13458,14086⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-3697),(-3026)⟩,⟨(-1224),(-558)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-565),(-74)⟩,⟨(-922),(-429)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-102),189⟩,⟨(-347),(-61)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-25),89⟩,⟨(-88),24⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-682769433012473714),(-682769433012473694)⟩,⟨241345100603588518,241345100603588537⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-1526916848675685412),(-1526916848675685386)⟩,⟨780516214266925386,780516214266925413⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-1328985496592624878),(-1328985496592624848)⟩,⟨1190408027548469401,1190408027548469429⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-565009449703259646),(-565009449703259618)⟩,⟨1103813413119319422,1103813413119319450⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-12755570012022754),(-12755570012022729)⟩,⟨634043533560465056,634043533560465083⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨117375630209914952,117375630209914976⟩,⟨220315707320630767,220315707320630791⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨66821544420580739,66821544420580765⟩,⟨40635488037376133,40635488037376162⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨20215864212260162,20215864212260193⟩,⟨362152187842757,362152187842788⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨4014672855947475,4014672855947509⟩,⟨(-2057154024228381),(-2057154024228347)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨569285239837270,569285239837305⟩,⟨(-719655810696311),(-719655810696274)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨57655395977218,57655395977265⟩,⟨(-172018785804145),(-172018785804102)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨2538732385871,2538732385925⟩,⟨(-37246951246213),(-37246951246160)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-851150181177),(-851150181120)⟩,⟨(-8473417489971),(-8473417489915)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-436141050721),(-436141050669)⟩,⟨(-2199642753785),(-2199642753737)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-158497140424),(-158497140385)⟩,⟨(-645501735395),(-645501735360)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-39035816411),(-39035816390)⟩,⟨(-148687693424),(-148687693403)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-2353043643074070330296),(-2353043643074062315285)⟩,⟨(-2863755217955801412573),(-2863755217955793397782)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-7207198669918137935882),(-7207198669918122004333)⟩,⟨(-6565473308578651017974),(-6565473308578635087302)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-11203834920421905365426),(-11203834920421894538371)⟩,⟨(-5499124113369954621981),(-5499124113369943796714)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-11745582462295175301158),(-11745582462295170354548)⟩,⟨(-543201042327981982300),(-543201042327977037090)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-7926964617657107927659),(-7926964617657106426466)⟩,⟨4091378395085568416370,4091378395085569917457⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-2603368507684878525182),(-2603368507684878304365)⟩,⟨5032148499145086577969,5032148499145086799409⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨646823764226039946531,646823764226039978444⟩,⟨3025409478379481655167,3025409478379481687312⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨1203106358234466113660,1203106358234466122413⟩,⟨875650832989514010129,875650832989514018790⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨642093034466961441025,642093034466961444893⟩,⟨(-73223749688230983850),(-73223749688230980048)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨174565442194111856881,174565442194111858562⟩,⟨(-193403479757785899971),(-193403479757785898286)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨6052553319938582042,6052553319938582719⟩,⟨(-100424629524589102056),(-100424629524589101367)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-19770107683050933547),(-19770107683050933193)⟩,⟨(-33026610386316046958),(-33026610386316046599)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-13001563002530608139),(-13001563002530607961)⟩,⟨(-7572108931946910751),(-7572108931946910570)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-6033390566017373505),(-6033390566017373414)⟩,⟨(-823022119149080233),(-823022119149080145)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-2414017305325338484),(-2414017305325338435)⟩,⟨320360837671936983,320360837671937031⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-633509987319614521),(-633509987319614498)⟩,⟨173629515473314017,173629515473314044⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨284103443639827998106004,284103443639831040138620⟩,⟨(-127698587385830526519516),(-127698587385827484457961)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨723763330792692413505020,723763330792703721519712⟩,⟨(-463002512499991527421197),(-463002512499980219350116)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨792471050711871960158656,792471050711898238829511⟩,⟨(-918862300989788895175215),(-918862300989762616492063)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨378012803693211276079078,378012803693260433346626⟩,⟨(-1280070190054716886395985),(-1280070190054667729222267)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-318021238600341298331773),(-318021238600269311024959)⟩,⟨(-1217765409075195535886208),(-1217765409075123548756886)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-823871516900464574850683),(-823871516900335959238124)⟩,⟨(-662894906472058137761665),(-662894906471929522211455)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-806241264522779689430257),(-806241264522635669348693)⟩,⟨24832050512887201640182,24832050513031221781461⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-400468785030977811999934),(-400468785030865348505563)⟩,⟨400094052129170549868695,400094052129283013427675⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-4437445562658070528078),(-4437445562573511852464)⟩,⟨370482331798488577585482,370482331798573136252821⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨157160600716477396592445,157160600716511835994047⟩,⟨167463403260857535758288,167463403260891975131840⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨136527681436289476406648,136527681436305112777553⟩,⟨12238023637747343664835,12238023637762980031433⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨67346736348497782773017,67346736348502462355664⟩,⟨(-43108129132043752809021),(-43108129132039073219936)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨19595588227721792820975,19595588227723008040840⟩,⟨(-41460485702721343809706),(-41460485702720128584841)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨109592511763337585083,109592511763779280388⟩,⟨(-25473256970032585392361),(-25473256970032143695965)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-3706121318704700660004),(-3706121318704559382970)⟩,⟨(-12209190424753822167432),(-12209190424753680890476)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-1669806642513758238641),(-1669806642513725894223)⟩,⟨(-3488639982600095566479),(-3488639982600063222176)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨679913190430372548319496,679913190430372550870550⟩,⟨877339871033594643079935,877339871033594645671260⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨2310462604421194193467113,2310462604421194201421968⟩,⟨2184950582368720515851086,2184950582368720523868564⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨4381722452583704236926828,4381722452583704251024403⟩,⟨2158956411748462828669811,2158956411748462842694168⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨6163624056603723270060495,6163624056603723290836741⟩,⟨223189689907367767042916,223189689907367787474568⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨6224699939132399180616255,6224699939132399208295129⟩,⟨(-3177383198023580099414280),(-3177383198023580072216869)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨3650853126517316893282041,3650853126517316927124243⟩,⟨(-6233837743271352924074944),(-6233837743271352890409694)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-622448094058770557273683),(-622448094058770520921691)⟩,⟨(-6810652317038110533826725),(-6810652317038110497339993)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-4117975741518161778505901),(-4117975741518161741193449)⟩,⟨(-4370410758546275962836063),(-4370410758546275925308148)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-4934763612278935042869281),(-4934763612278934979940340)⟩,⟨(-623807211811218945211333),(-623807211811218882251747)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-3339054095575706776098037),(-3339054095575706587558639)⟩,⟨2097620496422277281935059,2097620496422277470443479⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-1057663369477371042596239),(-1057663369477370330176829)⟩,⟨2826890372086431540214944,2826890372086432252635804⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨501673320185763415787664,501673320185765800617728⟩,⟨2174378219303727288167342,2174378219303729673011187⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨1036040282053147494788010,1036040282053151992492888⟩,⟨1186776063405040904665339,1186776063405045402370477⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨918422424009692658403050,918422424009697887490665⟩,⟨470076017638590941933501,470076017638596171011798⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨565584215653556086882644,565584215653561224612388⟩,⟨122816302585446356966234,122816302585451494689198⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨185218682475173753902028,185218682475175985845824⟩,⟨15257859120716502794307,15257859120718734735983⟩⟩
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
noncomputable def ans : CBox := ⟨⟨2117761819836414517860630,2117761819836532631915013⟩,⟨(-1783602304677667802306354),(-1783602304677549688380341)⟩⟩
lemma checked : cachedMomentRuleBox density0 hk9_1_14 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 9 14) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk9_1_14 (tableDensity false) (fullFactor true 9 14) density0_contains hk9_1_14_contains
noncomputable def atomAnswer : CBox := ⟨⟨2695549047467140422471138,2695549047467140435046439⟩,⟨(-2619147666214788856692458),(-2619147666214788844203609)⟩⟩
lemma atomChecked : tableAtomBox false ha9_1_14 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 9 14) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha9_1_14 9 14 ha9_1_14_contains
 def realAnswer : RBox := ⟨4813310867303554840331768,4813310867303673166961452⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 9 14) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm9_0_1_14
namespace hm9_1_1_14
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk9_1_14 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-16),21⟩,⟨(-23),16⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-23),50⟩,⟨(-39),34⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-28),95⟩,⟨(-62),59⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-84),108⟩,⟨(-51),140⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-175),71⟩,⟨(-99),144⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-151),112⟩,⟨(-196),68⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-119),274⟩,⟨(-169),228⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-358),243⟩,⟨(-271),326⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-293),318⟩,⟨(-373),227⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-398),358⟩,⟨(-377),389⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-313),343⟩,⟨(-402),226⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-260),377⟩,⟨(-258),399⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-348),228⟩,⟨(-245),329⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-202),135⟩,⟨(-208),156⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-104),115⟩,⟨(-115),55⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-40),40⟩,⟨(-40),21⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨1937894295,1937894313⟩,⟨(-19821738297),(-19821738280)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨3187293633,3187293652⟩,⟨(-40278263678),(-40278263659)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨1600552617,1600552636⟩,⟨(-30985155238),(-30985155219)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨487473106,487473133⟩,⟨(-13879288712),(-13879288690)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨246406093,246406125⟩,⟨(-4074022525),(-4074022497)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨143354456,143354496⟩,⟨(-837251368),(-837251328)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨53192013,53192060⟩,⟨(-122833653),(-122833607)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨12464109,12464166⟩,⟨(-11766867),(-11766810)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨1912320,1912402⟩,⟨(-323388),(-323308)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨176429,176524⟩,⟨120428,120522⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨1488,1584⟩,⟨25252,25353⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-2905),(-2783)⟩,⟨2051,2170⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-649),(-516)⟩,⟨(-280),(-146)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-95),7⟩,⟨(-182),(-77)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-23),47⟩,⟨(-70),(-2)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-16),25⟩,⟨(-23),16⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-159838811087458669),(-159838811087458651)⟩,⟨(-34373087574068845),(-34373087574068824)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-386320024746364074),(-386320024746364056)⟩,⟨(-32260425576356238),(-32260425576356218)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-397173933988238993),(-397173933988238972)⟩,⟨65690599378526857,65690599378526881⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-240311787547893828),(-240311787547893808)⟩,⟨135786489782285727,135786489782285747⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-79276165672948627),(-79276165672948607)⟩,⟨111289954501368925,111289954501368944⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-5651666360294930),(-5651666360294913)⟩,⟨50851260623797330,50851260623797348⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨6535260666950096,6535260666950113⟩,⟨13695311661546575,13695311661546593⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨3186196808208531,3186196808208549⟩,⟨1985260433072987,1985260433073008⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨816911285223669,816911285223686⟩,⟨16417926289559,16417926289580⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨148786195906052,148786195906075⟩,⟨(-70917483210604),(-70917483210584)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨22370186493247,22370186493264⟩,⟨(-23531214290142),(-23531214290123)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨3155999188886,3155999188906⟩,⟨(-5795262015560),(-5795262015540)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨470951131794,470951131815⟩,⟨(-1388112679064),(-1388112679042)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨81872271113,81872271133⟩,⟨(-364016368509),(-364016368491)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨17164605674,17164605693⟩,⟨(-106059118670),(-106059118650)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨3235603898,3235603916⟩,⟨(-24247690167),(-24247690149)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-58317972764328754144),(-58317972764322023222)⟩,⟨(-1237662581694280124599),(-1237662581694273393657)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-601404816470629369612),(-601404816470616001244)⟩,⟨(-3154617479357414880295),(-3154617479357401511836)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-1804581071517368692890),(-1804581071517359624649)⟩,⟨(-3566539232543238591820),(-3566539232543229523395)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-2799710118047451591424),(-2799710118047447462177)⟩,⟨(-2307828141470510801837),(-2307828141470506672449)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-2619269726011013824836),(-2619269726011012580330)⟩,⟨(-409979271390236238559),(-409979271390234994041)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-1452598515712974625641),(-1452598515712974449019)⟩,⟨751960714557861723756,751960714557861900318⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-335415168623286442607),(-335415168623286421412)⟩,⟨809690171147247634917,809690171147247656089⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨139813744449667561876,139813744449667565688⟩,⟨391184885670625859865,391184885670625863688⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨157310117718366137344,157310117718366138734⟩,⟨82658232597320804276,82658232597320805671⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨68484424388692484792,68484424388692485393⟩,⟨(-16888912334779347168),(-16888912334779346564)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨16243621226365234720,16243621226365234969⟩,⟨(-21459506156632630417),(-21459506156632630168)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨393518482613484021,393518482613484157⟩,⟨(-10243215998518520601),(-10243215998518520464)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-1836730722030756401),(-1836730722030756325)⟩,⟨(-3574982881734840726),(-3574982881734840653)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-1254603089697708288),(-1254603089697708244)⟩,⟨(-1054018936814375436),(-1054018936814375394)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-600465280826078582),(-600465280826078554)⟩,⟨(-274485220407905867),(-274485220407905834)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-171303120493581394),(-171303120493581376)⟩,⟨(-51595043152715723),(-51595043152715703)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨91072595574061099984627,91072595574063599525695⟩,⟨(-46682822613658785027845),(-46682822613656285492349)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨235836405741490395469219,235836405741499688020938⟩,⟨(-165478514562180925804769),(-165478514562171633264617)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨267900934935788624368842,267900934935810223377305⟩,⟨(-324210318694690495529113),(-324210318694668896524621)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨142419491652260863340149,142419491652301274636082⟩,⟨(-456011121955620585226225),(-456011121955580173912835)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-89443611709808175237295),(-89443611709748987226042)⟩,⟨(-450420166430421889154430),(-450420166430362701106096)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-277543160702648192848471),(-277543160702542442214536)⟩,⟨(-271783511904507283016403),(-271783511904401532367376)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-296895942960359570164192),(-296895942960241176082122)⟩,⟨(-27967585737940340078984),(-27967585737821946009050)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-171100083442507530068121),(-171100083442415123983482)⟩,⟨126184553593909325495033,126184553594001731564748⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-27700137239880468394263),(-27700137239811043162753)⟩,⟨139830169899977965866754,139830169900047391099204⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨44911535036199998308436,44911535036228243852880⟩,⟨78494686123267607956448,78494686123295853506412⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨50456926378124251323237,50456926378137059111205⟩,⟨20659988000443589992198,20659988000456397781065⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨30783034952827228556677,30783034952831056493288⟩,⟨(-6257405245824953929864),(-6257405245821125994402)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨13294392682972954919564,13294392682973947593322⟩,⟨(-11248836759818933956865),(-11248836759817941284014)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨4181275985861785949601,4181275985862146358108⟩,⟨(-8274767920287831045628),(-8274767920287470637319)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨826183177249227995546,826183177249343177172⟩,⟨(-4404329208669148406007),(-4404329208669033224371)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨51602601774768212104,51602601774794570177⟩,⟨(-1331267555344055624992),(-1331267555344029266898)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨21428063043132340757546,21428063043132341131014⟩,⟨25093561239720658359640,25093561239720658750509⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨80902674810972680595536,80902674810972681767771⟩,⟨45010527882063023647490,45010527882063024832927⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨139450461218952707738028,139450461218952709740265⟩,⟨(-46555864442116019287567),(-46555864442116017376435)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨59572026343403376172456,59572026343403379038042⟩,⟨(-319405012427801625399023),(-319405012427801622823149)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-357296244941416401957069),(-357296244941416397100319)⟩,⟨(-679118217698830125483846),(-679118217698830121029118)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-1132835885856048261631181),(-1132835885856048253262299)⟩,⟨(-782379669967950031302798),(-782379669967950023084704)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-1902776948877794462080653),(-1902776948877794450429578)⟩,⟨(-286566317623026884494098),(-286566317623026872699139)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-2100528358357031610804452),(-2100528358357031595315506)⟩,⟨709981695833374649898253,709981695833374665632700⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-1491776617388995131674399),(-1491776617388995092194581)⟩,⟨1620352153628061748776879,1620352153628061788280069⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-443813472792563444924676),(-443813472792563301607755)⟩,⟨1895939435119698933020959,1895939435119699076245511⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨434236453946236595950444,434236453946237168346963⟩,⟨1507703099948276659558586,1507703099948277231895088⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨816100774236357587677258,816100774236359527411435⟩,⟨845623483001923622069100,845623483001925561813312⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨774900068185927490579424,774900068185931159065032⟩,⟨294813765667574243496170,294813765667577912011052⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨545087569307036078280942,545087569307040348264996⟩,⟨1074520921185489457996,1074520921189759466958⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨299097851756638699721007,299097851756642898421701⟩,⟨(-77434171958876223619614),(-77434171958872024908325)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨92755993272455627271135,92755993272457451902294⟩,⟨(-37547076148904552172484),(-37547076148902727538894)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-692623053725591771673047),(-692623053725494758240997)⟩,⟨549831715860582819112565,549831715860679832454867⟩⟩
lemma checked : cachedMomentRuleBox density1 hk9_1_14 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 9 14) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk9_1_14 (tableDensity true) (fullFactor true 9 14) density1_contains hk9_1_14_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-3524948754380106722753036),(-3524948754380106706308411)⟩,⟨3425039255819339257804719,3425039255819339274136291⟩⟩
lemma atomChecked : tableAtomBox true ha9_1_14 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 9 14) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha9_1_14 9 14 ha9_1_14_contains
 def realAnswer : RBox := ⟨(-4217571808105698594426083),(-4217571808105601364549408)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 9 14) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm9_1_1_14
namespace hm9_0_1_15
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk9_1_15 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-61),34⟩,⟨(-34),58⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-164),74⟩,⟨(-128),111⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-268),55⟩,⟨(-188),135⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-267),249⟩,⟨(-416),99⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-218),602⟩,⟨(-455),365⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-483),534⟩,⟨(-259),752⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-894),365⟩,⟨(-797),471⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-958),1416⟩,⟨(-1235),1127⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-1223),1007⟩,⟨(-829),1338⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-1278),1427⟩,⟨(-1400),1394⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-1341),1120⟩,⟨(-892),1483⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-1226),900⟩,⟨(-1365),828⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-792),1223⟩,⟨(-1120),890⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-500),701⟩,⟨(-537),739⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-403),342⟩,⟨(-204),397⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-126),117⟩,⟨(-60),126⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-24098549321),(-24098549304)⟩,⟨55716278748,55716278767⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-48253344072),(-48253344043)⟩,⟨115456904231,115456904263⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-36909991173),(-36909991131)⟩,⟨91771918106,91771918148⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-17419602331),(-17419602276)⟩,⟨42445604664,42445604720⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-6025441359),(-6025441291)⟩,⟨12563548927,12563548996⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-1651709826),(-1651709735)⟩,⟨2459428019,2459428107⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-356312882),(-356312742)⟩,⟨307362477,307362618⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-57654058),(-57653876)⟩,⟨17134010,17134193⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-6429645),(-6429442)⟩,⟨(-2041967),(-2041767)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-349298),(-348993)⟩,⟨(-642607),(-642302)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨33041,33379⟩,⟨(-77977),(-77638)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨11090,11384⟩,⟨(-2372),(-2081)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨1232,1582⟩,⟨1162,1515⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-168),137⟩,⟨265,574⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-174),24⟩,⟨(-6),193⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-68),20⟩,⟨(-35),52⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨211389850849772813,211389850849772833⟩,⟨186934245576003450,186934245576003466⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨558218074630707757,558218074630707777⟩,⟨371507679071174472,371507679071174492⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨666505091844654489,666505091844654509⟩,⟨221771062636177495,221771062636177519⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨492281333861647707,492281333861647727⟩,⟨(-28550728751823801),(-28550728751823778)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨220887479808930238,220887479808930260⟩,⟨(-128334254467571949),(-128334254467571927)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨50413207299880575,50413207299880596⟩,⟨(-88808662170266047),(-88808662170266026)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-1295570522445019),(-1295570522444999)⟩,⟨(-32529095565956966),(-32529095565956946)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-4782311537669815),(-4782311537669793)⟩,⟨(-7119101981341810),(-7119101981341788)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-1745489357350277),(-1745489357350251)⟩,⟨(-871839917984739),(-871839917984717)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-404647120056076),(-404647120056049)⟩,⟨(-4092357802226),(-4092357802197)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-76272007317795),(-76272007317763)⟩,⟨28741994892029,28741994892061⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-13694684416817),(-13694684416786)⟩,⟨10170625151437,10170625151468⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-2672147877238),(-2672147877208)⟩,⟨2906100103766,2906100103797⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-620636429093),(-620636429063)⟩,⟨848818177789,848818177818⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-170747690994),(-170747690968)⟩,⟨263686725540,263686725565⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-38292935742),(-38292935722)⟩,⟨62089264414,62089264433⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-644037032343462419742),(-644037032343460159750)⟩,⟨1015370010901878734713,1015370010901880994858⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-1287724210238669156765),(-1287724210238664878751)⟩,⟨2899562020513727156831,2899562020513731435334⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-526348499814633795042),(-526348499814630174851)⟩,⟨4052606043789948522185,4052606043789952142911⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨1111110030280827355395,1111110030280829233361⟩,⟨3722781350557875447842,3722781350557877325986⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨2189466135833036031192,2189466135833036517816⟩,⟨2024534074922741193079,2024534074922741679502⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨1907767984225543064994,1907767984225543133792⟩,⟨220906448997392514710,220906448997392583272⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨885972797283323981058,885972797283323993104⟩,⟨(-591642641519388642091),(-591642641519388630042)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨120657096484719044543,120657096484719047454⟩,⟨(-507075801718422364224),(-507075801718422361255)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-115960839149243883669),(-115960839149243882394)⟩,⟨(-199133963699148772112),(-199133963699148770831)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-90289716264788730525),(-90289716264788729883)⟩,⟨(-28136878498954221705),(-28136878498954221073)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-34365713931976683312),(-34365713931976682981)⟩,⟨14117820764647010288,14117820764647010618⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-7730403009983715492),(-7730403009983715323)⟩,⟨12197159411832930913,12197159411832931084⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-265677403159344144),(-265677403159344059)⟩,⟨5716136619029888786,5716136619029888872⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨818110691392620536,818110691392620585⟩,⟨2193718690118795205,2193718690118795251⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨557820407592105845,557820407592105871⟩,⟨760898484564853794,760898484564853821⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨178287962015001181,178287962015001202⟩,⟨182997705321042740,182997705321042758⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-48197458390025909009934),(-48197458390025016242128)⟩,⟨(-71399809390245233461716),(-71399809390244340698638)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-161188189794493393455797),(-161188189794490142072177)⟩,⟨(-175470530618689395800877),(-175470530618686144423527)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-291415258774025290623780),(-291415258774018025095583)⟩,⟨(-171838871589938358079458),(-171838871589931092541018)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-373166973479032981751246),(-373166973479020251436105)⟩,⟨(-37796413281791277773699),(-37796413281778547418068)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-321563083448543743240314),(-321563083448522276474443)⟩,⟨155753391908615744593419,155753391908637211404943⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-137809325613097408740958),(-137809325613059272657181)⟩,⟨270808921252751170478968,270808921252789306565921⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨58192561168075369465641,58192561168113618803085⟩,⟨227666540618586111899716,227666540618624361210062⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨142454383678152150384242,142454383678188881861226⟩,⟨87881595746053943173250,87881595746090674638177⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨108196045360809093918559,108196045360833140016782⟩,⟨(-25940199202072271657408),(-25940199202048225551073)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨36948174288202645551447,36948174288213538084477⟩,⟨(-59506930265462777591857),(-59506930265451885051473)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-7835731919976705918333),(-7835731919971810217686)⟩,⟨(-41706863800592410421028),(-41706863800587514721393)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-18970590227132987194413),(-18970590227131684181634)⟩,⟨(-16431599419934798891200),(-16431599419933495881348)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-14416741697556538062806),(-14416741697556086897205)⟩,⟨(-2076970326838314391476),(-2076970326837863226797)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-7796587791166286693191),(-7796587791166140854847)⟩,⟨2435338058861568872832,2435338058861714711265⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-3380853145503004984096),(-3380853145502962111026)⟩,⟨2351802210435470603462,2351802210435513476777⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-905727071911487804310),(-905727071911478450555)⟩,⟨865297319513503595234,865297319513512949093⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨202724314151893128938980,202724314151893129565417⟩,⟨(-174872881354716719041147),(-174872881354716718421959)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨496985793936604409192045,496985793936604411130380⟩,⟨(-586598407992698418952368),(-586598407992698417021630)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨460974800366111482580211,460974800366111485972142⟩,⟨(-1093263214570835084567527),(-1093263214570835081145938)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-43237345149754573611831),(-43237345149754568670898)⟩,⟨(-1507714128558534232548355),(-1507714128558534227509540)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-893302962156740054137372),(-893302962156740047496758)⟩,⟨(-1474761946568447354364345),(-1474761946568447347609389)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-1623373085519110594884184),(-1623373085519110586680173)⟩,⟨(-780033786322073028813727),(-780033786322073020578481)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-1696334337147892896231554),(-1696334337147892887447791)⟩,⟨314625406758285686141525,314625406758285694879103⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-1002079987720965091360507),(-1002079987720965082163923)⟩,⟨1161833850857101874033606,1161833850857101883176833⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-13859337172690141605777),(-13859337172690124678694)⟩,⟨1287817682470018158547400,1287817682470018175472060⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨656518630961495285068191,656518630961495332387215⟩,⟨799706445114683600110507,799706445114683647439751⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨782725879840396463081408,782725879840396665112795⟩,⟨175491285152613119203554,175491285152613321234094⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨558526609867215099039786,558526609867215736013299⟩,⟨(-219347629393805852461747),(-219347629393805215490915)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨274710574458394080090645,274710574458395206856860⟩,⟨(-328119599617985029042361),(-328119599617983902274834)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨86228916114083295473200,86228916114084776000913⟩,⟨(-269047614099994955139374),(-269047614099993474608849)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨7355141874607219305536,7355141874608776057651⟩,⟨(-159209959422041388935603),(-159209959422039832181946)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-4506175206215520153737),(-4506175206214858257828)⟩,⟨(-51127402072503238605608),(-51127402072502576709268)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-464547654635894315640453),(-464547654635859933010037)⟩,⟨(-457730294494538484144648),(-457730294494504101475836)⟩⟩
lemma checked : cachedMomentRuleBox density0 hk9_1_15 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 9 15) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk9_1_15 (tableDensity false) (fullFactor true 9 15) density0_contains hk9_1_15_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-661064331533263703856467),(-661064331533263700238776)⟩,⟨(-589304302740379057759747),(-589304302740379054121511)⟩⟩
lemma atomChecked : tableAtomBox false ha9_1_15 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 9 15) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha9_1_15 9 15 ha9_1_15_contains
 def realAnswer : RBox := ⟨(-1125611986169158119496920),(-1125611986169123533248813)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 9 15) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm9_0_1_15
namespace hm9_1_1_15
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk9_1_15 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-18),16⟩,⟨(-16),17⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-35),16⟩,⟨(-27),23⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-52),16⟩,⟨(-46),30⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-47),54⟩,⟨(-77),25⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-45),109⟩,⟨(-77),76⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-90),88⟩,⟨(-51),128⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-147),71⟩,⟨(-137),79⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-157),229⟩,⟨(-199),186⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-200),168⟩,⟨(-138),222⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-214),239⟩,⟨(-237),234⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-231),200⟩,⟨(-154),259⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-221),157⟩,⟨(-240),150⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-141),218⟩,⟨(-203),155⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-88),128⟩,⟨(-98),132⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-73),66⟩,⟨(-39),73⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-28),28⟩,⟨(-16),28⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-7440366999),(-7440366983)⟩,⟨5856674925,5856674942⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-14858051950),(-14858051931)⟩,⟨12282001219,12282001236⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-11118609473),(-11118609455)⟩,⟨9927804411,9927804428⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-4879356270),(-4879356246)⟩,⟨4649636144,4649636166⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-1458975688),(-1458975666)⟩,⟨1377776221,1377776242⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-331679023),(-331678998)⟩,⟨264312140,264312162⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-60835439),(-60835406)⟩,⟨30355554,30355588⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-8830038),(-8829998)⟩,⟨792170,792209⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-912995),(-912952)⟩,⟨(-458505),(-458462)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-41888),(-41828)⟩,⟨(-106659),(-106599)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨6613,6685⟩,⟨(-12136),(-12068)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨1914,1975⟩,⟨(-242),(-179)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨190,265⟩,⟨220,299⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-44),22⟩,⟨42,113⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-40),9⟩,⟨(-12),41⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-22),16⟩,⟨(-16),16⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨18530139566968902,18530139566968918⟩,⟨60954177565382401,60954177565382418⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨62878035776722020,62878035776722038⟩,⟨137930102972322673,137930102972322691⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨100032455692681907,100032455692681924⟩,⟨122938071997279713,122938071997279731⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨94953757536700011,94953757536700028⟩,⟨55061476130193132,55061476130193149⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨54895024575971881,54895024575971898⟩,⟨3991962910166873,3991962910166889⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨18806528083868544,18806528083868561⟩,⟨(-9182571698759216),(-9182571698759198)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨3244177724999542,3244177724999560⟩,⟨(-5418996896761887),(-5418996896761869)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-83083496787348),(-83083496787332)⟩,⟨(-1589968153573794),(-1589968153573778)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-203579804034836),(-203579804034819)⟩,⟨(-288828577713337),(-288828577713318)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-64906491216947),(-64906491216929)⟩,⟨(-32712196849193),(-32712196849176)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-14543748388769),(-14543748388751)⟩,⟨(-1112268444023),(-1112268444006)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-2950002582040),(-2950002582022)⟩,⟨623041231401,623041231420⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-625845181916),(-625845181896)⟩,⟨264656601066,264656601084⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-151609555365),(-151609555347)⟩,⟨87300615907,87300615924⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-42053542847),(-42053542830)⟩,⟨28457696874,28457696891⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-9388263513),(-9388263496)⟩,⟨6827312305,6827312321⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-375496547702462337647),(-375496547702460439705)⟩,⟨143407038281260143006,143407038281262040937⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-912449124712789809856),(-912449124712786220207)⟩,⟨509506145363824523588,509506145363828113187⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-916028144187322680301),(-916028144187319648101)⟩,⟨934760070089448946597,934760070089451978739⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-414615247252686336789),(-414615247252684769007)⟩,⟨1124803793838609434399,1124803793838611002159⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨169767877262294900167,169767877262295302884⟩,⟨869789474337844825209,869789474337845227943⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨412783412805853364996,412783412805853419256⟩,⟨370135369710167045049,370135369710167099338⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨301755286960786660585,301755286960786668599⟩,⟨4403150300871394697,4403150300871402716⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨107573867026246926052,107573867026246927322⟩,⟨(-97987250255155368361),(-97987250255155367096)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨4434858312400344505,4434858312400344982⟩,⟨(-63207748232055651642),(-63207748232055651165)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-15978091748948011938),(-15978091748948011702)⟩,⟨(-20006022404600659936),(-20006022404600659702)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-9744643620904124219),(-9744643620904124094)⟩,⟨(-1954473525333377737),(-1954473525333377610)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-3498557242397340032),(-3498557242397339961)⟩,⟨1596547184471029146,1596547184471029215⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-882246245668081419),(-882246245668081380)⟩,⟨1248306243863685761,1248306243863685801⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-128988364924102882),(-128988364924102857)⟩,⟨616690017138850718,616690017138850745⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨18377845306976342,18377845306976361⟩,⟨255132785106249049,255132785106249070⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨14662565264595699,14662565264595715⟩,⟨68022149217718631,68022149217718647⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-17016580592506465533387),(-17016580592505731969667)⟩,⟨(-22617000973923619994638),(-22617000973922886429959)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-56514401108862089266466),(-56514401108859417374018)⟩,⟨(-56476235788415009550053),(-56476235788412337656182)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-102245201114285198153705),(-102245201114279226442235)⟩,⟨(-57419640443562310255898),(-57419640443556338546171)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-133346778769295110917933),(-133346778769284645554918)⟩,⟨(-15609356972772877741362),(-15609356972762412386558)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-120500500454857833858313),(-120500500454840183666753)⟩,⟨49759356347393380130366,49759356347411030311689⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-60060879707667167093819),(-60060879707635810611239)⟩,⟨94090952304725088000640,94090952304756444481511⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨10876018875245925845919,10876018875277369304070⟩,⟨86194858669557706157245,86194858669589149621008⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨47990606266358591803037,47990606266388772476340⟩,⟨40607256414343345237824,40607256414373525914049⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨42752843303074455801154,42752843303094198591980⟩,⟨(-2212231383631216013142),(-2212231383611473223845)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨19588519155600287663922,19588519155609220855659⟩,⟨(-19421713405077073777829),(-19421713405068140587563)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨1913615125982060363512,1913615125986070511377⟩,⟨(-16772039798982712474762),(-16772039798978702326723)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-4623435743698618136809),(-4623435743697552283525)⟩,⟨(-8708596928748097595345),(-8708596928747031741515)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-4656313146542927028902),(-4656313146542558475581)⟩,⟨(-2985816851775151556455),(-2985816851774783002957)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-2934397956066074844908),(-2934397956065955842768)⟩,⟨(-476155731578061874974),(-476155731577942872846)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-1434630982897310815451),(-1434630982897275860841)⟩,⟨184098014561766849170,184098014561801803738⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-414986569646817733961),(-414986569646810111406)⟩,⟨118170393372694717365,118170393372702339902⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨5773125802518706081097,5773125802518706175128⟩,⟨(-5478933434398491257237),(-5478933434398491165852)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨9795818752317347833825,9795818752317348118291⟩,⟨(-20123707930883481822813),(-20123707930883481536811)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-13290961406463861998731),(-13290961406463861542699)⟩,⟨(-33136682336534367531921),(-33136682336534367046308)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-78922647788724231293760),(-78922647788724230685115)⟩,⟨(-9422047392263508171467),(-9422047392263507483322)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-160749559035050628965746),(-160749559035050627860526)⟩,⟨100205783723867445366456,100205783723867446565384⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-171325627155989787761074),(-171325627155989785733663)⟩,⟨297639082858053495825278,297639082858053497878073⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-27729849832120392864933),(-27729849832120390013187)⟩,⟨484877023279492084041537,484877023279492086845684⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨235949196227964287413201,235949196227964291344746⟩,⟨515326979278499905117251,515326979278499908991120⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨461227749855225152262808,461227749855225162727503⟩,⟨335714118151885186879434,335714118151885197347408⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨508308642239346798706478,508308642239346834291085⟩,⟨52829686077395565379831,52829686077395600994288⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨381173669960537066031110,381173669960537228362993⟩,⟨(-169211805481439616631141),(-169211805481439454287681)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨192704590089893352364036,192704590089893870357859⟩,⟨(-250483428508210659948936),(-250483428508210141960767)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨46395937037396015781957,46395937037396934655541⟩,⟨(-220386891205775931277467),(-220386891205775012413407)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-23919781437130001881520),(-23919781437128792852747)⟩,⟨(-147338552727210273414384),(-147338552727209064391946)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-34770251805935414655047),(-34770251805934142364923)⟩,⟨(-77651938394823425814262),(-77651938394822153526174)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-14556277403799937642579),(-14556277403799396520229)⟩,⟨(-23491598966011444870261),(-23491598966010903748312)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨155630858400301098192425,155630858400329339035912⟩,⟨150316798244276911065137,150316798244305151930169⟩⟩
lemma checked : cachedMomentRuleBox density1 hk9_1_15 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 9 15) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk9_1_15 (tableDensity true) (fullFactor true 9 15) density1_contains hk9_1_15_contains
noncomputable def atomAnswer : CBox := ⟨⟨864468741235806377235322,864468741235806381966149⟩,⟨770628703583572609235822,770628703583572613993516⟩⟩
lemma atomChecked : tableAtomBox true ha9_1_15 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 9 15) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha9_1_15 9 15 ha9_1_15_contains
 def realAnswer : RBox := ⟨1020099599636107375427747,1020099599636135821002061⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 9 15) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm9_1_1_15
end SharpPlanar.CachedData

end OAI
