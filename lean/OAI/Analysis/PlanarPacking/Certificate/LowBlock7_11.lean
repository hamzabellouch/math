import OAI.Analysis.PlanarPacking.Certificate.TableDensityValues
import OAI.Analysis.PlanarPacking.Certificate.HighHeaders7

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm7_0_1_8
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk7_1_8 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-854065703),(-854064941)⟩,⟨(-680733065),(-680732307)⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-1401074890),(-1401072644)⟩,⟨(-1881427987),(-1881425742)⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-234499588),(-234496066)⟩,⟨(-2026505103),(-2026501584)⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨720517147,720521605⟩,⟨(-867256420),(-867251951)⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨445201052,445207340⟩,⟨105498486,105504786⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-12806818),(-12798317)⟩,⟨151058855,151067386⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-44176873),(-44166054)⟩,⟨(-10844543),(-10833711)⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨8453182,8464257⟩,⟨(-10802302),(-10791234)⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨1282590,1292235⟩,⟨4393443,4403009⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-1665410),(-1654765)⟩,⟨(-765692),(-755050)⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨798597,809588⟩,⟨(-406979),(-395897)⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-28940),(-19059)⟩,⟨531454,541322⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-357423),(-349821)⟩,⟨(-99129),(-91519)⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨24366,29498⟩,⟨(-259102),(-253973)⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨139610,142403⟩,⟨(-77350),(-74649)⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨54738,55651⟩,⟨(-590),293⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-38204008524767911),(-38204008524767744)⟩,⟨(-13789941793789040),(-13789941793788873)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-83913505725666113),(-83913505725665647)⟩,⟨(-31082554546258766),(-31082554546258301)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-74986519436821259),(-74986519436820548)⟩,⟨(-29960939258941404),(-29960939258940694)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-41273546471692075),(-41273546471691028)⟩,⟨(-19386967640898952),(-19386967640897906)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-15242281616822330),(-15242281616820802)⟩,⟨(-9441973842692511),(-9441973842690979)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-3811360933184104),(-3811360933182025)⟩,⟨(-3572292707996798),(-3572292707994721)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-582619609257148),(-582619609254488)⟩,⟨(-1042300237225133),(-1042300237222473)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-15991530050150),(-15991530046958)⟩,⟨(-227552449418386),(-227552449415198)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨19134938280238,19134938283710⟩,⟨(-34121015725568),(-34121015722097)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨6127122743130,6127122746431⟩,⟨(-2203149265145),(-2203149261845)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨1014294992681,1014294996564⟩,⟨516036121423,516036125304⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨53102733875,53102738272⟩,⟨217790702613,217790707004⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-29236859909),(-29236855955)⟩,⟨43453054898,43453058848⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-14239003355),(-14239000298)⟩,⟨3777270697,3777273756⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-4528299095),(-4528297135)⟩,⟨(-1255662379),(-1255660418)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-970405539),(-970404836)⟩,⟨(-596896034),(-596895330)⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨10736732775354544508573,10736732775354544541848⟩,⟨3985648929422546871471,3985648929422546903966⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨27305257690618009865380,27305257690618009949552⟩,⟨7249829330395197337532,7249829330395197419460⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨31805776027490206022648,31805776027490206125136⟩,⟨2347741674510095494901,2347741674510095594201⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨24589815565874566580027,24589815565874566669827⟩,⟨(-4717115728968491512559),(-4717115728968491425144)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨13120833073534980564581,13120833073534980624999⟩,⟨(-7361664149571986192812),(-7361664149571986133255)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨4665297509145136986829,4665297509145137018465⟩,⟨(-5516454377371077708043),(-5516454377371077676491)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨933431787194660389153,933431787194660402494⟩,⟨(-2701941731158248552314),(-2701941731158248538875)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-24216207493096928402),(-24216207493096922496)⟩,⟨(-961500198156124717989),(-961500198156124712014)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-97856488882828044017),(-97856488882828041247)⟩,⟨(-268473173654776071240),(-268473173654776068459)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-45713286788426305822),(-45713286788426304118)⟩,⟨(-63732568866011767115),(-63732568866011765405)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-15472229644871874708),(-15472229644871873068)⟩,⟨(-14108973590773205849),(-14108973590773204205)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-4743607882054490953),(-4743607882054489380)⟩,⟨(-3225452508378376826),(-3225452508378375254)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-1469415054519397313),(-1469415054519395859)⟩,⟨(-834410310031104921),(-834410310031103473)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-485781573900275597),(-485781573900274479)⟩,⟨(-254719905229265161),(-254719905229264042)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-167568570611112525),(-167568570611111845)⟩,⟨(-86569830089590740),(-86569830089590063)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-41805835557037189),(-41805835557036958)⟩,⟨(-21734933832099571),(-21734933832099342)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨10880422093381760556372181,10880422093381788609265417⟩,⟨(-6403503113056112104035130),(-6403503113056084050858333)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨27218389415355656663348521,27218389415355715190338705⟩,⟨(-20168520154998506654578975),(-20168520154998448126053644)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨29964080071596878894946207,29964080071596923952996048⟩,⟨(-33749093069450156979120945),(-33749093069450111917092713)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨18660593506434653600624266,18660593506434671470242458⟩,⟨(-41101593147991227450034637),(-41101593147991209574031516)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨1655654003631907996559040,1655654003631913142999051⟩,⟨(-37044569229457740077956314),(-37044569229457734927096341)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-10240695017750228897599221),(-10240695017750227827826688)⟩,⟨(-23894070159554931557155247),(-23894070159554930486577988)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-12549553596550489995308314),(-12549553596550489851709912)⟩,⟨(-9849963965060629072229575),(-9849963965060628929721109)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-8681278188980165490341758),(-8681278188980165463317495)⟩,⟨(-1183619115997342220850955),(-1183619115997342194943970)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-4051996685770110905229347),(-4051996685770110891583136)⟩,⟨1714854486125688200517108,1714854486125688213937325⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-1254225335455138933230460),(-1254225335455138925625247)⟩,⟨1643355681254404593556929,1643355681254404601248126⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-159173670609461576063733),(-159173670609461572032493)⟩,⟨918245667476544458170447,918245667476544462304305⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨103491150928323951495980,103491150928323953596820⟩,⟨400624519605627519741051,400624519605627521874819⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨105584673389772238924298,105584673389772239985851⟩,⟨151880202850524521446814,151880202850524522512858⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨64553800575671027818823,64553800575671028338311⟩,⟨53165557604843729256403,53165557604843729774232⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨31725676032759419442408,31725676032759419677115⟩,⟨17428898197911826111051,17428898197911826343998⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨9340048863253828409084,9340048863253828476142⟩,⟨4037479221222646131471,4037479221222646197889⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨434965942983591915414289283,434965942983597613355599106⟩,⟨(-326345737050310237178381479),(-326345737050304539215955934)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨1099856714435056411303660193,1099856714435077072707934456⟩,⟨(-1037976991142669831100219838),(-1037976991142649169666717920)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨1210184633951376172516115277,1210184633951423116323936106⟩,⟨(-1802799918386912025505183850),(-1802799918386865081739462417)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨640282237018642121641805139,640282237018731849983482659⟩,⟨(-2363564885532223786641520306),(-2363564885532134058483241771)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-361679684672436843728087310),(-361679684672301094520291405)⟩,⟨(-2360037675016681945957436984),(-2360037675016546197076493325)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-1248762907669370176122905113),(-1248762907669141027981964888)⟩,⟨(-1677938881287669198034934538),(-1677938881287440050124047819)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-1549922295742881176845238479),(-1549922295742563145374882378)⟩,⟨(-640559614291236598329757447),(-640559614290918566883828078)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-1226181848065532132773983489),(-1226181848065263691962397398)⟩,⟨222644756933050889759462691,222644756933319330674944355⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-627349256488762148653044496),(-627349256488603447371412508)⟩,⟨601131888603376695159840725,601131888603535396553467558⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-131423122743235150414454082),(-131423122743133385170571416)⟩,⟨560749862710806876947818923,560749862710908642216606879⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨114456036314079592236339451,114456036314120921325993351⟩,⟨349781163368295087214905904,349781163368336416286415700⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨165958174266227430178937661,165958174266239127746385116⟩,⟨158229830014775485099612605,158229830014787182640230577⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨131364693369166436697317643,131364693369170352619794953⟩,⟨47152154162141261662685864,47152154162145177571910770⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨81424160712154184994900552,81424160712155589156895097⟩,⟨1708757593251860164217604,1708757593253264322516188⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨41421737873040995791592562,41421737873041462685172886⟩,⟨(-8359796215950050030471706),(-8359796215949583137340028)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨12423556064438852894162876,12423556064438963697834115⟩,⟨(-3985461317440259141514331),(-3985461317440148337754361)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨881140074877730085160310374,881140074877730087267355525⟩,⟨(-1291912266316226759032867681),(-1291912266316226756904971689)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨2046969984106085387369889217,2046969984106085393815726432⟩,⟨(-3995826464260967425059658048),(-3995826464260967418491044388)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨1583968100642516975462686980,1583968100642516986518658335⟩,⟨(-6742382662172149449414791046),(-6742382662172149438010026844)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-943049203598606101150111614),(-943049203598606085309404214)⟩,⟨(-8750976742092737900657513011),(-8750976742092737884164091304)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-4895461783233498270835133252),(-4895461783233498249376221858)⟩,⟨(-8789978414054310761731937379),(-8789978414054310739563054182)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-8554135429966239777444087447),(-8554135429966239749597698043)⟩,⟨(-6123910814926172586743309459),(-6123910814926172558530290975)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-9999726791343161714438022326),(-9999726791343161681529780659)⟩,⟨(-1453552703100241952201261503),(-1453552703100241919285739760)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-8435269725880256743856904388),(-8435269725880256704573246455)⟩,⟨3220100450102810335720170053,3220100450102810374794352643⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-4788181398520321738483634270),(-4788181398520321667146174373)⟩,⟨5941928775871926723761717416,5941928775871926794918024022⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-943077479228542420958723102),(-943077479228542111355463192)⟩,⟨6112172805101026549753179678,6112172805101026859321820498⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨1633245835384096778645191293,1633245835384098043854463720⟩,⟨4560079064283192247209529076,4560079064283193512424589749⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨2594370485597714666909087945,2594370485597718040648986178⟩,⟨2585996671937299239382526154,2585996671937302613112013340⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨2416319308089135869942159453,2416319308089142124055820362⟩,⟨1064825042182713297868923261,1064825042182719551954069872⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨1744567710653027660746477385,1744567710653037938210190486⟩,⟨232056730004128815524457005,232056730004139092965618776⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨998141038287108148454760483,998141038287118325465664160⟩,⟨(-59361681066781998237119827),(-59361681066771821237428378)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨319289580763013220397813721,319289580763017468532427535⟩,⟨(-50338712249925083520723586),(-50338712249920835389248564)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-4250333507183255419177249448),(-4250333507183010405581604325)⟩,⟨(-3664958472229572821962727221),(-3664958472229327808171925333)⟩⟩
lemma checked : cachedMomentRuleBox density0 hk7_1_8 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 7 8) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk7_1_8 (tableDensity false) (fullFactor true 7 8) density0_contains hk7_1_8_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-5291461313845305461255746879),(-5291461313845305455315036914)⟩,⟨(-3666708850719308961454128310),(-3666708850719308955441430306)⟩⟩
lemma atomChecked : tableAtomBox false ha7_1_8 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 7 8) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha7_1_8 7 8 ha7_1_8_contains
 def realAnswer : RBox := ⟨(-9541794821028560880532996327),(-9541794821028315860796641239)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 7 8) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm7_0_1_8
namespace hm7_1_1_8
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk7_1_8 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-129408756),(-129408612)⟩,⟨(-134656500),(-134656356)⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-193105398),(-193104993)⟩,⟨(-353377830),(-353377425)⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨13773878,13774509⟩,⟨(-350429157),(-350428525)⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨145776034,145776824⟩,⟨(-124615855),(-124615064)⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨69542217,69543301⟩,⟨29959326,29960409⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-5663869),(-5662461)⟩,⟨23548383,23549793⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-6695022),(-6693290)⟩,⟨(-2374505),(-2372768)⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨1387709,1389462⟩,⟨(-1647532),(-1645779)⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨221657,223207⟩,⟨708556,710090⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-288699),(-286948)⟩,⟨(-114677),(-112922)⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨135764,137627⟩,⟨(-80937),(-79053)⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨1470,3181⟩,⟨95981,97686⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-65971),(-64650)⟩,⟨(-13366),(-12045)⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨722,1604⟩,⟨(-47173),(-46286)⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨23846,24327⟩,⟨(-16223),(-15762)⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨9809,9971⟩,⟨(-1101),(-945)⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-4218767159712052),(-4218767159711996)⟩,⟨(-4726457382383294),(-4726457382383239)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-9213573297460380),(-9213573297460252)⟩,⟨(-10251870714431758),(-10251870714431635)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-8128504589476475),(-8128504589476298)⟩,⟨(-9051358741471759),(-9051358741471581)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-4378776820049952),(-4378776820049734)⟩,⟨(-5067223885096001),(-5067223885095782)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-1564335600462446),(-1564335600462187)⟩,⟨(-2054350076834357),(-2054350076834098)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-367001756975195),(-367001756974885)⟩,⟨(-651855770627738),(-651855770627428)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-44750629154850),(-44750629154460)⟩,⟨(-166733981069130),(-166733981068741)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨4294566733561,4294566734036⟩,⟨(-33376214784432),(-33376214783957)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨3672701278903,3672701279440⟩,⟨(-4656022139730),(-4656022139199)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨996059278612,996059279143⟩,⟨(-225214744960),(-225214744431)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨156680924598,156680925247⟩,⟨100214190199,100214190847⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨5795180014,5795180781⟩,⟨37880444328,37880445098⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-5882717897),(-5882717173)⟩,⟨7240705594,7240706318⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-2672211363),(-2672210783)⟩,⟨426934338,426934919⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-815901843),(-815901461)⟩,⟨(-328554533),(-328554151)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-168497724),(-168497577)⟩,⟨(-133656563),(-133656415)⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨1592928500558721846913,1592928500558721857435⟩,⟨2036658681651290423525,2036658681651290434012⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨4378279646403639986065,4378279646403640012831⟩,⟨4649417023223910870613,4649417023223910897268⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨5769619592974604485929,5769619592974604517660⟩,⟨4298383893689852133966,4298383893689852165555⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨5144311429366850739054,5144311429366850765620⟩,⟨2137678679661000943974,2137678679661000970434⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨3226738595044512616808,3226738595044512633663⟩,⟨282033900450714627076,282033900450714643898⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨1426065424843980871097,1426065424843980879270⟩,⟨(-393892515000146977684),(-393892515000146969518)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨437801370444015870018,437801370444015873179⟩,⟨(-339986813561367026851),(-339986813561367023685)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨87580970560299782410,87580970560299783696⟩,⟨(-155584461335137922850),(-155584461335137921561)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨7374666345082587312,7374666345082587946⟩,⟨(-51236708094478465624),(-51236708094478464993)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-2330359108181649899),(-2330359108181649354)⟩,⟨(-13896816888633093577),(-13896816888633093033)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-1442012120907207445),(-1442012120907206758)⟩,⟨(-3458440705603219782),(-3458440705603219093)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-523877902318899741),(-523877902318898975)⟩,⟨(-867618012519390521),(-867618012519389758)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-170660173518672149),(-170660173518671444)⟩,⟨(-235331654298093363),(-235331654298092662)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-56736897721351657),(-56736897721351132)⟩,⟨(-71437516167476460),(-71437516167475935)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-19470974524625556),(-19470974524625243)⟩,⟨(-23452950664682488),(-23452950664682176)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-4841592698254020),(-4841592698253909)⟩,⟨(-5725079781061384),(-5725079781061274)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨4195406215686091877642858,4195406215686115440679622⟩,⟨458139832775744973897013,458139832775768536905053⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨11157943176762739091198643,11157943176762788214677695⟩,⟨64327809580515353789872,64327809580564477111357⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨14166911227993187334185901,14166911227993225092404645⟩,⟨(-2855717572461230448085260),(-2855717572461192690275773)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨12209202141917601299874941,12209202141917616230631417⟩,⟨(-6700202075507671388454862),(-6700202075507656458351450)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨6893410776719004193989369,6893410776719008468311674⟩,⟨(-8597548168662126728620861),(-8597548168662122454742160)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨1566652036037453333805485,1566652036037454204096803⟩,⟨(-7339832326475333509641237),(-7339832326475332639426093)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-1345537600832799863785611),(-1345537600832799759581250)⟩,⟨(-4314180217653609822791994),(-4314180217653609718477378)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-1816518628798943251038872),(-1816518628798943238127326)⟩,⟨(-1637505218852385698269210),(-1637505218852385685249505)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-1186309638395058708039509),(-1186309638395058702891263)⟩,⟨(-236426515575936275246608),(-236426515575936270079166)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-530432649228989451160682),(-530432649228989448415390)⟩,⟨178385025838894631566388,178385025838894634302035⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-171601960145595156936502),(-171601960145595155491625)⟩,⟨180860378748776339431499,180860378748776340866439⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-35177198404524681805591),(-35177198404524681053705)⟩,⟨104441557869067929501824,104441557869067930250703⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨1911396354238791985543,1911396354238792366991⟩,⟨49382344264669475727618,49382344264669476108736⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨7050861500054902585904,7050861500054902774157⟩,⟨21373193537364949387312,21373193537364949575762⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨4771615099751352381320,4771615099751352467155⟩,⟨8576317439562066519250,8576317439562066605260⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨1571035399232425180079,1571035399232425204753⟩,⟨2283028012288636054302,2283028012288636079037⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨137232875138525029481341799,137232875138529711929253780⟩,⟨(-114400659858284143610576123),(-114400659858279461168375653)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨353633012430915183150350222,353633012430932163739896638⟩,⟨(-363426754196332062516178845),(-363426754196315081936670783)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨406315499682492948550947486,406315499682531535195994546⟩,⟨(-633359274202290386190850400),(-633359274202251799542280619)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨242535101856661708129124452,242535101856735475341001130⟩,⟨(-841936494235223911499511342),(-841936494235150144252946561)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-80325187258504816794800507),(-80325187258393200502760148)⟩,⟨(-867012930319988070392940515),(-867012930319876454031716620)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-396348584460748594551717635),(-396348584460560181783233206)⟩,⟨(-657864260857563471572606847),(-657864260857375058749496829)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-538848296537101037493802974),(-538848296536839595043507897)⟩,⟨(-306303928449962162191418699),(-306303928449700719729496321)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-467672877453651725225915008),(-467672877453431152611865847)⟩,⟨13870533485531765319897168,13870533485752337913769490⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-279503040603560094436062745),(-279503040603429798795479179)⟩,⟨183047242988392169066262016,183047242988522464683171734⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-101586053802762309003557712),(-101586053802678846457910062)⟩,⟨202568597955772772946470462,202568597955856235486463658⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨2425287950858925166022529,2425287950892778817996701⟩,⟨146220797379181440081735020,146220797379215293736823572⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨38357771550856981057569537,38357771550866549810125187⟩,⟨81407571401641988131152596,81407571401651556888549022⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨37970768926122647491167951,37970768926125846434597659⟩,⟨36926993447089467908880208,36926993447092666854704491⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨26222738922894039943368442,26222738922895185758585664⟩,⟨13796790065698838749847474,13796790065699984565729185⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨14257717776792671366921429,14257717776793052053026413⟩,⟨4113480361100348851701984,4113480361100729537892522⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨4425792521017937533568795,4425792521018027839895802⟩,⟨781221844099429033016405,781221844099519339330752⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨24345413143513295575233865,24345413143513296049749288⟩,⟨(-39611703588694307398918906),(-39611703588694306895006429)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨29005932674074575691850655,29005932674074577089637620⟩,⟨(-127609039258496955907978328),(-127609039258496954386826638)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-109094488841911700818646931),(-109094488841911698649771498)⟩,⟨(-178692816974436965333340899),(-178692816974436962870724652)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-464784984810174099363373835),(-464784984810174096611827576)⟩,⟨(-21820888379200777001545277),(-21820888379200773726709718)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-962322067916291429095498022),(-962322067916291424638277519)⟩,⟨543377967432534466598447475,543377967432534471630964645⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-1292210579114588151661473737),(-1292210579114588143695754348)⟩,⟨1529774070880681139360681326,1529774070880681147614751446⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-1077144604286794045323223863),(-1077144604286794033189531489)⟩,⟨2625284373718054347380120186,2625284373718054359464850635⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-227275588616145774765016353),(-227275588616145756164837023)⟩,⟨3318778236676428646421241312,3318778236676428664724863290⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨905260677786517881086435291,905260677786517927946998662⟩,⟨3247713267035919335128533082,3247713267035919381681778130⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨1784546730762842377416444868,1784546730762842621389963760⟩,⟨2470938904466986915691231878,2470938904466987159575807525⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨2090569936823941715383080260,2090569936823942741486170761⟩,⟨1396893442869046458540221234,1396893442869047484677287528⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨1870924321607784253942762713,1870924321607787003354120133⟩,⟨463972488632148419505657781,463972488632151168987007466⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨1385419360267833482924306082,1385419360267838588044958318⟩,⟨(-103297513691877420045382269),(-103297513691872314867545492)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨876925959517710695197863439,876925959517719092713880578⟩,⟨(-309001667623100428312601316),(-309001667623092030774588744)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨461484426076455161704467172,461484426076463481463611280⟩,⟨(-268234662678691170704053562),(-268234662678682850938519488)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨141326378426067303041643374,141326378426070776760581232⟩,⟨(-101576013995333023807820165),(-101576013995329550087784763)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨813535111512273276155998391,813535111512474542893007185⟩,⟨1885786029100760199511524219,1885786029100961466481902951⟩⟩
lemma checked : cachedMomentRuleBox density1 hk7_1_8 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 7 8) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk7_1_8 (tableDensity true) (fullFactor true 7 8) density1_contains hk7_1_8_contains
noncomputable def atomAnswer : CBox := ⟨⟨6919603256566937903104279041,6919603256566937910872899765⟩,⟨4794926958632942480192639631,4794926958632942488055398559⟩⟩
lemma atomChecked : tableAtomBox true ha7_1_8 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 7 8) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha7_1_8 7 8 ha7_1_8_contains
 def realAnswer : RBox := ⟨7733138368079211179160277432,7733138368079412453865906950⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 7 8) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm7_1_1_8
namespace hm7_0_1_9
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk7_1_9 j i k))
noncomputable def s0_0 : CBox := ⟨⟨448386948,448387704⟩,⟨932476628,932477388⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨437947663,437949970⟩,⟨2185399117,2185401422⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-599431798),(-599427947)⟩,⟨1854886461,1854890316⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-967684990),(-967679642)⟩,⟨493113456,493118811⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-364586709),(-364580299)⟩,⟨(-255309670),(-255303238)⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨61996886,62003816⟩,⟨(-135607651),(-135600671)⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨38655915,38666048⟩,⟨23484747,23494852⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-11034266),(-11022685)⟩,⟨8268635,8280211⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-318275),(-307330)⟩,⟨(-4643580),(-4632679)⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨1532611,1542501⟩,⟨1050091,1059994⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-875727),(-864971)⟩,⟨297401,308297⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨68271,78379⟩,⟨(-551578),(-541469)⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨353216,361126⟩,⟨113803,121725⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-37947),(-32605)⟩,⟨259581,264920⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-146806),(-143922)⟩,⟨74845,77638⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-56987),(-56053)⟩,⟨(-426),476⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨13062428894489394,13062428894489544⟩,⟨29414648526141990,29414648526142141⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨28696439989595360,28696439989595800⟩,⟨65120924737756519,65120924737756959⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨25217893965658476,25217893965659208⟩,⟨59553172906874274,59553172906875005⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨12915789292833776,12915789292834823⟩,⟨34564254027582615,34564254027583667⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨3822836472545742,3822836472547102⟩,⟨14194599780724284,14194599780725644⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨391072322549531,391072322551081⟩,⟨4332066065894219,4332066065895770⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-189838695091063),(-189838695089329)⟩,⟨993518772089418,993518772091150⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-110459503316215),(-110459503313667)⟩,⟨162829800531206,162829800533760⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-31265967072011),(-31265967068574)⟩,⟨14256827526498,14256827529939⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-5636946935487),(-5636946931661)⟩,⟨(-1448487270511),(-1448487266687)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-529655766553),(-529655762955)⟩,⟨(-887505470380),(-887505466782)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨59127120508,59127123689⟩,⟨(-197748102750),(-197748099577)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨43305609616,43305612747⟩,⟨(-22400893877),(-22400890754)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨13496975307,13496978018⟩,⟨3001324936,3001327636⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨3296977703,3296979559⟩,⟨2964963451,2964965311⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨577773532,577774225⟩,⟨909879516,909880208⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-1122530139529011385548),(-1122530139529011367970)⟩,⟨(-7352792199883939430168),(-7352792199883939411895)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-4582520366850684317211),(-4582520366850684273074)⟩,⟨(-17833206625621366036477),(-17833206625621365990823)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-9018420289401827408886),(-9018420289401827356097)⟩,⟨(-18887417357407499891316),(-18887417357407499837291)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-10952953130903365947199),(-10952953130903365897895)⟩,⟨(-12472792838048469232868),(-12472792838048469183185)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-8804635172356477859395),(-8804635172356477820847)⟩,⟨(-4959183115186920093108),(-4959183115186920054800)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-4882513624762272731732),(-4882513624762272707758)⟩,⟨(-672372323227438065932),(-672372323227438042298)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-1921002750656270327098),(-1921002750656270315008)⟩,⟨498261966336422836696,498261966336422848611⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-547829694910401035014),(-547829694910401029817)⟩,⟨403577864378049675636,403577864378049680796⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-114149528168225283276),(-114149528168225281072)⟩,⟨171648814675053012638,171648814675053014838⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-16442227538925884789),(-16442227538925883570)⟩,⟨55295067772625174666,55295067772625175887⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-865147305012717782),(-865147305012716719)⟩,⟨15664333023729215390,15664333023729216454⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨479955020533076360,479955020533077373⟩,⟨4343988807776483490,4343988807776484507⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨273545007017544710,273545007017545712⟩,⟨1277048993789946834,1277048993789947841⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨110608606671344835,110608606671345667⟩,⟨414235905672148861,414235905672149689⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨40858152776771639,40858152776772174⟩,⟨142851363505043203,142851363505043735⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨10369523832119333,10369523832119520⟩,⟨35793748706180196,35793748706180385⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-5126798292363224703644116),(-5126798292363210757754386)⟩,⟨(-4506694368056382886522420),(-4506694368056368941292394)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-15037121715727464860534845),(-15037121715727436673837498)⟩,⟨(-10559205336199984844897250),(-10559205336199956660364113)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-22697434719044059182830157),(-22697434719044038826968337)⟩,⟨(-9568717231511942303428319),(-9568717231511921951332707)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-24761620318269819034302728),(-24761620318269808889971603)⟩,⟨(-2234061811342788530242897),(-2234061811342778389074939)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-19722186997004807115160815),(-19722186997004803779252059)⟩,⟨6172354143165227028319375,6172354143165230363177434⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-10578547247508554316782737),(-10578547247508553713888043)⟩,⟨10195683089865955685004181,10195683089865956288574333⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-2596452789542638726561717),(-2596452789542638653537599)⟩,⟨8784605948215214607880650,8784605948215214682069590⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨1315568975458153531037373,1315568975458153549974952⟩,⟨4945761419224136661513678,4945761419224136680816110⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨1902263769927889495304192,1902263769927889504868028⟩,⟨1796153767545764882958189,1796153767545764892441052⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨1221250916147966527163681,1221250916147966532371513⟩,⟨272799946343227143160684,272799946343227148229380⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨551765981033890705382093,551765981033890708098054⟩,⟨(-157673707779460804774846),(-157673707779460802101411)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨194697308864195615217024,194697308864195616550074⟩,⟨(-170525551429242588685702),(-170525551429242587352985)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨54404023092233202316686,54404023092233202947754⟩,⟨(-103899578473736752310654),(-103899578473736751672764)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨10460273619168360604375,10460273619168360897707⟩,⟨(-52569002132311705612097),(-52569002132311705313475)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨39387164343676033725,39387164343676161821⟩,⟨(-23374980958333041026473),(-23374980958333040895716)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-637773150719557492781),(-637773150719557456635)⟩,⟨(-6565270605895124358109),(-6565270605895124321281)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-182409905651266226801015681),(-182409905651263549360229415)⟩,⟨(-171907161677675372650654486),(-171907161677672695209169699)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-560469794471220103670726514),(-560469794471210522720716148)⟩,⟨(-417696140437023174863345115),(-417696140437013593897533024)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-924462516992936747612999190),(-924462516992915568693452729)⟩,⟨(-404376022356325792444279873),(-404376022356304613463195928)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-1143487817763774546045602901),(-1143487817763735955848978094)⟩,⟨(-89848577755248610422479219),(-89848577755210020094995876)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-1062277922238981058469992358),(-1062277922238917350123574080)⟩,⟨384850647642141190612016217,384850647642204899121141722⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-663900669244258636542243639),(-663900669244138481365427708)⟩,⟨750396082111017020771990798,750396082111137176015919003⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-139889195121166230832905206),(-139889195121012836696800587)⟩,⟨802392280253745591123634054,802392280253898985232596432⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨246320820180124682930698182,246320820180242674082206148⟩,⟨562792772744502821659263543,562792772744620812734190545⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨368646769623264568201415297,368646769623353954419685518⟩,⟨230923862270948982026037117,230923862271038368204246513⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨292715987299350994284519754,292715987299404024575766940⟩,⟨(-9109993607479177621419935),(-9109993607426147327126933)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨157706534068270235909470302,157706534068289388883757235⟩,⟨(-105873698525288972201235488),(-105873698525269819207826819)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨54767817935102583766373201,54767817935108726786712973⟩,⟨(-106747159312405044270053759),(-106747159312398901236397061)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨3416250079613089355357616,3416250079615445634741906⟩,⟨(-73817441594144698666979610),(-73817441594142342384294583)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-12281730563718441433710006),(-12281730563717665616631354)⟩,⟨(-41759297516118538674713893),(-41759297516117762858028657)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-11141578920186789493724424),(-11141578920186546078098646)⟩,⟨(-19815832845868975145235586),(-19815832845868731730612888)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-4129718635309365860987843),(-4129718635309309892923683)⟩,⟨(-5704846009945867728916803),(-5704846009945811761281797)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-537224648346631005944719423),(-537224648346631005075825722)⟩,⟨(-326495087479508921077525814),(-326495087479508920222509346)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-1652747966422826926732085888),(-1652747966422826924046825169)⟩,⟨(-735761099649341751980559694),(-735761099649341749360831595)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-2762507275225198873519358252),(-2762507275225198868847162244)⟩,⟨(-479894490105095310336536017),(-479894490105095305829281750)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-3534660396485819910160917361),(-3534660396485819903382004007)⟩,⟨614590241177572506851406111,614590241177572513339351760⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-3459215085534304433006718414),(-3459215085534304423696380540)⟩,⟨2269882656396724868933669772,2269882656396724877976134943⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-2246089641502723210423487601),(-2246089641502723198547212940)⟩,⟨3750741688754713990979180766,3750741688754714002735207586⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-221892064661600274595964547),(-221892064661600260742974256)⟩,⟨4243387999740197980292564623,4243387999740197994173653882⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨1734543860442756068721737844,1734543860442756085008696255⟩,⟨3432244464282368419382458029,3432244464282368435779855046⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨2784537598861440236982402299,2784537598861440268815335500⟩,⟨1759233948069321698822858386,1759233948069321730726499907⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨2704109590426991192081327338,2704109590426991329995010877⟩,⟨72371246957341087107777002,72371246957341225030016427⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨1902116142086729718780821850,1902116142086730261138762010⟩,⟨(-993307841157924431690725221),(-993307841157923889335132799)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨975802815430148420383739895,975802815430149794654270152⟩,⟨(-1320459695082101826699283412),(-1320459695082100452420137991)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨306281512210855284618679506,306281512210858384776897492⟩,⟨(-1155667560875517515135259175),(-1155667560875514414962245796)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-24604013707812042569507076),(-24604013707806999666110282)⟩,⟨(-802892980608940060292299397),(-802892980608935017378551269)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-103308256301189429486137047),(-103308256301184557746184599)⟩,⟨(-447151153563009773146270690),(-447151153563004901401732114)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-47714288612610917816436316),(-47714288612608908897585489)⟩,⟨(-140922100791270589341910325),(-140922100791268580421901244)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-1309793516639859794002045466),(-1309793516639740515099831101)⟩,⟨1838220459005347426429996982,1838220459005466705274639426⟩⟩
lemma checked : cachedMomentRuleBox density0 hk7_1_9 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 7 9) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk7_1_9 (tableDensity false) (fullFactor true 7 9) density0_contains hk7_1_9_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-1332638559565443798737812936),(-1332638559565443795881065620)⟩,⟨2274421587757913250946719311,2274421587757913253778240317⟩⟩
lemma atomChecked : tableAtomBox false ha7_1_9 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 7 9) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha7_1_9 7 9 ha7_1_9_contains
 def realAnswer : RBox := ⟨(-2642432076205303592839858402),(-2642432076205184310880896721)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 7 9) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm7_0_1_9
namespace hm7_1_1_9
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk7_1_9 j i k))
noncomputable def s0_0 : CBox := ⟨⟨54964869,54965013⟩,⟨168175301,168175442⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨22104995,22105411⟩,⟨381987112,381987525⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-150896107),(-150895421)⟩,⟨299223760,299224447⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-176432258),(-176431311)⟩,⟨54764643,54765588⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-52099568),(-52098467)⟩,⟨(-52068226),(-52067119)⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨13058429,13059580⟩,⟨(-19918139),(-19916985)⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨5638629,5640251⟩,⟨4250967,4252586⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-1777912),(-1776078)⟩,⟨1235466,1237300⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-66180),(-64427)⟩,⟨(-752026),(-750280)⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨268949,270575⟩,⟨163899,165530⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-150406),(-148584)⟩,⟨62531,64384⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨5546,7296⟩,⟨(-100148),(-98397)⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨65557,66931⟩,⟨16039,17416⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-3045),(-2127)⟩,⟨47422,48342⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-25113),(-24617)⟩,⟨15869,16349⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-10213),(-10046)⟩,⟨942,1104⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-390041168324270),(-390041168324223)⟩,⟨5004989984141134,5004989984141179⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-754504683019406),(-754504683019300)⟩,⟨10935290119153221,10935290119153326⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-568566560083595),(-568566560083436)⟩,⟨9726090892825217,9726090892825377⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-332508171516032),(-332508171515832)⟩,⟨5408356374892379,5408356374892578⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-216099778682091),(-216099778681863)⟩,⟨2105733501758608,2105733501758840⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-132797463506757),(-132797463506516)⟩,⟨608495268738002,608495268738246⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-61775946304526),(-61775946304264)⟩,⟨132532076380976,132532076381239⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-20700341085254),(-20700341084873)⟩,⟨20344508116961,20344508117343⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-5018502352204),(-5018502351672)⟩,⟨1395228574468,1395228574998⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-849635518590),(-849635517977)⟩,⟨(-333650033656),(-333650033042)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-71915486408),(-71915485801)⟩,⟨(-152843335435),(-152843334833)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨13015413772,13015414333⟩,⟨(-32796494431),(-32796493873)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨8041706798,8041707373⟩,⟨(-3281227574),(-3281227000)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨2411305236,2411305751⟩,⟨798166969,798167480⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨551031261,551031625⟩,⟨620648414,620648778⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨87880433,87880579⟩,⟨183511661,183511809⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨654085581706704239824,654085581706704245557⟩,⟨(-1546619856852347689944),(-1546619856852347684179)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨1247452786142127239877,1247452786142127254390⟩,⟨(-3970988610206584234999),(-3970988610206584220413)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨570681379659762361982,570681379659762379006⟩,⟨(-4687145294667974861576),(-4687145294667974844491)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-505128032611231586465),(-505128032611231571395)⟩,⟨(-3658495373133165138544),(-3658495373133165123456)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-964396400279443828387),(-964396400279443817545)⟩,⟨(-1950034585930490816087),(-1950034585930490805250)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-747799805063499319685),(-747799805063499313612)⟩,⟨(-677668811172150875533),(-677668811172150869472)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-364735627058625406245),(-364735627058625403493)⟩,⟨(-122545702852365500435),(-122545702852365497692)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-125698535088677059989),(-125698535088677058872)⟩,⟨12236009982370297329,12236009982370298444⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-32919077056021495829),(-32919077056021495308)⟩,⟨17621692363407726927,17621692363407727448⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-7026684783993919023),(-7026684783993918606)⟩,⟨7617524831341652288,7617524831341652704⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-1325113277777433117),(-1325113277777432634)⟩,⟨2474855818708034673,2474855818708035156⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-243205408106549317),(-243205408106548798)⟩,⟨732859252144501789,732859252144502308⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-48139726264720692),(-48139726264720220)⟩,⟨219449125708890653,219449125708891126⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-11060866934604553),(-11060866934604193)⟩,⟨70442465599846951,70442465599847313⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-2933458716995963),(-2933458716995741)⟩,⟨23832329930848865,23832329930849085⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-635601649259283),(-635601649259203)⟩,⟨5895806383831389,5895806383831470⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-473356681499766291693026),(-473356681499754578193193)⟩,⟨(-2232206691237125967386340),(-2232206691237114253818091)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-1875617168876830177112650),(-1875617168876806520624921)⟩,⟨(-5754031986249038345371113),(-5754031986249014688658704)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-3959967904602068252877120),(-3959967904602051198286418)⟩,⟨(-6821273773978777954001306),(-6821273773978760899021313)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-5701916861847927038786063),(-5701916861847918564639361)⟩,⟨(-5130643832177709010272592),(-5130643832177700535801601)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-5813860870699300737644682),(-5813860870699297965353870)⟩,⟨(-1977624721981883275868384),(-1977624721981880503474456)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-4192697501343231460471152),(-4192697501343230969435275)⟩,⟨641233493524349945227282,641233493524350436192585⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-2016977776396212832559771),(-2016977776396212780433718)⟩,⟨1632337167408823307791639,1632337167408823359801417⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-473893821951509154014811),(-473893821951509144792637)⟩,⟨1347595424158509051087215,1347595424158509060274979⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨154843442744795157695605,154843442744795161271044⟩,⟨702383444461458757127027,702383444461458760711416⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨232510714299749746257174,232510714299749748072505⟩,⟨246335184529808314099488,246335184529808315928471⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨146236734019010639006223,146236734019010639955968⟩,⟨46707183265536835594756,46707183265536836548444⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨68242860593960634995692,68242860593960635468858⟩,⟨(-9731475642544762789011),(-9731475642544762315894)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨27197539541645745353608,27197539541645745581353⟩,⟨(-15559440239857137545123),(-15559440239857137318040)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨9933294691077660188214,9933294691077660295870⟩,⟨(-10459614834916465983437),(-10459614834916465876271)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨3379388644869337143783,3379388644869337191442⟩,⟨(-5361544980402487854694),(-5361544980402487807274)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨802743626213088918294,802743626213088931836⟩,⟨(-1607207559469991799970),(-1607207559469991786487)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-62745839253700600417695506),(-62745839253698400134049751)⟩,⟨(-53338226775275589829680959),(-53338226775273389545062401)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-193725020877813626734412490),(-193725020877805752561519712)⟩,⟨(-131927538925410550502560970),(-131927538925402676329982575)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-323235529928350745467740127),(-323235529928333336856077045)⟩,⟨(-133451489601894949473264211),(-133451489601877540871063512)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-408600458479459731851038909),(-408600458479428006206482356)⟩,⟨(-38668273351676237732561457),(-38668273351644512113424378)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-395104920281896093135292154),(-395104920281843710436557693)⟩,⟨116985027389146713474237347,116985027389199096138270100⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-269478113894903678155761081),(-269478113894804882714530275)⟩,⟨250488639762927825320990722,250488639763026620744836882⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-88274699638761448653195345),(-88274699638635348572679110)⟩,⟨287804287857763000493852226,287804287857889100577498365⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨59872070196138107197538628,59872070196235058283512542⟩,⟨222751295047650306702858350,222751295047747257804485609⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨123097364531626491676775415,123097364531699878502510159⟩,⟨113278243877238714874710122,113278243877312101709031384⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨112860425816746704576096711,112860425816790197715028249⟩,⟨23296888149827307958130198,23296888149870801096722583⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨72299824536536206567052312,72299824536551895434351780⟩,⟨(-21692537918720996168154042),(-21692537918705307304403365)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨35159315375120982819071677,35159315375126007624191186⟩,⟨(-31322991041314991715096245),(-31322991041309966912443450)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨12779482646340688469920846,12779482646342613373550335⟩,⟨(-24962063368184380756016508),(-24962063368182455853001162)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨2793980890838386617720214,2793980890839019704627635⟩,⟨(-15588028387027477849494018),(-15588028387026844762525996)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-256708030104549068287311),(-256708030104350595719721)⟩,⟨(-7978996252934817394610522),(-7978996252934618921872350)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-341979044934420886784078),(-341979044934375272204537)⟩,⟨(-2401697743201018191262218),(-2401697743200972576610500)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-16415614580157257930770938),(-16415614580157257727872642)⟩,⟨(-8938053042090171402140974),(-8938053042090171214647891)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-51978062079190146445789777),(-51978062079190145834089321)⟩,⟨(-8859550237437718483743792),(-8859550237437717932427369)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-69588850329283547762384643),(-69588850329283546775912987)⟩,⟨48358937273046383706155052,48358937273046384557357156⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨3526711205076448023333458,3526711205076449328683429⟩,⟨189685974099501105850806635,189685974099501106924585410⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨251857742613286049048631209,251857742613286051178766704⟩,⟨378583210353649020850939070,378583210353649022765445451⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨677943514686036288005756734,677943514686036291483625234⟩,⟨483392767957054797523615760,483392767957054800910136748⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨1141554819059534287318073445,1141554819059534292379153446⟩,⟨349553624741657562350618694,349553624741657567461646479⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨1416594849841328881609571989,1416594849841328889133972988⟩,⟨(-49449246442254148771167132),(-49449246442254141097784526)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨1348270429378947276977601140,1348270429378947298078772582⟩,⟨(-548856038070819717373821309),(-548856038070819696155856136)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨974140026806935002195952058,974140026806935111061952428⟩,⟨(-910628723578784815050854095),(-910628723578784706164371684)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨486391821451223621568759848,486391821451224061499989827⟩,⟨(-1002250156853409028857668855),(-1002250156853408588952370077)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨82635530299240049314381974,82635530299241169234066428⟩,⟨(-860093114686607967310751313),(-860093114686606847427116588)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-143655367292757681040416996),(-143655367292755150039993331)⟩,⟨(-612411739271411813555603761),(-612411739271409282573876193)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-204072278677338704841064834),(-204072278677334584147210046)⟩,⟨(-372083531310169548636185312),(-372083531310165427946259035)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-156731622952198676914932351),(-156731622952194694130092771)⟩,⟨(-188296533375683885820443596),(-188296533375679903035254413)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-57091437632784328294551910),(-57091437632782685559384436)⟩,⟨(-56197542359716857299079732),(-56197542359715214563417537)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨722769331229046504626381031,722769331229144485675875989⟩,⟨(-438762609489637885652625893),(-438762609489539904696773332)⟩⟩
lemma checked : cachedMomentRuleBox density1 hk7_1_9 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 7 9) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk7_1_9 (tableDensity true) (fullFactor true 7 9) density1_contains hk7_1_9_contains
noncomputable def atomAnswer : CBox := ⟨⟨1742681193277888040767547350,1742681193277888044503293840⟩,⟨(-2974243614760348101094621953),(-2974243614760348097391863715)⟩⟩
lemma atomChecked : tableAtomBox true ha7_1_9 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 7 9) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha7_1_9 7 9 ha7_1_9_contains
 def realAnswer : RBox := ⟨2465450524506934545293928381,2465450524507032530279169829⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 7 9) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm7_1_1_9
namespace hm7_0_1_10
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk7_1_10 j i k))
noncomputable def s0_0 : CBox := ⟨⟨1256609,1257160⟩,⟨(-882198449),(-882197896)⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨461424648,461426395⟩,⟨(-1849241689),(-1849239942)⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨1130751344,1130754489⟩,⟨(-1237589931),(-1237586786)⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨939518142,939522960⟩,⟨(-61214929),(-61210118)⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨214098798,214105296⟩,⟨325556911,325563421⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-92160142),(-92153464)⟩,⟨94459575,94466288⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-26689669),(-26681885)⟩,⟨(-30455637),(-30447929)⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨11571120,11581325⟩,⟨(-4645542),(-4635338)⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-639292),(-628615)⟩,⟨4190242,4200913⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-1230961),(-1221830)⟩,⟨(-1201374),(-1192225)⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨827523,836831⟩,⟨(-179269),(-169793)⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-116826),(-107590)⟩,⟨492476,501735⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-327252),(-319869)⟩,⟨(-130558),(-123163)⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨37103,42103⟩,⟨(-243562),(-238565)⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨133501,136184⟩,⟨(-70090),(-67492)⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨51658,52523⟩,⟨(-322),514⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨8695711062219641,8695711062219744⟩,⟨(-21241797312338059),(-21241797312337956)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨19171924404646449,19171924404646723⟩,⟨(-47187336363362223),(-47187336363361946)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨17702849671378782,17702849671379201⟩,⟨(-43123393810634421),(-43123393810634001)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨10868943873627005,10868943873627642⟩,⟨(-24575079105718488),(-24575079105717854)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨5104769527054031,5104769527054997⟩,⟨(-9570765032948194),(-9570765032947228)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨1940393555077574,1940393555078919⟩,⟨(-2619070163662557),(-2619070163661209)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨597854664800102,597854664801811⟩,⟨(-487003990570455),(-487003990568744)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨145522048970689,145522048972652⟩,⟨(-46390457725182),(-46390457723217)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨26601270151721,26601270153844⟩,⟨5502232873732,5502232875853⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨3096497697071,3096497699947⟩,⟨3511565672523,3511565675398⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-20244740449),(-20244737131)⟩,⟨844493731108,844493734430⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-125063319480),(-125063316099)⟩,⟨116653135027,116653138400⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-40837085207),(-40837082518)⟩,⟨(-970002875),(-970000190)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-8956148770),(-8956146930)⟩,⟨(-7496346348),(-7496344520)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-1384275186),(-1384273929)⟩,⟨(-3501845933),(-3501844672)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-102723052),(-102722564)⟩,⟨(-911942210),(-911941716)⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-3438697198443539557735),(-3438697198443539545613)⟩,⟨2660230581997257360104,2660230581997257372140⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-7809192653966949864525),(-7809192653966949833071)⟩,⟨7460636165229334287404,7460636165229334318797⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-7042890077095857336659),(-7042890077095857296408)⟩,⟨10159802312603162221720,10159802312603162262247⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-3106859525227423871397),(-3106859525227423833890)⟩,⟨9404275935760563001808,9404275935760563039905⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨205361179812842230113,205361179812842257269⟩,⟨6105101379389423370690,6105101379389423398424⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨1256901084998107180181,1256901084998107196067⟩,⟨2752569996089937197366,2752569996089937213466⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨923550639066961597056,923550639066961604489⟩,⟨827386782614116726346,827386782614116733805⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨410406713803795820667,410406713803795823521⟩,⟨138767249547123243732,138767249547123246576⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨133682237233664868887,133682237233664870044⟩,⟨(-6371356471041012647),(-6371356471041011488)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨35594098757153036691,35594098757153037464⟩,⟨(-13829884773051510084),(-13829884773051509313)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨8553449763111664010,8553449763111664818⟩,⟨(-6224146786935978475),(-6224146786935977669)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨2050385907485973090,2050385907485973912⟩,⟨(-2185480110777345483),(-2185480110777344661)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨536886242263879976,536886242263880768⟩,⟨(-732821769568000400),(-732821769567999608)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨161740216872302818,161740216872303446⟩,⟨(-254586013156506984),(-254586013156506351)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨53867163763989990,53867163763990381⟩,⟨(-90526086319521086),(-90526086319520692)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨13349812529062550,13349812529062685⟩,⟨(-22921523161879422),(-22921523161879285)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-1303837931827809594955322),(-1303837931827804082839677)⟩,⟨3055002028934621382692581,3055002028934626895343665⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-2576186900876912972946555),(-2576186900876901246472548)⟩,⟨8591466109682959098281980,8591466109682970826191444⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-868764959350607359112553),(-868764959350596249805708)⟩,⟨12068109079353178797457746,12068109079353189908231026⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨3004256196030149655050157,3004256196030155512041240⟩,⟨11952650812613904957009903,11952650812613910814706174⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨6283657877243637026997678,6283657877243638739676906⟩,⟨8243317730158623531209180,8243317730158625243598223⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨6755812737585911803203721,6755812737585912075040628⟩,⟨3194726580782916312564897,3194726580782916583520002⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨4714274880936249722506647,4714274880936249763503579⟩,⟨(-428910196872955971145112),(-428910196872955930606838)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨2132757922635458295308871,2132757922635458306245472⟩,⟨(-1639977892106363227286216),(-1639977892106363216326538)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨470781989619031487040940,470781989619031492083842⟩,⟨(-1318559628466876654542693),(-1318559628466876649350205)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-143717748737394676209414),(-143717748737394673528362)⟩,⟨(-666381591464970077193112),(-666381591464970074453586)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-211691620395827620309148),(-211691620395827618970552)⟩,⟨(-237324443436599407990437),(-237324443436599406652775)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-135038131430043265717377),(-135038131430043265101162)⟩,⟨(-54710320725772719115094),(-54710320725772718510245)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-66924648247913914220905),(-66924648247913913904898)⟩,⟨(-93395842486515468821),(-93395842486515160279)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-29572000688151837804099),(-29572000688151837634273)⟩,⟨9022754100547634958741,9022754100547635126217⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-11928631168182811065477),(-11928631168182810983847)⟩,⟨6500994297749081488633,6500994297749081569639⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-3172509524193004165464),(-3172509524193004141426)⟩,⟨2178344211759793011453,2178344211759793035376⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-57367368953587518307596740),(-57367368953586418911068674)⟩,⟨86724098317481935351022667,86724098317483034743215503⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-130800295353012108602091237),(-130800295353008230320336870)⟩,⟨259691129530598118231086820,259691129530601996495005242⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-97642119768757876199034566),(-97642119768749567887207834)⟩,⟨410566966238364969563582201,410566966238373277833503805⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨51993386029265654656267619,51993386029280155727271060⟩,⟨480738261717729593197073571,480738261717744094197035918⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨248681349466507137636963664,248681349466537359032850148⟩,⟨411951937338650163464532041,411951937338680384805648593⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨375366858291694691431052050,375366858291748762660139460⟩,⟨213728205768883292026948407,213728205768937363246718128⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨355626618297069907293990868,355626618297133269954348299⟩,⟨(-16629833263094525277593736),(-16629833263031162588942816)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨217713054341382722838953585,217713054341433569629387859⟩,⟨(-163977337457187181639593432),(-163977337457136334812789290)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨60251025763611680649587416,60251025763655542433353525⟩,⟨(-186517402605522454516217890),(-186517402605478592724111067)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-38641714128942504028639825),(-38641714128919288853488137)⟩,⟨(-128330411879799635489053168),(-128330411879776420322388988)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-67225071436608485863040463),(-67225071436600466111355975)⟩,⟨(-57147959845646663902486862),(-57147959845638644161891106)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-55518374222888328836897477),(-55518374222884959899138415)⟩,⟨(-10475626573207805956914715),(-10475626573204437022693589)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-34098982513552160215905919),(-34098982513551001506485796)⟩,⟨8784728081213763854285113,8784728081214922564044362⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-17362085299975228432191688),(-17362085299974877878163187)⟩,⟨11702418267334181903586835,11702418267334532458929209⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-7466725152186517190176821),(-7466725152186414535437246)⟩,⟨8087156311419516646288838,8087156311419619302071421⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-2010328725698468316466476),(-2010328725698445688142369)⟩,⟨2768519351410598060503171,2768519351410620689200899⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-107769977430300469608084444),(-107769977430300469296627100)⟩,⟨200300497674198360480052534,200300497674198360798520832⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-233730447762642817878989265),(-233730447762642816923384744)⟩,⟨613052683661687521270579862,613052683661687522255737885⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-115452880992473892850301544),(-115452880992473891201746217)⟩,⟨1015060088193249073307533562,1015060088193249075024647601⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨308976536385965941189335720,308976536385965943586061576⟩,⟨1279383120098793816638411495,1279383120098793819147260558⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨930710253761760220906412140,930710253761760224320766282⟩,⟨1215986278419070790021590152,1215986278419070793524901653⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨1466740269452217256151299260,1466740269452217260589596480⟩,⟨722668724228554040507493559,722668724228554044978316541⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨1606871947236741598550755596,1606871947236741603778229737⟩,⟨(-64121970896542885874841766),(-64121970896542880669817906)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨1240115748950081994512192733,1240115748950082000651872182⟩,⟨(-797013304959960785459605133),(-797013304959960779369061561)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨554932968039748970759735358,554932968039748983536160370⟩,⟨(-1152864316448045681586533815),(-1152864316448045668832775361)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-105885064202345851827887999),(-105885064202345797426635600)⟩,⟨(-1059598048417656807318452695),(-1059598048417656752917955709)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-496160278491296341493978171),(-496160278491296136661543644)⟩,⟨(-697034032137013306603399763),(-697034032137013101770211647)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-584712277541696026556615490),(-584712277541695478950050468)⟩,⟨(-311152020511776478637383284),(-311152020511775931035640320)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-484603770974055453485618183),(-484603770974054075412185370)⟩,⟨(-50116172079312366801839991),(-50116172079310988734935364)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-323807112242977975871873245),(-323807112242975814545682872)⟩,⟨63456083458531457752210611,63456083458533619074533755⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-174996891016577131701471578),(-174996891016575092719262372)⟩,⟨72897799388006615025906284,72897799388008654006790527⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-54189829429175099553555759),(-54189829429174269124235282)⟩,⟨29363171980820548945823412,29363171980821379374900842⟩⟩
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
noncomputable def ans : CBox := ⟨⟨707755117698256073016090624,707755117698308352773363706⟩,⟨409124987804381805382004398,409124987804434085153305101⟩⟩
lemma checked : cachedMomentRuleBox density0 hk7_1_10 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 7 10) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk7_1_10 (tableDensity false) (fullFactor true 7 10) density0_contains hk7_1_10_contains
noncomputable def atomAnswer : CBox := ⟨⟨874838616778330148773440074,874838616778330150005618177⟩,⟨421640386806199550051417057,421640386806199551291116842⟩⟩
lemma atomChecked : tableAtomBox false ha7_1_10 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 7 10) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha7_1_10 7 10 ha7_1_10_contains
 def realAnswer : RBox := ⟨1582593734476586221689530698,1582593734476638502878981883⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 7 10) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm7_0_1_10
namespace hm7_1_1_10
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk7_1_10 j i k))
noncomputable def s0_0 : CBox := ⟨⟨20117170,20117279⟩,⟨(-149508294),(-149508185)⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨122730194,122730514⟩,⟨(-303306874),(-303306555)⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨224826782,224827347⟩,⟨(-180310752),(-180310188)⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨159259959,159260809⟩,⟨16833196,16834046⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨25550396,25551514⟩,⟨59199831,59200950⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-16827124),(-16826014)⟩,⟨12690654,12691770⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-3670760),(-3669512)⟩,⟨(-5145618),(-5144380)⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨1841187,1842804⟩,⟨(-664148),(-662532)⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-90283),(-88570)⟩,⟨681457,683165⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-219163),(-217658)⟩,⟨(-192212),(-190708)⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨143495,145073⟩,⟨(-41271),(-39660)⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-14830),(-13229)⟩,⟨90058,91661⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-60910),(-59628)⟩,⟨(-19451),(-18164)⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨3245,4108⟩,⟨(-44547),(-43683)⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨22866,23328⟩,⟨(-14819),(-14372)⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨9259,9416⟩,⟨(-997),(-847)⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨2769044587380104,2769044587380143⟩,⟨(-2269364228736092),(-2269364228736055)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨5995602840037805,5995602840037883⟩,⟨(-5059464496265900),(-5059464496265822)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨5268572516206273,5268572516206385⟩,⟨(-4642396284910982),(-4642396284910873)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨2926002629160569,2926002629160707⟩,⟨(-2647034420210262),(-2647034420210123)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨1178724274466083,1178724274466254⟩,⟨(-1024502847010387),(-1024502847010218)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨377532050672442,377532050672648⟩,⟨(-274311683347948),(-274311683347740)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨101018797605897,101018797606153⟩,⟨(-47102914254325),(-47102914254070)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨22390746252582,22390746252877⟩,⟨(-2489375017657),(-2489375017358)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨3852821009043,3852821009376⟩,⟨1452340446172,1452340446505⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨414678560265,414678560728⟩,⟨605963896004,605963896468⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-16817240622),(-16817240064)⟩,⟨137034856555,137034857112⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-23035871097),(-23035870502)⟩,⟨18006600216,18006600810⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-7230120271),(-7230119774)⟩,⟨(-825293897),(-825293402)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-1498346022),(-1498345669)⟩,⟨(-1535744764),(-1535744412)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-184015269),(-184015020)⟩,⟨(-680388664),(-680388412)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨1208696,1208803⟩,⟨(-173238867),(-173238762)⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-975939271265230521655),(-975939271265230517768)⟩,⟨104673449827495113128,104673449827495117011⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-2389534391806956653848),(-2389534391806956643668)⟩,⟨500996746665345106597,500996746665345116775⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-2570919106962885063376),(-2570919106962885050601)⟩,⟨1080893362909530150366,1080893362909530163155⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-1729591902460601745017),(-1729591902460601733687)⟩,⟨1365399557195937742446,1365399557195937753806⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-704090662127769170646),(-704090662127769163051)⟩,⟨1110641579246296702321,1110641579246296709939⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-105496946317665844828),(-105496946317665840770)⟩,⟨610489905918523792291,610489905918523796359⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨62329100891998811723,62329100891998813459⟩,⟨232152993446760810202,232152993446760811941⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨52214905078910665294,52214905078910665927⟩,⟨61136153830749016831,61136153830749017465⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨21880865722627179002,21880865722627179286⟩,⟨10429405238251314612,10429405238251314895⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨6834657972319905164,6834657972319905410⟩,⟨585262868882910483,585262868882910730⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨1857843683307228485,1857843683307228822⟩,⟨(-362401120591937888),(-362401120591937555)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨490332107035670780,490332107035671176⟩,⟨(-199712920832742491),(-199712920832742096)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨136267604009906606,136267604009906987⟩,⟨(-76492428953225720),(-76492428953225340)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨41732896809784150,41732896809784443⟩,⟨(-27828734538725898),(-27828734538725604)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨13725970534626505,13725970534626681⟩,⟨(-10070314295414174),(-10070314295413995)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨3349904976012253,3349904976012323⟩,⟨(-2568000488471694),(-2568000488471626)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-959882582892975738659264),(-959882582892971108629582)⟩,⟨558157212699826922507198,558157212699831552481165⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-2376683653850983212545753),(-2376683653850973370119070)⟩,⟨1754735734032978512310334,1754735734032988354587489⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-2548007298942943030370459),(-2548007298942933720723361)⟩,⟨2918459347361038755687399,2918459347361048065182124⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-1468404640496463092056747),(-1468404640496458197687727)⟩,⟨3507142380492886283484109,3507142380492891177780504⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨61905919778395844193261,61905919778397266599694⟩,⟨3079347130862862387867574,3079347130862863810304370⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨1060399310102522416869549,1060399310102522636104816⟩,⟨1878694638446270473802943,1878694638446270693127155⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨1168698266387531223813636,1168698266387531252223080⟩,⟨657263431179368456507484,657263431179368484962327⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨749702468316140567002528,749702468316140572271766⟩,⟨(-43054765265002928190450),(-43054765265002922924041)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨310838499836043450018856,310838499836043451925718⟩,⟨(-226989531558216446529810),(-226989531558216444637524)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨68804181372293540390757,68804181372293541358533⟩,⟨(-171222940784627136849903),(-171222940784627135887499)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-11945142111244019508701),(-11945142111244019033984)⟩,⟨(-84230387811139236438918),(-84230387811139235963959)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-22173197615016959102752),(-22173197615016958886237)⟩,⟨(-31846489101222690908068),(-31846489101222690690454)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-15051601109777112057688),(-15051601109777111946145)⟩,⟨(-9651178538995385882306),(-9651178538995385770080)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-8025763597690219508273),(-8025763597690219447100)⟩,⟨(-2195552780760378594097),(-2195552780760378532721)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-3676342474460513851144),(-3676342474460513821262)⟩,⟨(-227208410358955805833),(-227208410358955775901)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-1047231988709060552118),(-1047231988709060543233)⟩,⟨43630548609702919113,43630548609702928003⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-17364623270007863023287288),(-17364623270006959564181456)⟩,⟨29421731561808100508734579,29421731561809003968221891⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-40110915688607232945564948),(-40110915688604045596498649)⟩,⟨88867225577118983551261565,88867225577122170902748716⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-30874525632908519823052612),(-30874525632901690673344206)⟩,⟨142968022336912593445490969,142968022336919422602494371⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨15858064643727702481040736,15858064643739623890708032⟩,⟨172302347156874824806911352,172302347156886746230564702⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨81566161803906360347604724,81566161803931209128890101⟩,⟨155396288210574227807608564,155396288210599076600860822⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨129537738767260754267983046,129537738767305213343434456⟩,⟨91546837888124881801092457,91546837888169340879844968⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨131185570677329348371474754,131185570677381436757254465⟩,⟨10291918017147949885221452,10291918017200038265831821⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨90029504871480764403496464,90029504871522543229174818⟩,⟨(-48663638652866626569148262),(-48663638652824847751093867)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨35925494708596499869566109,35925494708632511140413527⟩,⟨(-66273262841533190689393276),(-66273262841497179420395516)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-3044133933188733761207144),(-3044133933169693467153636)⟩,⟨(-52654808945879604107866851),(-52654808945860563812182232)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-18817005227605232415324234),(-18817005227598663392636321)⟩,⟨(-29589383325458538902800476),(-29589383325451969877992294)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-18839825604002082249122803),(-18839825603999326505509282)⟩,⟨(-11696053723872354217813909),(-11696053723869598473511962)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-13159160325268196710058777),(-13159160325267250116454118)⟩,⟨(-2324659885612856627949559),(-2324659885611910034390624)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-7553621935150079817521940),(-7553621935149793751733081)⟩,⟨984755649210194228828766,984755649210480294390165⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-3637209869520594176047648),(-3637209869520510473603566)⟩,⟨1307972094328918412184049,1307972094329002114448061⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-1057284984374600016465765),(-1057284984374581573972234)⟩,⟨520668527702185694665083,520668527702204137095117⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-2917775506935871187510831),(-2917775506935871121040547)⟩,⟨6100716151288726617637514,6100716151288726690964574⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-2177746803043823744417572),(-2177746803043823549390117)⟩,⟨18996102337350385460863027,18996102337350385681596005⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨19085497371347886994192108,19085497371347887293501413⟩,⟨24263492301087670105069998,24263492301087670459454455⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨69373882442058618652754828,69373882442058619037766574⟩,⟨(-5848372923969718893882513),(-5848372923969718420230295)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨133013295295722745532898102,133013295295722746270320329⟩,⟨(-103243306805675991485509566),(-103243306805675990676983338)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨159502085827049243415301000,159502085827049244702249952⟩,⟨(-267664792893556681524383726),(-267664792893556680214113274)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨91986412983317924666325190,91986412983317926588002022⟩,⟨(-442605819361397518785631236),(-442605819361397516893738901)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-74877469029510000927888666),(-74877469029509998074718192)⟩,⟨(-538406511721173509693251537),(-538406511721173506903876768)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-271882952176515913581847761),(-271882952176515904971039611)⟩,⟨(-496049442733690384831301404),(-496049442733690376256735215)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-404007730962944816141707510),(-404007730962944773117570167)⟩,⟨(-335364381347002357165658132),(-335364381347002314142269525)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-422448635216918561079584782),(-422448635216918394922296281)⟩,⟨(-137449089315317870976505551),(-137449089315317704804850439)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-348122240578916941743196327),(-348122240578916495425030445)⟩,⟨17957230073594191825135625,17957230073594638157664215⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-237435337417518157484403354),(-237435337417517032279043519)⟩,⟨96602358297794697028473132,96602358297795822237628046⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-137228385237543858332758554),(-137228385237542092223528833)⟩,⟨107505516586717951151133658,107505516586719717259705283⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-65886913182973710272421975),(-65886913182972043356549635)⟩,⟨76814133572264115022741418,76814133572265781937377449⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-18940795573517384879573282),(-18940795573516705827304002)⟩,⟨27250305148390378619037676,27250305148391057670787274⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-197887242887552943682478747),(-197887242887509999171630469)⟩,⟨(-242491066805660589793225256),(-242491066805617645249278920)⟩⟩
lemma checked : cachedMomentRuleBox density1 hk7_1_10 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 7 10) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk7_1_10 (tableDensity true) (fullFactor true 7 10) density1_contains hk7_1_10_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-1144019729633200965391962232),(-1144019729633200963780652404)⟩,⟨(-551375890438876336303768177),(-551375890438876334682622305)⟩⟩
lemma atomChecked : tableAtomBox true ha7_1_10 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 7 10) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha7_1_10 7 10 ha7_1_10_contains
 def realAnswer : RBox := ⟨(-1341906972520753909174440979),(-1341906972520710962852282873)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 7 10) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm7_1_1_10
namespace hm7_0_1_11
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk7_1_11 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-298087763),(-298087330)⟩,⟨615415012,615415446⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-939483082),(-939481848)⟩,⟨1145689274,1145690513⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-1205679011),(-1205677066)⟩,⟨513663056,513665009⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-699202855),(-699199522)⟩,⟨(-248218958),(-248215630)⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-62710609),(-62705444)⟩,⟨(-303684316),(-303679149)⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨95432982,95439118⟩,⟨(-46532914),(-46526772)⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨13262141,13268441⟩,⟨30149823,30156031⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-10185687),(-10178053)⟩,⟨1212874,1220508⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨1259190,1268221⟩,⟨(-3290284),(-3281230)⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨834370,842613⟩,⟨1155831,1164087⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-714493),(-707307)⟩,⟨52349,59711⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨127037,134654⟩,⟨(-411444),(-403796)⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨262386,268635⟩,⟨118260,124524⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-41235),(-36983)⟩,⟨199133,203384⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-114828),(-112561)⟩,⟨55292,57495⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-44007),(-43280)⟩,⟨(-531),175⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-13842603859225210),(-13842603859225130)⟩,⟨5461067513660957,5461067513661035⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-30727879529523336),(-30727879529523120)⟩,⟨12412308745453418,12412308745453630⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-28238082129596344),(-28238082129595992)⟩,⟨11646398284068262,11646398284068620⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-16517987184206335),(-16517987184205820)⟩,⟨6605217101239860,6605217101240376⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-6888512048181519),(-6888512048180856)⟩,⟨2342597646477791,2342597646478455⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-2173732998522568),(-2173732998521826)⟩,⟨453263186150665,453263186151407⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-534323022611730),(-534323022610704)⟩,⟨(-7890403061099),(-7890403060069)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-100967624786375),(-100967624784843)⟩,⟨(-37709101167545),(-37709101166017)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-13092219136533),(-13092219134591)⟩,⟨(-14478979044242),(-14478979042296)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-430752336754),(-430752334823)⟩,⟨(-3396378702525),(-3396378700598)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨347049981225,347049983237⟩,⟨(-522939441372),(-522939439356)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨125686671616,125686674136⟩,⟨(-28243861266),(-28243858741)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨26923810704,26923813056⟩,⟨15588584517,15588586868⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨3457979323,3457981140⟩,⟨8275028442,8275030256⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-248154674),(-248153532)⟩,⟨2896416526,2896417672⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-237841220),(-237840814)⟩,⟨669343821,669344228⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨2122932234373286238602,2122932234373286245748⟩,⟨911114662650002895331,911114662650002902335⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨5506716668775007038180,5506716668775007056458⟩,⟨1686324675283235532378,1686324675283235550228⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨6612764310550078663350,6612764310550078686086⟩,⟨576574986762661658253,576574986762661680338⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨5251868685239730446503,5251868685239730466943⟩,⟨(-1130699783850897544551),(-1130699783850897524610)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨2807447013641422501976,2807447013641422516014⟩,⟨(-1840348332125826312678),(-1840348332125826298803)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨921583649255321956946,921583649255321964364⟩,⟨(-1415306456004095058463),(-1415306456004095051035)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨101056971164388469867,101056971164388473708⟩,⟨(-697004602518335555305),(-697004602518335551420)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-70222535760226422484),(-70222535760226420620)⟩,⟨(-240723397147767138146),(-240723397147767136258)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-49802111381905927844),(-49802111381905926951)⟩,⟨(-61311395307341047567),(-61311395307341046670)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-19703237299197206067),(-19703237299197205530)⟩,⟨(-11824428220520178617),(-11824428220520178075)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-6270573557124611564),(-6270573557124611065)⟩,⟨(-1650911977657589007),(-1650911977657588508)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-1865982072740346878),(-1865982072740346420)⟩,⟨(-86317693214817138),(-86317693214816679)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-571844883594068165),(-571844883594067713)⟩,⟨54627138493986101,54627138493986550⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-189848058400227902),(-189848058400227516)⟩,⟨34141252657356986,34141252657357369⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-66278047593917483),(-66278047593917227)⟩,⟨14729627598748457,14729627598748713⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-16696674225815008),(-16696674225814914)⟩,⟨3980607072284596,3980607072284692⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨1463998251530683399043422,1463998251530686245661811⟩,⟨125699568805400089762843,125699568805402936204260⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨3978642436390292661271766,3978642436390299062017992⟩,⟨(-117662647349937344333193),(-117662647349930943974671)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨5227905014974317404664204,5227905014974323061075720⟩,⟨(-1364173259053375993125826),(-1364173259053370336983026)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨4638072841341876577198857,4638072841341879297251010⟩,⟨(-3055246093964110775393514),(-3055246093964108055225636)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨2556213220635078886404149,2556213220635079592625514⟩,⟨(-3975290601091513847685802),(-3975290601091513140972712)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨274703727558963380846653,274703727558963496793952⟩,⟨(-3444679398849476467558408),(-3444679398849476351184720)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-1004966625134495778594294),(-1004966625134495757181636)⟩,⟨(-1983833249640734194373966),(-1983833249640734172912711)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-1115999982789189339406541),(-1115999982789189334424158)⟩,⟨(-638516509938795967683499),(-638516509938795962814162)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-679425306339242540800986),(-679425306339242538540094)⟩,⟨48252280206237242580358,48252280206237244767051⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-269855961463580888805315),(-269855961463580887618315)⟩,⟨202878054148508408261113,202878054148508409444327⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-61260721208682396133978),(-61260721208682395442640)⟩,⟨148043904870119903944851,148043904870119904649231⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨6081497188207312933522,6081497188207313317082⟩,⟨74316275087584043117529,74316275087584043508854⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨16019560381015315770883,16019560381015315976813⟩,⟨30800772966632798531119,30800772966632798738650⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨11502229682987361811012,11502229682987361916907⟩,⟨11426297645031822205446,11426297645031822311277⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨6038487927163367521563,6038487927163367570973⟩,⟨3880090995027242986834,3880090995027243035977⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨1825098051724506285029,1825098051724506299365⟩,⟨913902963254836002539,913902963254836016767⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨35916632588337628296163198,35916632588338026495606221⟩,⟨15741304232232635365471949,15741304232233033568006919⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨105283521183393070918811202,105283521183394452694118890⟩,⟨31728366340479315915640462,31728366340480697701741941⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨160219510099977915495590892,160219510099980764248304367⟩,⟨8760261259277269661987215,8760261259280118436305362⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨177368068660214863821098314,177368068660220542558819700⟩,⟨(-53682135363609145477612994),(-53682135363603466712810556)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨137749839677640483891889048,137749839677653243018890278⟩,⟨(-125440254799283762367851415),(-125440254799271003227300486)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨51783560036800604886626932,51783560036821781365724187⟩,⟨(-161178037087706269449073765),(-161178037087685092974110597)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-37201021182446182999373235),(-37201021182423604200308731)⟩,⟨(-136488753003694949350063508),(-136488753003672370568138957)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-84625742562731533757946421),(-84625742562708881502402416)⟩,⟨(-70165413184169639990982161),(-70165413184146987746634733)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-80119401415509996332079993),(-80119401415491650451963500)⟩,⟨(-5235302904656097088820410),(-5235302904637751207939577)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-47421321974382965370840875),(-47421321974374360022938534)⟩,⟨29327742023997917468891896,29327742024006522822984201⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-15515451742441663504648129),(-15515451742437926883328308)⟩,⟨33875220242131450371144760,33875220242135186996055236⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨2440562398285538006884119,2440562398287066499456179⟩,⟨24063261056481080641631768,24063261056482609134420459⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨7980023996085875250795218,7980023996086348577071999⟩,⟨12999781589253539477155466,12999781589254012802462833⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨7172719233055844822470342,7172719233055974055843541⟩,⟨5690496691687991869574344,5690496691688121101933286⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨4398842039719589669610461,4398842039719631015653836⟩,⟨2030538044484612841478603,2030538044484654186981796⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨1438151513969722969440059,1438151513969733749133330⟩,⟨463687850231573008211423,463687850231583787760432⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨67650636376138653930443960,67650636376138654036283289⟩,⟨31942613386208334622396307,31942613386208334725276510⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨206021859658269803681069472,206021859658269804008733933⟩,⟨65915832708833385115033311,65915832708833385431064550⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨337884819638618769855250702,337884819638618770427144099⟩,⟨18433310792214416487762050,18433310792214417034216020⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨419109870026884153067497233,419109870026884153912453434⟩,⟨(-130467744969002737671085030),(-130467744969002736863876130)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨385342243376536372253412988,385342243376536373445793624⟩,⟨(-341991730808619545841514128),(-341991730808619544675450121)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨204148839362990951805780678,204148839362990953326259914⟩,⟨(-517112594138010483822374498),(-517112594138010482308604785)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-72841545442654739467419630),(-72841545442654737703968437)⟩,⟨(-548478998802860469495104301),(-548478998802860467719893682)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-320833654569446856164759724),(-320833654569446854080287942)⟩,⟨(-401210996647221483064685630),(-401210996647221480961804608)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-426907850312162457620179008),(-426907850312162453037223776)⟩,⟨(-148014947005445243883949679),(-148014947005445239294791184)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-371399956751115780234268634),(-371399956751115761042818654)⟩,⟨85387370684473083175673886,85387370684473102366465449⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-225645373162358328322271841),(-225645373162358259653076789)⟩,⟨212748490581413380618121071,212748490581413449287138648⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-81378985473498632926293391),(-81378985473498417903540280)⟩,⟨228866953047349903519819908,228866953047350118544635074⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨9557464873330044275598028,9557464873330585014851969⟩,⟨180226496585805998525178364,180226496585806539266594232⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨42992754341535523844402318,42992754341536343155732015⟩,⟨115477581111480911714688574,115477581111481731027050298⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨37957093281305292626052153,37957093281306046825851021⟩,⟨60226074107116319630924667,60226074107117073830923828⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨14353238369815037061944663,14353238369815340107226760⟩,⟨18241418377636932493720851,18241418377637235538989908⟩⟩
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
noncomputable def ans : CBox := ⟨⟨111325435912378645891127978,111325435912399495358433116⟩,⟨(-245209253901442431924572156),(-245209253901421582460267621)⟩⟩
lemma checked : cachedMomentRuleBox density0 hk7_1_11 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 7 11) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk7_1_11 (tableDensity false) (fullFactor true 7 11) density0_contains hk7_1_11_contains
noncomputable def atomAnswer : CBox := ⟨⟨115356115795241848538948134,115356115795241849035417664⟩,⟨(-303846520899602844322404102),(-303846520899602843827786235)⟩⟩
lemma atomChecked : tableAtomBox false ha7_1_11 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 7 11) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha7_1_11 7 11 ha7_1_11_contains
 def realAnswer : RBox := ⟨226681551707620494330076112,226681551707641344493850780⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 7 11) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm7_0_1_11
namespace hm7_1_1_11
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk7_1_11 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-64412303),(-64412214)⟩,⟨97590363,97590451⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-187148522),(-187148292)⟩,⟨172260262,172260494⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-218406970),(-218406615)⟩,⟨55352754,55353109⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-110049231),(-110048640)⟩,⟨(-61781096),(-61780500)⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-1501595),(-1500706)⟩,⟨(-51288031),(-51287139)⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨16185443,16186460⟩,⟨(-5043643),(-5042623)⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨1589993,1591006⟩,⟨4887726,4888728⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-1604371),(-1603158)⟩,⟨133707,134919⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨193547,194998⟩,⟨(-537511),(-536058)⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨151780,153139⟩,⟨188018,189381⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-124959),(-123739)⟩,⟨17593,18847⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨17830,19148⟩,⟨(-75653),(-74322)⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨49136,50222⟩,⟨18019,19110⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-4528),(-3794)⟩,⟨36550,37284⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-19697),(-19304)⟩,⟨11828,12206⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-7890),(-7755)⟩,⟨691,819⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-2304442793058034),(-2304442793058001)⟩,⟨(-277699421744204),(-277699421744173)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-5078813719931434),(-5078813719931375)⟩,⟨(-509888917069617),(-509888917069558)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-4590478789663172),(-4590478789663088)⟩,⟨(-311620658568249),(-311620658568167)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-2609949752282423),(-2609949752282315)⟩,⟨(-100766199560423),(-100766199560318)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-1046702789782339),(-1046702789782219)⟩,⟨(-39213358013085),(-39213358012965)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-316303630013002),(-316303630012877)⟩,⟨(-31465582609472),(-31465582609346)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-74601247409535),(-74601247409377)⟩,⟨(-19998609359953),(-19998609359790)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-13508702902910),(-13508702902676)⟩,⟨(-8378975759762),(-8378975759530)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-1618358015374),(-1618358015068)⟩,⟨(-2476853058371),(-2476853058061)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-2015007553),(-2015007239)⟩,⟨(-536923665196),(-536923664881)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨64814437658,64814438003⟩,⟨(-79509494123),(-79509493778)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨21827190261,21827190707⟩,⟨(-2942326232),(-2942325783)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨4528112889,4528113325⟩,⟨3196388448,3196388882⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨479079918,479080264⟩,⟨1576445751,1576446101⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-106915852),(-106915622)⟩,⟨533540690,533540919⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-59600211),(-59600121)⟩,⟨120124700,120124792⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨300405741027804200195,300405741027804202463⟩,⟨426361193108607725945,426361193108607728207⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨856230903501603881746,856230903501603887566⟩,⟨980736057138927893574,980736057138927899373⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨1188836806512797309823,1188836806512797316863⟩,⟨910596279950789958974,910596279950789965987⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨1113752513323490433754,1113752513323490439804⟩,⟨433830126451545269512,433830126451545275541⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨722500197548630037949,722500197548630041874⟩,⟨13339444590368580598,13339444590368584520⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨319257011331804986285,319257011331804988212⟩,⟨(-132750069762785985312),(-132750069762785983386)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨90219574550430800417,90219574550430801322⟩,⟨(-102450873920954706987),(-102450873920954706082)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨11693937878445566711,11693937878445567115⟩,⟨(-45035472930130889318),(-45035472930130888913)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-2698791663882155990),(-2698791663882155774)⟩,⟨(-14047757941878344645),(-14047757941878344431)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-2242314721073443180),(-2242314721073442993)⟩,⟨(-3465435497337602047),(-3465435497337601861)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-891980458563305067),(-891980458563304839)⟩,⟨(-741977526718458614),(-741977526718458388)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-293213368160390301),(-293213368160390058)⟩,⟨(-151442222439429130),(-151442222439428886)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-93421852885035980),(-93421852885035751)⟩,⟨(-32187282092784519),(-32187282092784292)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-31167461692950342),(-31167461692950167)⟩,⟨(-7587467512260023),(-7587467512259847)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-10790193400916475),(-10790193400916364)⟩,⟨(-1990066469917609),(-1990066469917496)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-2698460486518891),(-2698460486518842)⟩,⟨(-422574442968208),(-422574442968161)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨367212828708118658061248,367212828708121048868463⟩,⟨326232236303046792181998,326232236303049183007701⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨1071606522919338014506104,1071606522919343386331764⟩,⟨755266778316345505056443,755266778316350876922712⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨1599672363098887371605027,1599672363098892111096000⟩,⟨658754557156990946153225,658754557156995685672409⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨1710228641099314195824004,1710228641099316468336832⟩,⟨103248789179922958180865,103248789179925230682035⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨1310226465211804176065682,1310226465211804762259100⟩,⟨(-505341492149928201411224),(-505341492149927615267648)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨638637588795250212783129,638637588795250306181512⟩,⟨(-766257880351416170661303),(-766257880351416077305548)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨84247969394539859509743,84247969394539874681282⟩,⟨(-624230651574081082818995),(-624230651574081067652069)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-157044144656950353333014),(-157044144656950350978731)⟩,⟨(-322682883869702530138127),(-322682883869702527772708)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-161911637520860134282593),(-161911637520860133456224)⟩,⟨(-94051785395759960296718),(-94051785395759959463458)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-91270736593904603750482),(-91270736593904603324427)⟩,⟨4579277628529567862347,4579277628529568288473⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-35590490039246566804085),(-35590490039246566556670)⟩,⟨23878873712966388121344,23878873712966388367458⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-9451016743448607056636),(-9451016743448606919173)⟩,⟨17465978277702818043700,17465978277702818180442⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-825890993245923306124),(-825890993245923231998)⟩,⟨9238526192818712431821,9238526192818712505815⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨975813416505468251885,975813416505468290319⟩,⟨4252763521346296838887,4252763521346296877333⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨827083878896938619394,827083878896938637491⟩,⟨1761590148723765295660,1761590148723765313786⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨288910420438157313095,288910420438157318381⟩,⟨474950238111660289103,474950238111660294404⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨12050088865786234791224467,12050088865786562020286790⟩,⟨4560838885289920752737589,4560838885290247981357760⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨35724768805282108364243620,35724768805283243964255495⟩,⟨9125814576889940784263900,9125814576891076382519606⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨55582281227846336716326055,55582281227848678283474406⟩,⟨1880751916262791236758620,1880751916265132799963439⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨63771322073033353277609196,63771322073038021838741161⟩,⟨(-18194418968880526726090910),(-18194418968875858170340148)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨52886728561729747512317111,52886728561740238401063219⟩,⟨(-42669689198189032986490686),(-42669689198178542100835450)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨24696931399706530642820645,24696931399723942613237068⟩,⟨(-57054540947187448356074136),(-57054540947170036385225679)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-7351454964084154123606353),(-7351454964065592810192746)⟩,⟨(-51771364897552016756962118),(-51771364897533455440089201)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-27483069881871397237081238),(-27483069881852784879149656)⟩,⟨(-30800243331384146527935462),(-30800243331365534167587592)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-29925417862198117131208146),(-29925417862183054708464881)⟩,⟨(-7627413205512216049018491),(-7627413205497153626396639)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-20836971636927523161292652),(-20836971636920465260686561)⟩,⟨6884266672155240804457742,6884266672162298703822674⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-9868970111872558948853805),(-9868970111869498326037887)⟩,⟨11041071365852750694377925,11041071365855811316475175⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-2514881226047086792791488),(-2514881226045836485478805)⟩,⟨9154365234501180405733763,9154365234502430712980036⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨712964029343498512207461,712964029343885191962838⟩,⟨5744651958804461431277088,5744651958804848111200421⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨1408687510413460236077582,1408687510413565692145981⟩,⟨3018511576281501031514442,3018511576281606487760653⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨1040771596405617678974626,1040771596405651388992649⟩,⟨1345847418749135876646261,1345847418749169586758197⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨363734132785844762585344,363734132785853547760484⟩,⟨372306240025861240785932,372306240025870025985797⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨2054189769933576896652136,2054189769933576920677814⟩,⟨853097549270197430195690,853097549270197451550113⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨6292164405396138954129606,6292164405396139026325181⟩,⟨374571205651925496663248,374571205651925559153846⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨7647238003552275740919051,7647238003552275856234815⟩,⟨(-6784918450188042321559484),(-6784918450188042226341324)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-3462178984389356973802261),(-3462178984389356815400239)⟩,⟨(-22966024768709599284072055),(-22966024768709599155318288)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-37930720435225566203634179),(-37930720435225565926192019)⟩,⟨(-42122270633643696371171311),(-42122270633643696114602044)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-95199285970674998160420025),(-95199285970674997714538388)⟩,⟨(-46618372715648496517317322),(-46618372715648496075636836)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-154627706122144292407050254),(-154627706122144291769556743)⟩,⟨(-17494304729288315549432012),(-17494304729288314898055665)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-184013189998805992566802531),(-184013189998805991607427045)⟩,⟨45324593610216526669618153,45324593610216527652016750⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-163080310725402635775669305),(-163080310725402632653753671)⟩,⟨115489293714901629241213676,115489293714901632372529607⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-100875731123543838451967578),(-100875731123543823246123835)⟩,⟨158585448041200804692170599,158585448041200819895680912⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-28401316948462961375773831),(-28401316948462905659963007)⟩,⟨158524364852945712739478958,158524364852945768448756438⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨25258060185215913286438467,25258060185216088580697790⟩,⟨125325484420228180541284223,125325484420228355831243952⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨49019586821830102974731215,49019586821830544480761633⟩,⟨81331446337428317906888327,81331446337428759412567224⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨47925897010441063063658523,47925897010441732535554072⟩,⟨44057515595082467753150896,44057515595083137225913926⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨32570063346260665342549361,32570063346261281903326331⟩,⟨19581698184232139345318297,19581698184232755906893073⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨11321859543716207874399223,11321859543716455672863002⟩,⟨5292914268460319523678546,5292914268460567322439461⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-71485240302717533639406065),(-71485240302700407270896218)⟩,⟨77226724597027501796723927,77226724597044628154827047⟩⟩
lemma checked : cachedMomentRuleBox density1 hk7_1_11 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 7 11) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk7_1_11 (tableDensity true) (fullFactor true 7 11) density1_contains hk7_1_11_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-150850305270700879507853868),(-150850305270700878858624483)⟩,⟨397337758099480641928643538,397337758099480642575451517⟩⟩
lemma atomChecked : tableAtomBox true ha7_1_11 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 7 11) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha7_1_11 7 11 ha7_1_11_contains
 def realAnswer : RBox := ⟨(-222335545573418413247259933),(-222335545573401286029520701)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 7 11) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm7_1_1_11
namespace hm7_0_1_12
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk7_1_12 j i k))
noncomputable def s0_0 : CBox := ⟨⟨380799455,380799818⟩,⟨(-301748370),(-301748007)⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨954472617,954473695⟩,⟨(-451308340),(-451307256)⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨938842982,938844715⟩,⟨23435276,23437007⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨393138022,393140209⟩,⟨364244176,364246361⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-39250639),(-39247390)⟩,⟨222757156,222760398⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-77827525),(-77822953)⟩,⟨8562195,8566757⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-2685296),(-2679891)⟩,⟨(-24420071),(-24414720)⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨7645647,7650772⟩,⟨1100750,1105883⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-1479824),(-1473126)⟩,⟨2229461,2236192⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-484182),(-477418)⟩,⟨(-987928),(-981155)⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨544837,550088⟩,⟨24351,29752⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-130971),(-125258)⟩,⟨300833,306582⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-201386),(-196553)⟩,⟨(-107016),(-102170)⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨32923,36235⟩,⟨(-155540),(-152229)⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨86976,88739⟩,⟨(-43205),(-41495)⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨33237,33799⟩,⟨(-60),485⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨8036014541831645,8036014541831697⟩,⟨3692366853366570,3692366853366618⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨18071561177113798,18071561177113917⟩,⟨8006758673095032,8006758673095152⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨16906935509753095,16906935509753272⟩,⟨7125722382662872,7125722382663048⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨9970443483787870,9970443483788140⟩,⟨4139730629102225,4139730629102497⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨4075444504253795,4075444504254216⟩,⟨1845194086539433,1845194086539855⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨1201927348089611,1201927348090203⟩,⟨691286547143333,691286547143924⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨256759250552864,256759250553596⟩,⟨222042996177101,222042996177835⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨36284666130453,36284666131250⟩,⟨59526084158991,59526084159790⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨1329051746600,1329051747788⟩,⟨12788876701439,12788876702631⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-1039807439216),(-1039807437674)⟩,⟨2045635665938,2045635667482⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-389750418642),(-389750417076)⟩,⟨175464850315,175464851880⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-84744324228),(-84744322827)⟩,⟨(-27002800867),(-27002799463)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-11258433762),(-11258432301)⟩,⟨(-18573528067),(-18573526603)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨518457233,518458525⟩,⟨(-6291442871),(-6291441576)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨1070672665,1070673556⟩,⟨(-1756649344),(-1756648453)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨359800820,359801155⟩,⟨(-352952543),(-352952206)⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-114069653499823780122),(-114069653499823777123)⟩,⟨(-1119478057636073177848),(-1119478057636073174735)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-597568730358363816707),(-597568730358363809118)⟩,⟨(-2750940677556292796769),(-2750940677556292788935)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-1368595746380726764958),(-1368595746380726755734)⟩,⟨(-2966692877106099134481),(-2966692877106099125061)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-1807460435698081262927),(-1807460435698081253973)⟩,⟨(-1966736494306189383379),(-1966736494306189374372)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-1527118511137185600102),(-1527118511137185592731)⟩,⟨(-726193130283604783770),(-726193130283604776457)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-864020227146478536332),(-864020227146478531546)⟩,⟨(-10259345700756264814),(-10259345700756260098)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-331352625883833516203),(-331352625883833513706)⟩,⟨157060481116119470654,157060481116119473131⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-83344049021284037453),(-83344049021284036371)⟩,⟨103700617630138789788,103700617630138790871⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-10737056703451908697),(-10737056703451908249)⟩,⟨41363140261256499659,41363140261256500107⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨1507964996332620638,1507964996332620890⟩,⟨12585158104723373636,12585158104723373885⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨1508628274939068981,1508628274939069249⟩,⟨3316360684321520318,3316360684321520590⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨655338061159830007,655338061159830301⟩,⟨842451276865617027,842451276865617320⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨244087144466400416,244087144466400719⟩,⟨226477108296169596,226477108296169897⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨90093820483150724,90093820483150972⟩,⟨68338276479905495,68338276479905744⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨33182848470779140,33182848470779298⟩,⟨22538695984098112,22538695984098273⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨8542419813027085,8542419813027147⟩,⟨5539886967190996,5539886967191059⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-137048369706405577723974),(-137048369706404274637156)⟩,⟨(-579872263698979177610626),(-579872263698977874494311)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-555911421472756461998338),(-555911421472753627423061)⟩,⟨(-1520769426315449544086485),(-1520769426315446709473198)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-1216414217634857971610788),(-1216414217634855616696820)⟩,⟨(-1847067772357137794290054),(-1847067772357135439437100)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-1823600178154727366802910),(-1823600178154726334848180)⟩,⟨(-1392201450258047983765131),(-1392201450258046952032879)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-1926348335507344358076426),(-1926348335507344102184404)⟩,⟨(-437646232283157617142720),(-437646232283157361527318)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-1406639267863275143631364),(-1406639267863275085047155)⟩,⟨408452404184471650940604,408452404184471709442485⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-634130537408447959634638),(-634130537408447950675040)⟩,⟨717655937894168888870605,717655937894168897884444⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-69689954557834535970042),(-69689954557834534118408)⟩,⟨558933696063638005054909,558933696063638006976761⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨141557027376756375915647,141557027376756377008717⟩,⟨268754483457340378780451,268754483457340379884143⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨134953829178169967513996,134953829178169968191274⟩,⟨72652081775883386621898,72652081775883387288321⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨73867701362551497434321,73867701362551497817068⟩,⟨(-4272496549416309335589),(-4272496549416308960642)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨29852586283337527716035,29852586283337527917260⟩,⟨(-18231956905394665246465),(-18231956905394665046326)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨9459906639385116708482,9459906639385116808203⟩,⟨(-13530008423370002126179),(-13530008423370002025853)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨2224826432332429532648,2224826432332429580925⟩,⟨(-7469114712467305403796),(-7469114712467305354859)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨244670583007861026729,244670583007861048345⟩,⟨(-3467627119947130711784),(-3467627119947130689780)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-40297011200979786316),(-40297011200979780149)⟩,⟨(-991552687543410825971),(-991552687543410819694)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨3244932915539987399197185,3244932915540115351914079⟩,⟨(-13162640415233478965878307),(-13162640415233351014702720)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨4518679549230152382204622,4518679549230587495473017⟩,⟨(-37849450683970350460282430),(-37849450683969915352048751)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-6930722516174934951753118),(-6930722516174024041992758)⟩,⟨(-55494138520295393986782979),(-55494138520294483085767404)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-30066649755042636199285671),(-30066649755040398188793279)⟩,⟨(-57742992099043194930338868),(-57742992099040956927122012)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-53172150473318069990134802),(-53172150473313339035415981)⟩,⟨(-39305749326778668650532698),(-39305749326773937697745960)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-60491888423681467135165687),(-60491888423674190213589432)⟩,⟨(-6320024714470322858790388),(-6320024714463045933010616)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-45575272932881770578523348),(-45575272932873928544001144)⟩,⟨24046062031443044212542071,24046062031450886254135232⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-18014490069361387684932123),(-18014490069352219909614203)⟩,⟨36433062675582173018884130,36433062675591340796390401⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨5456384296017361462778930,5456384296023974478350536⟩,⟨29650629613323486426115284,29650629613330099439848379⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨15478834803392991182604716,15478834803396070291060633⟩,⟨14579412467602615289598510,14579412467605694395375421⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨14251223141746000024169113,14251223141747613254874661⟩,⟨2218327768579111441912196,2218327768580724671969485⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨8783494995112591542418436,8783494995113176184468242⟩,⟨(-3596895151323175571977303),(-3596895151322590929486087)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨4002282106756601149755817,4002282106756762150848091⟩,⟨(-4546477114947289531276053),(-4546477114947128529510583)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨1305313306549668072090271,1305313306549721859293079⟩,⟨(-3430145958519852615186723),(-3430145958519798827614596)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨232843503275193945369256,232843503275214051181223⟩,⟨(-1940913993249240326428517),(-1940913993249220220489647)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-2607533379464650779436),(-2607533379459623469305)⟩,⟨(-611732211461162517224851),(-611732211461157489886589)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨8547704864410497353528891,8547704864410497384602655⟩,⟨(-20874178999019118258557884),(-20874178999019118226396056)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨16493791566728881687309373,16493791566728881782859176⟩,⟨(-63257626999836072736629820),(-63257626999836072637000590)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-437302903529874001883962),(-437302903529873836354141)⟩,⟨(-102743160989592137945662853),(-102743160989592137771604639)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-48102787648444595035877571),(-48102787648444594786085876)⟩,⟨(-125274353392131936003727604),(-125274353392131935742713386)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-113820324055041167499093675),(-113820324055041167135844555)⟩,⟨(-110883814683280574575232864),(-110883814683280574205033093)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-165832068547447252505280934),(-165832068547447252034931070)⟩,⟨(-50244898630279770669705423),(-50244898630279770198646377)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-170133872746028668619840752),(-170133872746028668071788493)⟩,⟨38797448284526669885313406,38797448284526670428405529⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-116908416421546918489817434),(-116908416421546917828423756)⟩,⟨115162581859085693659146654,115162581859085694314613835⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-31755160535858115734218419),(-31755160535858114242862523)⟩,⟨142779701636633629083196532,142779701636633630573153216⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨43147965065352744325985686,43147965065352750427887621⟩,⟨117334430338660937958892328,117334430338660944061308496⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨80291666049713025194910456,80291666049713046628078593⟩,⟨64585605369577082393509840,64585605369577103826721232⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨80122660201867619332510296,80122660201867698092071523⟩,⟨15759511542545231024922839,15759511542545309783787844⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨59953544085194160911725089,59953544085194350328633481⟩,⟨(-12717469058732642828023813),(-12717469058732453411710156)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨36619791257910635427755862,36619791257910912615233208⟩,⟨(-20933074053142990580231263),(-20933074053142713392947483)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨18260595752543217755471636,18260595752543466128612059⟩,⟨(-16342356259062486496560766),(-16342356259062238123382632)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨5367573101824982039998266,5367573101825080289493331⟩,⟨(-5949468698251267829108704),(-5949468698251169579572913)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-77091466031779067759237503),(-77091466031771435919064488)⟩,⟨(-25947180124446471056885870),(-25947180124438839215980498)⟩⟩
lemma checked : cachedMomentRuleBox density0 hk7_1_12 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 7 12) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk7_1_12 (tableDensity false) (fullFactor true 7 12) density0_contains hk7_1_12_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-95959419172917142443332258),(-95959419172917142258644894)⟩,⟨(-26630826050962016000563710),(-26630826050962015815534903)⟩⟩
lemma atomChecked : tableAtomBox false ha7_1_12 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 7 12) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha7_1_12 7 12 ha7_1_12_contains
 def realAnswer : RBox := ⟨(-173050885204696210302569761),(-173050885204688578077709382)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 7 12) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm7_0_1_12
namespace hm7_1_1_12
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk7_1_12 j i k))
noncomputable def s0_0 : CBox := ⟨⟨71355464,71355537⟩,⟨(-42556328),(-42556249)⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨173067664,173067865⟩,⟨(-53860478),(-53860274)⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨158869071,158869389⟩,⟨28828560,28828876⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨55391667,55392063⟩,⟨72405254,72405648⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-12793194),(-12792631)⟩,⟨35170007,35170570⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-12488858),(-12488094)⟩,⟨(-525700),(-524939)⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-37293),(-36419)⟩,⟨(-3832503),(-3831638)⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨1192870,1193688⟩,⟨214814,215631⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-232583),(-231506)⟩,⟨366240,367327⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-90919),(-89800)⟩,⟨(-162796),(-161679)⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨96142,97038⟩,⟨(-2164),(-1237)⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-19782),(-18786)⟩,⟨55752,56755⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-37826),(-36982)⟩,⟨(-16806),(-15958)⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨3739,4314⟩,⟨(-28582),(-28006)⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨14937,15245⟩,⟨(-9212),(-8915)⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨5958,6062⟩,⟨(-619),(-516)⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨828645576878654,828645576878676⟩,⟨1102806931384863,1102806931384886⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨1889924652961709,1889924652961750⟩,⟨2386658853744878,2386658853744922⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨1807504121432999,1807504121433049⟩,⟨2090373302895419,2090373302895474⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨1089866070695390,1089866070695458⟩,⟨1150657516050039,1150657516050104⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨453077582108772,453077582108855⟩,⟨457588200668346,457588200668427⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨134435343352526,134435343352624⟩,⟨145991653271982,145991653272080⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨28132971721831,28132971721950⟩,⟨40188550092329,40188550092447⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨3523383958276,3523383958405⟩,⟨9658598873110,9658598873239⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-102658076070),(-102658075878)⟩,⟨1946044454789,1946044454980⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-200981645436),(-200981645182)⟩,⟨298532958632,298532958887⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-66200876301),(-66200876033)⟩,⟨22315994616,22315994889⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-14033790366),(-14033790109)⟩,⟨(-5857755881),(-5857755627)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-1701060380),(-1701060103)⟩,⟨(-3475689086),(-3475688810)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨211046443,211046695⟩,⟨(-1140418384),(-1140418127)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨235999767,235999950⟩,⟨(-304291162),(-304290981)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨75360870,75360946⟩,⟨(-58083946),(-58083867)⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨110515056530325431230,110515056530325432210⟩,⟨(-228751787352137479854),(-228751787352137478871)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨213432450951440803034,213432450951440805522⟩,⟨(-599526035197004664913),(-599526035197004662413)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨98803441791766762942,98803441791766765907⟩,⟨(-730426443323549522197),(-730426443323549519223)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-94493993168554094083),(-94493993168554091357)⟩,⟨(-586739592312557886217),(-586739592312557883487)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-183426035148105328528),(-183426035148105326465)⟩,⟨(-314404958977996528009),(-314404958977996525945)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-144826959612830846058),(-144826959612830844846)⟩,⟨(-101546615735168102051),(-101546615735168100844)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-70415327805600621625),(-70415327805600621045)⟩,⟨(-9595423824287422064),(-9595423824287421485)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-23136023888689464644),(-23136023888689464399)⟩,⟨8600713711085527372,8600713711085527614⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-5253754662145848208),(-5253754662145848094)⟩,⟨5681237742683118394,5681237742683118510⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-752149787922213050),(-752149787922212956)⟩,⟨2148815613341848771,2148815613341848865⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-6185724530150928),(-6185724530150815)⟩,⟨651868969509249149,651868969509249262⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨43089046907263684,43089046907263827⟩,⟨183569279331609482,183569279331609628⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨22077217687554733,22077217687554879⟩,⟨52846290800512811,52846290800512956⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨9099345237701984,9099345237702101⟩,⟨16455918366462907,16455918366463021⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨3514855450540383,3514855450540463⟩,⟨5446776112852328,5446776112852404⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨922929167749892,922929167749926⟩,⟨1331568098160389,1331568098160425⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨79147303489680357450464,79147303489681451938941⟩,⟨(-182783365213743676238034),(-182783365213742581752667)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨154062517793555420197768,154062517793557799206572⟩,⟨(-510570822255625031406238),(-510570822255622652401521)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨44965444750744827907114,44965444750746801029131⟩,⟨(-706709827077550179452857),(-706709827077548206324687)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-192821551464434839430731),(-192821551464433977590103)⟩,⟨(-680963725843653688397443),(-680963725843652826534092)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-385309560340685284523446),(-385309560340685072587101)⟩,⟨(-442744559679118309419341),(-442744559679118097455136)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-399617495963429842958070),(-399617495963429795646148)⟩,⟨(-138057163822807657750036),(-138057163822807610430065)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-263208482278104788573336),(-263208482278104782149957)⟩,⟨65541971539152588018724,65541971539152594436602⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-103925432607931826023912),(-103925432607931825122690)⟩,⟨117958950661335028227821,117958950661335029122250⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-9363956618352947204062),(-9363956618352946791024)⟩,⟨82974400911577034201453,82974400911577034613636⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨19245631324501141796484,19245631324501142034677⟩,⟨36751350677017863188693,36751350677017863428010⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨17079790711189806872620,17079790711189807005537⟩,⟨10000992942900328616804,10000992942900328750460⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨9312128772289216250145,9312128772289216321214⟩,⟨273462832532858672311,273462832532858743472⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨4076311606693726610841,4076311606693726646703⟩,⟨(-1684530207277211309954),(-1684530207277211274153)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨1579394232105135105657,1579394232105135123331⟩,⟨(-1380057521394786721648),(-1380057521394786704039)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨556158011141078618160,556158011141078626192⟩,⟨(-760949135074135047214),(-760949135074135039219)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨134166087244942558078,134166087244942560395⟩,⟨(-234630716641322938442),(-234630716641322936140)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨843282064335423093426338,843282064335528238500287⟩,⟨(-4373629405103287994311632),(-4373629405103182848986193)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨973220056678513120004628,973220056678870704469774⟩,⟨(-12744882934908673287136872),(-12744882934908315701790584)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-2801735829558934518204593),(-2801735829558185798649973)⟩,⟨(-19180511247993068840176281),(-19180511247992320118985856)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-10428419047642058081136381),(-10428419047640218189497019)⟩,⟨(-20834216812810139314924333),(-20834216812808299421813423)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-18503285330006759345221610),(-18503285330002869434573190)⟩,⟨(-15470812511994458223351930),(-15470812511990568312205695)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-21883433509587517372030240),(-21883433509581534054775993)⟩,⟨(-4476544613734505112578681),(-4476544613728521796100683)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-17823779577810635697771746),(-17823779577804189075205315)⟩,⟨6717799865373571482626351,6717799865380018103689404⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-8733645635158740162980829),(-8733645635151207343935722)⟩,⟨12516890323212507299107019,12516890323220040117644025⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-27287185781552492153070),(-27287185776122987237588)⟩,⟨11597013106155014736979028,11597013106160444242269065⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨4590177175173612478339122,4590177175176137783296291⟩,⟨6998761562052976113526981,6998761562055501419036836⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨5151099245470281987094858,5151099245471603385254695⟩,⟨2516294181455890593908366,2516294181457211992210380⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨3724937557819612745772574,3724937557820090986198183⟩,⟨(-72269219446238594397717),(-72269219445760354044625)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨2097174211668243633040408,2097174211668375160390658⟩,⟨(-941137324732414303292396),(-941137324732282776061838)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨982729349553632094691810,982729349553675984263507⟩,⟨(-903925028625893747317049),(-903925028625849857810610)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨387306153865950517447251,387306153865966910435109⟩,⟨(-566754074699218959621461),(-566754074699202566655916)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨97470713074349542647317,97470713074353639849450⟩,⟨(-186819041964670689049046),(-186819041964666591851817)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨224364117865109959973554,224364117865109966241204⟩,⟨(-631986744188314125684051),(-631986744188314118487764)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨9093247272471567740734,9093247272471586024707⟩,⟨(-1904773089463329060860350),(-1904773089463329039280263)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-2193480635009106789393280),(-2193480635009106761770882)⟩,⟨(-2195529497593097614770566),(-2195529497593097580503664)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-6938711718716729143734571),(-6938711718716729103334572)⟩,⟨1516381755191690756337169,1516381755191690805493991⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-12109523776843811972969517),(-12109523776843811891628919)⟩,⟨12622440714734461904022884,12622440714734461990827109⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-12055800209886066948664672),(-12055800209886066810608605)⟩,⟨30779501456326566159024157,30779501456326566297222061⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-1000842175464689837568659),(-1000842175464689636906888)⟩,⟨49093240732865973853245928,49093240732865974048425987⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨20474164884425221621942674,20474164884425221935288452⟩,⟨56999250255751773453816825,56999250255751773760045066⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨43203471754348672960631317,43203471754348673990240180⟩,⟨48176764510842883323313049,48176764510842884351019741⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨55791598769179979386030720,55791598769179984228463723⟩,⟨26281303543289400596745859,26281303543289405440779764⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨53475462989466989733387260,53475462989467007110925618⟩,⟨2138957110103779836699316,2138957110103797216750553⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨40430187444191967337054950,40430187444192031538827719⟩,⟨(-14585724324851798207308363),(-14585724324851734004570228)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨24697073554031578306125369,24697073554031732954444159⟩,⟨(-20735990239957062837388760),(-20735990239956908189275183)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨12221438630556986448070946,12221438630557212934818811⟩,⟨(-18634664100488363340649978),(-18634664100488136854395189)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨4775162587802688476743851,4775162587802891517548746⟩,⟨(-12179306432837072534020326),(-12179306432836869493594986)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨1139195385816249411956187,1139195385816329748277147⟩,⟨(-4161399310498906074491900),(-4161399310498825738305342)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨26627413025682455479092160,26627413025688724434312057⟩,⟨18469796836395488879699685,18469796836401757837815932⟩⟩
lemma checked : cachedMomentRuleBox density1 hk7_1_12 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 7 12) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk7_1_12 (tableDensity true) (fullFactor true 7 12) density1_contains hk7_1_12_contains
noncomputable def atomAnswer : CBox := ⟨⟨125485394303045493722843323,125485394303045493964357568⟩,⟨34824926374334943758776412,34824926374334944000737158⟩⟩
lemma atomChecked : tableAtomBox true ha7_1_12 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 7 12) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha7_1_12 7 12 ha7_1_12_contains
 def realAnswer : RBox := ⟨152112807328727949101935483,152112807328734218498669625⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 7 12) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm7_1_1_12
namespace hm7_0_1_13
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk7_1_13 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-310947333),(-310947100)⟩,⟨69682662,69682893⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-694465285),(-694464575)⟩,⟨(-418377),(-417670)⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-558645715),(-558644475)⟩,⟨(-271680062),(-271678821)⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-144867315),(-144865535)⟩,⟨(-326653099),(-326651319)⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨79906891,79908982⟩,⟨(-129641156),(-129639069)⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨51831649,51834443⟩,⟨12372549,12375331⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-3286058),(-3282142)⟩,⟨16582110,16586009⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-4940690),(-4937023)⟩,⟨(-2121222),(-2117551)⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨1346995,1351374⟩,⟨(-1309328),(-1304915)⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨213482,218449⟩,⟨740872,745844⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-384611),(-380892)⟩,⟨(-70511),(-66689)⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨107812,111739⟩,⟨(-208909),(-204951)⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨135370,138812⟩,⟨80286,83739⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-28913),(-26532)⟩,⟨107317,109697⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-63289),(-62028)⟩,⟨28721,29950⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-23964),(-23559)⟩,⟨(-403),(-10)⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-1588687755174997),(-1588687755174962)⟩,⟨(-4584020794184866),(-4584020794184830)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-3759768195441545),(-3759768195441460)⟩,⟨(-10211998316802643),(-10211998316802562)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-3791001423713832),(-3791001423713703)⟩,⟨(-9439684068994363),(-9439684068994234)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-2373579618603939),(-2373579618603753)⟩,⟨(-5562037337304349),(-5562037337304162)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-971783053797895),(-971783053797658)⟩,⟨(-2345713789720003),(-2345713789719766)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-252458057905100),(-252458057904824)⟩,⟨(-758249383461686),(-758249383461414)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-31633159690147),(-31633159689717)⟩,⟨(-196503279480739),(-196503279480308)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨4917626983949,4917626984561⟩,⟨(-41328992222406),(-41328992221795)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨3938003451820,3938003452524⟩,⟨(-6752861562436),(-6752861561734)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨1243037963602,1243037964397⟩,⟨(-685860658306),(-685860657509)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨266098247755,266098248805⟩,⟨37164456034,37164457085⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨37921081921,37921083051⟩,⟨42129123004,42129124132⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨614744299,614745186⟩,⟨13982320347,13982321235⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-2179540757),(-2179540086)⟩,⟨3474525448,3474526122⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-1137482312),(-1137481789)⟩,⟨715561831,715562350⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-313121311),(-313121104)⟩,⟨104531198,104531406⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-415136797449026063124),(-415136797449026061569)⟩,⟨289217415063706418530,289217415063706420067⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-950757877156934923179),(-950757877156934919098)⟩,⟨842275138575662731196,842275138575662735264⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-861705224660238694886),(-861705224660238689504)⟩,⟨1208674362465429125620,1208674362465429131035⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-358055727224326421510),(-358055727224326416297)⟩,⟨1172503922542591579492,1172503922542591584784⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨80708228650385901484,80708228650385905415⟩,⟨782133260994161494542,782133260994161498550⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨214508308294668759682,214508308294668762054⟩,⟨347142777649320310937,347142777649320313335⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨151019034815229898833,151019034815229899953⟩,⟨90830206573597640472,90830206573597641589⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨65009454736459665379,65009454736459665852⟩,⟨4359034318219362542,4359034318219363012⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨19812355023300195746,19812355023300195997⟩,⟨(-7930261007237700485),(-7930261007237700232)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨4592106156222102891,4592106156222103063⟩,⟨(-4534529989960314596),(-4534529989960314425)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨837956437323048774,837956437323048943⟩,⟨(-1693671635956916738),(-1693671635956916571)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨113099120310887932,113099120310888093⟩,⟨(-551452227768750208),(-551452227768750046)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨3632603705285670,3632603705285822⟩,⟨(-178117391245908169),(-178117391245908018)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-5805375066989863),(-5805375066989732)⟩,⟨(-60914750737526034),(-60914750737525900)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-3459901585673236),(-3459901585673143)⟩,⟨(-21601256630148507),(-21601256630148411)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-1031478161845051),(-1031478161845010)⟩,⟨(-5478534047949427),(-5478534047949385)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-190163757589020131495074),(-190163757589019636844062)⟩,⟨116542823508452383555691,116542823508452878212675⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-476058486068729603904472),(-476058486068728561379595)⟩,⟨378208311431837321780814,378208311431838364338075⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-513211788507725264413508),(-513211788507724453783662)⟩,⟨659508403803041651237491,659508403803042461952867⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-271676263251946183131384),(-271676263251945850279485)⟩,⟨831593128568922604232508,831593128568922937214363⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨94789010007889395734741,94789010007889510885724⟩,⟨756250107661072017415261,756250107661072132632791⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨344469071930880884271703,344469071930880908159589⟩,⟨458028709796992712661997,458028709796992736538634⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨358202413681879920541451,358202413681879923816245⟩,⟨128901211438190359617179,128901211438190362846103⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨219418824914232186588928,219418824914232187533944⟩,⟨(-61116807079493897751887),(-61116807079493896822609)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨77850059372295179929110,77850059372295180450643⟩,⟨(-97849130083963956541445),(-97849130083963956013951)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨3948104877452856855912,3948104877452857156047⟩,⟨(-64105474707681172533612),(-64105474707681172226157)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-15341271223174522163837),(-15341271223174522000280)⟩,⟨(-27559352315286973723601),(-27559352315286973558920)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-12866826110759815904585),(-12866826110759815824340)⟩,⟨(-7992873791965646511221),(-7992873791965646431734)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-7186268355839666638998),(-7186268355839666601846)⟩,⟨(-933143809599508979894),(-933143809599508943528)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-3386970690846233971575),(-3386970690846233951492)⟩,⟨697502618576227875129,697502618576227894903⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-1412458348310400615996),(-1412458348310400605877)⟩,⟨648209335498296214851,648209335498296224885⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-380733425907764467223),(-380733425907764464168)⟩,⟨231067054775466121725,231067054775466124763⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-4315415486709415457555498),(-4315415486709378921026747)⟩,⟨(-304104275946040122544352),(-304104275946003585387398)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-12178901837067331992902063),(-12178901837067208669853591)⟩,⟨671264878895955305759396,671264878896078630749721⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-17172157875174487087882448),(-17172157875174164484846544)⟩,⟨5370820889980286554143177,5370820889980609159589198⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-16596591107881280593268960),(-16596591107880495629764463)⟩,⟨13047848741679875893713865,13047848741680660858730666⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-9246055767402341483782849),(-9246055767400784500125063)⟩,⟨19590332149968582449158688,19590332149970139432488855⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨2067698831684931894235552,2067698831687131916759492⟩,⟨20063965636250113843637549,20063965636252313863929326⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨11226832694563293125639500,11226832694566115399165406⟩,⟨13196548344914920617254429,13196548344917742888760437⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨13517734325829153865648843,13517734325832384202086877⟩,⟨3109754980163820377401143,3109754980167050713798599⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨9501711331032797023502197,9501711331034859954460643⟩,⟨(-4349199618350820424007693),(-4349199618348757491918407)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨3549345151669985279603555,3549345151671179501753586⟩,⟨(-6590527052174091167854840),(-6590527052172896944996331)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-620492469176811111235004),(-620492469176218232838527)⟩,⟨(-5116040219179940105794349),(-5116040219179347227450273)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-2151975096400539950199884),(-2151975096400350964282676)⟩,⟨(-2681405727095351889232989),(-2681405727095162903653458)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-2024180493783986089593864),(-2024180493783927287189867)⟩,⟨(-912176123309102702821262),(-912176123309043900654887)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-1355825057254354758425740),(-1355825057254331633129482)⟩,⟨(-76761958383365514961444),(-76761958383342389735130)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-714456979956112003075971),(-714456979956103967110820)⟩,⟨140130959457412795660704,140130959457420831617429⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-216970929530341139004625),(-216970929530339198621059)⟩,⟨72003369343549238775251,72003369343551179160778⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-5926349702044603457935724),(-5926349702044603448936699)⟩,⟨(-2070923352749461021516576),(-2070923352749461012874416)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-17871766765235699746235908),(-17871766765235699718347448)⟩,⟨(-3631465912519237242922249),(-3631465912519237216326481)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-28739221409531598674189520),(-28739221409531598625433111)⟩,⟨1813502710266315584931083,1813502710266315631081733⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-34398261247907590085805005),(-34398261247907590011367685)⟩,⟨15836594197398260921967834,15836594197398260993441836⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-29134202930744159234319381),(-29134202930744159128733266)⟩,⟨34609184995482002526851379,34609184995482002630803325⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-10507512814276466483892007),(-10507512814276466350023393)⟩,⟨48732063542060898937293085,48732063542060899071359921⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨15807034491325235471389784,15807034491325235624435242⟩,⟨48280268844643914476285963,48280268844643914631130208⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨37334003588268698160960890,37334003588268698351158176⟩,⟨30785205771317916897572694,30785205771317917089418942⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨43471738577668676240823482,43471738577668676682178243⟩,⟨4533852698286067822172703,4533852698286068263758300⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨33599688103618754034401522,33599688103618755806376683⟩,⟨(-17441896057266773329415232),(-17441896057266771557681346)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨16248674832350100678308014,16248674832350107408017410⟩,⟨(-27107463297244515756716299),(-27107463297244509027015997)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨1184889173598439175940561,1184889173598465123695583⟩,⟨(-25311836368736667414724338),(-25311836368736641466767118)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-6858835646002856579153351),(-6858835646002796840936784)⟩,⟨(-17945092153588252663769747),(-17945092153588192925420867)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-8403613948255581306484794),(-8403613948255497083844314)⟩,⟨(-10345331770540365778539587),(-10345331770540281555892445)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-6088264598883772981165919),(-6088264598883699850673065)⟩,⟨(-4854413642665014374313893),(-4854413642664941243867205)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-2158050357467976758442572),(-2158050357467948382780003)⟩,⟨(-1364818279541971323533386),(-1364818279541942947895021)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-4927467972061798682975988),(-4927467972059216701401604)⟩,⟨22137610286865467108608060,22137610286868049089901134⟩⟩
lemma checked : cachedMomentRuleBox density0 hk7_1_13 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 7 13) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk7_1_13 (tableDensity false) (fullFactor true 7 13) density0_contains hk7_1_13_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-4818529933431725841674826),(-4818529933431725777055858)⟩,⟨27705380636894736828786355,27705380636894736893379110⟩⟩
lemma atomChecked : tableAtomBox false ha7_1_13 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 7 13) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha7_1_13 7 13 ha7_1_13_contains
 def realAnswer : RBox := ⟨(-9745997905493524624650814),(-9745997905490942378457462)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 7 13) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm7_0_1_13
namespace hm7_1_1_13
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk7_1_13 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-54279431),(-54279378)⟩,⟨4796031,4796082⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-118049153),(-118049017)⟩,⟨(-16704656),(-16704519)⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-87713149),(-87712917)⟩,⟨(-60940713),(-60940483)⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-14854781),(-14854458)⟩,⟨(-58940444),(-58940120)⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨16744236,16744605⟩,⟨(-18826830),(-18826463)⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨7879775,7880247⟩,⟨3202441,3202911⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-767545),(-766911)⟩,⟨2522455,2523088⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-763006),(-762419)⟩,⟨(-359675),(-359084)⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨214005,214714⟩,⟨(-216692),(-215978)⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨42950,43775⟩,⟨123411,124238⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-68435),(-67797)⟩,⟨(-7870),(-7208)⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨16841,17530⟩,⟨(-38956),(-38264)⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨25597,26203⟩,⟨12788,13392⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-3652),(-3233)⟩,⟨19789,20207⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-10888),(-10663)⟩,⟨6199,6418⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-4303),(-4221)⟩,⟨354,431⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨122113995172871,122113995172892⟩,⟨(-746815140184622),(-746815140184599)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨219263864790751,219263864790783⟩,⟨(-1661619869212642),(-1661619869212614)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨117984408789260,117984408789300⟩,⟨(-1527542352277101),(-1527542352277065)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨13869805385503,13869805385546⟩,⟨(-887585003264253),(-887585003264207)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-10082725224790),(-10082725224737)⟩,⟨(-365284158509076),(-365284158509027)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-1927318174817),(-1927318174764)⟩,⟨(-114357131484255),(-114357131484197)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨2507952956119,2507952956195⟩,⟨(-28651309046895),(-28651309046821)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨1906992809303,1906992809403⟩,⟨(-5833904328145),(-5833904328044)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨748697917009,748697917128⟩,⟨(-918184885110),(-918184884992)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨206593362737,206593362873⟩,⟨(-83011830863),(-83011830721)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨42692913501,42692913686⟩,⟨10290511614,10290511801⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨5834706934,5834707140⟩,⟨7738802572,7738802781⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-114147990),(-114147816)⟩,⟨2491083083,2491083253⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-462610291),(-462610153)⟩,⟨594851813,594851951⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-226591538),(-226591428)⟩,⟨109243399,109243509⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-61037104),(-61037051)⟩,⟨12567337,12567391⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-114041676737684150518),(-114041676737684150013)⟩,⟨6495380710647138786,6495380710647139293⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-283047333278912786267),(-283047333278912784942)⟩,⟨48311527406976306752,48311527406976308074⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-310403483463105031329),(-310403483463105029622)⟩,⟨125690483584045707522,125690483584045709231⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-210223389216251868907),(-210223389216251867327)⟩,⟨173796589418900368377,173796589418900369956⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-80552281978334502886),(-80552281978334501782)⟩,⟨148849764442215685214,148849764442215686321⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-3858705764655923072),(-3858705764655922460)⟩,⟨83436469907975662164,83436469907975662781⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨14890583290592431004,14890583290592431273⟩,⟨30731836292812123435,30731836292812123705⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨9942224428356113245,9942224428356113355⟩,⟨6872769905941091280,6872769905941091394⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨3839824360227658283,3839824360227658353⟩,⟨430235927022218087,430235927022218154⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨1099098251506621610,1099098251506621674⟩,⟨(-368095993639158344),(-368095993639158281)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨263966770856776184,263966770856776265⟩,⟨(-211258465073489512),(-211258465073489432)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨58819846170470720,58819846170470807⟩,⟨(-80186591019136302),(-80186591019136214)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨13259505551824898,13259505551824981⟩,⟨(-27624574591263857),(-27624574591263774)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨3217771584459175,3217771584459241⟩,⟨(-9652871167402125),(-9652871167402054)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨848101511592093,848101511592141⟩,⟨(-3431979265295280),(-3431979265295234)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨179087841436609,179087841436635⟩,⟨(-868827153936606),(-868827153936582)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-74249493900342553102215),(-74249493900342137639415)⟩,⟨(-6768197798427560802530),(-6768197798427145340338)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-200178716073671300125956),(-200178716073670425156410)⟩,⟨5572015955540843013868,5572015955541717980082⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-258324157407086105865646),(-258324157407085426653582)⟩,⟨69708468207188895267861,69708468207189574471116⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-220850738857527835593413),(-220850738857527557610407)⟩,⟨155077738871339015597871,155077738871339293567581⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-109865712605823103309806),(-109865712605823007748609)⟩,⟨197999207611480414117007,197999207611480509671569⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨4891194970315100339888,4891194970315119697955⟩,⟨165344482158680360027203,165344482158680379386524⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨62848546611746475273700,62848546611746477535159⟩,⟨87608304193028319162989,87608304193028321429035⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨60211217332885194261733,60211217332885194698921⟩,⟨20392559728711249576884,20392559728711250015559⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨32821332145027340586609,32821332145027340781403⟩,⟨(-10208362023422216794081),(-10208362023422216599907)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨10604379599954858328173,10604379599954858435779⟩,⟨(-13775186768562733726008),(-13775186768562733619108)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨670503850247524710172,670503850247524768155⟩,⟨(-8410392068735543994753),(-8410392068735543936865)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-1708483601763023970924),(-1708483601763023942634)⟩,⟨(-3654488838409734092681),(-3654488838409734064316)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-1483426625867273372545),(-1483426625867273359412)⟩,⟨(-1244058409145101872324),(-1244058409145101859118)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-870970220287502738117),(-870970220287502730885)⟩,⟨(-327879378576148121263),(-327879378576148114005)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-417787452041450052830),(-417787452041450049121)⟩,⟨(-54812863784239481783),(-54812863784239478067)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-121286437610167528941),(-121286437610167527805)⟩,⟨(-1768451027860233993),(-1768451027860232854)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-1421127892883111284395646),(-1421127892883081260561921)⟩,⟨(-27174112190844406582740),(-27174112190814382858387)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-4070651318366993619870238),(-4070651318366892270613047)⟩,⟨398868441130348090661489,398868441130449439564729⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-5912189549695185686689268),(-5912189549694920519510998)⟩,⟨1985016174559761325922479,1985016174560026492639852⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-6013787050003919920588437),(-6013787050003274590850214)⟩,⟨4574111922357468800319669,4574111922358114129743213⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-3794088042580717388778774),(-3794088042579437197583399)⟩,⟨6931573025455472363946258,6931573025456752555183652⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨36903452627064475389609,36903452628873402182070⟩,⟨7407717379131399663362528,7407717379133208590609383⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨3509140610140069635886823,3509140610142389696954578⟩,⟨5357846890956211211182674,5357846890958531272707760⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨4844997647548598189794608,4844997647551252455367899⟩,⟨1913496234846332210471596,1913496234848986476077264⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨3900050039664508739163066,3900050039666202492451964⟩,⟨(-974682457667377706936076),(-974682457665683953882147)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨1962615706845399600841610,1962615706846379014097162⟩,⟨(-2197949600617225622681282),(-2197949600616246209575970)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨365493518989509097577492,365493518989994730209834⟩,⟨(-2015738882181214978550245),(-2015738882180729345913831)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-407764196018744832565502),(-407764196018590240209982)⟩,⟨(-1286549437528144720483240),(-1286549437527990128067738)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-555701825221917825451994),(-555701825221869790643427)⟩,⟨(-633345661155726588142213),(-633345661155678553290873)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-428715768293008459433168),(-428715768292989589302832)⟩,⟨(-245535073780222267806877),(-245535073780203397664015)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-245248980744844023263534),(-245248980744837471235745)⟩,⟨(-72231108415076604727125),(-72231108415070052697743)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-77679067424982137205475),(-77679067424980555819037)⟩,⟨(-12913046105245752584661),(-12913046105244171198515)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-178922584996284074049391),(-178922584996284072065236)⟩,⟨(-53129064467480907116726),(-53129064467480905424621)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-530670515366358875282895),(-530670515366358869346895)⟩,⟨26509756673543401521613,26509756673543406439516⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-577776714281456997066911),(-577776714281456987700331)⟩,⟨649991939513640054873035,649991939513640062233405⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨555407853742482637983687,555407853742482652207655⟩,⟨1926432868039925592136271,1926432868039925604064055⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨3837728009573178575283849,3837728009573178600223675⟩,⟨3177756180693278931431167,3177756180693278955100816⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨9114924504859305182198786,9114924504859305221481988⟩,⟨2732380740313468464351338,2732380740313468503929071⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨14265601276648360704507646,14265601276648360759156041⟩,⟨(-1027670489608983457311143),(-1027670489608983400760832)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨16101782217486186195748426,16101782217486186286626461⟩,⟨(-7742656242690062568548938),(-7742656242690062475785278)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨12825931184486005801405932,12825931184486006109554765⟩,⟨(-14479727488314083111747531),(-14479727488314082803378898)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨5767672729366416870202269,5767672729366418274294283⟩,⟨(-17766962075756876176389348),(-17766962075756874773022189)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-1595586807291679614926815),(-1595586807291674161767343)⟩,⟨(-16338978267515381596472989),(-16338978267515376144095837)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-6319734373496209115708441),(-6319734373496187964864558)⟩,⟨(-11746145442423711665161184),(-11746145442423690514471119)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-7624140000723556925758327),(-7624140000723508155177207)⟩,⟨(-6637554528178651554953966),(-6637554528178602784214460)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-6436678797053475190902793),(-6436678797053406376193435)⟩,⟨(-2855712056832088873319821),(-2855712056832020058399110)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-4068950404077128241917187),(-4068950404077068460966377)⟩,⟨(-850219520033052926553827),(-850219520032993145453025)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-1368392360012153136896013),(-1368392360012129935493218)⟩,⟨(-133297539641276780264436),(-133297539641253578809964)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨4127241148398521577936704,4127241148400642450494320⟩,⟨(-8226431500451062424200987),(-8226431500448941552345759)⟩⟩
lemma checked : cachedMomentRuleBox density1 hk7_1_13 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 7 13) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk7_1_13 (tableDensity true) (fullFactor true 7 13) density1_contains hk7_1_13_contains
noncomputable def atomAnswer : CBox := ⟨⟨6301154528333795246919199,6301154528333795331420927⟩,⟨(-36230113140554655937495759),(-36230113140554655853028310)⟩⟩
lemma atomChecked : tableAtomBox true ha7_1_13 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 7 13) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha7_1_13 7 13 ha7_1_13_contains
 def realAnswer : RBox := ⟨10428395676732316724855903,10428395676734437881915247⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 7 13) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm7_1_1_13
end SharpPlanar.CachedData

end OAI
