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
namespace hm7_0_1_14
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk7_1_14 j i k))
noncomputable def s0_0 : CBox := ⟨⟨188994954,188995072⟩,⟨44088538,44088654⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨383241234,383241589⟩,⟨181770635,181770987⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨243010094,243010783⟩,⟨294143962,294144650⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨2512903,2514033⟩,⟨221206557,221207688⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-76332964),(-76331409)⟩,⟨56891886,56893439⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-28202686),(-28201101)⟩,⟨(-18405507),(-18403931)⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨5181043,5183452⟩,⟨(-9480026),(-9477614)⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨2724548,2727196⟩,⟨2146476,2149128⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-1042992),(-1040404)⟩,⟨641217,643832⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-58031),(-54742)⟩,⟨(-506251),(-502956)⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨243000,245540⟩,⟨75673,78276⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-85463),(-82975)⟩,⟨128340,130850⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-88479),(-86206)⟩,⟨(-60160),(-57880)⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨19559,21147⟩,⟨(-71776),(-70184)⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨41067,41911⟩,⟨(-19265),(-18445)⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨15504,15775⟩,⟨39,303⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-1125529089529836),(-1125529089529812)⟩,⟨2200178175231627,2200178175231652⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-2410687101379645),(-2410687101379597)⟩,⟨5013774756266159,5013774756266206⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-2078571093363055),(-2078571093362995)⟩,⟨4806996604890031,4806996604890096⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-1138968193562943),(-1138968193562853)⟩,⟨2932000498229306,2932000498229399⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-471467999318511),(-471467999318367)⟩,⟨1252248236548562,1252248236548705⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-168905625864115),(-168905625863922)⟩,⟨392942483707241,392942483707437⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-55569118341081),(-55569118340850)⟩,⟨93025621581694,93025621581923⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-16294807723873),(-16294807723581)⟩,⟨16334354220357,16334354220650⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-4044656381469),(-4044656381009)⟩,⟨1764910819098,1764910819555⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-812093608176),(-812093607654)⟩,⟨(-74961941108),(-74961940588)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-119894982831),(-119894982325)⟩,⟨(-101083112308),(-101083111806)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-6778297743),(-6778297077)⟩,⟨(-32849062799),(-32849062129)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨3695358859,3695359498⟩,⟨(-7514891211),(-7514890570)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨2131791412,2131791899⟩,⟨(-1256363078),(-1256362586)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨811079420,811079721⟩,⟨(-81080436),(-81080136)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨199032948,199033059⟩,⟨26300824,26300938⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨189714011479334916973,189714011479334917730⟩,⟨92897914449904904507,92897914449904905252⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨502635868532096829245,502635868532096831190⟩,⟨174838442824941669308,174838442824941671218⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨623107398861084634961,623107398861084637443⟩,⟨62597503300358452902,62597503300358455325⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨508136520577434227639,508136520577434229947⟩,⟨(-121572601658925752908),(-121572601658925750646)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨270352825914806489637,270352825914806491272⟩,⟨(-205342638911309012803),(-205342638911309011178)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨78138271423233804601,78138271423233805559⟩,⟨(-160986934379822867473),(-160986934379822866512)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-3558601067687278435),(-3558601067687277869)⟩,⟨(-78563340144366204099),(-78563340144366203528)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-15313738380243672091),(-15313738380243671807)⟩,⟨(-25364937579041040621),(-25364937579041040335)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-8408870878106535810),(-8408870878106535672)⟩,⟨(-5216687061937053266),(-5216687061937053129)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-3024659433385742642),(-3024659433385742560)⟩,⟨(-400963994084790078),(-400963994084789997)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-887078653878952993),(-887078653878952914)⟩,⟨203073221082886822,203073221082886900⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-241254612242049055),(-241254612242048970)⟩,⟨133417576788702296,133417576788702381⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-67281657062417593),(-67281657062417500)⟩,⟨57508960652523422,57508960652523512⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-20545477982382088),(-20545477982382007)⟩,⟨22874528602421324,22874528602421401⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-6761726571418016),(-6761726571417960)⟩,⟨8775706419552965,8775706419553022⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-1654413475606235),(-1654413475606205)⟩,⟨2301452856682727,2301452856682753⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨59129850169228699844464,59129850169228856965199⟩,⟨50133107056069604506672,50133107056069761619605⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨177498826043998581379496,177498826043998900224371⟩,⟨115922758099974743071972,115922758099975061890384⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨276985813151842716995365,276985813151842955239288⟩,⟨96159239269673740573106,96159239269673978771411⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨309698813297649676520348,309698813297649810751636⟩,⟨(-6361343205358506499095),(-6361343205358372300686)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨243100552060315630022180,243100552060315675109684⟩,⟨(-124346681234502449832468),(-124346681234502404748474)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨111257782288466224707155,111257782288466232764727⟩,⟨(-176003566782218130112299),(-176003566782218122034766)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-4619367950204988325328),(-4619367950204987104296)⟩,⟨(-140443300290678409293817),(-140443300290678408057693)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-52936871529179268033773),(-52936871529179267644164)⟩,⟨(-67175489598680994891898),(-67175489598680994503228)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-46213141701563823946696),(-46213141701563823739819)⟩,⟨(-12197720959920126767556),(-12197720959920126566120)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-23292561050057917123142),(-23292561050057917007495)⟩,⟨9058081182339814202015,9058081182339814316167⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-7179410741478105741554),(-7179410741478105682507)⟩,⟨10214704217884344355853,10214704217884344415442⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-542359727779632930396),(-542359727779632896439)⟩,⟨6066525288445670898898,6066525288445670933521⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨1018191288819602151446,1018191288819602170595⟩,⟨2772602529681236503832,2772602529681236523174⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨913186092700946077657,913186092700946088078⟩,⟨1093657341867815599977,1093657341867815610414⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨517528726179936219109,517528726179936224170⟩,⟨385202454010476495665,385202454010476500710⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨161023143185534076465,161023143185534077966⟩,⟨92293806940751379298,92293806940751380799⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨129253640343970046324594,129253640343980165294644⟩,⟨1275376195779149165938607,1275376195779159284706650⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨822532963881847313134970,822532963881887525631168⟩,⟨3529662591896469576284954,3529662591896509788280873⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨2491694868897312570360612,2491694868897419178048948⟩,⟨4762716876615297682666872,4762716876615404289836447⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨4786239986162845949238588,4786239986163091962850637⟩,⟨4183837001313771452340371,4183837001314017465766737⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨6392671543423851094700465,6392671543424308744735182⟩,⟨1600778803389128931588637,1600778803389586582010015⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨5916166463089454242850546,5916166463090077894649148⟩,⟨(-1891927752550629136304456),(-1891927752550005483652706)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨3258257226633017051136845,3258257226633993577557212⟩,⟨(-4318126252375395814095462),(-4318126252374419287292932)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-30797110460872661876341),(-30797110459872118909295)⟩,⟨(-4395615871018529657257535),(-4395615871017529114500262)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-2105851260033637739941901),(-2105851260033015717978110)⟩,⟨(-2622437460193876519360191),(-2622437460193254497827565)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-2381061158528115118517278),(-2381061158527684201389864)⟩,⟨(-563799885451137313837361),(-563799885450706396817372)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-1577694020640566724910938),(-1577694020640379274108546)⟩,⟨659315400863912927128389,659315400864100378041243⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-659518316800829759359918),(-659518316800772294323805)⟩,⟨949981788720779867874566,949981788720837333049575⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-94160893420355096235665),(-94160893420331651126578)⟩,⟨749796006643329354924295,749796006643352800077635⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨115669691299173092573973,115669691299181403489901⟩,⟨452022488796348301154085,452022488796356612068770⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨122208156617958239355154,122208156617960938007779⟩,⟨220153023861621194260339,220153023861623892902085⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨47156503982260300693241,47156503982260928695402⟩,⟨63790283156255668505135,63790283156256296502328⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-454120752247568063392252),(-454120752247568061165859)⟩,⟨1557533990185944758968878,1557533990185944761301301⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-686673984434226681422725),(-686673984434226674566910)⟩,⟨4674003081322829565388973,4674003081322829572618911⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨910451194197809652256969,910451194197809664234650⟩,⟨7438853209014853985553541,7438853209014853998245645⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨4725239563544076248176840,4725239563544076267125843⟩,⟨8725877890527075003678446,8725877890527075023338883⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨9684120485726036088904481,9684120485726036116397099⟩,⟨7017769473199739404920842,7017769473199739432751520⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨13204794839112078343108045,13204794839112078378369645⟩,⟨1733348396573378966009621,1733348396573379001110346⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨12602772586994421151380655,12602772586994421191662254⟩,⟨(-5456908982503739717334133),(-5456908982503739677629267)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨7329288165969134715479912,7329288165969134766970389⟩,⟨(-11037840333187036183067446),(-11037840333187036131973514)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-133814985160981325180208),(-133814985160981203132449)⟩,⟨(-12126975037564891470224596),(-12126975037564891348188761)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-6056848567869345768456510),(-6056848567869345296484718)⟩,⟨(-8753837489309514370739391),(-8753837489309513898677264)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-8281445530180692335907704),(-8281445530180690289026772)⟩,⟨(-3526247853508714646105896),(-3526247853508712599224883)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-7264599976182466383217026),(-7264599976182458635166876)⟩,⟨733847715990337821477298,733847715990345569476917⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-4849494822658501975211282),(-4849494822658484907089501)⟩,⟨2784018288502098446140672,2784018288502115514242053⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-2595362839844100048586787),(-2595362839844076981268733)⟩,⟨2925413939056621790417276,2925413939056644857750003⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-1112457779038761495962919),(-1112457779038742233366071)⟩,⟨2010206969530092707856506,2010206969530111970476830⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-289923460830632905797513),(-289923460830625569681472)⟩,⟨697715366810017205829681,697715366810024541955945⟩⟩
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
noncomputable def ans : CBox := ⟨⟨5835388470347539047920409,5835388470348351128408138⟩,⟨636234210613076557623497,636234210613888638248140⟩⟩
lemma checked : cachedMomentRuleBox density0 hk7_1_14 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 7 14) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk7_1_14 (tableDensity false) (fullFactor true 7 14) density0_contains hk7_1_14_contains
noncomputable def atomAnswer : CBox := ⟨⟨7342110006070401950002262,7342110006070401971286896⟩,⟨490806249934567835396068,490806249934567856668517⟩⟩
lemma atomChecked : tableAtomBox false ha7_1_14 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 7 14) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha7_1_14 7 14 ha7_1_14_contains
 def realAnswer : RBox := ⟨13177498476417940897922671,13177498476418753199695034⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 7 14) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm7_0_1_14
namespace hm7_1_1_14
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk7_1_14 j i k))
noncomputable def s0_0 : CBox := ⟨⟨31040993,31041023⟩,⟨11737320,11737354⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨60798190,60798263⟩,⟨40080739,40080813⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨33497484,33497619⟩,⟨56404336,56404470⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-5966880),(-5966670)⟩,⟨37154526,37154735⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-14071519),(-14071242)⟩,⟨7074619,7074898⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-4005148),(-4004876)⟩,⟨(-3583953),(-3583679)⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨950941,951337⟩,⟨(-1390520),(-1390122)⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨415361,415791⟩,⟨351324,351756⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-166886),(-166461)⟩,⟨107411,107838⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-14464),(-13911)⟩,⟨(-85151),(-84602)⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨43648,44087⟩,⟨10419,10869⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-13767),(-13328)⟩,⟨24150,24597⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-16790),(-16388)⟩,⟨(-9768),(-9365)⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨2511,2793⟩,⟨(-13255),(-12971)⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨7067,7220⟩,⟨(-4151),(-3997)⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨2777,2835⟩,⟨(-278),(-224)⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-317659214575807),(-317659214575790)⟩,⟨218371085761070,218371085761088⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-687935328437205),(-687935328437183)⟩,⟨510745637858250,510745637858276⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-601371973025024),(-601371973024996)⟩,⟨510336089870269,510336089870295⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-327786852843664),(-327786852843633)⟩,⟨325118592983371,325118592983403⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-127716091521591),(-127716091521553)⟩,⟨144098942708816,144098942708853⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-39914605044296),(-39914605044253)⟩,⟨46396833257255,46396833257298⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-11069572744262),(-11069572744216)⟩,⟨11072198484034,11072198484081⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-2828447673043),(-2828447672986)⟩,⟨1890664218249,1890664218305⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-647070586519),(-647070586438)⟩,⟨168993194872,168993194955⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-124978982839),(-124978982744)⟩,⟨(-27166086841),(-27166086745)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-17893270851),(-17893270755)⟩,⟨(-18353728795),(-18353728698)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-668020052),(-668019923)⟩,⟨(-5696309205),(-5696309077)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨775713385,775713516⟩,⟨(-1274684825),(-1274684701)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨412904080,412904184⟩,⟨(-190283103),(-190282998)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨152571523,152571590⟩,⟨1929054,1929122⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨36716701,36716736⟩,⟨9395844,9395880⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨25487657661208459608,25487657661208459856⟩,⟨40308281005111965094,40308281005111965343⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨75659027276139658882,75659027276139659512⟩,⟨93536652326355565065,93536652326355565689⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨111018567527353123950,111018567527353124727⟩,⟨87384861958977489844,87384861958977490619⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨109245533830417566724,109245533830417567415⟩,⟨39728910515831124334,39728910515831125022⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨72979628717480371350,72979628717480371814⟩,⟨(-3698808674000256411),(-3698808674000255946)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨31799185989348140677,31799185989348140932⟩,⟨(-18170283275412682782),(-18170283275412682527)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨7741071312549127830,7741071312549127970⟩,⟨(-13124491899490076946),(-13124491899490076805)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-28957320609843682),(-28957320609843610)⟩,⟨(-5495433934772729957),(-5495433934772729885)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-895181662007143906),(-895181662007143864)⟩,⟨(-1551783683420459259),(-1551783683420459216)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-456026374025182814),(-456026374025182774)⟩,⟨(-303811177445990972),(-303811177445990933)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-159195159006939234),(-159195159006939193)⟩,⟨(-34159094950136183),(-34159094950136142)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-48566281120235648),(-48566281120235601)⟩,⟨3626329902453314,3626329902453362⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-14629695063189645),(-14629695063189597)⟩,⟨4208167156630232,4208167156630281⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-4663605867136910),(-4663605867136866)⟩,⟨2094847907551682,2094847907551725⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-1559606781564845),(-1559606781564812)⟩,⟨878956301505538,878956301505570⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-382574397229426),(-382574397229405)⟩,⟨238869775309108,238869775309133⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨5827910789026758919042,5827910789026890879724⟩,⟨25250673846392379878501,25250673846392511839992⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨23858591958589775630034,23858591958590043204544⟩,⟨65622081405441324390380,65622081405441591967641⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨52282825460839330257244,52282825460839529821470⟩,⟨77968942058098768310427,77968942058098967879372⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨77634201083836328801343,77634201083836440900180⟩,⟨55697754517892399242941,55697754517892511345150⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨80103356575808361005495,80103356575808398412000⟩,⟨12802623265394759358952,12802623265394796765781⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨55541737459963454282285,55541737459963460771416⟩,⟨(-22949082372587014387931),(-22949082372587007900825)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨21482565051686665088014,21482565051686665916280⟩,⟨(-33500695584905847977697),(-33500695584905847150927)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-1649820105719502836502),(-1649820105719502655582)⟩,⟨(-23812829055406199990827),(-23812829055406199809797)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-8618813801323447640112),(-8618813801323447565613)⟩,⟨(-9916105685728520189384),(-9916105685728520114358)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-6595777350673719792815),(-6595777350673719752072)⟩,⟨(-1500478257444522061238),(-1500478257444522020367)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-3112834579112273011540),(-3112834579112272990528)⟩,⟨1209717621984813373015,1209717621984813393970⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-1003194127460604621075),(-1003194127460604608914)⟩,⟨1274678425451384527017,1274678425451384539115⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-169722567586534860445),(-169722567586534853541)⟩,⟨770640807346788296678,770640807346788303565⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨50687709755550584263,50687709755550588058⟩,⟨380077665564070560241,380077665564070564036⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨63294855033606148222,63294855033606150088⟩,⟨163068857384175855599,163068857384175857471⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨23802364518741511202,23802364518741511767⟩,⟨44594681938573037772,44594681938573038338⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨63871679336487524947968,63871679336495839911839⟩,⟨416313184302314558655701,416313184302322873656217⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨326000440853679708832179,326000440853712756000413⟩,⟨1170792317270583515100772,1170792317270616562363333⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨897848165460145807383761,897848165460233434609259⟩,⟨1632586115407552416119785,1632586115407640043448029⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨1688852801817773539169746,1688852801817975790388794⟩,⟨1524691885471207850449164,1524691885471410101710329⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨2292882403023969267122576,2292882403024345558604241⟩,⟨722451339635261929881802,722451339635638221288153⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨2230318202095552774261089,2230318202096065559995001⟩,⟨(-479502880672257979660884),(-479502880671745194109721)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨1394247972265430134328982,1394247972266232896567307⟩,⟨(-1433549599951879012987355),(-1433549599951076250848578)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨235321913644144801192611,235321913644966920720886⟩,⟨(-1634052354505648993582953),(-1634052354504826874018391)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-611469066563733615581488),(-611469066563222925183959)⟩,⟨(-1140368409206601937977267),(-1140368409206091247488944)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-859972533174573015298662),(-859972533174219603958138)⟩,⟨(-434069497673400220705759),(-434069497673046809340917)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-676661097894101595079760),(-676661097893948050325892)⟩,⟨64949528114122714827785,64949528114276259562002⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-376097052940829289807118),(-376097052940782284820329)⟩,⟨254267123628052471310252,254267123628099476271645⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-150441400788818008811638),(-150441400788798856350386)⟩,⟨244157062925746991617627,244157062925766144070749⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-35897883045328473029782),(-35897883045321691270298)⟩,⟨165906982257413727347584,165906982257420509107197⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨2355126097519606531674,2355126097521806845347⟩,⟨88387814927375226009844,88387814927377426325362⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨4121994392337017270591,4121994392337529077311⟩,⟨27012373437296258877187,27012373437296770684746⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-11285389189254200848057),(-11285389189254200425440)⟩,⟨46895908406233219135594,46895908406233219642165⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨14369852569932223019868,14369852569932224242763⟩,⟨136873466675698373548091,136873466675698375059479⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨177732972781534273806211,177732972781534275663005⟩,⟨140066253804231232868859,140066253804231235269943⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨494335002698003029910760,494335002698003033184186⟩,⟨(-178346246189006252333098),(-178346246189006248512750)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨764179474605318816970513,764179474605318823331777⟩,⟨(-1073760040776778358799683),(-1073760040776778352179778)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨528131267607125764694100,528131267607125775161984⟩,⟨(-2488114115532016164185235),(-2488114115532016153884892)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-632474590018212579378768),(-632474590018212564701422)⟩,⟨(-3816360593097225765455751),(-3816360593097225751368204)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-2564845507397335030290183),(-2564845507397335004771508)⟩,⟨(-4168292495445778813489128),(-4168292495445778788394128)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-4400733766565233759337304),(-4400733766565233673878263)⟩,⟨(-3075868322661696842310410),(-3075868322661696756818032)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-5161637242396288048827701),(-5161637242396287677161622)⟩,⟨(-979510088269691433716052),(-979510088269691061783596)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-4547939305434490304239592),(-4547939305434488646100358)⟩,⟨1087406419463578733952682,1087406419463580392291038⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-3080701963639573417446166),(-3080701963639567102184992)⟩,⟨2298480631443345455490609,2298480631443351770756148⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-1563671209862405035796141),(-1563671209862391101974255)⟩,⟨2492506858562804859424484,2492506858562818793175493⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-520505542992144880307815),(-520505542992126033709175)⟩,⟨1999525442142404202811666,1999525442142423049334196⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-46991362604229831019659),(-46991362604214085234056)⟩,⟨1225597997684529947676807,1225597997684545693410863⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨29670141727265817365175,29670141727271815564606⟩,⟨405740639440395003369219,405740639440401001551306⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-2300155728893364014526737),(-2300155728892696969129324)⟩,⟨(-767910174005938568469308),(-767910174005271522929062)⟩⟩
lemma checked : cachedMomentRuleBox density1 hk7_1_14 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 7 14) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk7_1_14 (tableDensity true) (fullFactor true 7 14) density1_contains hk7_1_14_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-9601220777168987193221325),(-9601220777168987165387573)⟩,⟨(-641823557606742581797292),(-641823557606742553979473)⟩⟩
lemma atomChecked : tableAtomBox true ha7_1_14 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 7 14) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha7_1_14 7 14 ha7_1_14_contains
 def realAnswer : RBox := ⟨(-11901376506062351307748062),(-11901376506061684034516897)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 7 14) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm7_1_1_14
namespace hm7_0_1_15
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk7_1_15 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-85857823),(-85857732)⟩,⟨(-69261986),(-69261899)⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-153100262),(-153100022)⟩,⟨(-187151069),(-187150828)⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-56829253),(-56828899)⟩,⟨(-211202827),(-211202477)⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨49145575,49146146⟩,⟨(-117993339),(-117992767)⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨53637398,53638336⟩,⟨(-14421858),(-14420921)⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨12000072,12001140⟩,⟨15824554,15825618⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-4644437),(-4643163)⟩,⟨4464197,4465481⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-1252340),(-1250657)⟩,⟨(-1676184),(-1674499)⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨701776,703311⟩,⟨(-246056),(-244510)⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-19659),(-17674)⟩,⟨309231,311216⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-143701),(-142049)⟩,⟨(-66913),(-65229)⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨57978,59434⟩,⟨(-75639),(-74163)⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨51004,52404⟩,⟨38553,39956⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-14286),(-13294)⟩,⟨42798,43790⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-25900),(-25371)⟩,⟨11046,11561⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-9697),(-9523)⟩,⟨(-212),(-41)⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨1125420768697313,1125420768697335⟩,⟨(-337643414055130),(-337643414055110)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨2518287573345705,2518287573345740⟩,⟨(-839211786315510),(-839211786315477)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨2343744824800898,2343744824800939⟩,⟨(-916279581312938),(-916279581312892)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨1390221586506365,1390221586506425⟩,⟨(-631614162313072),(-631614162313013)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨590315133435342,590315133435414⟩,⟨(-290950965116309),(-290950965116239)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨193510608647374,193510608647464⟩,⟨(-90516450079671),(-90516450079580)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨52009525420735,52009525420874⟩,⟨(-18066495238950),(-18066495238811)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨11849576325186,11849576325368⟩,⟨(-1440210496658),(-1440210496479)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨2268999785126,2268999785331⟩,⟨507047664847,507047665052⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨337713372019,337713372322⟩,⟨277704552061,277704552363⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨25953158849,25953159184⟩,⟨81385781877,81385782210⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-5929385585),(-5929385276)⟩,⟨17548836287,17548836597⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-3825383026),(-3825382686)⟩,⟨2689990655,2689990992⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-1391215672),(-1391215368)⟩,⟨75992514,75992818⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-431510477),(-431510264)⟩,⟨(-163529608),(-163529399)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-95010947),(-95010863)⟩,⟨(-62924848),(-62924762)⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-4245362736602134796),(-4245362736602134510)⟩,⟨(-82204262797393191853),(-82204262797393191557)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-36504796343797014590),(-36504796343797013877)⟩,⟨(-204877167715937168754),(-204877167715937168021)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-100351066011107915371),(-100351066011107914484)⟩,⟨(-225245712334922168561),(-225245712334922167657)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-144088122528420538796),(-144088122528420537900)⟩,⟨(-149763917073961958815),(-149763917073961957915)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-127331152291976112190),(-127331152291976111423)⟩,⟨(-50036782434556513937),(-50036782434556513176)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-72768038856336959500),(-72768038856336958981)⟩,⟨8302621001871284748,8302621001871285258⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-26426889909066005104),(-26426889909066004821)⟩,⟨19352614111913987849,19352614111913988130⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-5098342077644593459),(-5098342077644593328)⟩,⟨11495404951771587660,11495404951771587789⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨340517193766395528,340517193766395594⟩,⟨4269020781527184422,4269020781527184485⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨678489709574777802,678489709574777853⟩,⟨1162825692733424388,1162825692733424439⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨322832484196934182,322832484196934232⟩,⟨251171050622916141,251171050622916191⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨118015836147362272,118015836147362325⟩,⟨44171867570597235,44171867570597286⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨40663204532286070,40663204532286116⟩,⟨5559537031579029,5559537031579078⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨14418251915215504,14418251915215550⟩,⟨(-175644166251500),(-175644166251454)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨5210616720043182,5210616720043214⟩,⟨(-517492932837009),(-517492932836975)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨1332199295456858,1332199295456879⟩,⟨(-185237925463599),(-185237925463575)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨9456642749991181440198,9456642749991222503863⟩,⟨(-23302934891954398597060),(-23302934891954357529261)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨17579194563762741640889,17579194563762834012458⟩,⟨(-66714835117932807399675),(-66714835117932715017425)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨671206313552470517694,671206313552561678184⟩,⟨(-96012785905421587420361),(-96012785905421496249507)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-35760613753896191052945),(-35760613753896141467564)⟩,⟨(-95919518669410507724168),(-95919518669410458135515)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-66816288184373321281099),(-66816288184373306684230)⟩,⟨(-62226161571020880450411),(-62226161571020865859570)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-69179550516893071528138),(-69179550516893069112475)⟩,⟨(-14125242825036149710278),(-14125242825036147303817)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-44374137662450715301795),(-44374137662450714810883)⟩,⟨19351550554266796137788,19351550554266796627065⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-14569377764409006969737),(-14569377764409006837729)⟩,⟨26194705696334355905934,26194705696334356040642⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨2649212886884651482520,2649212886884651550935⟩,⟨16844520518859821921172,16844520518859821991223⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨6532074256725720013876,6532074256725720058784⟩,⟨6301844560123150997578,6301844560123151042310⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨4552001853743309484127,4552001853743309511993⟩,⟨745693844663285032770,745693844663285060143⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨2124789025138158060104,2124789025138158075730⟩,⟨(-842684641759329891092),(-842684641759329875602)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨755776941160500606692,755776941160500614806⟩,⟨(-831456143194210069172),(-831456143194210061043)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨204476142898175678041,204476142898175682192⟩,⟨(-508313466896824218021),(-508313466896824213829)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨34669953622913302529,34669953622913304472⟩,⟨(-247548518219294375180),(-247548518219294373210)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨1125941409755158138,1125941409755158710⟩,⟨(-72179562502580598314),(-72179562502580597732)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨341462073047489281294298,341462073047492474369916⟩,⟨(-95368559923551246025111),(-95368559923548052905693)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨924629977419050856905005,924629977419063254822971⟩,⟨(-394024415651272343910763),(-394024415651259945890701)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨1183160373038880414615995,1183160373038912043015917⟩,⟨(-919963568402181284881932),(-919963568402149656397972)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨906484398472887984216935,906484398472957438108795⟩,⟨(-1539595245307585027209228),(-1539595245307515573342548)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨93017710723363566049131,93017710723483975684069⟩,⟨(-1868813304730480626685779),(-1868813304730360217237610)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-881396501804454891128827),(-881396501804269670058928)⟩,⟨(-1552476560812928761610677),(-1552476560812743540773226)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-1434861970885527796358903),(-1434861970885228728883337)⟩,⟨(-652703482347399347946750),(-652703482347100280506679)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-1262843047547619255055204),(-1262843047547346182193690)⟩,⟨309259654594407501091667,309259654594680574076888⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-608914794792803861510209),(-608914794792605686197348)⟩,⟨806214661946000748246979,806214661946198923669255⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨21678041208175830128345,21678041208310762041187⟩,⟨746217862793027194619363,746217862793162126524887⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨329246857389426003453793,329246857389477412967685⟩,⟨414714593059091677506224,414714593059143086960901⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨344726261037508046173051,344726261037528383107351⟩,⟨113924571791689868516281,113924571791710205419373⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨236455841105535022139895,236455841105542903226246⟩,⟨(-41453250466360875032925),(-41453250466352993947743)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨126960869457691717975843,126960869457694251555419⟩,⟨(-79174507338983254465350),(-79174507338980720877284)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨55458752830157577916307,55458752830158338428209⟩,⟨(-59416260310926010408475),(-59416260310925249888935)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨14887403944506464600958,14887403944506633159408⟩,⟨(-20939337477025822418216),(-20939337477025653856930)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨380913261407918118069893,380913261407918118632771⟩,⟨89678584789362712126918,89678584789362712660941⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨1137429009131813006791152,1137429009131813008535966⟩,⟨104104262203153804578755,104104262203153806223847⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨1790813814896417602769025,1790813814896417605859619⟩,⟨(-326905669009130190868243),(-326905669009130187953418)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨2054714747037065076522097,2054714747037065081350495⟩,⟨(-1291548770648036649612460),(-1291548770648036644941372)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨1553568309744065920925426,1553568309744065927739556⟩,⟨(-2508815730101348730048398),(-2508815730101348723293933)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨161508379899122699573420,161508379899122708106825⟩,⟨(-3316836053230556847357406),(-3316836053230556838757058)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-1663882543275355761969192),(-1663882543275355752382868)⟩,⟨(-3039483124118879368791887),(-3039483124118879359043604)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-2999096805720201267976760),(-2999096805720201255142037)⟩,⟨(-1571851780448766900447826),(-1571851780448766887528044)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-3115893668334140138109097),(-3115893668334140106006428)⟩,⟨394735018290883425975372,394735018290883458067684⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-2078513888529846515394049),(-2078513888529846398589753)⟩,⟨1866682870469964404629237,1866682870469964521404372⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-626834870548446294774928),(-626834870548445709208370)⟩,⟨2309006594951153052740471,2309006594951153638308392⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨482294244600321338024555,482294244600323449063275⟩,⟨1903534675144778718317129,1903534675144780829366504⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨951921490680025872675109,951921490680030308847297⟩,⟨1183862033689129533602326,1183862033689133969774671⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨905807681375776082049987,905807681375781780403916⟩,⟨571397726506458600169246,571397726506464298514578⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨596942288726780607107851,596942288726785719148595⟩,⟨209675706472296104943315,209675706472301216975970⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨203463639272134373621113,203463639272136669460611⟩,⟨46294521929866339380606,46294521929868635217406⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-10224457718115574257278),(-10224457717877012646772)⟩,⟨(-1417016479381637489116460),(-1417016479381398927561885)⟩⟩
lemma checked : cachedMomentRuleBox density0 hk7_1_15 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 7 15) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk7_1_15 (tableDensity false) (fullFactor true 7 15) density0_contains hk7_1_15_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-82909349467710732378644),(-82909349467710725741982)⟩,⟨(-1790789712273786050633886),(-1790789712273786043991224)⟩⟩
lemma atomChecked : tableAtomBox false ha7_1_15 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 7 15) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha7_1_15 7 15 ha7_1_15_contains
 def realAnswer : RBox := ⟨(-93133807185826406635922),(-93133807185587638388754)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 7 15) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm7_0_1_15
namespace hm7_1_1_15
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk7_1_15 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-12990749),(-12990719)⟩,⟨(-13677427),(-13677402)⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-21545141),(-21545088)⟩,⟨(-35483611),(-35483556)⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-4063021),(-4062949)⟩,⟨(-37386106),(-37386028)⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨11647147,11647259⟩,⟨(-18360130),(-18360018)⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨9152611,9152787⟩,⟨(-806917),(-806746)⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨1510888,1511075⟩,⟨2785512,2785699⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-789675),(-789460)⟩,⟨620506,620722⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-187193),(-186915)⟩,⟨(-269486),(-269206)⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨112883,113142⟩,⟨(-42262),(-42000)⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-460),(-123)⟩,⟨52502,52839⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-26054),(-25763)⟩,⟨(-10073),(-9774)⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨9501,9765⟩,⟨(-14347),(-14079)⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨9749,10001⟩,⟨6315,6571⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-1956),(-1775)⟩,⟨7927,8108⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-4472),(-4369)⟩,⟨2405,2505⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-1747),(-1704)⟩,⟨131,169⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨179462100039869,179462100039885⟩,⟨37169006599343,37169006599359⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨403435323137050,403435323137069⟩,⟨66061775103932,66061775103950⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨377556751461597,377556751461618⟩,⟨32666558577796,32666558577816⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨224094605615208,224094605615232⟩,⟨(-1678352692814),(-1678352692791)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨94285437231758,94285437231784⟩,⟨(-8780448722275),(-8780448722252)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨30295846816394,30295846816417⟩,⟨(-4057716626778),(-4057716626751)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨7923886597115,7923886597150⟩,⟨(-696178794803),(-696178794771)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨1754903358456,1754903358496⟩,⟨134166802391,134166802432⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨327750527738,327750527783⟩,⟨129281156952,129281156998⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨47274438573,47274438635⟩,⟨49664539845,49664539905⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨2927062120,2927062189⟩,⟨13652665518,13652665587⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-1269839714),(-1269839644)⟩,⟨2901883371,2901883438⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-721813358),(-721813281)⟩,⟨416411618,416411691⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-255729065),(-255728997)⟩,⟨(-11802839),(-11802772)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-76838017),(-76837966)⟩,⟨(-39468718),(-39468664)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-16397014),(-16396987)⟩,⟨(-13926592),(-13926564)⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨8909530700159376990,8909530700159377092⟩,⟨(-16308732145412915072),(-16308732145412914970)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨17432084872268142015,17432084872268142255⟩,⟨(-43695994097672585194),(-43695994097672584954)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨8182036292486490947,8182036292486491239⟩,⟨(-55027289111132304380),(-55027289111132304087)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-8387399771432654863),(-8387399771432654586)⟩,⟨(-45471210363526393072),(-45471210363526392794)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-16562163591861044290),(-16562163591861044064)⟩,⟨(-24346742277551115794),(-24346742277551115571)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-13250924497411087186),(-13250924497411087047)⟩,⟨(-7004459684288014526),(-7004459684288014387)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-6336290556500014731),(-6336290556500014656)⟩,⟨341645534847686454,341645534847686528⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-1904168492943695449),(-1904168492943695411)⟩,⟨1346383896716480314,1346383896716480354⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-310900480584808076),(-310900480584808049)⟩,⟨710150076237713969,710150076237713995⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨17470739447810166,17470739447810193⟩,⟨241139162858353635,241139162858353660⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨33350185175382375,33350185175382404⟩,⟨65139605196987089,65139605196987121⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨15686359790971620,15686359790971652⟩,⟨15793613805702171,15793613805702204⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨5968715519933353,5968715519933385⟩,⟨3767748277400086,3767748277400118⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨2203893804806859,2203893804806890⟩,⟨943896249420805,943896249420832⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨807812084154525,807812084154550⟩,⟨251756495931770,251756495931794⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨207307336449504,207307336449521⟩,⟨53203173202967,53203173202983⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨7190802595922630246110,7190802595922664734584⟩,⟨(-4355116750226460741204),(-4355116750226426253155)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨17816410971034065056211,17816410971034142576201⟩,⟨(-14103836961257909930857),(-14103836961257832411984)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨18676549247698478516631,18676549247698554891488⟩,⟨(-24416876010836479123524),(-24416876010836402749744)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨8908999969255594868932,8908999969255636278739⟩,⟨(-30291608753774405237892),(-30291608753774363828423)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-5112872926677046139072),(-5112872926677034047906)⟩,⟨(-26637096635749616853712),(-26637096635749604761928)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-13951218111430726919700),(-13951218111430725001402)⟩,⟨(-14852744694269933289273),(-14852744694269931370052)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-13458397081051320171256),(-13458397081051319837126)⟩,⟨(-2614304562464037305567),(-2614304562464036971278)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-7477214581428537922807),(-7477214581428537861524)⟩,⟨3750845633121972720167,3750845633121972781185⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-2001679061240038522722),(-2001679061240038497153)⟩,⟨4238144041388491453115,4238144041388491478533⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨509088309989832185274,509088309989832201176⟩,⟨2403226204148996404524,2403226204148996420444⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨902854111824311371767,902854111824311381449⟩,⟨840884720911528522931,840884720911528532656⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨596612887926397538286,596612887926397543788⟩,⟨120957457804852850238,120957457804852855752⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨289763108621261526209,289763108621261529126⟩,⟨(-78430278618430336279),(-78430278618430333366)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨119560453697801573135,119560453697801574659⟩,⟨(-86300427705585048498),(-86300427705585046976)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨43653124083628795209,43653124083628795937⟩,⟨(-51843367665455574290),(-51843367665455573563)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨10703230056620685179,10703230056620685404⟩,⟨(-16492517896065441907),(-16492517896065441682)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨110439108207403180289954,110439108207405804207397⟩,⟨(-37038862894402444342079),(-37038862894399820432988)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨304153606789879995213285,304153606789890184234696⟩,⟨(-145223235041030042031796),(-145223235041019853030684)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨403413600727681328250471,403413600727707325764483⟩,⟨(-327360760585466531068366),(-327360760585440533572299)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨333251056921527883450289,333251056921584982533038⟩,⟨(-545796276472803434025801),(-545796276472746334939590)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨74690353222835537930608,74690353222934541582815⟩,⟨(-678508970182215200934955),(-678508970182116197244281)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-266520756566817958168882),(-266520756566665664061327)⟩,⟨(-599090969362919835393183),(-599090969362767541232696)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-496197766974526305640803),(-496197766974280453920078)⟩,⟨(-305603668421085760606238),(-305603668420839908871875)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-486351340629903179921337),(-486351340629678801866197)⟩,⟨43948967991693962959341,43948967991918340990041⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-287195546714962819941193),(-287195546714800118986800)⟩,⟨261980877779715822184575,261980877779878523115667⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-60106204929706227928030),(-60106204929595563763117)⟩,⟨287716266701984047347562,287716266702094711513248⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨76283692460849646046502,76283692460891756893438⟩,⟨196218512504380589171059,196218512504422700029093⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨110040051677860133149695,110040051677876768010216⟩,⟨90586028030055200857448,90586028030071835723867⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨88185530898731449512139,88185530898737887720486⟩,⟨22876804517172968871705,22876804517179407080354⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨54193521378948676451217,54193521378950743888940⟩,⟨(-5106694488070833759569),(-5106694488068766323313)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨26909351423126868585061,26909351423127488660588⟩,⟨(-9509900205057233744550),(-9509900205056613670345)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨7899894564306548162509,7899894564306685531314⟩,⟨(-3988921671310388147007),(-3988921671310250778682)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨11438657653733504562813,11438657653733504683183⟩,⟨2124865672017844001325,2124865672017844099457⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨32850077574738662744018,32850077574738663102014⟩,⟨(-5277553854924315790939),(-5277553854924315508472)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨31401574559370735083304,31401574559370735666759⟩,⟨(-45101757429585693794846),(-45101757429585693343968)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-51460560177448896211600),(-51460560177448895258281)⟩,⟨(-117818593984590257198138),(-117818593984590256364624)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-278150686400732858522784),(-278150686400732856891007)⟩,⟨(-168794250649721025320650),(-168794250649721023733329)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-629454561631619084376805),(-629454561631619081873249)⟩,⟨(-80405709471777584862663),(-80405709471777582295497)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-944572814624993939722914),(-944572814624993936315535)⟩,⟨247817909678937591363156,247817909678937594930925⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-992309934588904805334990),(-992309934588904798871823)⟩,⟨762263241245089292239477,762263241245089298784947⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-660870311226476966381744),(-660870311226476944172123)⟩,⟨1223924803669196621422323,1223924803669196643600797⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-84286398613401288096124),(-84286398613401196613652)⟩,⟨1376561123342844805319890,1376561123342844896717718⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨451931574113335161039943,451931574113335635504660⟩,⟨1158099251191725643553670,1158099251191726117978025⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨733182554906681215198507,733182554906682935763991⟩,⟨728791919619071176642926,728791919619072897217327⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨734940360570916453022984,734940360570920074332897⟩,⟨314399143369007832231938,314399143369011453567032⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨563451448638664239666057,563451448638668895102666⟩,⟨51840833570730023533775,51840833570734678994411⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨334938933086953477323308,334938933086957656008222⟩,⟨(-43566308256799519162551),(-43566308256795340463615)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨109050451154090077454462,109050451154091954641239⟩,⟨(-27044764731028538131954),(-27044764731026660941470)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-105296669580150802617989),(-105296669579954850515464)⟩,⟨586262271539929180189157,586262271540125132268142⟩⟩
lemma checked : cachedMomentRuleBox density1 hk7_1_15 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 7 15) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk7_1_15 (tableDensity true) (fullFactor true 7 15) density1_contains hk7_1_15_contains
noncomputable def atomAnswer : CBox := ⟨⟨108419918534698641354899,108419918534698650033611⟩,⟨2341801931434950980603908,2341801931434950989290466⟩⟩
lemma atomChecked : tableAtomBox true ha7_1_15 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 7 15) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha7_1_15 7 15 ha7_1_15_contains
 def realAnswer : RBox := ⟨3123248954547738736910,3123248954743899518147⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 7 15) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm7_1_1_15
end SharpPlanar.CachedData

end OAI
