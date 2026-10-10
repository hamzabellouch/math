import OAI.Analysis.PlanarPacking.Certificate.KernelValues10
import OAI.Analysis.PlanarPacking.Certificate.TableDensityValues
import OAI.Analysis.PlanarPacking.TableRuleBridge
import OAI.Analysis.PlanarPacking.Certificate.AtomKernels

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_9_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (kernel9_0 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨9724426581,9724426597⟩,⟨(-8084170276),(-8084170260)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨20038264554,20038264570⟩,⟨(-14465940369),(-14465940351)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨15611023347,15611023366⟩,⟨(-8102298874),(-8102298850)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨6806410987,6806411008⟩,⟨(-1628624614),(-1628624594)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨1731470332,1731470350⟩,⟨230662380,230662399⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨234037624,234037646⟩,⟨178979280,178979300⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨7749283,7749305⟩,⟨35339764,35339787⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-2238218),(-2238192)⟩,⟨2721369,2721390⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-292772),(-292746)⟩,⟨(-67723),(-67701)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-1270),(-1247)⟩,⟨(-25008),(-24984)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨2221,2242⟩,⟨(-461),(-439)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨66,86⟩,⟨228,248⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-44),(-20)⟩,⟨6,27⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-16),2⟩,⟨(-16),0⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),2⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨1033736294296294059,1033736294296294079⟩,⟨530603521805111454,530603521805111474⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨2416084454535359941,2416084454535359965⟩,⟨1016484680209096151,1016484680209096176⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨2399436998215053158,2399436998215053187⟩,⟨619444654633215153,619444654633215179⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨1494756500887448205,1494756500887448233⟩,⟨75798662223984614,75798662223984639⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨627427146835454499,627427146835454520⟩,⟨(-119348613173410299),(-119348613173410275)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨183304876973936103,183304876973936121⟩,⟨(-86151326967879859),(-86151326967879837)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨38694928261669773,38694928261669792⟩,⟨(-31203676032389216),(-31203676032389192)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨6274424181989246,6274424181989267⟩,⟨(-7623276018951117),(-7623276018951098)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨863965959839915,863965959839936⟩,⟨(-1436290221225962),(-1436290221225939)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨116560589612226,116560589612245⟩,⟨(-232100331753818),(-232100331753800)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨17769133194845,17769133194864⟩,⟨(-35399255462183),(-35399255462163)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨3276285883601,3276285883620⟩,⟨(-5540549025091),(-5540549025071)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨728093578472,728093578492⟩,⟨(-953248554945),(-953248554925)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨191172929934,191172929952⟩,⟨(-189670274805),(-189670274785)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨56406098688,56406098705⟩,⟨(-43951777316),(-43951777300)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨12970794309,12970794326⟩,⟨(-8733057439),(-8733057422)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨44910965140247787380529,44910965140247937662639⟩,⟨(-63064474855885816397906),(-63064474855885666106696)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨96602912070968853450499,96602912070969136240266⟩,⟨(-169290711910089017655691),(-169290711910088734839421)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨72546706883103761900199,72546706883103946869269⟩,⟨(-217050890761973439183865),(-217050890761973254178756)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨7497067943622186433080,7497067943622268039011⟩,⟨(-189808046288286351265941),(-189808046288286269637703)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-38418436282191317149946),(-38418436282191296718680)⟩,⟨(-116226359280661839316412),(-116226359280661818879367)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-43124659426158629354491),(-43124659426158626609592)⟩,⟨(-47256855210856821235189),(-47256855210856818492895)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-26158867595240773223957),(-26158867595240772980857)⟩,⟨(-10032476926038611301803),(-10032476926038611062137)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-10530425523346500924277),(-10530425523346500883362)⟩,⟨1288325673258627954350,1288325673258627994217⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-2944325069598004061812),(-2944325069598004048444)⟩,⟨2055913958302934214382,2055913958302934227710⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-536486546844704226935),(-536486546844704222057)⟩,⟨991794980148743657523,991794980148743662481⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-24654967275820332462),(-24654967275820330693)⟩,⟨341451464634375261461,341451464634375263272⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨30564357256991568109,30564357256991568764⟩,⟨100473332658108548533,100473332658108549197⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨19036809306551297450,19036809306551297703⟩,⟨28054336837996666347,28054336837996666600⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨8648162692864046797,8648162692864046905⟩,⟨7997452133501145902,7997452133501146010⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨3510903137312726710,3510903137312726762⟩,⟨2369050889170441008,2369050889170441058⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨940258153721123223,940258153721123250⟩,⟨534903677138701287,534903677138701311⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨23970232659016335688838577,23970232659016950788527948⟩,⟨(-55805092339568703539036811),(-55805092339568088444031897)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨46773321218604349909368632,46773321218606372947518232⟩,⟨(-154339184848419968027899698),(-154339184848417945004976200)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨15570589853484593700837338,15570589853488371605647403⟩,⟨(-210691857911325331007226239),(-210691857911321553129299655)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-51285911422267924249457756),(-51285911422261760765796305)⟩,⟨(-201726920405024142310530482),(-201726920405017978857390668)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-104466008636042344622393544),(-104466008636031148898514155)⟩,⟨(-134455478237686874584598741),(-134455478237675678875093466)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-109791961470559361431007264),(-109791961470544347893933098)⟩,⟨(-50168151564701009730045142),(-50168151564685996192941474)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-75576065333119772541247484),(-75576065333106676832790592)⟩,⟨7843705473191249722898080,7843705473204345438198476⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-34027746209980930025923080),(-34027746209972905958703456)⟩,⟨26786431584196456107203483,26786431584204480180118483⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-7360996021305316846739472),(-7360996021300211904077305)⟩,⟨21600894026850919595585752,21600894026856024539244897⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨2687937810548788266515473,2687937810550805473976828⟩,⟨11060128329410622655426049,11060128329412639862281346⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨3855029401321375561893171,3855029401321887885533547⟩,⟨3937749588202245319591937,3937749588202757642546031⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨2523330966547991494441905,2523330966548143575191392⟩,⟨816663063222353054811112,816663063222505135333060⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨1281898284306960600340648,1281898284307003236820904⟩,⟨(-121670398119595666733683),(-121670398119553030280539)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨574332519470375755821019,574332519470386847886028⟩,⟨(-249817281090518144490149),(-249817281090507052406511)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨232011895637753468473856,232011895637756430550466⟩,⟨(-167217840279298201702272),(-167217840279295239607946)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨61459285452539406963290,61459285452540034057532⟩,⟨(-55292490137629779459179),(-55292490137629152358562)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨110666656397718711796665405,110666656397718714121426710⟩,⟨(-1464901816835560494955085567),(-1464901816835560492473279624)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-199947743550308376133229999),(-199947743550308369235228514)⟩,⟨(-4068071205076611369676858519),(-4068071205076611362311363670)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-1680356302148494371635844750),(-1680356302148494359996219473)⟩,⟨(-5617526856717998470949277336),(-5617526856717998458726865788)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-3951361293333218560285784771),(-3951361293333218544087776849)⟩,⟨(-5448346839915247982085658330),(-5448346839915247965435999315)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-5772051077033485083028515508),(-5772051077033485063170192481)⟩,⟨(-3488584765088008676281093189),(-3488584765088008656258391190)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-5990044408097846889993102280),(-5990044408097846868661262837)⟩,⟨(-620796666740724650326236271),(-620796666740724629074032008)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-4500911607058230005362617923),(-4500911607058229984993904583)⟩,⟨1760474897343839907551698884,1760474897343839927728888865⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-2258040325644974755553933232),(-2258040325644974735913906945)⟩,⟨2738340545317183417505581163,2738340545317183437022825036⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-393550395666093112376651260),(-393550395666093083272568474)⟩,⟨2409249002958464370465546454,2409249002958464399551883166⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨571313025774019811557570481,571313025774019890907139269⟩,⟨1501399666370833622676101465,1501399666370833702033883646⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨780011236501464365831526095,780011236501464576374387001⟩,⟨669587889405068751265935816,669587889405068961810702950⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨622390245596354441852918357,622390245596355028363932713⟩,⟨169015725658844767278714877,169015725658845353785016669⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨392912909095337141660413637,392912909095338325266523972⟩,⟨(-41281124086521271933168467),(-41281124086520088331024478)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨213888725347239772419881065,213888725347241298722023044⟩,⟨(-87532049534506509862622741),(-87532049534504983561710978)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨100197866300186824566131145,100197866300188087197755405⟩,⟨(-65750433314785138926492814),(-65750433314783876294879860)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨28786771196802246086352812,28786771196802727095612904⟩,⟨(-23184510504939554141372168),(-23184510504939073131998021)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-3701829061804096058538475559),(-3701829061804083853459432051)⟩,⟨(-2069075260485955948224339672),(-2069075260485943742923222070)⟩⟩
lemma checked : cachedMomentRuleBox density0 kernel9_0 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (tableMomentRule false 9 0) := by
  rw [← checked]
  simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Bool.false_eq_true,ite_false,ite_true] using @tableRule_contains_bridge false 9 false density0 kernel9_0
    density0_contains kernel9_0_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-5228957982970673769556563959),(-5228957982970673765550616868)⟩,⟨(-544649371312902746670181835),(-544649371312902742706373570)⟩⟩
lemma atomChecked : tableAtomBox false atomKernel9_0 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (tableMomentAtom false 9 0) := by
  rw [← atomChecked]
  exact tableAtomBox_contains false atomKernel9_0_contains
noncomputable def realAnswer : RBox := ⟨(-8930787044774769828195039518),(-8930787044774757618910048919)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma KContains : realAnswer.Contains (tableMomentK false 9 0) := by
  rw [← realChecked]
  exact tableMomentK_contains atomContains contains (by norm_num) (by norm_num)
end tm0_9_0

namespace tm0_9_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (kernel9_1 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-28),16⟩,⟨(-25),18⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-38),16⟩,⟨(-32),18⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-31),47⟩,⟨(-47),18⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-24),55⟩,⟨(-28),52⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-59),25⟩,⟨(-38),45⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-35),67⟩,⟨(-65),38⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-82),56⟩,⟨(-58),78⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-58),70⟩,⟨(-78),52⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-64),64⟩,⟨(-68),60⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-40),69⟩,⟨(-53),60⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-62),40⟩,⟨(-48),56⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-33),41⟩,⟨(-47),31⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-19),32⟩,⟨(-29),32⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-21),19⟩,⟨(-16),21⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-89610549523),(-89610549500)⟩,⟨(-10164228465),(-10164228439)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-174154399150),(-174154399117)⟩,⟨(-30951396526),(-30951396486)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-120657395544),(-120657395493)⟩,⟨(-38896299484),(-38896299433)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-43711143653),(-43711143593)⟩,⟨(-26204860166),(-26204860107)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-8143746516),(-8143746445)⟩,⟨(-9989410727),(-9989410656)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-413723055),(-413722971)⟩,⟨(-2168710942),(-2168710858)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨128508580,128508667⟩,⟨(-244045508),(-244045419)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨26729733,26729823⟩,⟨(-5808941),(-5808847)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨1547076,1547176⟩,⟨1802892,1802988⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-105105),(-105010)⟩,⟨171762,171860⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-17431),(-17338)⟩,⟨(-6697),(-6606)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨420,502⟩,⟨(-2063),(-1984)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨266,337⟩,⟨(-32),40⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-7),49⟩,⟨28,81⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-32),16⟩,⟨(-2),34⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-222161278343409369),(-222161278343409320)⟩,⟨(-6788107497801328521),(-6788107497801328471)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-1729400710855516343),(-1729400710855516243)⟩,⟨(-15276811324910815969),(-15276811324910815869)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-3851059991294465907),(-3851059991294465799)⟩,⟨(-14119206575186345487),(-14119206575186345379)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-4122702155355850277),(-4122702155355850188)⟩,⟨(-7919329758660676207),(-7919329758660676119)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-2584888885878326559),(-2584888885878326493)⟩,⟨(-2866157087266519814),(-2866157087266519747)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-1048394148373671937),(-1048394148373671883)⟩,⟨(-667864006248216046),(-667864006248215988)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-295948186413048390),(-295948186413048335)⟩,⟨(-93781196148583516),(-93781196148583461)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-62634447518646827),(-62634447518646772)⟩,⟨(-5033121264452783),(-5033121264452729)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-10832100233532355),(-10832100233532290)⟩,⟨993963621646812,993963621646871⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-1686794654100188),(-1686794654100127)⟩,⟨329293646716324,329293646716383⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-260697196509786),(-260697196509724)⟩,⟨57673628622697,57673628622758⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-43474654178285),(-43474654178224)⟩,⟨7558858207340,7558858207401⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-8319421231519),(-8319421231465)⟩,⟨620444635121,620444635172⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-1892370566713),(-1892370566666)⟩,⟨(-86944098850),(-86944098806)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-501002281351),(-501002281318)⟩,⟨(-77565589243),(-77565589208)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-108696615401),(-108696615376)⟩,⟨(-23944050807),(-23944050784)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-359790637946035812884151),(-359790637946035188853827)⟩,⟨(-111730650282597954491373),(-111730650282597330521428)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-932905003572507167599233),(-932905003572505824342941)⟩,⟨(-186883271713635346226486),(-186883271713634003105647)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-1124019516369950717644863),(-1124019516369949630142637)⟩,⟨4964791084524596997245,4964791084525684382102⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-900374973884132206508886),(-900374973884131745076332)⟩,⟨275087230312758553098593,275087230312759014488795⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-482303534340403429222966),(-482303534340403325096438)⟩,⟨379668560735696004011192,379668560735696108157279⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-147170312360268469647711),(-147170312360268457232330)⟩,⟨290103053098810807010771,290103053098810819463355⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨1632716255685220317484,1632716255685221612910⟩,⟨144711263788241669118855,144711263788241670430503⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨27532441444757485878359,27532441444757486143831⟩,⟨48471547582993370365488,48471547582993370632160⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨16393665025962610823539,16393665025962610914579⟩,⟨10010778677305368361233,10010778677305368450930⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨6127391299002471535229,6127391299002471570122⟩,⟨395209657300251204841,395209657300251239003⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨1763079323479500557279,1763079323479500570458⟩,⟨(-698630905567196364733),(-698630905567196351665)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨427859841672599518167,427859841672599523008⟩,⟨(-407727885161158334579),(-407727885161158329734)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨91715002729784394909,91715002729784396725⟩,⟨(-170296390369515501405),(-170296390369515499579)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨17070909984171205807,17070909984171206518⟩,⟨(-65758026741568804577),(-65758026741568803862)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨2285960434542914259,2285960434542914543⟩,⟨(-24507938445769121609),(-24507938445769121323)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨78150576102499804,78150576102499891⟩,⟨(-6310751227987334144),(-6310751227987334058)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-245069926260178379871244281),(-245069926260176011594814249)⟩,⟨(-58508637073572474821096585),(-58508637073570106516357388)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-665988585699872165860963685),(-665988585699864518394018721)⟩,⟨(-80578530751740374578317414),(-80578530751732727025056555)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-878673084482137676894351685),(-878673084482123436567684729)⟩,⟨92619851111498066841477590,92619851111512307303178194⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-795656982642581376536027864),(-795656982642552254267298729)⟩,⟨369713653404306023635076791,369713653404335146005424822⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-475303014377329721689389264),(-475303014377279094837678783)⟩,⟨547498426896587812038653734,547498426896638438920581135⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-114637946382461749096684143),(-114637946382398284242342331)⟩,⟨507490269587818341624837496,507490269587881806454989420⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨105202666326144401803721791,105202666326195539699427466⟩,⟨314908233167878087492699418,314908233167929225345454410⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨150388536097348832503608523,150388536097388795312222138⟩,⟨119468665219940416986937011,119468665219980379777218109⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨102448921750277936912221910,102448921750301492992671233⟩,⟨8385818832305554455659208,8385818832329110536931430⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨45711861834440059411636730,45711861834448376070842658⟩,⟨(-24935602099544111442263241),(-24935602099535794777696116)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨12744954838218887868822631,12744954838221348464809397⟩,⟨(-22190213256431627610536890),(-22190213256429167011699261)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨321378872320935292924317,321378872321723574319323⟩,⟨(-12482271654184314858286727),(-12482271654183526576480551)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-2348382665360777019904756),(-2348382665360576205641268)⟩,⟨(-5667533628374436711979582),(-5667533628374235897928599)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-1979992211045618113504901),(-1979992211045570038274356)⟩,⟨(-2270271500717446475509085),(-2270271500717398400526508)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-1116170098565116090086666),(-1116170098565104146312800)⟩,⟨(-819427538197463987925501),(-819427538197452044303805)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-348132636715436060643284),(-348132636715433614992010)⟩,⟨(-200260529722605252499148),(-200260529722602806896251)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-5313816206645151054510464307),(-5313816206645151045221203184)⟩,⟨(-121842765904017170396541535),(-121842765904017161719453632)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-14691539950289463726114832159),(-14691539950289463698183756571)⟩,⟨1528768946936434526329356684,1528768946936434552555090288⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-20072334518799345005543656524),(-20072334518799344958648129378)⟩,⟨7312462833711828097884142238,7312462833711828142770876890⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-19006413767282847043490763135),(-19006413767282846979013084546)⟩,⟨15757147471312703213808452414,15757147471312703276807172013⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-11329698953074224692788878500),(-11329698953074224614266070899)⟩,⟨22238462201287596863771785208,22238462201287596941885608214⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-487692982689973930981512966),(-487692982689973846386417738)⟩,⟨22514309588056132989176465207,22514309588056133074242669548⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨8196676924385357077266868650,8196676924385357158935659380⟩,⟨16347334599470572459178893502,16347334599470572541674105195⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨11329147082100434886816608884,11329147082100434968444054813⟩,⟨7528164455146402171623385205,7528164455146402253657623286⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨9470130031776756336863283565,9470130031776756455570639246⟩,⟨448340613049308161120651916,448340613049308279856259070⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨5579245256904407752204926481,5579245256904408055929984425⟩,⟨(-2973973816486369381684292761),(-2973973816486369078005191940)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨2219024372290882690536987488,2219024372290883533499421037⟩,⟨(-3445152608739501775037414333),(-3445152608739500932080921481)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨306084157645094659323732187,306084157645097204364631359⟩,⟨(-2583199036095713729543370058),(-2583199036095711184483291841)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-414748634783097088111702184),(-414748634783092152990148871)⟩,⟨(-1555392224776827125327981062),(-1555392224776822190193593430)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-497199716144378443641681028),(-497199716144372278744924317)⟩,⟨(-808653054004819814710121448),(-808653054004813649811554285)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-336840552501480354230384911),(-336840552501475380481629364)⟩,⟨(-362768590231385944989959439),(-362768590231380971243251513)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-114844459356533817462587124),(-114844459356531950087438776)⟩,⟨(-101272616212053379543100077),(-101272616212051512169125562)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-6322169733967723643235671498),(-6322169733967670945591468917)⟩,⟨13912670257375713621459603921,13912670257375766318404064827⟩⟩
lemma checked : cachedMomentRuleBox density0 kernel9_1 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (tableMomentRule false 9 1) := by
  rw [← checked]
  simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Bool.false_eq_true,ite_false,ite_true] using @tableRule_contains_bridge false 9 true density0 kernel9_1
    density0_contains kernel9_1_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-923424386511920245166739646),(-923424386511920229922906662)⟩,⟨19036194329455527413133444733,19036194329455527428572877251⟩⟩
lemma atomChecked : tableAtomBox false atomKernel9_1 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (tableMomentAtom false 9 1) := by
  rw [← atomChecked]
  exact tableAtomBox_contains false atomKernel9_1_contains
noncomputable def realAnswer : RBox := ⟨(-7245594120479643888502411144),(-7245594120479591175414375579)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma KContains : realAnswer.Contains (tableMomentK false 9 1) := by
  rw [← realChecked]
  exact tableMomentK_contains atomContains contains (by norm_num) (by norm_num)
end tm0_9_1

namespace tm1_9_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (kernel9_0 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨1934135631,1934135647⟩,⟨(-387736282),(-387736266)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨3770639174,3770639190⟩,⟨(-535959927),(-535959911)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨2652212146,2652212163⟩,⟨(-51173865),(-51173848)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨1011946989,1011947005⟩,⟨189752374,189752391⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨221173694,221173710⟩,⟨120813240,120813258⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨24206314,24206331⟩,⟨34627782,34627798⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-181744),(-181727)⟩,⟨5230774,5230790⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-403753),(-403736)⟩,⟨327376,327392⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-42167),(-42150)⟩,⟨(-17194),(-17176)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨286,306⟩,⟨(-3918),(-3902)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨362,378⟩,⟨(-45),(-28)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨1,18⟩,⟨32,50⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-16),0⟩,⟨(-6),12⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-16),4⟩,⟨(-16),0⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),2⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨135992547255184601,135992547255184619⟩,⟨224327296887814882,224327296887814901⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨342705496413224027,342705496413224046⟩,⟨483363449781810173,483363449781810190⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨381845827168432409,381845827168432426⟩,⟨408374511380497492,408374511380497512⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨268529110456981666,268529110456981687⟩,⟨197199837017702527,197199837017702544⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨126276579057856340,126276579057856358⟩,⟨54860139640062384,54860139640062403⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨41033974280164856,41033974280164875⟩,⟨6611838615716296,6611838615716314⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨9613837735594387,9613837735594406⟩,⟨(-965688543780744),(-965688543780728)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨1729634763851709,1729634763851726⟩,⟨(-617448340930123),(-617448340930106)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨261500654957519,261500654957536⟩,⟨(-155058518736575),(-155058518736557)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨37218374180953,37218374180969⟩,⟨(-28190108249069),(-28190108249053)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨5563139697692,5563139697711⟩,⟨(-4397114650576),(-4397114650559)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨935113258904,935113258921⟩,⟨(-648815814443),(-648815814427)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨182089517410,182089517426⟩,⟨(-97558726042),(-97558726026)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨41880865905,41880865922⟩,⟨(-15995192523),(-15995192507)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨11170959036,11170959052⟩,⟨(-2981523649),(-2981523632)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨2437193405,2437193421⟩,⟨(-502129440),(-502129423)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨24637992816335984855338,24637992816336111084100⟩,⟨(-7926381831839319683256),(-7926381831839193455432)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨58920376559399287212348,58920376559399524564002⟩,⟨(-25525617229092451530981),(-25525617229092214182069)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨60409422179811129705506,60409422179811284699595⟩,⟨(-41545530103851885761903),(-41545530103851730771537)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨36981710544532690018795,36981710544532758215920⟩,⟨(-45521532057437253147045),(-45521532057437184952208)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨11182411698975482903638,11182411698975499889894⟩,⟨(-34647972648793784697451),(-34647972648793767711766)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-2289414859571986250383),(-2289414859571984017459)⟩,⟨(-18340132805822500257555),(-18340132805822498024359)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-4492507912890642745676),(-4492507912890642574425)⟩,⟨(-6547153346474262379292),(-6547153346474262207697)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-2632858506590729736544),(-2632858506590729717323)⟩,⟨(-1358526846555554630433),(-1358526846555554611115)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-987699261124083528025),(-987699261124083522988)⟩,⟨12390109013181397002,12390109013181402043⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-270824868710497455849),(-270824868710497454086)⟩,⟨141134818183236418875,141134818183236420631⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-56154065497788162905),(-56154065497788162265)⟩,⟨72383662302051219552,72383662302051220190⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-7801312317704138590),(-7801312317704138348)⟩,⟨26862968201606649789,26862968201606650032⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨246319987597361389,246319987597361490⟩,⟨9053620244690343201,9053620244690343302⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨818477378309192134,818477378309192181⟩,⟨3062119071140581406,3062119071140581453⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨464501335064536250,464501335064536278⟩,⟨1050132145114494483,1050132145114494510⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨139567993097025019,139567993097025037⟩,⟨259469696754687547,259469696754687564⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨6926056817023405100839501,6926056817023910541927355⟩,⟨(-18714035788376711233811520),(-18714035788376205791957880)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨13458761352262582577830165,13458761352264245109024652⟩,⟨(-52363823244695645208270017),(-52363823244693982674330993)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨3854298165092750305131464,3854298165095855479239465⟩,⟨(-73089204361782806339377812),(-73089204361779701159953203)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-17232714628941306661394403),(-17232714628936239728571982)⟩,⟨(-72425864723691668451142678),(-72425864723686601511750682)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-35133368703868164520724554),(-35133368703858959212162115)⟩,⟨(-51184368276186708487059829),(-51184368276177503174782097)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-38338836785192585763730163),(-38338836785180241190824127)⟩,⟨(-22234572408656818498553164),(-22234572408644473925185614)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-28068664857787078259289544),(-28068664857776312645298204)⟩,⟨(-591134606552173969617306),(-591134606541408356992643)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-14122033086277884802635333),(-14122033086271291666318044)⟩,⟨8039624882192516471340801,8039624882199109606377720⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-4294217299159487423003595),(-4294217299155296080502004)⟩,⟨7646193233314426668395827,7646193233318618010631935⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨22978411074108593909557,22978411075763079373225⟩,⟨4476046084060507597585031,4476046084062162083158318⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨1004592022123652408919286,1004592022124072076231565⟩,⟨1945418738925888741607582,1945418738926308409050353⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨809312518132147693459231,809312518132272095699422⟩,⟨655206762872285537829796,655206762872409940114557⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨462357902054289410528370,462357902054324242158547⟩,⟨159074228786387310945503,159074228786422142581759⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨227664592822970840037392,227664592822979891539860⟩,⟨12011748701764754913924,12011748701773806413418⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨99404912943558396655876,99404912943560811822132⟩,⟨(-14471536390544964098606),(-14471536390542548935345)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨27609798081733451974544,27609798081733963057204⟩,⟨(-6976206518365904938354),(-6976206518365393856761)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨1225328174824012591432207,1225328174824012923355553⟩,⟨(-43661850945513926187556749),(-43661850945513925751016888)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-34813709072493756910959496),(-34813709072493755979521453)⟩,⟨(-113512049474632373427962199),(-113512049474632372182610032)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-154730448084121409946624207),(-154730448084121408306773355)⟩,⟨(-85835995971107072582952704),(-85835995971107070555369401)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-314903849553048381183865309),(-314903849553048378630819800)⟩,⟨159715724495345356718426425,159715724495345359557285336⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-376372604857481138568921220),(-376372604857481134461757543)⟩,⟨631239482919489499461825518,631239482919489503658477423⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-205371252856244685123669361),(-205371252856244679423399303)⟩,⟨1120053284550725924334335268,1120053284550725929941324499⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨176006911683155259670704697,176006911683155266425589381⟩,⟨1338652258082958595952044639,1338652258082958602506943077⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨568263950315064547926251322,568263950315064556420148333⟩,⟨1172171160906757895479645660,1172171160906757903835732310⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨765230031972835388912713916,765230031972835407358192849⟩,⟨756168669014239318676487341,756168669014239337104546085⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨719977014153295117832967352,719977014153295179117619869⟩,⟨326644836336613763834865198,326644836336613825143677452⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨532050886961601616127299105,532050886961601785663127458⟩,⟨37093995322382270644180893,37093995322382440206717740⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨326457489095271749061814993,326457489095272226422535320⟩,⟨(-92670370562053318180590412),(-92670370562052840809452436)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨172188035147808522303504366,172188035147809488244486089⟩,⟨(-116430279401881544849791568),(-116430279401880578908261795)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨79694160658823820503920819,79694160658825067421451289⟩,⟨(-92484202965732202935937060),(-92484202965730956019740316)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨31950468942233449171688995,31950468942234481260434837⟩,⟨(-55422111803360458979031338),(-55422111803359426891441816)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨8223362648186986968650130,8223362648187380253858207⟩,⟨(-18123402520123064906290310),(-18123402520122671621492057)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨364160062348334551250302660,364160062348344564816252473⟩,⟨775954521205517585343480386,775954521205527599044252876⟩⟩
lemma checked : cachedMomentRuleBox density1 kernel9_0 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (tableMomentRule true 9 0) := by
  rw [← checked]
  simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Bool.false_eq_true,ite_false,ite_true] using @tableRule_contains_bridge true 9 false density1 kernel9_0
    density1_contains kernel9_0_contains
noncomputable def atomAnswer : CBox := ⟨⟨6837868131577034924181575904,6837868131577034929420122100⟩,⟨712233793255334355846796207,712233793255334361030237784⟩⟩
lemma atomChecked : tableAtomBox true atomKernel9_0 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (tableMomentAtom true 9 0) := by
  rw [← atomChecked]
  exact tableAtomBox_contains true atomKernel9_0_contains
noncomputable def realAnswer : RBox := ⟨7202028193925369475331878564,7202028193925379494336374573⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma KContains : realAnswer.Contains (tableMomentK true 9 0) := by
  rw [← realChecked]
  exact tableMomentK_contains atomContains contains (by norm_num) (by norm_num)
end tm1_9_0

namespace tm1_9_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (kernel9_1 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-11541558258),(-11541558242)⟩,⟨(-8043438058),(-8043438042)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-21533626580),(-21533626560)⟩,⟨(-16711705830),(-16711705811)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-13708253345),(-13708253323)⟩,⟨(-13327182637),(-13327182614)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-4297980372),(-4297980353)⟩,⟨(-6142475926),(-6142475906)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-578686933),(-578686912)⟩,⟨(-1766928053),(-1766928030)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨37660317,37660341⟩,⟨(-314316219),(-314316194)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨26759672,26759697⟩,⟨(-29592957),(-29592929)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨4034686,4034714⟩,⟨(-52176),(-52149)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨187983,188013⟩,⟨306923,306949⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-19714),(-19683)⟩,⟨24632,24660⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-2728),(-2698)⟩,⟨(-1377),(-1350)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨95,123⟩,⟨(-352),(-323)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨40,67⟩,⟨(-10),20⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-10),17⟩,⟨0,21⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-16),9⟩,⟨(-12),16⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨760387994026983283,760387994026983312⟩,⟨(-1331513416605360184),(-1331513416605360157)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨1490046065353754647,1490046065353754688⟩,⟨(-3139787235568141823),(-3139787235568141781)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨975913839300983411,975913839300983456⟩,⟨(-3154299261799496341),(-3154299261799496297)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨203983618926987943,203983618926987978⟩,⟨(-1976912730207854424),(-1976912730207854386)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-112764920866217301),(-112764920866217272)⟩,⟨(-824300152475240866),(-824300152475240837)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-100360130263675535),(-100360130263675509)⟩,⟨(-234489237762784532),(-234489237762784506)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-38190234556066593),(-38190234556066568)⟩,⟨(-46712439303592331),(-46712439303592305)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-9515258860842524),(-9515258860842500)⟩,⟨(-6785196201141052),(-6785196201141030)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-1815148558989612),(-1815148558989585)⟩,⟨(-772778008644531),(-772778008644507)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-298202991850305),(-298202991850282)⟩,⟨(-80713148927189),(-80713148927166)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-46657616766223),(-46657616766198)⟩,⟨(-10384334029218),(-10384334029193)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-7543971406970),(-7543971406949)⟩,⟨(-1991368111322),(-1991368111300)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-1348469148685),(-1348469148664)⟩,⟨(-495689328557),(-495689328538)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-282211508934),(-282211508914)⟩,⟨(-140723744537),(-140723744517)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-69677960646),(-69677960628)⟩,⟨(-43173747204),(-43173747180)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-14556221793),(-14556221776)⟩,⟨(-10091674963),(-10091674947)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-74094514293683642707432),(-74094514293683118694951)⟩,⟨(-101839819917017231870216),(-101839819917016707851480)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-208938334993299825233690),(-208938334993298698115685)⟩,⟨(-233639710826746018837154),(-233639710826744891705089)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-288528099977155993398223),(-288528099977155082346215)⟩,⟨(-215446548052738635842110),(-215446548052737724777929)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-273416063559127205645706),(-273416063559126820167904)⟩,⟨(-98656353694621538877181),(-98656353694621153395013)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-182436650219046748630542),(-182436650219046662142513)⟩,⟨6466971862614902431498,6466971862614988917493⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-83100926210623792516528),(-83100926210623782481339)⟩,⟨43876590695743551365546,43876590695743561396983⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-22883975044209486736935),(-22883975044209485845118)⟩,⟨34036514456310341303473,34036514456310342193694⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-1268069437729719334532),(-1268069437729719210723)⟩,⟨15515518526212222311966,15515518526212222435678⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨2181102729182953451481,2181102729182953484627⟩,⟨4812252311097931622240,4812252311097931655530⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨1314750013922505560675,1314750013922505572782⟩,⟨1018204278609904661326,1018204278609904673503⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨496290054913550443208,496290054913550447818⟩,⟨106011113073435716298,106011113073435720916⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨154782375667685664556,154782375667685666274⟩,⟨(-28705606544330709005),(-28705606544330707285)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨45151052351342306434,45151052351342307096⟩,⟨(-25124987514925345195),(-25124987514925344533)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨13332072565211272598,13332072565211272866⟩,⟨(-12508191514543833276),(-12508191514543833010)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨4058469664154400316,4058469664154400430⟩,⟨(-5297284083492840016),(-5297284083492839900)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨931112393265992077,931112393265992118⟩,⟨(-1444877256012895428),(-1444877256012895384)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-81396680608966009855585460),(-81396680608964063837700281)⟩,⟨(-15073991666800314229343612),(-15073991666798368216424105)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-224223985197353966307472287),(-224223985197347681766529111)⟩,⟨(-17462486740589537740435620),(-17462486740583253215636695)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-303672612790612286113504223),(-303672612790600581734464565)⟩,⟨38498750150609248200947500,38498750150620952552940558⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-286600730796100273515827696),(-286600730796076332334807442)⟩,⟨127850505729225172687996081,127850505729249113846137135⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-184783028041855020762188461),(-184783028041813394632894360)⟩,⟨189064896384710791990812064,189064896384752418110639760⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-59934055768017423212588012),(-59934055767965240713172255)⟩,⟨181384856059849674056964142,181384856059901856559562348⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨24124082126082241007843096,24124082126124279839817642⟩,⟨120287639361972240955483840,120287639362014279796311537⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨49135961219971246821947330,49135961220004082960008888⟩,⟨52730751926945965540154850,52730751926978801682487176⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨38125254730069762895413173,38125254730089103406059250⟩,⟨10345664934797147042920503,10345664934816487553616787⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨19758653520940358661378210,19758653520947179929800273⟩,⟨(-5384537354336006184430216),(-5384537354329184917041636)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨7431185288625311667400559,7431185288627327150055296⟩,⟨(-6940375513988131333741965),(-6940375513986115851638076)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨1879224369315337667038181,1879224369315982487255649⟩,⟨(-4528072939076496802019779),(-4528072939075851981890498)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨77437376833422968534472,77437376833587021342190⟩,⟨(-2328269567440158185750621),(-2328269567439994132909089)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-275709837466087839048465),(-275709837466048609580513)⟩,⟨(-1061289015376418465189940),(-1061289015376379235679338)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-214854922403123280688415),(-214854922403113543124402)⟩,⟨(-436319444147592835548363),(-436319444147583097958222)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-73913852563634178580196),(-73913852563632185668666)⟩,⟨(-116945749128380615621103),(-116945749128378622701388)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-157985121347701090452612515),(-157985121347701088903277072)⟩,⟨3860270133598057727482697,3860270133598058874879439⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-404106820846560317111042276),(-404106820846560312520097335)⟩,⟨148544019358906221568651863,148544019358906225037634204⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-278802426830490464837828746),(-278802426830490457199155928)⟩,⟨581134714817595696336869484,581134714817595702674412816⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨660358150453573116921108617,660358150453573127626823671⟩,⟨1114685802549904429512592581,1114685802549904439321747351⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨2432522358652277597803181708,2432522358652277613813701030⟩,⟨1219594616739103922784460221,1219594616739103938629880902⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨4239537123436275611617141057,4239537123436275633353814885⟩,⟨423160854585834674402029608,423160854585834696636688200⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨4985126830293501770381997191,4985126830293501796259727511⟩,⟨(-1129274825019650207681095912),(-1129274825019650180956687636)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨4246169234043762138385037714,4246169234043762173142550721⟩,⟨(-2629621544796356741839513485),(-2629621544796356706646605291)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨2578634645509781568311375964,2578634645509781642281747731⟩,⟨(-3289210843808055490302022106),(-3289210843808055416332141512)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨919402889758825394263474660,919402889758825626764980870⟩,⟨(-2973432153053848420672915301),(-2973432153053848188304231669)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-143323618289066504232279168),(-143323618289065826620730597)⟩,⟨(-2121554709997240444766835888),(-2121554709997239767264969052)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-562846730291684387224065348),(-562846730291682316179194365)⟩,⟨(-1247773075804514102819814295),(-1247773075804512031800657984)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-577580808381839652358209466),(-577580808381835625319122804)⟩,⟨(-619435475012431904886483873),(-619435475012427877840663926)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-427924251588082105386150760),(-427924251588077069384535152)⟩,⟨(-261440068383688991909069146),(-261440068383683955897251245)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-247742273320935476863706124),(-247742273320931411535176411)⟩,⟨(-91930551171866742578952755),(-91930551171862677243493053)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-79760956180735805741576572),(-79760956180734279017464362)⟩,⟨(-20865334238958848474912255),(-20865334238957321748507540)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨2696650666469813114628562368,2696650666469856353452949940⟩,⟨(-1704545226785050389459191574),(-1704545226785007151037280934)⟩⟩
lemma checked : cachedMomentRuleBox density1 kernel9_1 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (tableMomentRule true 9 1) := by
  rw [← checked]
  simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Bool.false_eq_true,ite_false,ite_true] using @tableRule_contains_bridge true 9 true density1 kernel9_1
    density1_contains kernel9_1_contains
noncomputable def atomAnswer : CBox := ⟨⟨1207554966977126454514570251,1207554966977126474448813383⟩,⟨(-24893484892364920483518377943),(-24893484892364920463328350805)⟩⟩
lemma atomChecked : tableAtomBox true atomKernel9_1 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (tableMomentAtom true 9 1) := by
  rw [← atomChecked]
  exact tableAtomBox_contains true atomKernel9_1_contains
noncomputable def realAnswer : RBox := ⟨3904205633446939569043132619,3904205633446982828001763323⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma KContains : realAnswer.Contains (tableMomentK true 9 1) := by
  rw [← realChecked]
  exact tableMomentK_contains atomContains contains (by norm_num) (by norm_num)
end tm1_9_1

end SharpPlanar.CachedData

end OAI
