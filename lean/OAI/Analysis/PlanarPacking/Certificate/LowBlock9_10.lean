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
namespace hm9_0_1_2
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk9_1_2 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-21),39⟩,⟨(-32),27⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-52),86⟩,⟨(-57),84⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-71),129⟩,⟨(-56),142⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-190),77⟩,⟨(-97),170⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-193),132⟩,⟨(-228),99⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-122),269⟩,⟨(-179),209⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-304),141⟩,⟨(-211),238⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-270),359⟩,⟨(-334),285⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-347),266⟩,⟨(-264),342⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-277),274⟩,⟨(-281),306⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-304),193⟩,⟨(-269),235⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-153),266⟩,⟨(-216),205⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-181),148⟩,⟨(-114),194⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-119),66⟩,⟨(-119),98⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-68),75⟩,⟨(-75),37⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-29),30⟩,⟨(-30),18⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨194963826624,194963826656⟩,⟨255741442314,255741442349⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨354137098968,354137099033⟩,⟨524651834911,524651834978⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨206244632920,206244633020⟩,⟨407660976603,407660976702⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨46962480891,46962481022⟩,⟨179520178313,179520178445⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-3343464713),(-3343464548)⟩,⟨47428754681,47428754845⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-4258913975),(-4258913763)⟩,⟨7091308909,7091309117⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-974077093),(-974076848)⟩,⟨395455100,395455345⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-95395299),(-95395020)⟩,⟨(-46604793),(-46604518)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-703463),(-703160)⟩,⟨(-9365150),(-9364849)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨738635,738955⟩,⟨(-332708),(-332387)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨45360,45665⟩,⟨60825,61133⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-6039),(-5764)⟩,⟨6132,6407⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-1224),(-974)⟩,⟨(-749),(-498)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-68),116⟩,⟨(-338),(-152)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-9),111⟩,⟨(-96),23⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-16),40⟩,⟨(-27),28⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-17028289354395166074),(-17028289354395165953)⟩,⟨10199254616055370718,10199254616055370836⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-36599526443052048122),(-36599526443052047861)⟩,⟨26333194370153606053,26333194370153606315⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-30563185076944639221),(-30563185076944638934)⟩,⟨30551907973565997317,30551907973565997607⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-14148483410731100154),(-14148483410731099923)⟩,⟨22560161177523331374,22560161177523331606⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-3346363150729114822),(-3346363150729114655)⟩,⟨11171476974278201706,11171476974278201873⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-11128454018073761),(-11128454018073631)⟩,⟨3814415218902337882,3814415218902338014⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨266490653883121049,266490653883121183⟩,⟨932085973545095049,932085973545095179⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨100795293635487880,100795293635488006⟩,⟨172684964932220776,172684964932220905⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨23395911356792552,23395911356792697⟩,⟨26427844414559058,26427844414559201⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨4275845120844661,4275845120844806⟩,⟨3748213085935054,3748213085935197⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨705320356273437,705320356273578⟩,⟨558880542592834,558880542592979⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨116418254632978,116418254633109⟩,⟨96561602112426,96561602112558⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨20835090823081,20835090823202⟩,⟨20187185617554,20187185617670⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨4279774038602,4279774038694⟩,⟨5106577505455,5106577505546⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨1017214144437,1017214144501⟩,⟨1481538672665,1481538672727⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨205218622260,205218622293⟩,⟨338824057215,338824057248⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨15240139117221451627056,15240139117223322938430⟩,⟨916496199043249836343025,916496199043251707743761⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨285217655395317849139595,285217655395321735341361⟩,⟨2304562712052524178732834,2304562712052528065109750⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨898158274098861275366021,898158274098864232905637⟩,⟨2610168032292369222590429,2610168032292372180215888⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨1379265041832881052562887,1379265041832882209678392⟩,⟨1881669645919553252224118,1881669645919554409262223⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨1306931928981481185463344,1306931928981481419862125⟩,⟨812546409593786698636076,812546409593786932869573⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨822214702926437106926026,822214702926437135600926⟩,⟨88998878567744125293138,88998878567744153862287⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨345874953654442334314369,345874953654442338226512⟩,⟨(-141700832626194261657079),(-141700832626194257759371)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨89720189893792936149393,89720189893792936879185⟩,⟨(-115758577511873433938345),(-115758577511873433199749)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨6921211789499990769022,6921211789499991020210⟩,⟨(-50904287641199307017232),(-50904287641199306759789)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-5999727223480230930241),(-5999727223480230829828)⟩,⟨(-15603652258738421682368),(-15603652258738421581005)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-3864425064523668715585),(-3864425064523668677242)⟩,⟨(-3557880479815831203196),(-3557880479815831164971)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-1565923978519196528785),(-1565923978519196514599)⟩,⟨(-560011511108222781000),(-560011511108222766952)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-551698969762257748268),(-551698969762257742928)⟩,⟨(-7400574980472804500),(-7400574980472799224)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-190379380385579358604),(-190379380385579356520)⟩,⟨46256219107906062804,46256219107906064874⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-65664211276671168990),(-65664211276671168170)⟩,⟨28351501298356434933,28351501298356435749⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-16222845532366635679),(-16222845532366635450)⟩,⟨8704507021804604582,8704507021804604810⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-32906046910661577120322308),(-32906046910657189061642504)⟩,⟨521579191058645223304377728,521579191058649611287450174⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨74540326612861794775123790,74540326612875841557719827⟩,⟨1393279730451142654710163941,1393279730451156701273437950⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨517351195318737913817678413,517351195318770395260806617⟩,⟨1773624507917063674166833021,1773624507917096155362038645⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨1075922407195598562185448965,1075922407195665620540595919⟩,⟨1503850398510342848576396611,1503850398510409906789615161⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨1339931112711052575088870773,1339931112711162540399493178⟩,⟨766434165007671146083185265,766434165007781111397234078⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨1121089782052017367143697251,1121089782052145614573362619⟩,⟨17592669715819725809082161,17592669715947973340511093⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨621642037017731557209948502,621642037017840902316562534⟩,⟨(-373857743382745689757165690),(-373857743382636344550114414)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨180908587443661755340229552,180908587443758154159713468⟩,⟨(-385588543777373037198277163),(-385588543777276638358330093)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-38053533285578915052528852),(-38053533285527805593277786)⟩,⟨(-228354400011018235440311104),(-228354400010967125994750163)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-82088378978713322148892821),(-82088378978696069437775346)⟩,⟨(-86301341809259349810775761),(-86301341809242097114957232)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-57617869960967482202359048),(-57617869960960921890308391)⟩,⟨(-14506681725637576680608459),(-14506681725631016372232624)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-28393112911163408075696918),(-28393112911161533756409400)⟩,⟨7600271019342157820771173,7600271019344032140732024⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-11261451148192184734835218),(-11261451148191753928709770)⟩,⟨9313991825845174425725121,9313991825845605233127412⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-3765885697621703752073938),(-3765885697621606220322576)⟩,⟨6188652368563246257907045,6188652368563343790514235⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-1055235160611743774937238),(-1055235160611712597251165)⟩,⟨3181584448881330153488309,3181584448881361331492314⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-199415583958454332220285),(-199415583958446930360432)⟩,⟨954957830870459907452262,954957830870467309388851⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨284108961892598164813047343,284108961892598181067941807⟩,⟨9611195472764182807762324467,9611195472764182825162498077⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨4221109131878579896651605423,4221109131878579946637751787⟩,⟨26448921381037215999478638733,26448921381037216052445615359⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨15443667864169009770887614434,15443667864169009856910200928⟩,⟨35720971115766048133059376855,35720971115766048222509966059⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨31095564854999751170991435762,31095564854999751292650259248⟩,⟨32917355402445217128255788569,32917355402445217252281968556⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨42557564078940650970079291319,42557564078940651122453728325⟩,⟨17929043648863315300249544116,17929043648863315453005279339⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨42030126055912041016100920710,42030126055912041184042942188⟩,⟨(-2523653602182276598012627903),(-2523653602182276431267307596)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨29373395121236999557777045449,29373395121236999723564621600⟩,⟨(-18281932130261310935250277618),(-18281932130261310771134820571)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨12115006090385829623100848535,12115006090385829791651454035⟩,⟨(-23078431825708704746187313233),(-23078431825708704578282927363)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-1238640390975472963727885020),(-1238640390975472725107659221)⟩,⟨(-18368363615228218114839915312),(-18368363615228217876194942453)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-7187211476289322511040071267),(-7187211476289321940198546644)⟩,⟨(-10155519427508349362304016076),(-10155519427508348791345791485)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-7407139488176841661213338923),(-7407139488176839872989162111)⟩,⟨(-3442373856391628548556057054),(-3442373856391626760324119313)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-5243750585471822138433212651),(-5243750585471816755629932315)⟩,⟨153690161205440578914752013,153690161205445961682035121⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-2999083945173488386986998439),(-2999083945173478349170016139)⟩,⟨1326771211808978362649786971,1326771211808988400448808423⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-1473284750022175736508831473),(-1473284750022163626163154628)⟩,⟨1276851408051601862721525237,1276851408051613973070209006⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-622662018179313019527969635),(-622662018179303534914181338)⟩,⟨810944777480471173734110620,810944777480480658356090797⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-166470755801476747999872781),(-166470755801473251210105878)⟩,⟨269952326531223485167287879,269952326531226981960753759⟩⟩
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
noncomputable def ans : CBox := ⟨⟨25910580076132431146368814755,25910580076132545037001795781⟩,⟨9256450066072415721626989239,9256450066072529613328257686⟩⟩
lemma checked : cachedMomentRuleBox density0 hk9_1_2 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 9 2) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk9_1_2 (tableDensity false) (fullFactor true 9 2) density0_contains hk9_1_2_contains
noncomputable def atomAnswer : CBox := ⟨⟨34541376661778509081358060040,34541376661778509111180455714⟩,⟨(-263867004946587503947649880),(-263867004946587474559384238)⟩⟩
lemma atomChecked : tableAtomBox false ha9_1_2 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 9 2) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha9_1_2 9 2 ha9_1_2_contains
 def realAnswer : RBox := ⟨60451956737910940227626874795,60451956737911054148282251495⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 9 2) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm9_0_1_2
namespace hm9_1_1_2
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk9_1_2 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),24⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-16),31⟩,⟨(-16),32⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-40),17⟩,⟨(-26),31⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-38),36⟩,⟨(-48),20⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-31),48⟩,⟨(-39),43⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-50),33⟩,⟨(-42),43⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-52),60⟩,⟨(-61),51⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-59),53⟩,⟨(-50),62⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-53),56⟩,⟨(-52),58⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-59),40⟩,⟨(-51),53⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-32),53⟩,⟨(-40),40⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-41),33⟩,⟨(-21),44⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-29),17⟩,⟨(-30),28⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨7776377076,7776377094⟩,⟨49556464522,49556464539⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨10673663373,10673663393⟩,⟨96954996145,96954996165⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨614329637,614329661⟩,⟨68894217342,68894217370⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-4465008586),(-4465008556)⟩,⟨26925732817,26925732847⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-2907506477),(-2907506443)⟩,⟨6211468640,6211468673⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-889798919),(-889798878)⟩,⟨784017909,784017949⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-150672925),(-150672879)⟩,⟨20508425,20508471⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-12416161),(-12416107)⟩,⟨(-9544756),(-9544703)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨120117,120175⟩,⟨(-1417746),(-1417686)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨121317,121381⟩,⟨(-37247),(-37183)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨6359,6421⟩,⟨10613,10678⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-1126),(-1067)⟩,⟨945,1007⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-214),(-154)⟩,⟨(-156),(-97)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-15),33⟩,⟨(-66),(-20)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-5),30⟩,⟨(-23),12⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-4480912620699840232),(-4480912620699840184)⟩,⟨(-53498060255377004),(-53498060255376960)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-10168906710498818278),(-10168906710498818185)⟩,⟨691191908824081966,691191908824082060⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-9517250319111884893),(-9517250319111884793)⟩,⟨2116959167965871297,2116959167965871396⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-5393510564944460603),(-5393510564944460523)⟩,⟨2459307494977429147,2459307494977429228⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-1951786219529480460),(-1951786219529480401)⟩,⟨1584142060080489875,1584142060080489933⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-443307242433866311),(-443307242433866267)⟩,⟨644961817214213600,644961817214213641⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-55696289167109746),(-55696289167109704)⟩,⟨179966514218192805,179966514218192844⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-406261724461673),(-406261724461634)⟩,⟨37180892511117378,37180892511117415⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨1463282292171791,1463282292171830⟩,⟨6231263149619714,6231263149619753⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨392316116075158,392316116075194⟩,⟨943756975186615,943756975186653⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨72097050168870,72097050168903⟩,⟨144065531551939,144065531551974⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨11586737518787,11586737518819⟩,⟨24102924670170,24102924670201⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨1827282578516,1827282578545⟩,⟨4649657379951,4649657379979⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨307428386090,307428386111⟩,⟨1065649681665,1065649681688⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨57880873192,57880873214⟩,⟨284739232092,284739232115⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨9744054726,9744054745⟩,⟨62280378396,62280378413⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-179058722024795186746365),(-179058722024793615151668)⟩,⟨248660084688946634541224,248660084688948206126632⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-380319943668670452878092),(-380319943668667191578530)⟩,⟨663750314636427832493999,663750314636431093775298⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-273480228000891360237299),(-273480228000888882350301)⟩,⟨840933890928684853209186,840933890928687331087163⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-7420703203857297369848),(-7420703203856330834528)⟩,⟨720243207079454700587667,720243207079455667130843⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨171066137205488811914467,171066137205489006319572⟩,⟨424489028983360328751527,424489028983360523173379⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨179074400235723057165147,179074400235723080108192⟩,⟨158130761481984043213814,158130761481984066167453⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨103500872572748792915955,103500872572748795615170⟩,⟨22534928616811609590588,22534928616811612291187⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨38907348776526688916342,38907348776526689251748⟩,⟨(-12605338770576061392018),(-12605338770576061057505)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨9446086516934506111393,9446086516934506203788⟩,⟨(-10508678920516127218576),(-10508678920516127126796)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨1021085556924580091221,1021085556924580126829⟩,⟨(-4410781431496807960364),(-4410781431496807924844)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-332691229537825067157),(-332691229537825053718)⟩,⟨(-1365674789794223053846),(-1365674789794223040395)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-267867127083654455792),(-267867127083654450816)⟩,⟨(-352785515288107739276),(-352785515288107734290)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-123096068140911151162),(-123096068140911149265)⟩,⟨(-81068886593175951599),(-81068886593175949695)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-49960641973071748770),(-49960641973071748009)⟩,⟨(-16829490739813265318),(-16829490739813264555)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-19163977177579364913),(-19163977177579364605)⟩,⟨(-2958252124599693763),(-2958252124599693455)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-5002791825075557741),(-5002791825075557648)⟩,⟨(-338686174296022207),(-338686174296022111)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-2020328819894069269850423),(-2020328819890463814340510)⟩,⟨171694156206185989180116807,171694156206189594649274624⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨44900687016852295745584114,44900687016863838474345888⟩,⟨465616096282901944261617928,465616096282913487031966286⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨192158310110653275252595603,192158310110679972066335316⟩,⟨610579501429784371153532326,610579501429811068017885300⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨376540848781605889310372483,376540848781661017145067682⟩,⟨543804427238552813107519222,543804427238607940976363911⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨471258983858794173003125183,471258983858884587719114550⟩,⟨307825291325620426939855547,307825291325710841661428353⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨409085698769233250060721386,409085698769338698239703692⟩,⟨46295645222720622076740103,46295645222826070237996271⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨245089156961568825553478247,245089156961658713409270980⟩,⟨(-108553049255205044138381148),(-108553049255115156303528980)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨88670302293683739462471108,88670302293762947703571521⟩,⟨(-132991646469310393591655072),(-132991646469231185355696484)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨1619611218260981105233311,1619611218302944351817491⟩,⟨(-88962189315520501999390094),(-88962189315478538750311627)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-23562620170306269488863034),(-23562620170292119406006855)⟩,⟨(-40491879755552623236016857),(-40491879755538473150148823)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-20191311573712070280213167),(-20191311573706696631600104)⟩,⟨(-12238638652870844679896619),(-12238638652865471030554722)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-11475958706156880194381589),(-11475958706155346977095181)⟩,⟨(-1223183586950812844844597),(-1223183586949279627659380)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-5355846747806547905676114),(-5355846747806195965645922)⟩,⟨1452832050085013710886080,1452832050085365650692648⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-2232684286221487763265366),(-2232684286221408181051724)⟩,⟨1403079262729487161022046,1403079262729566743086225⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-844762922374906173974904),(-844762922374880755418171)⟩,⟨820086703246907409885513,820086703246932828387277⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-214166117525930961031189),(-214166117525924929064258)⟩,⟨258960449232238666745533,258960449232244698699388⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨21967296518923980802907642,21967296518923982856377064⟩,⟨285037883139057573257763054,285037883139057576052698549⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨308959093568113997312904522,308959093568114004004982651⟩,⟨716879108241711511934624442,716879108241711520543421980⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨1086619790154587866444624811,1086619790154587878611652780⟩,⟨444321913332138405495820725,444321913332138419821829513⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨1961456744879693425792273372,1961456744879693444523620045⟩,⟨(-1342700491251663943620894195),(-1342700491251663923530132573)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨1923725353671502923373504190,1923725353671502953738783173⟩,⟨(-4655856447770424344633948448),(-4655856447770424314271885923)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨140311860005202612141022784,140311860005202655163722629⟩,⟨(-7969424405144864868900609496),(-7969424405144864827082440867)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-2996022081013712715339077376),(-2996022081013712662428508782)⟩,⟨(-9199810425852862531024643757),(-9199810425852862479799819369)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-5852092406032453564373174547),(-5852092406032453492565399471)⟩,⟨(-7578068521493049642969631738),(-7578068521493049571812735714)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-6920066440090589565846345911),(-6920066440090589419581817086)⟩,⟨(-4245665181641751864543295258),(-4245665181641751718146914513)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-6033738461053199240699083001),(-6033738461053198808335925775)⟩,⟨(-1059480691248653744923621747),(-1059480691248653312226976891)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-4150522173488774234419729777),(-4150522173488772797916787406)⟩,⟨860966481012945655725854687,860966481012947092427657318⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-2322871036025688769262882336),(-2322871036025684389820118016)⟩,⟨1491942516139851045765201714,1491942516139855425228493312⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-1063968498863686153818215721),(-1063968498863677964044843044)⟩,⟨1358379512257756659172601676,1358379512257764848915134338⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-387369435509525170848222814),(-387369435509515278976892001)⟩,⟨954281942899621712125833799,954281942899631603967033223⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-101833630454105874682435060),(-101833630454098122912482304)⟩,⟨536179549214820892610257117,536179549214828644361627784⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-14628276732241260302389153),(-14628276732238401588088615)⟩,⟨170140137607062312235483286,170140137607065170943837399⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-3772830745709500302530722925),(-3772830745709406844540202200)⟩,⟨(-4577423037665570319424206664),(-4577423037665476860877202483)⟩⟩
lemma checked : cachedMomentRuleBox density1 hk9_1_2 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 9 2) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk9_1_2 (tableDensity true) (fullFactor true 9 2) density1_contains hk9_1_2_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-45169492557710358068466749779),(-45169492557710358029468232360)⟩,⟨345056852622460543654579389,345056852622460582085388304⟩⟩
lemma atomChecked : tableAtomBox true ha9_1_2 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 9 2) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha9_1_2 9 2 ha9_1_2_contains
 def realAnswer : RBox := ⟨(-48942323303419858371097472704),(-48942323303419764873908434560)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 9 2) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm9_1_1_2
namespace hm9_0_1_3
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk9_1_3 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-85),31⟩,⟨(-64),55⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-186),134⟩,⟨(-218),101⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-264),215⟩,⟨(-386),92⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-146),527⟩,⟨(-372),302⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-429),440⟩,⟨(-227),642⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-733),351⟩,⟨(-656),428⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-409),894⟩,⟨(-626),675⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-1110),794⟩,⟨(-921),981⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-814),1105⟩,⟨(-1052),857⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-878),891⟩,⟨(-961),872⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-628),952⟩,⟨(-730),874⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-832),486⟩,⟨(-656),665⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-451),563⟩,⟨(-599),351⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-203),351⟩,⟨(-291),359⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-214),193⟩,⟨(-97),212⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-76),72⟩,⟨(-36),76⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨118121756964,118121757033⟩,⟨(-755279903488),(-755279903417)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨310970757736,310970757919⟩,⟨(-1477748996147),(-1477748995966)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨347543755274,347543755572⟩,⟨(-1041152166590),(-1041152166294)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨223400236995,223400237392⟩,⟨(-391105659316),(-391105658918)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨85866683541,85866684041⟩,⟨(-79374628995),(-79374628492)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨19733944491,19733945106⟩,⟨(-6118828065),(-6118827452)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨2540097337,2540098033⟩,⟨826936096,826936790⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨119000963,119001708⟩,⟨247605276,247606023⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-13129080),(-13128316)⟩,⟨20978794,20979554⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-2139695),(-2138945)⟩,⟨(-380798),(-380045)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-16287),(-15626)⟩,⟨(-207090),(-206426)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨22558,23108⟩,⟨(-6944),(-6393)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨1588,2112⟩,⟨2742,3270⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-580),(-177)⟩,⟨378,781⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-307),(-51)⟩,⟨(-99),157⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-87),21⟩,⟨(-71),37⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨33480249133454169419,33480249133454169592⟩,⟨19356855877483764376,19356855877483764544⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨79901678357345661364,79901678357345661749⟩,⟨37239438791172500793,37239438791172501173⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨82065155947424456262,82065155947424456681⟩,⟨22414761181024558337,22414761181024558752⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨52928274815262858316,52928274815262858657⟩,⟨1558552771764521984,1558552771764522320⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨22731933043750261481,22731933043750261741⟩,⟨(-5923519501702653925),(-5923519501702653664)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨6605421381458458055,6605421381458458268⟩,⟨(-4154387996979696436),(-4154387996979696219)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨1310724814309936786,1310724814309937012⟩,⟨(-1534522205613660216),(-1534522205613659984)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨178305271256529402,178305271256529648⟩,⟨(-384863008672125711),(-384863008672125473)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨16139418088830032,16139418088830328⟩,⟨(-74625720771552712),(-74625720771552413)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨769604209526426,769604209526746⟩,⟨(-12517818828169649),(-12517818828169331)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-26248135856203),(-26248135855858)⟩,⟨(-2021820146216417),(-2021820146216077)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-4779377270211),(-4779377269872)⟩,⟨(-345591101248165),(-345591101247827)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨2878991662032,2878991662345⟩,⟨(-67193199617131),(-67193199616817)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨2021940548557,2021940548801⟩,⟨(-15491505020785),(-15491505020539)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨901295492043,901295492209⟩,⟨(-4150277510372),(-4150277510203)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨245986233554,245986233624⟩,⟨(-907117387398),(-907117387330)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨1404450224424240227777869,1404450224424243532149342⟩,⟨(-487905277888551258784164),(-487905277888547954449273)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨3412064370358824929320998,3412064370358831597099940⟩,⟨(-1622966768375476859098733),(-1622966768375470191321208)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨3574573328909605039968046,3574573328909609839976915⟩,⟨(-2765153624681535519369683),(-2765153624681530719152834)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨2183410678652208814457703,2183410678652210535768711⟩,⟨(-3176255530298903482721817),(-3176255530298901760994405)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨532525607360984358092818,532525607360984696738173⟩,⟨(-2516507259172977852948708),(-2516507259172977513940577)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-352033620370078208942963),(-352033620370078150899073)⟩,⟨(-1356776878590440103976967),(-1356776878590440045847293)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-446361984875088234508027),(-446361984875088227781813)⟩,⟨(-463630373466541105041003),(-463630373466541098341163)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-247605128696564365800223),(-247605128696564364623322)⟩,⟨(-67041157426054638843098),(-67041157426054637698042)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-88079459643319424473508),(-88079459643319424050029)⟩,⟨25136319733663724831516,25136319733663725248381⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-21170530923419386309335),(-21170530923419386146945)⟩,⟨21737914308116731093141,21737914308116731256217⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-2817045023363713673788),(-2817045023363713613925)⟩,⟨9281480489792109258459,9281480489792109319289⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨381585890766038080427,381585890766038102332⟩,⟨3096282438713582159177,3096282438713582181398⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨472588329281122093719,472588329281122101933⟩,⟨936802587858446141181,936802587858446149448⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨251380559107932409748,251380559107932412915⟩,⟨280497260490965849542,280497260490965852714⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨109233746195363740013,109233746195363741239⟩,⟨85235020701998659762,85235020701998660983⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨30075768852046454944,30075768852046455278⟩,⟨19425729703413226077,19425729703413226408⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨718444686218187380760060958,718444686218193122669027126⟩,⟨(-78145557586461905716658191),(-78145557586456163695156367)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨1884893126307877341254136452,1884893126307898728120546943⟩,⟨(-435982503078639694058418522),(-435982503078618306926507307)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨2304819263284999207518884326,2304819263285049526744740540⟩,⟨(-1149450689824706614201953114),(-1149450689824656294723065592)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨1796892072193080619959450226,1796892072193179564947971474⟩,⟨(-1876493708476666800523747763),(-1876493708476567855442653234)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨697948533976641133042744918,697948533976794341759153934⟩,⟨(-2076891624264473415737775565),(-2076891624264320207121485185)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-305505649834306601065001406),(-305505649834141557692011411)⟩,⟨(-1581643071219309954624951353),(-1581643071219144911461922118)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-728306095310207261679361158),(-728306095310031106070235954)⟩,⟨(-765481002734464001965319817),(-765481002734287846470559246)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-616351945926628968372892696),(-616351945926482626426928982)⟩,⟨(-128806587953005097370136593),(-128806587952858755423128953)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-318509531046146112633044835),(-318509531046076874859728953)⟩,⟨139176679358240443755226088,139176679358309681565548542⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-94838404559724127617901638),(-94838404559695734191028081)⟩,⟨154904236456721819780757034,154904236456750213226607819⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨2582378950036474625624318,2582378950047182124815369⟩,⟨91934306475125672785651300,91934306475136380285534527⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨24065054532713328645518748,24065054532716059568778480⟩,⟨39351474200222228406984582,39351474200224959326689824⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨19393543239428855827166467,19393543239429446816001683⟩,⟨12748807435268933352382870,12748807435269524338437052⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨11282435774834948878816355,11282435774835133821352392⟩,⟨2757589923106771172689246,2757589923106956114279625⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨5409592047055863933273381,5409592047055921879437927⟩,⟨39094287836298648013087,39094287836356593930562⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨1570178752579755255795786,1570178752579768536122694⟩,⟨(-173881357700582987346039),(-173881357700569707062152)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨11557381943455720945761497258,11557381943455720967607788775⟩,⟨(-950170624765793989390049095),(-950170624765793968875504354)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨31646822003470774235435280458,31646822003470774302099464804⟩,⟨(-6839213988186194343315748777),(-6839213988186194280092379374)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨42206388730962504025920030608,42206388730962504139074695280⟩,⟨(-21269163070697439506256297530),(-21269163070697439396957830674)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨37705156495075458216276545362,37705156495075458374371272305⟩,⟨(-40547112067695448466736896989),(-40547112067695448311093730972)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨18256371769321573560885957879,18256371769321573757581096389⟩,⟨(-53959928541986876436280029093),(-53959928541986876239586573666)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-7408110609467118292821130096),(-7408110609467118075607752152)⟩,⟨(-51959366024553211441361296744),(-51959366024553211222275130318)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-26364097553707031604499496432),(-26364097553707031386136016971)⟩,⟨(-34773923895509486256385823373),(-34773923895509486035889996253)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-30918847210361078587480869823),(-30918847210361078360524590789)⟩,⟨(-12359824521834295756240584676),(-12359824521834295528639996096)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-23439415025785932966333671947),(-23439415025785932650923447349)⟩,⟨4313620521814267973438805372,4313620521814268288714452114⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-12030554928207835737919281607),(-12030554928207835026475109669)⟩,⟨11030598582649880752895917821,11030598582649881464155292084⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-3185085378469221774165192716),(-3185085378469219203475178986)⟩,⟨10375675980539060968374176488,10375675980539063539062907311⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨1238834323209002904107614628,1238834323209010319507278476⟩,⟨6943469765272438267058370191,6943469765272445682499291481⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨2412708134702805400879180256,2412708134702818678275569350⟩,⟨3744007098121774994664353310,3744007098121788272072550545⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨2052127342223892613072108387,2052127342223907999014649190⟩,⟨1707093365564053889139179881,1707093365564069275068542454⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨1243975837992594883040442706,1243975837992606490649568116⟩,⟨659017255692249275517258577,659017255692260883110239934⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨406299947691273401469059888,406299947691277648471828068⟩,⟨163454338077588227138854568,163454338077592474135140775⟩⟩
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
noncomputable def ans : CBox := ⟨⟨8465615923538483201673749118,8465615923538647506039841718⟩,⟨(-31897719643380992620171458966),(-31897719643380828316869639249)⟩⟩
lemma checked : cachedMomentRuleBox density0 hk9_1_3 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 9 3) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk9_1_3 (tableDensity false) (fullFactor true 9 3) density0_contains hk9_1_3_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-2695386910296400595389496802),(-2695386910296400557495425495)⟩,⟨(-41641432141394290308711272536),(-41641432141394290270195269227)⟩⟩
lemma atomChecked : tableAtomBox false ha9_1_3 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 9 3) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha9_1_3 9 3 ha9_1_3_contains
 def realAnswer : RBox := ⟨5770229013242082606184252316,5770229013242246948644416223⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 9 3) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm9_0_1_3
namespace hm9_1_1_3
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk9_1_3 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-22),16⟩,⟨(-19),16⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-36),31⟩,⟨(-45),23⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-50),48⟩,⟨(-73),21⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-34),100⟩,⟨(-66),67⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-83),77⟩,⟨(-45),114⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-121),73⟩,⟨(-122),73⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-69),149⟩,⟨(-105),118⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-181),129⟩,⟨(-155),159⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-133),184⟩,⟨(-178),142⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-150),153⟩,⟨(-161),148⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-109),169⟩,⟨(-132),153⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-151),89⟩,⟨(-117),123⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-86),101⟩,⟨(-112),66⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-38),66⟩,⟨(-59),68⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-42),41⟩,⟨(-20),41⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-21),20⟩,⟨(-16),21⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨72246596380,72246596403⟩,⟨(-94869219190),(-94869219167)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨148391782238,148391782278⟩,⟨(-179242649548),(-179242649512)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨116597531990,116597532041⟩,⟨(-117477608339),(-117477608290)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨53462225302,53462225364⟩,⟨(-39114169074),(-39114169011)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨15669572998,15669573078⟩,⟨(-6236167338),(-6236167260)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨2961695291,2961695385⟩,⟨20467113,20467209⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨326314921,326315031⟩,⟨206858465,206858575⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨9914515,9914634⟩,⟨39288858,39288980⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-2468225),(-2468098)⟩,⟨2822277,2822406⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-325146),(-325017)⟩,⟨(-101067),(-100937)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨732,856⟩,⟨(-33888),(-33766)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨3926,4036⟩,⟨(-844),(-734)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨224,334⟩,⟨509,616⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-122),(-38)⟩,⟨57,143⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-65),(-2)⟩,⟨(-28),29⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-23),16⟩,⟨(-23),16⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨4147521670123368424,4147521670123368489⟩,⟨7683049945613420403,7683049945613420466⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨10901321405957192951,10901321405957193088⟩,⟨16681290995370786481,16681290995370786614⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨12910714470365235236,12910714470365235380⟩,⟨14202020127722419663,14202020127722419802⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨9645349375260076021,9645349375260076131⟩,⟨6774772713465656529,6774772713465656640⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨4768232715165605268,4768232715165605351⟩,⟨1703456721720153809,1703456721720153894⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨1599732339348254694,1599732339348254757⟩,⟨60677370206669187,60677370206669253⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨376281720339257055,376281720339257117⟩,⟨(-110337842713743541),(-110337842713743480)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨65196042330636900,65196042330636960⟩,⟨(-44380362906913829),(-44380362906913770)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨8992112571882758,8992112571882823⟩,⟨(-10526866323089847),(-10526866323089784)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨1117043415657033,1117043415657096⟩,⟨(-1957897476192365),(-1957897476192301)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨148826975389627,148826975389691⟩,⟨(-329951557846380),(-329951557846316)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨24720009885652,24720009885715⟩,⟨(-55885753826078),(-55885753826014)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨5240826064139,5240826064193⟩,⟨(-10327573283509),(-10327573283449)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨1351454227165,1351454227212⟩,⟨(-2221761657293),(-2221761657247)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨396156617385,396156617422⟩,⟨(-560844598808),(-560844598773)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨91015167325,91015167348⟩,⟨(-118687988803),(-118687988784)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨473880252635101276057394,473880252635104051205062⟩,⟨149895787669878175300721,149895787669880950452249⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨1220027639175564224563435,1220027639175569820214099⟩,⟨246655065034895885962234,246655065034901481613209⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨1447595797464005593484838,1447595797464009615097668⟩,⟨(-18179657788855437766975),(-18179657788851416175429)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨1127346675457234956590027,1127346675457236394438911⟩,⟨(-380738819599587495947417),(-380738819599586058141097)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨569606135547926856724120,569606135547927137636352⟩,⟨(-510534104691549428676284),(-510534104691549147800608)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨143272787983423083620676,143272787983423130513920⟩,⟨(-378692327242716455572192),(-378692327242716408687417)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-29632569595064612599363),(-29632569595064607913675)⟩,⟨(-179956354887018973785003),(-179956354887018969096644)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-46595576524891734406576),(-46595576524891733887256)⟩,⟨(-54405859618473493056240),(-54405859618473492533814)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-23921336153061218578343),(-23921336153061218424187)⟩,⟨(-7903187593708143802861),(-7903187593708143648101)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-8047013991166270029439),(-8047013991166269971783)⟩,⟨1665036531753853937245,1665036531753853994822⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-2004382094526498381018),(-2004382094526498359789)⟩,⟨1648901334379177502156,1648901334379177523294⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-365380601116998579102),(-365380601116998571300)⟩,⟨746285178903330396085,746285178903330403860⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-28468608414429223323),(-28468608414429220370)⟩,⟨278846798316902398964,278846798316902401917⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨16892703104345740311,16892703104345741468⟩,⟨99936229410859236694,99936229410859237853⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨12790321651065417041,12790321651065417501⟩,⟨35319163732200997417,35319163732200997876⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨4129255243447105946,4129255243447106079⟩,⟨8833976198372105647,8833976198372105782⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨234421280997803734779030840,234421280997808452598116626⟩,⟨(-37730842550325351535802117),(-37730842550320633737337184)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨625120726492806282625642988,625120726492823857382439154⟩,⟨(-173004933210135885998133775),(-173004933210118311292430106)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨789988573669359316220123782,789988573669400674586132379⟩,⟨(-415004008365218550296618556),(-415004008365177191983696644)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨653067638631957452656073542,653067638632038794125791426⟩,⟨(-661289697446926290656906679),(-661289697446844949213173023)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨298791312559890973867187684,298791312560016943309210930⟩,⟨(-741022148509224875757255350),(-741022148509098906301861628)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-55389903595490269142845954),(-55389903595354567176401586)⟩,⟨(-588911962760441506143087420),(-588911962760305804136895619)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-231919357909810849141456531),(-231919357909666039663385338)⟩,⟨(-314111465751646954173573165),(-314111465751502144671353773)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-221551852832485445505828907),(-221551852832365199772431974)⟩,⟨(-82229290225583019443525422),(-82229290225462773709458487)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-130129062440094574585480379),(-130129062440037726654511630)⟩,⟨30277979799403225792288372,30277979799460073715813235⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-50389451964238268979943807),(-50389451964214982291622797)⟩,⟨50652761216485433468340093,50652761216508720152861838⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-9758544035380566714044259),(-9758544035371795927558724)⟩,⟨35223540432554577002536198,35223540432563347788845940⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨3261108998669399397612671,3261108998671633342973624⟩,⟨17816223477519093064506627,17816223477521327010503780⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨4704045788148406284924530,4704045788148889064186015⟩,⟨7452665277430753505261747,7452665277431236285022942⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨3225737105426887972197506,3225737105427038879965806⟩,⟨2732676456949227032252971,2732676456949377940188513⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨1679003217047844744431041,1679003217047891988103846⟩,⟨889547296653574126386221,889547296653621370102331⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨506393924026768583708385,506393924026779406433475⟩,⟨199242541538624923352639,199242541538635746085217⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨341895708236023460328137649,341895708236023463814575981⟩,⟨(-44490797349165247873461466),(-44490797349165245232416746)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨844819457677166169856180337,844819457677166180587659051⟩,⟨(-420242400031775980097062389),(-420242400031775971527508505)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨460543002900066160488791927,460543002900066178326807553⟩,⟨(-1349001429529701970903630568),(-1349001429529701955422057295)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-1795690867795149389553585578),(-1795690867795149364531972137)⟩,⟨(-2286517473762389251771337420),(-2286517473762389228057025475)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-5904004477916342123948871237),(-5904004477916342085777392359)⟩,⟨(-1949208229091312205278940430),(-1949208229091312166722899237)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-9920400671361800180861242340),(-9920400671361800127606026111)⟩,⟨638692641104164225861075631,638692641104164280949418988⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-11212664462813189252795227427),(-11212664462813189185115475312)⟩,⟨4832279034389738310939760804,4832279034389738380736749571⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-8863670982368024603602736386),(-8863670982368024507833958343)⟩,⟨8436444954545995049078582393,8436444954545995145440500313⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-4437285732342703566613206911),(-4437285732342703376047045196)⟩,⟨9531463318812413280556125126,9531463318812413470785976956⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-383585592757469056784450744),(-383585592757468523081318292)⟩,⟨8029539044180825725175848378,8029539044180826258356791739⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨1887357338425027112722951596,1887357338425029178465505011⟩,⟨5307809809682812984042015421,5307809809682815049579561540⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨2442380338992086652940074600,2442380338992092685129353018⟩,⟨2795248160702259227434836169,2795248160702265259636209723⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨2046968501915961561253526152,2046968501915972392699114113⟩,⟨1141074718393535263292228789,1141074718393546094801025942⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨1375293221851482837046633019,1375293221851495403126083386⟩,⟨311549983896666972538641218,311549983896679538670857646⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨751308976608002087414527801,751308976608011573422381669⟩,⟨15067190061085730542542622,15067190061095216581394449⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨234969030623902442012178538,234969030623905913763345777⟩,⟨(-19862310058557919154210284),(-19862310058554447393458493)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-5035211391453284608828353004),(-5035211391453149766538755288)⟩,⟨5350109529043964538408619781,5350109529044099380244740603⟩⟩
lemma checked : cachedMomentRuleBox density1 hk9_1_3 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 9 3) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk9_1_3 (tableDensity true) (fullFactor true 9 3) density1_contains hk9_1_3_contains
noncomputable def atomAnswer : CBox := ⟨⟨3524736728849139190570941032,3524736728849139240124726587⟩,⟨54454180492592533430255352066,54454180492592533480622433316⟩⟩
lemma atomChecked : tableAtomBox true ha9_1_3 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 9 3) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha9_1_3 9 3 ha9_1_3_contains
 def realAnswer : RBox := ⟨(-1510474662604145418357411972),(-1510474662604010526314028701)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 9 3) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm9_1_1_3
namespace hm9_0_1_4
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk9_1_4 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-68),164⟩,⟨(-84),152⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-323),319⟩,⟨(-182),456⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-539),372⟩,⟨(-143),766⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-992),173⟩,⟨(-673),491⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-600),910⟩,⟨(-1184),326⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-715),1346⟩,⟨(-644),1404⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-1829),816⟩,⟨(-1543),1113⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-1698),2426⟩,⟨(-2044),2097⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-2547),1804⟩,⟨(-2024),2320⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-2121),2071⟩,⟨(-2027),2218⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-2231),1531⟩,⟨(-2117),1694⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-1169),1968⟩,⟨(-1553),1602⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-1340),1051⟩,⟨(-846),1408⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-812),474⟩,⟨(-833),666⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-438),487⟩,⟨(-485),218⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-152),165⟩,⟨(-164),72⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-1117793352687),(-1117793352598)⟩,⟨779857668098,779857668189⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-2286058118085),(-2286058117847)⟩,⟨1440386712694,1440386712934⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-1773877754098),(-1773877753724)⟩,⟨874649031196,874649031576⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-788690466686),(-788690466151)⟩,⟨224245929754,224245930288⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-215673034497),(-215673033763)⟩,⟨(-1748051300),(-1748050563)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-35202327018),(-35202326022)⟩,⟨(-16082711002),(-16082710005)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-2685789415),(-2685788174)⟩,⟨(-4324503457),(-4324502216)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨116462402,116463876⟩,⟨(-520230060),(-520228587)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨45465405,45467065⟩,⟨(-18033531),(-18031873)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨3121983,3123765⟩,⟨3056672,3058455⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-199226),(-197526)⟩,⟨373713,375410⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-48544),(-47048)⟩,⟨(-12811),(-11316)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-1030),298⟩,⟨(-8055),(-6727)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨805,1737⟩,⟨(-1188),(-254)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨92,647⟩,⟨(-162),393⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-58),154⟩,⟨(-41),174⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨975627950563058527,975627950563058824⟩,⟨(-56503469177639800564),(-56503469177639800262)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-9665580207106679241),(-9665580207106678548)⟩,⟨(-128901710452169490834),(-128901710452169490126)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-31358437574356950083),(-31358437574356949291)⟩,⟨(-121623132820569454060),(-121623132820569453255)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-37948193814185001122),(-37948193814185000461)⟩,⟨(-69251026385923504257),(-69251026385923503592)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-25480561068040245228),(-25480561068040244728)⟩,⟨(-24702313330411562325),(-24702313330411561823)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-10806410637426704834),(-10806410637426704434)⟩,⟨(-5153301003224756588),(-5153301003224756191)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-3127631055419543774),(-3127631055419543356)⟩,⟨(-381653808649433561),(-381653808649433144)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-664544507435050343),(-664544507435049913)⟩,⟨117367222152613554,117367222152613986⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-113088890996854879),(-113088890996854364)⟩,⟨50538221411853909,50538221411854423⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-17157428001758263),(-17157428001757729)⟩,⟨11662536956585761,11662536956586295⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-2614620953997694),(-2614620953997143)⟩,⟨2184887577854820,2184887577855368⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-445257786035400),(-445257786034885)⟩,⟨390631713878753,390631713879272⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-90630571442622),(-90630571442167)⟩,⟨73890884707956,73890884708418⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-22460479023794),(-22460479023452)⟩,⟨15822267618398,15822267618743⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-6450761481285),(-6450761481054)⟩,⟨3879446802130,3879446802356⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-1470486664388),(-1470486664303)⟩,⟨796854219635,796854219722⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-1097603539181190129842186),(-1097603539181186185146577)⟩,⟨(-1437593377170229087758002),(-1437593377170225143154558)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-3192658216188434916749822),(-3192658216188427189132656)⟩,⟨(-3326745362527036968855133),(-3326745362527029241583660)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-4625253103329935057553390),(-4625253103329929837526067)⟩,⟨(-3065965104251197924394294),(-3065965104251192705025018)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-4607530222484274371594144),(-4607530222484272548578805)⟩,⟨(-1256236143919477567743732),(-1256236143919475745443684)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-3193323946629637230578842),(-3193323946629636725114991)⟩,⟨447381248624233633776771,447381248624234138969047⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-1454715820762495836292178),(-1454715820762495759100821)⟩,⟨1028883084325075890297920,1028883084325075967515443⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-343988834180243200603733),(-343988834180243193182282)⟩,⟨756564658539185234092356,756564658539185241608267⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨43871289206778494193562,43871289206778495488567⟩,⟨334103253425522758433077,334103253425522759760934⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨78076697852219395741559,78076697852219396234039⟩,⟨94373814231459787672481,94373814231459788164416⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨38934193441247210286207,38934193441247210492930⟩,⟨13798084301781334216748,13798084301781334419416⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨13272254309842596233706,13272254309842596318396⟩,⟨(-2071300190771303031726),(-2071300190771302948313)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨3650237830430135095270,3650237830430135128949⟩,⟨(-2437326206357042968729),(-2437326206357042935167)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨873087625754748220371,873087625754748233771⟩,⟨(-1215435750657584916903),(-1215435750657584903459)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨185060215400571759611,185060215400571765038⟩,⟨(-510596999373791969187),(-510596999373791963724)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨32470243011435595310,32470243011435597480⟩,⟨(-198665329806984259132),(-198665329806984256944)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨3581341482338255948,3581341482338256542⟩,⟨(-52098844271719785478),(-52098844271719784877)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-206909620758105964519368344),(-206909620758099183393915617)⟩,⟨(-720376592813382220867840841),(-720376592813375439834638981)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-785639038752237970199675465),(-785639038752213233725719925)⟩,⟨(-1852187547628576188329554238),(-1852187547628551452061582866)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-1611223295319977634819949404),(-1611223295319921434608056531)⟩,⟨(-2157592556661007776030648371),(-2157592556660951575979206291)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-2293589656480785648799461228),(-2293589656480680012088998831)⟩,⟨(-1495064305073307851543953389),(-1495064305073202214816377097)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-2313124206890625301995527796),(-2313124206890471507888438979)⟩,⟨(-299593797632407757557628528),(-299593797632253963247222748)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-1600553257275195528314408475),(-1600553257275024331318137927)⟩,⟨671675692975669592399630737,671675692975840789646903001⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-643311670411617431595129612),(-643311670411407066653987845)⟩,⟨958353562065010280763913990,958353562065220645777512738⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨18629600724494466350613624,18629600724652229839436116⟩,⟨697916339105850598941124708,697916339106008362394297448⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨239621673567310742512591691,239621673567382698600481472⟩,⟨309495703492121842275528855,309495703492193798312638882⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨199158914525445687638432838,199158914525482101038317105⟩,⟨59061394187321544921867444,59061394187357958310374042⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨101912743083014469762127649,101912743083026614235730359⟩,⟨(-31843056853300525874118649),(-31843056853288381395448911)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨36390270768349278437067505,36390270768352060199235431⟩,⟨(-40289226266838041430272610),(-40289226266835259661622896)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨7726995694847082917481487,7726995694847893077925212⟩,⟨(-26541439872073599772084401),(-26541439872072789609258886)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-938305519042025220230249),(-938305519041778328923691)⟩,⟨(-13934169115600870033861340),(-13934169115600623142130458)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-1971326627053186587503056),(-1971326627053114026878891)⟩,⟨(-6244187475641513575298916),(-6244187475641441014728128)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-793631758721560759746602),(-793631758721544657585510)⟩,⟨(-1746838661099805480125394),(-1746838661099789378016418)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-1406600779228699458335484104),(-1406600779228699439002582514)⟩,⟨(-10394369545914841003015021429),(-10394369545914840982528511751)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-7756677406594339100283514813),(-7756677406594339040585897982)⟩,⟨(-28311220766667271273373018207),(-28311220766667271210720418191)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-21595710940678311931576735728),(-21595710940678311827947993435)⟩,⟨(-37240378745011306422433042250),(-37240378745011306315593554569)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-39344335568423977352839288381),(-39344335568423977204355805213)⟩,⟨(-32099204468137502835818635229),(-32099204468137502685510300840)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-51013363888652114259444696191),(-51013363888652114070301187510)⟩,⟨(-13229701206441835268031994546),(-13229701206441835079323152108)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-47848679368465497592652755995),(-47848679368465497380029721614)⟩,⟨10865211476545162858564405608,10865211476545163069094272187⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-30464827855899548583067371738),(-30464827855899548364710508339)⟩,⟨27856215257662496542490733699,27856215257662496758916927871⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-8729197347253107360571299456),(-8729197347253107132997054714)⟩,⟨30685713718776835390073638943,30685713718776835617212623194⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨6765111212924556336542005672,6765111212924556644800120016⟩,⟨22129132789383177789822575365,22129132789383178098309122143⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨12256965319111596503863783164,12256965319111597208726263180⟩,⟨10376974489940255730261738985,10376974489940256435324642433⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨10677384645489948290483145974,10677384645489951007616483359⟩,⟨1729965185383265269176013274,1729965185383267986303208414⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨6742399317272092246924362453,6742399317272099740600614113⟩,⟨(-2263094878243321888141320359),(-2263094878243314394496451449)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨3385779940915135361082878386,3385779940915148192117003351⟩,⟨(-3020166137729360464496469098),(-3020166137729347633460517223)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨1388161777149317202447924770,1388161777149331353961987719⟩,⟨(-2363616994640873674589540614),(-2363616994640859523053031137)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨456664690806381248834151116,456664690806393124116479860⟩,⟨(-1380155981045849995602195662),(-1380155981045838120301647888)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨95608301681763040352303468,95608301681768071546922608⟩,⟨(-443366300636290374485454270),(-443366300636285343284963060)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-29210711342382426720085257044),(-29210711342382248848985839646)⟩,⟨(-5176231910101104937500127168),(-5176231910100927065619071389)⟩⟩
lemma checked : cachedMomentRuleBox density0 hk9_1_4 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 9 4) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk9_1_4 (tableDensity false) (fullFactor true 9 4) density0_contains hk9_1_4_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-37510553686821157316992208189),(-37510553686821157279546608892)⟩,⟨4622772124521094635901232630,4622772124521094672708673547⟩⟩
lemma atomChecked : tableAtomBox false ha9_1_4 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 9 4) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha9_1_4 9 4 ha9_1_4_contains
 def realAnswer : RBox := ⟨(-66721265029203584037177465233),(-66721265029203406128432448538)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 9 4) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm9_0_1_4
namespace hm9_1_1_4
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk9_1_4 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-21),34⟩,⟨(-21),34⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-66),58⟩,⟨(-40),87⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-109),64⟩,⟨(-32),137⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-174),39⟩,⟨(-132),81⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-97),173⟩,⟨(-201),70⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-130),216⟩,⟨(-107),240⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-292),141⟩,⟨(-255),177⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-274),388⟩,⟨(-325),335⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-414),295⟩,⟨(-326),378⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-353),345⟩,⟨(-338),372⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-387),261⟩,⟨(-362),295⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-203),348⟩,⟨(-279),276⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-235),190⟩,⟨(-146),252⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-146),83⟩,⟨(-148),122⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-85),87⟩,⟨(-87),39⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-34),34⟩,⟨(-34),18⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-211236508763),(-211236508736)⟩,⟨24069555529,24069555556⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-415077806813),(-415077806770)⟩,⟨32496986030,32496986074⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-298224689135),(-298224689077)⟩,⟨(-410546635),(-410546573)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-119346530917),(-119346530838)⟩,⟨(-17203060295),(-17203060216)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-28936877344),(-28936877241)⟩,⟨(-11404503115),(-11404503003)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-4111386347),(-4111386203)⟩,⟨(-3724296529),(-3724296385)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-221512132),(-221511947)⟩,⟨(-702097023),(-702096837)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨32129188,32129411⟩,⟨(-71764780),(-71764553)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨7233765,7234029⟩,⟨(-1605102),(-1604835)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨425488,425782⟩,⟨536174,536468⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-38475),(-38184)⟩,⟨57421,57715⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-8078),(-7806)⟩,⟨(-2907),(-2637)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-72),179⟩,⟨(-1441),(-1190)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨153,338⟩,⟨(-201),(-14)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨6,124⟩,⟨(-34),88⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-21),35⟩,⟨(-16),41⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨6872572567051843072,6872572567051843173⟩,⟨(-10749174148091758959),(-10749174148091758855)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨13519042406372849403,13519042406372849636⟩,⟨(-25905282570237962756),(-25905282570237962526)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨8753539962712462044,8753539962712462302⟩,⟨(-26951718937288940137),(-26951718937288939879)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨1433490808055894060,1433490808055894266⟩,⟨(-17519346341377551755),(-17519346341377551546)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-1540643865705124108),(-1540643865705123959)⟩,⟨(-7492430778943315397),(-7492430778943315250)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-1233953539371579379),(-1233953539371579271)⟩,⟨(-2123475968173901354),(-2123475968173901246)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-468140022915390271),(-468140022915390170)⟩,⟨(-394412663949739890),(-394412663949739787)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-117219842195275416),(-117219842195275320)⟩,⟨(-44720033022464190),(-44720033022464097)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-22397641960893922),(-22397641960893823)⟩,⟨(-1652473806376441),(-1652473806376338)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-3692102523783147),(-3692102523783048)⟩,⟨520144920554261,520144920554360⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-589539268036049),(-589539268035955)⟩,⟨156442703566805,156442703566900⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-100356819508804),(-100356819508717)⟩,⟨29928497405104,29928497405188⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-19473058208376),(-19473058208302)⟩,⟨5121589142226,5121589142302⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-4484564254071),(-4484564254012)⟩,⟨894981006740,894981006799⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-1205039108461),(-1205039108416)⟩,⟨170185410028,170185410071⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-264627738576),(-264627738554)⟩,⟨28480469014,28480469037⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-6875123838739331090088),(-6875123838736018075142)⟩,⟨(-604597669842443755829141),(-604597669842440442804723)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-183884360319800462859151),(-183884360319793977725794)⟩,⟨(-1507778601030053764984098),(-1507778601030047279815020)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-592045910905354032510330),(-592045910905349659366558)⟩,⟨(-1676100196194501959604098),(-1676100196194497586392438)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-905921828196490912835525),(-905921828196489390741965)⟩,⟨(-1163116602228672107599723),(-1163116602228670585432922)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-844959411275036040472439),(-844959411275035620853530)⟩,⟨(-453218012612839581600139),(-453218012612839161954150)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-514656033955788212228645),(-514656033955788149556133)⟩,⟨11675551708812672320,11675551708875341929⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-201899882695194205817928),(-201899882695194200537845)⟩,⟨121252301457768129739903,121252301457768135010616⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-42413923564775467463722),(-42413923564775466842295)⟩,⟨83993979122116729306369,83993979122116729924735⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨3164237727293293107413,3164237727293293291352⟩,⟨33539038715426356751968,33539038715426356936047⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨6640904362653604563081,6640904362653604635210⟩,⟨9001665493133391714582,9001665493133391787114⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨3262784265940720934527,3262784265940720963975⟩,⟨1507882711395075640621,1507882711395075670187⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨1168965795573116670881,1168965795573116682754⟩,⟨(-12655695228403603555),(-12655695228403591673)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨371416730631731685002,371416730631731689805⟩,⟨(-147886533899246461908),(-147886533899246457110)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨115465548713815535009,115465548713815536992⟩,⟨(-89582834640994018382),(-89582834640994016406)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨36098898256415511334,36098898256415512142⟩,⟨(-40931426808986767846),(-40931426808986767038)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨8364365736591802224,8364365736591802454⟩,⟨(-11503483678695227963),(-11503483678695227732)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-80013747055496520419044514),(-80013747055490948714044923)⟩,⟨(-232888729140740931474800412),(-232888729140735359752577441)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-289663592749880258610987763),(-289663592749859931288335259)⟩,⟨(-609170664388213825061059553),(-609170664388193497697988315)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-573906685831442654258479237),(-573906685831396462258453175)⟩,⟨(-735642094736562698361278744),(-735642094736516506326171653)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-812176162363143164532548715),(-812176162363056322064389385)⟩,⟨(-547446941104194166347572854),(-547446941104107323876641117)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-835630194257385449544618511),(-835630194257258999128911938)⟩,⟨(-158898150246355400380680773),(-158898150246228950001599794)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-608877516564312875443699808),(-608877516564172114268697262)⟩,⟨188530104769389120888066527,188530104769529882013433721⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-279890079662300209297585388),(-279890079662127276981642082)⟩,⟨321887780377753515643583978,321887780377926447943853979⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-32071548868679910120635670),(-32071548868550278871643512)⟩,⟨260072911659800762634009138,260072911659930393890086262⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨68874096521902838491794227,68874096521961916739253527⟩,⟨133774430869773612180987820,133774430869832690439102097⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨70849027875713637288730502,70849027875743501970225138⟩,⟨40731574813182617012357929,40731574813212481696207679⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨42435397448230666955894305,42435397448240614937817447⟩,⟨(-187308399779905060026417),(-187308399769957079033302)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨19023712924435186601595973,19023712924437462125490775⟩,⟨(-9622398792114365574701712),(-9622398792112090052007009)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨6839117514840756541331978,6839117514841418368497601⟩,⟨(-7963426854207610074163860),(-7963426854206948247438612)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨1960477486891645045900007,1960477486891846509707062⟩,⟨(-4690149070925414133325657),(-4690149070925212669597140)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨398596950741238429077883,398596950741297589871572⟩,⟨(-2265061240782643135315089),(-2265061240782583974513337)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨38772140963294178438641,38772140963307301158923⟩,⟨(-659778971137698092055453),(-659778971137684969326591)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-56410874369489057591209874),(-56410874369489055059435725)⟩,⟨(-306710548910403355101329907),(-306710548910403351851399819)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-422254778106032209356124677),(-422254778106032201174377708)⟩,⟨(-743913075719728730091577513),(-743913075719728720096369447)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-1251153238244547007853707663),(-1251153238244546993157967333)⟩,⟨(-346017419937987667258756308),(-346017419937987650665885608)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-1985244499233314164633031533),(-1985244499233314142231926653)⟩,⟨1780949544302415453030742921,1780949544302415476300642173⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-1401166051499206014130791327),(-1401166051499205977626022924)⟩,⟨5582032861330039406119486787,5582032861330039441918371528⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨1354716743590979166146746374,1354716743590979218679977795⟩,⟨9199506786349095705862473384,9199506786349095756382545780⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨5530188081094997460059958565,5530188081094997528969394992⟩,⟨10146587971282862436602846254,10146587971282862503624889957⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨8918421834929994643196326275,8918421834929994738993289157⟩,⟨7618289047212717916101160803,7618289047212718011560114354⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨9689685048801213052146594974,9689685048801213235235680596⟩,⟨3222571461865758574843938152,3222571461865758758414724593⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨7887112679442040614660568689,7887112679442041140976930173⟩,⟨(-619418248423629189555987922),(-619418248423628662685546026)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨4983674549859964118229271758,4983674549859966301994085219⟩,⟨(-2586726797948393029465382435),(-2586726797948390845559528098)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨2427024543606343608076796288,2427024543606349702926355244⟩,⟨(-2849771940122149344607007773),(-2849771940122143249806830904)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨824454548347260124950062523,824454548347270590815673219⟩,⟨(-2240360545139401503113424960),(-2240360545139391037331583507)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨86737046166301817956311025,86737046166313374488981040⟩,⟨(-1445464542878690513214016624),(-1445464542878678956745948991)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-114114523317055615233699085),(-114114523317045910604133039)⟩,⟨(-767575151385958901022423747),(-767575151385949196424571194)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-61466755520673153430988336),(-61466755520669040445912691)⟩,⟨(-236351032591313015317638244),(-236351032591308902340408288)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨5517519361002446925691892499,5517519361002592918430249499⟩,⟨4006339095091631139165342362,4006339095091777132121004184⟩⟩
lemma checked : cachedMomentRuleBox density1 hk9_1_4 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 9 4) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk9_1_4 (tableDensity true) (fullFactor true 9 4) density1_contains hk9_1_4_contains
noncomputable def atomAnswer : CBox := ⟨⟨49052262513535359519407103935,49052262513535359568374426093⟩,⟨(-6045163547450662264311342330),(-6045163547450662216178534978)⟩⟩
lemma atomChecked : tableAtomBox true ha9_1_4 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 9 4) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha9_1_4 9 4 ha9_1_4_contains
 def realAnswer : RBox := ⟨54569781874537806444998996434,54569781874537952486904675592⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 9 4) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm9_1_1_4
namespace hm9_0_1_5
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk9_1_5 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-274),176⟩,⟨(-313),136⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-539),749⟩,⟨(-853),431⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-600),1303⟩,⟨(-1376),525⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-690),1868⟩,⟨(-857),1702⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-2058),998⟩,⟨(-929),2127⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-1993),1385⟩,⟨(-2498),848⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-1193),2700⟩,⟨(-1326),2602⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-3974),2715⟩,⟨(-3590),3157⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-3062),4506⟩,⟨(-3912),3676⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-3812),3947⟩,⟨(-4007),3670⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-2947),4132⟩,⟨(-3110),4049⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-3709),2239⟩,⟨(-3109),2890⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-1960),2552⟩,⟨(-2647),1636⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-904),1519⟩,⟨(-1231),1561⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-899),805⟩,⟨(-403),894⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-296),273⟩,⟨(-126),296⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨1906273667963,1906273668117⟩,⟨381121385314,381121385468⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨3757809605152,3757809605592⟩,⟨915215369709,915215370150⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨2694889199125,2694889199866⟩,⟨930358325678,930358326417⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨1049223389850,1049223390882⟩,⟨570133924584,570133925616⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨230173416536,230173417861⟩,⟨219772597939,219772599264⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨23282783177,23282784823⟩,⟨53117630520,53117632172⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-1117182021),(-1117180167)⟩,⟨7679804972,7679806825⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-642261432),(-642259504)⟩,⟨521921321,521923252⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-74804092),(-74802135)⟩,⟨(-19608681),(-19606723)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-1379031),(-1376665)⟩,⟨(-6897105),(-6894743)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨600235,602779⟩,⟨(-345459),(-342914)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨56956,59410⟩,⟨56158,58610⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-6599),(-4251)⟩,⟨9978,12326⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-3337),(-1601)⟩,⟨(-779),958⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-1003),58⟩,⟨(-986),77⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-229),179⟩,⟨(-343),64⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-58299862600350768416),(-58299862600350768051)⟩,⟨31072095839428289791,31072095839428290158⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-126351377631277671845),(-126351377631277670989)⟩,⟨83837835958565868342,83837835958565869191⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-106366441088479966806),(-106366441088479965848)⟩,⟨103412820035119031886,103412820035119032841⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-48336174609228072690),(-48336174609228071913)⟩,⟨80866238440200458985,80866238440200459762⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-9521587941471804481),(-9521587941471803912)⟩,⟨41821148654084512722,41821148654084513290⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨1751426620234889417,1751426620234889851⟩,⟨14590006332787183836,14590006332787184272⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨1761605078909503295,1761605078909503735⟩,⟨3519110208562134031,3519110208562134469⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨606202413285270208,606202413285270627⟩,⟨608453897261340712,608453897261341137⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨139734597442075515,139734597442076021⟩,⟨79489241124349962,79489241124350467⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨26099834681072006,26099834681072604⟩,⟨8514209128544370,8514209128544973⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨4509408497932773,4509408497933474⟩,⟨874356669427714,874356669428417⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨803637186909076,803637186909817⟩,⟨116773484546325,116773484547063⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨160572084200801,160572084201515⟩,⟨25903617107353,25903617108062⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨37773317716467,37773317717039⟩,⟨8192541252943,8192541253516⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨10275012193353,10275012193752⟩,⟨2888617972011,2888617972409⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨2265468522658,2265468522800⟩,⟨732658485420,732658485565⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-995340740617169156453288),(-995340740617165774886604)⟩,⟨1451828219259553492870463,1451828219259556874651128⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-2099047248611089865970747),(-2099047248611083490670183)⟩,⟨3982099135595496617021087,3982099135595502992964371⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-1392657901926675468142222),(-1392657901926671005182653)⟩,⟨5270105446873851305114918,5270105446873855768909420⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨330591799484476056169211,330591799484478198427901⟩,⟨4722329070795896719057083,4722329070795898861766593⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨1513181232052469016618979,1513181232052469565866796⟩,⟨2857873409731069076474252,2857873409731069625752304⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨1502157465276678481225482,1502157465276678554357159⟩,⟨1013280790079159506672674,1013280790079159579640355⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨857563864748075111134731,857563864748075118651576⟩,⟨42094270314279798933465,42094270314279806346075⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨306323608947608242046285,306323608947608243762815⟩,⟨(-177673111547421796290073),(-177673111547421794580580)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨58919295785899878013262,58919295785899878647669⟩,⟨(-117036173734612711513100),(-117036173734612710867572)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-4090530595298447012777),(-4090530595298446746884)⟩,⟨(-44798544946611122055747),(-44798544946611121785233)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-8456613938400721394317),(-8456613938400721285035)⟩,⟨(-12246392177439244695074),(-12246392177439244585512)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-4297114661181762315888),(-4297114661181762272966)⟩,⟨(-2437156917525494197090),(-2437156917525494154444)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-1690294890760536389723),(-1690294890760536372866)⟩,⟨(-242069268566136479148),(-242069268566136462472)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-619925716419985721388),(-619925716419985714621)⟩,⟨90318875599871126286,90318875599871132994⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-220688429982458258410),(-220688429982458255724)⟩,⟨77717946719171099573,77717946719171102244⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-55228559474861567534),(-55228559474861566804)⟩,⟨25745725016047552937,25745725016047553663⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-559663966776559576895602050),(-559663966776553430180873914)⟩,⟨271070867434213349076212492,271070867434219495845070002⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-1404628139829071107728986681),(-1404628139829049073146525639)⟩,⟨910319341142632803923222873,910319341142654838613972839⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-1536187083802140446037635360),(-1536187083802091937696663043)⟩,⟨1647168646107077259681138925,1647168646107125768065725832⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-880918902749862825778704477),(-880918902749775702792467727)⟩,⟨2133372212556822617916459785,2133372212556909740792963373⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨132222034236659229483508444,132222034236777261478839005⟩,⟨1981988420932807049566776789,1981988420932925081313564996⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨849658606478630603682431106,849658606478790448077367218⟩,⟨1231650493205341835719546618,1231650493205501679932241485⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨939731992829310776314755360,939731992829501493658636838⟩,⟨366705995089252369138765773,366705995089443086468073405⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨598569222364608280556204735,598569222364736684393517403⟩,⟨(-158865120788202483705766967),(-158865120788074079808033370)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨217599867955466852092464239,217599867955535419297108793⟩,⟨(-277465922877396074573032844),(-277465922877327507329299836)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨5165184579323038338695061,5165184579357709699892859⟩,⟨(-189997355419064108598165119),(-189997355419029437236712710)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-54147924629793980330808447),(-54147924629783808349012720)⟩,⟨(-83075161110736967737064663),(-83075161110726795765081449)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-46092030407026362405422934),(-46092030407023669119279183)⟩,⟨(-22107749440068749561127599),(-22107749440066056280508451)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-26337399227643959744652524),(-26337399227643100740197090)⟩,⟨394057435649092291422957,394057435649951294944837⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-12504656033799088658415584),(-12504656033798849742117393)⟩,⟨4910592033812623662522776,4910592033812862579137439⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-5164740145184788845654948),(-5164740145184723059992278)⟩,⟨3678087526114051313140457,3678087526114117099191934⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-1373389497091931109298974),(-1373389497091917041039855)⟩,⟨1260588108492649343922102,1260588108492663412328586⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-7457758861844093671997014283),(-7457758861844093656687241556)⟩,⟨1410963181314924411959419863,1410963181314924426475442611⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-20196925083250565885355421824),(-20196925083250565838440767660)⟩,⟨6737855664011138264774217170,6737855664011138309676773787⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-26165886943669259384233485488),(-26165886943669259303892490718)⟩,⟨17301883804151272811121363715,17301883804151272889357448973⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-21632012894824864067476739386),(-21632012894824863953738323113)⟩,⟨30328962255470763518322536442,30328962255470763631043581970⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-7030622528655360081790132568),(-7030622528655359937836577323)⟩,⟨38366309129549448399536524950,38366309129549448544134763273⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨11019005282882056482001291558,11019005282882056644039811400⟩,⟨35003766968354310905902004708,35003766968354311069749350173⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨23110358428610476669998633714,23110358428610476840469679636⟩,⟨21020429510191200728539661347,21020429510191200900322850028⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨24084490858565869240457874039,24084490858565869420179728961⟩,⟨4233091442510086170962791092,4233091442510086350873897568⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨16474192329648191203607752936,16474192329648191441804990232⟩,⟨(-7187737733111422200570203247),(-7187737733111421962623960809)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨6888574393802861335387873473,6888574393802861915357810409⟩,⟨(-10599594141865344122604682542),(-10599594141865343542793530271)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨201648070264316893060128605,201648070264319142011326592⟩,⟨(-8621525735649328439464813852),(-8621525735649326190504673720)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-2604080448990198931033903223),(-2604080448990193005519336070)⟩,⟨(-5112191601848742765860280474),(-5112191601848736840330633821)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-2859839777054195020540896659),(-2859839777054185386486539466)⟩,⟨(-2343331076164903887039972187),(-2343331076164894252998862156)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-2100930399980878815880442644),(-2100930399980867501383765333)⟩,⟨(-810491966620217063009580995),(-810491966620205748535404895)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-1187158784773659938612253332),(-1187158784773648865911400645)⟩,⟨(-181730468552577715990662283),(-181730468552566643302758316)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-375444547678780606688213946),(-375444547678776004386717885)⟩,⟨(-15887565027914643706605127),(-15887565027910041409018825)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-1936066719201458807918506125),(-1936066719201304701672785340)⟩,⟨21228460898190465149529172394,21228460898190619255329161740⟩⟩
lemma checked : cachedMomentRuleBox density0 hk9_1_5 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 9 5) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk9_1_5 (tableDensity false) (fullFactor true 9 5) density0_contains hk9_1_5_contains
noncomputable def atomAnswer : CBox := ⟨⟨4945362991033159113377415260,4945362991033159142126140952⟩,⟨26920361936861448652084711517,26920361936861448681341731570⟩⟩
lemma atomChecked : tableAtomBox false ha9_1_5 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 9 5) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha9_1_5 9 5 ha9_1_5_contains
 def realAnswer : RBox := ⟨3009296271831700305358909135,3009296271831854440553355612⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 9 5) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm9_0_1_5
namespace hm9_1_1_5
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk9_1_5 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-51),40⟩,⟨(-62),30⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-96),141⟩,⟨(-151),85⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-102),243⟩,⟨(-236),111⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-141),315⟩,⟨(-142),317⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-370),162⟩,⟨(-184),348⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-312),254⟩,⟨(-418),144⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-206),425⟩,⟨(-207),430⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-631),433⟩,⟨(-575),498⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-490),724⟩,⟨(-633),588⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-632),652⟩,⟨(-665),604⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-492),712⟩,⟨(-534),686⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-652),385⟩,⟨(-532),511⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-350),443⟩,⟨(-468),277⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-151),268⟩,⟨(-221),272⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-158),149⟩,⟨(-66),158⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-56),55⟩,⟨(-25),56⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨233284250597,233284250631⟩,⟨193731970708,193731970738⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨446853179531,446853179598⟩,⟨394308145190,394308145258⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨301979616944,301979617049⟩,⟨305926498895,305926499002⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨106665624228,106665624370⟩,⟨139475652808,139475652950⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨19597096390,19597096572⟩,⟨41493491666,41493491852⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨876951083,876951316⟩,⟨8265659713,8265659946⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-431327021),(-431326753)⟩,⟨1036054434,1036054700⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-108160758),(-108160466)⟩,⟨56558682,56558975⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-10718187),(-10717880)⟩,⟨(-4728656),(-4728346)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-79671),(-79286)⟩,⟨(-1099018),(-1098635)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨103065,103496⟩,⟨(-46280),(-45845)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨8807,9242⟩,⟨10414,10850⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-1358),(-923)⟩,⟨1669,2104⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-621),(-285)⟩,⟨(-197),138⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-185),28⟩,⟨(-202),11⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-47),45⟩,⟨(-73),20⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-14886191012882831275),(-14886191012882831148)⟩,⟨(-922906247226049517),(-922906247226049391)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-34262784072431336506),(-34262784072431336226)⟩,⟨1028014386005893497,1028014386005893776⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-32770353349080208454),(-32770353349080208143)⟩,⟨6811173053564595904,6811173053564596214⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-18891922426813573470),(-18891922426813573233)⟩,⟨9104197733529069251,9104197733529069489⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-6771804709823374639),(-6771804709823374474)⟩,⟨6292924771104701775,6292924771104701942⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-1391942040954869204),(-1391942040954869088)⟩,⟨2673552159594853412,2673552159594853532⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-87444740642879351),(-87444740642879244)⟩,⟨759452850425799656,759452850425799766⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨38613577996995550,38613577996995642⟩,⟨154920485144754447,154920485144754540⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨15474203405497936,15474203405498038⟩,⟨24697654900370503,24697654900370604⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨3533987084470660,3533987084470770⟩,⟨3442880028305582,3442880028305694⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨665243682297290,665243682297408⟩,⟨483239638286010,483239638286128⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨120513696225169,120513696225286⟩,⟨78037161682500,78037161682614⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨23320866748129,23320866748238⟩,⟨15506621603757,15506621603865⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨5196994044784,5196994044872⟩,⟨3791815773915,3791815774004⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨1346941379390,1346941379452⟩,⟨1078585576175,1078585576239⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨289265728245,289265728279⟩,⟨244723676970,244723676998⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-556861848923028856545254),(-556861848923026016266656)⟩,⟨190178985596564688142734,190178985596567528399211⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-1340251563828928088980974),(-1340251563828922738246877)⟩,⟨634573970914650499622476,634573970914655850289933⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-1372375856644805073881156),(-1372375856644801334511212)⟩,⟨1079580602538046400907229,1079580602538050140190790⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-792294871508521527830860),(-792294871508519737853187)⟩,⟨1227891300488520753626892,1227891300488522543558275⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-138542599956833559596178),(-138542599956833103308651)⟩,⟨951497467339157715723083,951497467339158172007945⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨185230042720272796169216,185230042720272855242893⟩,⟨489468530568321474234553,489468530568321533324861⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨193346499867465937909128,193346499867465942977409⟩,⟨147683881703610487501523,147683881703610492580071⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨98621548575991660433997,98621548575991661225936⟩,⟨7172264845865768224605,7172264845865769017082⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨31499439514732463741886,31499439514732463976449⟩,⟨(-17507098224438051163929),(-17507098224438050930504)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨5878366504289484381900,5878366504289484476367⟩,⟨(-10669799430063928917530),(-10669799430063928823510)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-66200278404975361728),(-66200278404975323313)⟩,⟨(-3981602186456013079919),(-3981602186456013041527)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-604065658299820739323),(-604065658299820724252)⟩,⟨(-1168906276980201530468),(-1168906276980201515371)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-345574444981520312337),(-345574444981520306362)⟩,⟨(-297738641672982943470),(-297738641672982937482)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-154023759054717041602),(-154023759054717039157)⟩,⟨(-68517696355146919922),(-68517696355146917472)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-61875129742418680232),(-61875129742418679242)⟩,⟨(-13975099517614689316),(-13975099517614688324)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-16468883061629501044),(-16468883061629500764)⟩,⟨(-2050051774375791658),(-2050051774375791379)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-179076108370384329795121970),(-179076108370379279188684055)⟩,⟨98362228845817871307450993,98362228845822921903510465⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-457476522384518181356254576),(-457476522384500073976452831)⟩,⟨325028888815971562099172820,325028888815989669457075722⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-520136227952508518655856292),(-520136227952468648525953841)⟩,⟨581840025371190843623095930,581840025371230713741935736⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-326908156873290960431827309),(-326908156873219338016465117)⟩,⟨758288402701889214879486395,758288402701960837313665814⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨5414509355317928193293039,5414509355414974135981891⟩,⟨724419294178126525087558236,724419294178223571079500311⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨266702766275751565487225529,266702766275882992409564444⟩,⟨480409566333862429051043256,480409566333993856011204940⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨327767241068453961803877823,327767241068610743256990821⟩,⟨177619244054641705735775393,177619244054798487192492058⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨231047922348381107259941717,231047922348486614997331601⟩,⟨(-25525842209538967386985483),(-25525842209433459662553554)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨101704321177275925082710433,101704321177332219595220586⟩,⟨(-89624637804056194516634114),(-89624637803999900012705361)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨19275272688574716560400743,19275272688603152910203589⟩,⟨(-72253885757299085673542185),(-72253885757270649323920089)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-10859538738709987680627672),(-10859538738701655312850641)⟩,⟨(-37889731865612395683809364),(-37889731865604063314171447)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-13764996424415761030337277),(-13764996424413557978311407)⟩,⟨(-14612017575662562349393314),(-14612017575660359296308735)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-9167793545006492976348389),(-9167793545005791228171940)⟩,⟨(-3999925191408403879976803),(-3999925191407702131610111)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-4870560268198744852874776),(-4870560268198549890865002)⟩,⟨(-434657202334080301024826),(-434657202333885339064762)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-2205576077555729023127510),(-2205576077555675384308189)⟩,⟨308173621233374232993052,308173621233427871746477⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-620992143310717666697603),(-620992143310706201156822)⟩,⟨163506171518365765822430,163506171518377231338425⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-219490756064052433951982550),(-219490756064052431536988461)⟩,⟨52406606250227538322393206,52406606250227540252863459⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-521977792342439176253481396),(-521977792342439168832612440)⟩,⟨335263186353732686542640995,335263186353732692758563935⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-197734726782903221100436931),(-197734726782903208799193703)⟩,⟨924828622211329736814126719,924828622211329747919312054⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨1399515256466024917451701483,1399515256466024934690771527⟩,⟨1368272117495374159280904446,1368272117495374176127134444⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨4198273742338087342779430727,4198273742338087369497965992⟩,⟨733497204138718310915837762,733497204138718338413108130⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨6778105554930423646898245353,6778105554930423684989876503⟩,⟨(-1573778635701379736265237789),(-1573778635701379696454252294)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨7264813757098630609522376579,7264813757098630662528585177⟩,⟨(-4876277190371217540189142508),(-4876277190371217485922543287)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨5106493854872109524201950635,5106493854872109599439306307⟩,⟨(-7404187366636303545727937443),(-7404187366636303470407955653)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨1626154092620797304348394816,1626154092620797443895783387⟩,⟨(-7765992132225126076253346727),(-7765992132225125937194818596)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-1265011810981146130391873768),(-1265011810981145696468140331)⟩,⟨(-6099106671673611480465544049),(-6099106671673611046969988506)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-2586572377823018677811326248),(-2586572377823016869851768154)⟩,⟨(-3654626005055519912486077613),(-3654626005055518104589085939)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-2561379708641081550550211386),(-2561379708641076732006754421)⟩,⟨(-1599524210409895154480200317),(-1599524210409890335869524476)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-1907915174275156747107139746),(-1907915174275148890306448203)⟩,⟨(-380176734584654747702768339),(-380176734584646890820199960)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-1183314407616150158067305193),(-1183314407616140918599583853)⟩,⟨122208161877953698291890355,122208161877962937813603701⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-609502370828494207008126536),(-609502370828485157764055913)⟩,⟨198761198353321465281886470,198761198353330514545785584⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-184374236187345669248801208),(-184374236187341906757800184)⟩,⟨83339853728200561439961979,83339853728204323935541294⟩⟩
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
noncomputable def ans : CBox := ⟨⟨2426536891477384113465801355,2426536891477510612688004050⟩,⟨(-4438049833419011607551595851),(-4438049833418885108353087127)⟩⟩
lemma checked : cachedMomentRuleBox density1 hk9_1_5 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 9 5) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk9_1_5 (tableDensity true) (fullFactor true 9 5) density1_contains hk9_1_5_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-6467013142120285032011107399),(-6467013142120284994416619955)⟩,⟨(-35203550225126509814062264361),(-35203550225126509775803084292)⟩⟩
lemma atomChecked : tableAtomBox true ha9_1_5 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 9 5) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha9_1_5 9 5 ha9_1_5_contains
 def realAnswer : RBox := ⟨(-4040476250642900918645306044),(-4040476250642774381628615905)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 9 5) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm9_1_1_5
namespace hm9_0_1_6
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk9_1_6 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-293),310⟩,⟨(-155),441⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-1147),619⟩,⟨(-679),1092⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-2074),656⟩,⟨(-1021),1710⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-2491),1409⟩,⟨(-2849),1055⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-1449),3536⟩,⟨(-3022),1967⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-2955),2993⟩,⟨(-1656),4264⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-4007),2408⟩,⟨(-4485),1988⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-3438),5115⟩,⟨(-3799),4922⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-6349),4116⟩,⟨(-5330),5217⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-5949),5691⟩,⟨(-5384),5868⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-6281),4650⟩,⟨(-6351),4682⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-3556),5786⟩,⟨(-4449),4985⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-4044),3049⟩,⟨(-2631),4136⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-2367),1439⟩,⟨(-2443),1910⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-1236),1387⟩,⟨(-1385),629⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-416),452⟩,⟨(-451),193⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-1241000531082),(-1241000530935)⟩,⟨(-1949081260304),(-1949081260155)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-2335313598865),(-2335313598456)⟩,⟨(-3978750536500),(-3978750536093)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-1483094839256),(-1483094838605)⟩,⟨(-3086868239899),(-3086868239256)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-425923760026),(-425923759072)⟩,⟨(-1385167163260),(-1385167162305)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-21269497607),(-21269496213)⟩,⟨(-390731669869),(-390731668480)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨22504617104,22504619079⟩,⟨(-68836738369),(-68836736394)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨7371454408,7371456955⟩,⟨(-6546583262),(-6546580712)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨1070461186,1070464253⟩,⟨(-15336668),(-15333600)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨64106076,64109504⟩,⟨79179205,79182631⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-3686168),(-3682618)⟩,⟨8677393,8680942⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-944884),(-941729)⟩,⟨(-43283),(-40130)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-30443),(-27842)⟩,⟨(-110359),(-107769)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨12808,15474⟩,⟨(-11334),(-8675)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨2074,4214⟩,⟨419,2560⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-376),1004⟩,⟨190,1561⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-324),218⟩,⟨(-74),462⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨54036851309751993261,54036851309751993552⟩,⟨34955559893839076535,34955559893839076824⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨131892085917794789126,131892085917794789788⟩,⟨67658380515093626236,67658380515093626893⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨140312193302854916594,140312193302854917317⟩,⟨40420229954388180987,40420229954388181702⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨93661739824446863160,93661739824446863764⟩,⟨746031994853551162,746031994853551761⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨40974734534578782436,40974734534578782933⟩,⟨(-13679415037967358912),(-13679415037967358418)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨11649369055369874839,11649369055369875273⟩,⟨(-9497171421855936716),(-9497171421855936285)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨2039083571848333008,2039083571848333508⟩,⟨(-3552427701868313840),(-3552427701868313336)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨161696604801633883,161696604801634451⟩,⟨(-896485120428619869),(-896485120428619305)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-20156021141235697),(-20156021141234972)⟩,⟨(-172694369363077731),(-172694369363077004)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-10187389643356909),(-10187389643356101)⟩,⟨(-28508614084031505),(-28508614084030693)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-2436313870335286),(-2436313870334409)⟩,⟨(-4548785534973822),(-4548785534972946)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-494484495835508),(-494484495834649)⟩,⟨(-785026063658954),(-785026063658093)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-101248418207021),(-101248418206242)⟩,⟨(-159028609400461),(-159028609399689)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-22905639139295),(-22905639138708)⟩,⟨(-39097927085232),(-39097927084643)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-5837716951565),(-5837716951175)⟩,⟨(-11179138204455),(-11179138204064)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-1225122621934),(-1225122621794)⟩,⟨(-2545142057947),(-2545142057807)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨1370705337279746643220669,1370705337279749045382745⟩,⟨398980448937629776630341,398980448937632178567856⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨3612896733416020203054968,3612896733416025493769071⟩,⟨598811908497406061109080,598811908497411351324477⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨4451648669788638698710373,4451648669788643132945397⟩,⟨(-306230317493893558934951),(-306230317493889125105562)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨3592501239310261607799481,3592501239310263548141261⟩,⟨(-1544280104339342351917641),(-1544280104339340411653515)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨1814394990873261819908829,1814394990873262260774389⟩,⟨(-2002890759151922440173906),(-2002890759151921999121170)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨352516126754596587367379,352516126754596640777466⟩,⟨(-1494522500795990571077664),(-1494522500795990517463384)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-238604061365893613365782),(-238604061365893605774526)⟩,⟨(-699601852492859922043906),(-699601852492859914414824)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-246859180592808369490613),(-246859180592808367904713)⟩,⟨(-187707986324101610404352),(-187707986324101608837627)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-116645424196082483173412),(-116645424196082482579608)⟩,⟨(-6199460813397090125008),(-6199460813397089544971)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-35372935470166108851685),(-35372935470166108605624)⟩,⟨20382545586992496389332,20382545586992496634224⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-6789932705725427628977),(-6789932705725427533107)⟩,⟨11945454052805134310919,11945454052805134407650⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-230394851969830819010),(-230394851969830782830)⟩,⟨4627801703967430371467,4627801703967430408173⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨539091848814387902601,539091848814387916541⟩,⟨1531482455785485328183,1531482455785485342238⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨358217644514965153712,358217644514965159177⟩,⟨484070530108980845017,484070530108980850494⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨168634210906602219791,168634210906602221917⟩,⟨151395197333217954352,151395197333217956476⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨47885943514579706081,47885943514579706654⟩,⟨34894477219734386405,34894477219734386976⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨250657318022443360968622374,250657318022447846315241949⟩,⟨349331580552513831586748593,349331580552518316912462043⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨790062291573821915696166277,790062291573837740110119000⟩,⟨849957623107963350069313021,849957623107979174453948054⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨1320263225320252950255794859,1320263225320286727169416020⟩,⟨849464181025518270727330895,849464181025552047674237851⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨1587382292828602585535714863,1587382292828660310023947733⟩,⟨330895265659820967492725377,330895265659878692121860746⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨1361613021234235564084531432,1361613021234314300344602160⟩,⟨(-365206075779744957128237216),(-365206075779666220664797384)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨740763793423634175217407565,740763793423760881569001270⟩,⟨(-778859253654998706552394684),(-778859253654872000117608000)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨111882753195824417071479639,111882753195961661170710582⟩,⟨(-726086818456512277491365371),(-726086818456375033417457583)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-216330842275355349193395900),(-216330842275268661995006575)⟩,⟨(-403435390425850603268069852),(-403435390425763916128223190)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-241913753919799154661808686),(-241913753919741397131253537)⟩,⟨(-107484297759529013966370525),(-107484297759471256452367548)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-140972718130962302731272743),(-140972718130936619186088429)⟩,⟨33598815656472288070037205,33598815656497971622785742⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-50510808726122631949077499),(-50510808726115523899992827)⟩,⟨57784143271473147927256938,57784143271480255985902536⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-6384239815964491267467524),(-6384239815962052999814782)⟩,⟨39600415872747451616696937,39600415872749889886695735⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨6444959828700820877431009,6444959828701512070711814⟩,⟨19897915677793443125108246,19897915677794134317975795⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨6781416665923982973036851,6781416665924157792732045⟩,⟨8365946284998838824899059,8365946284999013643770283⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨4107170639285330207596339,4107170639285374537517144⟩,⟨3051099182535020847602355,3051099182535065176963970⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨1315824600770528867564601,1315824600770538090688791⟩,⟨739550784080250055594115,739550784080259278536841⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨1085545366935967761594717238,1085545366935967770643023195⟩,⟨4446290366739793808520603300,4446290366739793818020454767⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨4732459395524059408704501045,4732459395524059436737981301⟩,⟨11967177169648785578800146469,11967177169648785607963783490⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨11420774975256108420740868182,11420774975256108469748186439⟩,⟨15244696890827319723855571719,15244696890827319773990251195⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨19359799247507811073562773830,19359799247507811144519112736⟩,⟨11997272104015719309338307648,11997272104015719380714543902⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨23915204760468675388865920107,23915204760468675480446548124⟩,⟨2610264182724564141609616460,2610264182724564232594475279⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨21182953566852899223465530370,21182953566852899328128586631⟩,⟨(-8625235289683864296273661342),(-8625235289683864192851608927)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨11860830038084751085070354652,11860830038084751196735739831⟩,⟨(-15731330323721839464921484637),(-15731330323721839353967110729)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨1104810774590298873541634395,1104810774590298990763526615⟩,⟨(-15580637113663115708136075040),(-15580637113663115590940834427)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-5842839671410445862579524225),(-5842839671410445711561140508)⟩,⟨(-10060751787311027835953499687),(-10060751787311027684727192573)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-7466520396369857945460530020),(-7466520396369857542576078877)⟩,⟨(-3607140870161875447903519243),(-3607140870161875044925266801)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-5692615499155992143182819423),(-5692615499155990622514071510)⟩,⟨651082450094106006477845049,651082450094107527139092690⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-3142461325148563517067856170),(-3142461325148559701678690385)⟩,⟨2236034020905515324470782776,2236034020905519139857732806⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-1270339095970354683499274214),(-1270339095970348712983530479)⟩,⟨2165706760830279124959699221,2165706760830285095492084829⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-314320660750473394935527497),(-314320660750464784823309495)⟩,⟨1509209081101604206545267133,1509209081101612816672259744⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨13014101476100124610667087,13014101476108402658360371⟩,⟨826712027996303872892250828,826712027996312150947071517⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨33069388404344823774356321,33069388404348209178231717⟩,⟨257334534207730056667692444,257334534207733442073487981⟩⟩
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
noncomputable def ans : CBox := ⟨⟨12753179736742141864870508198,12753179736742253168673662279⟩,⟨77182423086208501323483210,77182423086319805328935451⟩⟩
lemma checked : cachedMomentRuleBox density0 hk9_1_6 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 9 6) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk9_1_6 (tableDensity false) (fullFactor true 9 6) density0_contains hk9_1_6_contains
noncomputable def atomAnswer : CBox := ⟨⟨16026114467064975630828034119,16026114467064975649983063678⟩,⟨(-3954047714761567412614011353),(-3954047714761567393788605680)⟩⟩
lemma atomChecked : tableAtomBox false ha9_1_6 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 9 6) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha9_1_6 9 6 ha9_1_6_contains
 def realAnswer : RBox := ⟨28779294203807117495598542317,28779294203807228818756725957⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 9 6) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm9_0_1_6
namespace hm9_1_1_6
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk9_1_6 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-61),56⟩,⟨(-34),83⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-210),111⟩,⟨(-132),190⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-376),117⟩,⟨(-207),285⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-410),281⟩,⟨(-512),181⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-245),615⟩,⟨(-487),376⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-520),467⟩,⟨(-286),700⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-626),410⟩,⟨(-725),315⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-548),809⟩,⟨(-597),785⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-1022),652⟩,⟨(-851),840⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-980),941⟩,⟨(-879),969⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-1079),774⟩,⟨(-1076),800⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-604),1011⟩,⟨(-783),852⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-697),540⟩,⟨(-445),728⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-414),236⟩,⟨(-421),340⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-224),240⟩,⟨(-239),100⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-79),80⟩,⟨(-80),35⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-25664709811),(-25664709781)⟩,⟨(-359511992284),(-359511992252)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-33148202232),(-33148202165)⟩,⟨(-710081278664),(-710081278598)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨5983055397,5983055492⟩,⟨(-516300971567),(-516300971472)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨25896087020,25896087152⟩,⟨(-211491329856),(-211491329721)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨17363310945,17363311141⟩,⟨(-53678883431),(-53678883244)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨6057972466,6057972743⟩,⟨(-8426869639),(-8426869362)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨1266896739,1266897102⟩,⟨(-653573865),(-653573500)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨155156228,155156683⟩,⟨29219097,29219551⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨7689400,7689923⟩,⟨13380891,13381420⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-742357),(-741789)⟩,⟨1276950,1277521⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-152749),(-152217)⟩,⟨(-22421),(-21889)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-3541),(-3079)⟩,⟨(-19210),(-18748)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨2422,2912⟩,⟨(-1791),(-1301)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨340,750⟩,⟨126,536⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-93),176⟩,⟨33,305⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-72),44⟩,⟨(-22),94⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨6254694688459866742,6254694688459866844⟩,⟨13114489364050597540,13114489364050597643⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨17256478037081847051,17256478037081847273⟩,⟨28724226308661502881,28724226308661503103⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨21819829170276215338,21819829170276215572⟩,⟨24682846099148634747,24682846099148634982⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨17313279739523510543,17313279739523510732⟩,⟨11616947915177088537,11616947915177088724⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨8957640836349982396,8957640836349982539⟩,⟨2537404305678314332,2537404305678314474⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨3071742293058680386,3071742293058680503⟩,⟨(-259889192698674357),(-259889192698674241)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨708979559291470380,708979559291470501⟩,⟨(-360956672748716976),(-360956672748716855)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨111353924169972768,111353924169972889⟩,⟨(-127545788419490881),(-127545788419490761)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨11622034626126922,11622034626127059⟩,⟨(-29296567847466215),(-29296567847466079)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨617658824235009,617658824235152⟩,⟨(-5405251992010405),(-5405251992010264)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-50781611123465),(-50781611123321)⟩,⟨(-922262806424782),(-922262806424639)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-21545688710980),(-21545688710846)⟩,⟨(-162604476226144),(-162604476226010)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-4531317069699),(-4531317069585)⟩,⟨(-32142059932477),(-32142059932363)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-851751228478),(-851751228390)⟩,⟨(-7493534617344),(-7493534617254)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-163115298276),(-163115298214)⟩,⟨(-2032354683140),(-2032354683075)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-26608769415),(-26608769383)⟩,⟨(-448711037538),(-448711037506)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨287608684488314200867984,287608684488316218000128⟩,⟨380831493557900554187016,380831493557902571342441⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨833780422905393282890177,833780422905397722246722⟩,⟨871904558639862969288109,871904558639867408696485⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨1197737536520436419860125,1197737536520440134549551⟩,⟨780000065325728367715570,780000065325732082447150⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨1173316703612984889596621,1173316703612986510403995⟩,⟨283360296548433471298747,283360296548435092114200⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨787000807112553463237279,787000807112553829216452⟩,⟨(-162137025983541964062758),(-162137025983541598102674)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨332367965651503076952384,332367965651503119855022⟩,⟨(-293612755133602041330093),(-293612755133601998447946)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨56789369070224637551703,56789369070224642780661⟩,⟨(-201603436654366287371780),(-201603436654366282146487)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-27442059319157614706631),(-27442059319157613992389)⟩,⟨(-82129836682187751030461),(-82129836682187750314273)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-25569968450317412282470),(-25569968450317412070771)⟩,⟨(-19448622016662028754953),(-19448622016662028541914)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-11026642539804409030927),(-11026642539804408944367)⟩,⟨(-794007318264261962532),(-794007318264261875868)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-3284113773731101365003),(-3284113773731101331170)⟩,⟨1652562290244630622921,1652562290244630656675⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-724687463098907202155),(-724687463098907189289)⟩,⟨998900470097493703943,998900470097493716757⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-99071898448452199975),(-99071898448452194964)⟩,⟨422254062428671509383,422254062428671514383⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨11955786220160572578,11955786220160574570⟩,⟨161604029590712802079,161604029590712804070⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨16890132538751053581,16890132538751054370⟩,⟨59073951242472036153,59073951242472036938⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨6000808906381365307,6000808906381365529⟩,⟨14980235094005804232,14980235094005804455⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨88124836311902028755067473,88124836311905714284553796⟩,⟨110405203312665779414048915,110405203312669464947774132⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨276813874849279691290461135,276813874849292695408346821⟩,⟨273404124460423263853887691,273404124460436267978290563⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨463592123523033232314340635,463592123523060994425669978⟩,⟨284637885385028590643102776,284637885385056352749007483⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨566040772036183162065487743,566040772036230616463096520⟩,⟨127151393252192554813760226,127151393252240009183559568⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨503613021156057019918717967,503613021156121757165135011⟩,⟨(-103597400384105954547341061),(-103597400384041217343588154)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨298491277276873288596551804,298491277276977469487220857⟩,⟨(-258300996215069516451160303),(-258300996214965335579399196)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨74372627983365687568969490,74372627983478511177205315⟩,⟨(-261131632264471315030442110),(-261131632264358491417307492)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-57759079025602616718589377),(-57759079025531387644076266)⟩,⟨(-161840368241829610995171607),(-161840368241758381907656458)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-83912073447882506287770500),(-83912073447835085963313338)⟩,⟨(-57595439354246196140383918),(-57595439354198775811878237)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-57023626005492751998245166),(-57023626005471686856703936)⟩,⟨22781508063746041928141,22781508084811182088297⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-25946988466163808206400832),(-25946988466157985837455490)⟩,⟨16046752072380735994721007,16046752072386558361830156⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-7935344421713275289659568),(-7935344421711280794091010)⟩,⟨13607634024349195104031840,13607634024351189599124205⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-897182174961014617618786),(-897182174960449957907483)⟩,⟨7891646955377618562505487,7891646955378183222274337⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨847478704149386367896922,847478704149529020973552⟩,⟨3827121611928125881602760,3827121611928268534820790⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨784639731240579991388650,784639731240616132656200⟩,⟨1616690833391821831757499,1616690833391857973121170⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨282154468287484028353461,282154468287491544008957⟩,⟨436723545752344364814628,436723545752351880500866⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨38501689940252098127987589,38501689940252099348290163⟩,⟨130514022716683281548157832,130514022716683283038607383⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨219560236262438076111947549,219560236262438080028201645⟩,⟨303923531736283732945816352,303923531736283737521422441⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨567596801812189257015722847,567596801812189263977120110⟩,⟨86626349541810225312341300,86626349541810232884385255⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨778976952079081047025485431,778976952079081057533982471⟩,⟨(-908813436712003261746860258),(-908813436712003251148551082)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨262538570885782643346677715,262538570885782660514805053⟩,⟨(-2616884591742516769580313708),(-2616884591742516753047997116)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-1324129699038967126773914612),(-1324129699038967101658582513)⟩,⟨(-4132309952117776162516217235),(-4132309952117776138569268839)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-3485544185727135343813517203),(-3485544185727135308466336369)⟩,⟨(-4281307847163466675897259494),(-4281307847163466641219299888)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-5042447903655188552349000011),(-5042447903655188503534614460)⟩,⟨(-2758394111855531828442730355),(-2758394111855531779569449893)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-5116004402341134747404482988),(-5116004402341134660644281280)⟩,⟨(-470599591654449901712966107),(-470599591654449814566753814)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-3865469451454932850143600237),(-3865469451454932547689174588)⟩,⟨1326912529402130787829356697,1326912529402131090531740634⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-2170646501645421764723674731),(-2170646501645420542040918996)⟩,⟨2034687160728960218225414598,2034687160728961440917338437⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-811054127239718293990090019),(-811054127239715191904584219)⟩,⟨1861106851510159308938723502,1861106851510162410962605638⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-53810173017141846372510992),(-53810173017136977948048088)⟩,⟨1320049838375444070073002046,1320049838375448938435555410⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨213899829772203175244076839,213899829772210207101166015⟩,⟨785810633431578203356086715,785810633431585235184266522⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨204934947674176062674522416,204934947674182828309497527⟩,⟨390895353427779479734260961,390895353427786245360272639⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨78259008447866045673466748,78259008447868813409804809⟩,⟨115720221137723651116870163,115720221137726418851427970⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-2910124888241381995953122136),(-2910124888241290622757991236)⟩,⟨(-1135653526456391130582402515),(-1135653526456299757448937511)⟩⟩
lemma checked : cachedMomentRuleBox density1 hk9_1_6 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 9 6) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk9_1_6 (tableDensity true) (fullFactor true 9 6) density1_contains hk9_1_6_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-20957226610777275849977852502),(-20957226610777275824928967694)⟩,⟨5170677780842049668800484350,5170677780842049693418322539⟩⟩
lemma atomChecked : tableAtomBox true ha9_1_6 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 9 6) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha9_1_6 9 6 ha9_1_6_contains
 def realAnswer : RBox := ⟨(-23867351499018657846030974638),(-23867351499018566447586958930)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 9 6) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm9_1_1_6
namespace hm9_0_1_7
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk9_1_7 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-215),349⟩,⟨(-434),111⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-435),1237⟩,⟨(-930),746⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-419),2355⟩,⟨(-1412),1357⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-1979),2335⟩,⟨(-873),3439⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-4478),1563⟩,⟨(-2890),3157⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-3418),4474⟩,⟨(-5512),2375⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-4148),5164⟩,⟨(-2842),6511⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-7000),5265⟩,⟨(-7195),5229⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-4506),7334⟩,⟨(-5633),6394⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-7073),7479⟩,⟨(-7153),6565⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-6195),8055⟩,⟨(-5954),8406⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-7674),4798⟩,⟨(-6797),5834⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-4050),5475⟩,⟨(-5524),3614⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-1963),3163⟩,⟨(-2536),3275⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-1845),1632⟩,⟨(-843),1833⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-592),545⟩,⟨(-252),591⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-558456285764),(-558456285584)⟩,⟨2286855643130,2286855643312⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-1259779463400),(-1259779462866)⟩,⟨4545598534179,4545598534711⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-1184478564447),(-1184478563533)⟩,⟨3321194112848,3321194113764⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-691258401390),(-691258400095)⟩,⟨1339595039682,1339595040979⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-265581742490),(-265581740796)⟩,⟨315505815859,315505817551⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-67043240430),(-67043238328)⟩,⟨38905690942,38905693037⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-10731005961),(-10731003671)⟩,⟨280605354,280607643⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-942326140),(-942323513)⟩,⟨(-721814821),(-721812197)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-5387547),(-5384015)⟩,⟨(-114918259),(-114914725)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨9115935,9120229⟩,⟨(-5856423),(-5852129)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨902834,907255⟩,⟨627677,632100⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-37664),(-33649)⟩,⟨126818,130833⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-22388),(-18821)⟩,⟨572,4130⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-3759),(-1322)⟩,⟨(-4563),(-2126)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-565),832⟩,⟨(-1814),(-427)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-96),422⟩,⟨(-437),71⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨3610718753133620912,3610718753133621192⟩,⟨(-53617632394370808652),(-53617632394370808367)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-4596429083311439219),(-4596429083311438555)⟩,⟨(-124121238742148817735),(-124121238742148817062)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-29107009861901762612),(-29107009861901761828)⟩,⟨(-119701961700347974752),(-119701961700347973958)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-39856970260726413773),(-39856970260726413094)⟩,⟨(-69154471433328637169),(-69154471433328636487)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-28462408155689277127),(-28462408155689276591)⟩,⟨(-24093818505398004535),(-24093818505398004001)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-12498434893024289757),(-12498434893024289315)⟩,⟨(-4173365995082225078),(-4173365995082224634)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-3646537352279669211),(-3646537352279668731)⟩,⟨235840050025648919,235840050025649399⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-752590329059642259),(-752590329059641759)⟩,⟨345539485764884781,345539485764885277⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-117966792641124527),(-117966792641123940)⟩,⟨109821646147365065,109821646147365658⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-15417147351624085),(-15417147351623493)⟩,⟨24106370228404296,24106370228404881⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-1915541650033046),(-1915541650032378)⟩,⟨4584507369729550,4584507369730217⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-270422765136421),(-270422765135654)⟩,⟨867355487578130,867355487578898⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-51207463978672),(-51207463977889)⟩,⟨180161680431757,180161680432551⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-13338483810239),(-13338483809577)⟩,⟨43536867736117,43536867736777⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-4190146407933),(-4190146407462)⟩,⟨12066104264485,12066104264952⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-1013880123767),(-1013880123599)⟩,⟨2687374794479,2687374794650⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-34211458631872423994508),(-34211458631870382438304)⟩,⟨(-991806135016511632589298),(-991806135016509590940103)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-398318316240459446348560),(-398318316240455130993256)⟩,⟨(-2522509120123014243224267),(-2522509120123009927695391)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-1206888640769936670292059),(-1206888640769933299989031)⟩,⟨(-2888930428237897654075842),(-2888930428237894283722398)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-1871134199095135596748168),(-1871134199095134255122113)⟩,⟨(-2040652038923856576507058),(-2040652038923855235042342)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-1791822938641534467098748),(-1791822938641534196707053)⟩,⟨(-732861111569341170290622),(-732861111569340900157838)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-1105936802507950648142825),(-1105936802507950604367402)⟩,⟨144814908907308632169716,144814908907308675849427⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-414901835017663848824257),(-414901835017663843072618)⟩,⟨354076794579977857123779,354076794579977862890868⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-58714091569682881579905),(-58714091569682880519261)⟩,⟨225259349985579763376515,225259349985579764465654⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨31463112176049778124392,31463112176049778527660⟩,⟨83527178064028789828056,83527178064028790236477⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨25914388116867064292316,25914388116867064451524⟩,⟨18356257427630571868319,18356257427630572025903⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨10848959196990611161972,10848959196990611222312⟩,⟨730631748795180218102,730631748795180277195⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨3406680198391773751521,3406680198391773777639⟩,⟨(-1506934699033763548390),(-1506934699033763522482)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨903518555641832107376,903518555641832118648⟩,⟨(-966745535666549392883),(-966745535666549381605)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨211923611349042468115,211923611349042472946⟩,⟨(-448637147300176396241),(-448637147300176391382)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨43069547457949323175,43069547457949325177⟩,⟨(-183149994308158649694),(-183149994308158647675)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨6150870807558041176,6150870807558041734⟩,⟨(-48998829896684354224),(-48998829896684353663)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨178664872376480913166463202,178664872376483632995248811⟩,⟨(-181673926876187394659219300),(-181673926876184674828162338)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨416252796064958886222175490,416252796064968331688006714⟩,⟨(-549792372368051178983514484),(-549792372368041733527863653)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨359107929992599678841379614,359107929992619192669751410⟩,⟨(-866485256136937657504432886),(-866485256136918143733157639)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨18951866184982657131169004,18951866185014112362928856⟩,⟨(-976235230403305153317337390),(-976235230403273698205690554)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-378793739057318644128471653),(-378793739057267684670326820)⟩,⟨(-769370369008239602249073384),(-769370369008188642900702389)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-562940757826171718376644016),(-562940757826089707549631276)⟩,⟨(-348037376801346817549175703),(-348037376801264806741814290)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-457599003291090375984077194),(-457599003291009845379450922)⟩,⟨30386906763327039497936934,30386906763407570140016367⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-217095175147243881609453984),(-217095175147188233119682561)⟩,⟨192342402325546404576535217,192342402325602053102042360⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-29007732189908626344829343),(-29007732189869662638354103)⟩,⟨167852340124279341586748322,167852340124318305295091449⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨45004766903507541605612083,45004766903522723389599877⟩,⟨83337608736894110989584561,83337608736909292763931498⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨45989173094986832731080166,45989173094991947396830748⟩,⟨21846694142914045697815788,21846694142919160358561039⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨26758652431765202423821872,26758652431766926875075238⟩,⟨(-3432322147892182879498683),(-3432322147890458428336787)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨11655648926060841516403213,11655648926061276779098003⟩,⟨(-8172962311588297002743650),(-8172962311587861738998453)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨4071527311007385611136624,4071527311007486613505691⟩,⟨(-6178750076158844981111551),(-6178750076158743977880921)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨1132944339521175444096312,1132944339521208199501582⟩,⟨(-3352595558911620893764349),(-3352595558911588138020114)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨203892100757452924218825,203892100757460911177705⟩,⟨(-1027516111017942522029903),(-1027516111017934534990068)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨2265544047103104809246539914,2265544047103104814281976377⟩,⟨(-680856198651646875504029319),(-680856198651646870686824473)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨6056947666444184803011265882,6056947666444184818494663063⟩,⟨(-2786391803266105313371980995),(-2786391803266105298426278657)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨7572014775701654888688248917,7572014775701654915397912091⟩,⟨(-6399874777952353113906744798),(-6399874777952353087701436342)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨5617007373119164894946841029,5617007373119164933164592228⟩,⟨(-10531100773972031001304001238),(-10531100773972030963198004247)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨460035380466386370577883480,460035380466386419599462966⟩,⟨(-12709807806689839618735937080),(-12709807806689839569295791949)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-5516167571355359692492936406),(-5516167571355359636132226337)⟩,⟨(-10902420412211652350654482718),(-10902420412211652293598252725)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-9057153698102809778632272288),(-9057153698102809717281797164)⟩,⟨(-5602527391867711125350846921),(-5602527391867711063683063236)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-8547338431973270595104825800),(-8547338431973270530294389574)⟩,⟨277262489136008584467600564,277262489136008649240523833⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-5173950120598831436056091423),(-5173950120598831353769753219)⟩,⟨3859631880414026188201723867,3859631880414026270351357840⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-1483246197377971261317322211),(-1483246197377971022585879997)⟩,⟨4420059312655222531380460598,4420059312655222770069768321⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨810960891067675324589551668,810960891067676189101751283⟩,⟨3160637109260189037400990674,3160637109260189901917771138⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨1540268086167790204846743568,1540268086167792257995447623⟩,⟨1601962145102638473106210643,1601962145102640526251200276⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨1360176228745890943922793619,1360176228745894483098705005⟩,⟨534625758223293801678533659,534625758223297340841868823⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨903780105184869935193763551,903780105184875444932871904⟩,⟨38410096472110054393870723,38410096472115564125132271⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨479718937917302908495333997,479718937917308042872197789⟩,⟨(-88972858946158973184041875),(-88972858946153838810168096)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨146779428733040913346671136,146779428733042981986883458⟩,⟨(-45067580017151886502105816),(-45067580017149817862515675)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-518179113744631166907520192),(-518179113744562222850840640)⟩,⟨(-6513462846723113316737431820),(-6513462846723044372752787002)⟩⟩
lemma checked : cachedMomentRuleBox density0 hk9_1_7 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 9 7) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk9_1_7 (tableDensity false) (fullFactor true 9 7) density0_contains hk9_1_7_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-2546442028712917303337441314),(-2546442028712917292696232524)⟩,⟨(-8135409803195629982388193061),(-8135409803195629971567211782)⟩⟩
lemma atomChecked : tableAtomBox false ha9_1_7 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 9 7) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha9_1_7 9 7 ha9_1_7_contains
 def realAnswer : RBox := ⟨(-3064621142457548470344961506),(-3064621142457479515447073164)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 9 7) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm9_0_1_7
namespace hm9_1_1_7
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk9_1_7 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-40),70⟩,⟨(-80),29⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-83),221⟩,⟨(-159),146⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-85),414⟩,⟨(-227),271⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-388),376⟩,⟨(-162),603⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-763),279⟩,⟨(-540),500⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-533),773⟩,⟨(-889),417⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-694),802⟩,⟨(-457),1044⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-1104),839⟩,⟨(-1144),822⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-714),1180⟩,⟨(-907),1021⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-1170),1232⟩,⟨(-1180),1068⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-1027),1386⟩,⟨(-1013),1422⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-1342),812⟩,⟨(-1162),1025⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-712),947⟩,⟨(-972),606⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-321),549⟩,⟨(-447),563⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-317),292⟩,⟨(-133),314⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-105),102⟩,⟨(-43),105⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-246301090143),(-246301090104)⟩,⟨272345053580,272345053618⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-497778879015),(-497778878940)⟩,⟨529552625295,529552625374⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-382106941958),(-382106941830)⟩,⟨369580767997,369580768127⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-173117341583),(-173117341406)⟩,⟨138361227823,138361228003⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-52061331353),(-52061331123)⟩,⟨28707023960,28707024192⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-10842595616),(-10842595325)⟩,⟨2408498913,2408499205⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-1513401912),(-1513401582)⟩,⟨(-344266948),(-344266616)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-114999971),(-114999581)⟩,⟨(-131970445),(-131970054)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨1948351,1948894⟩,⟨(-17317825),(-17317283)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨1531157,1531845⟩,⟨(-732634),(-731947)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨136326,137067⟩,⟨116653,117392⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-8355),(-7650)⟩,⟨21011,21718⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-4015),(-3361)⟩,⟨(-243),413⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-634),(-170)⟩,⟨(-890),(-426)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-90),187⟩,⟨(-345),(-69)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-24),91⟩,⟨(-86),26⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨7037840854919197941,7037840854919198040⟩,⟨(-9882532196650799666),(-9882532196650799568)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨13922629149936837984,13922629149936838207⟩,⟨(-24382860551183889810),(-24382860551183889586)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨8951087928916869471,8951087928916869726⟩,⟨(-26313556840678698393),(-26313556840678698139)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨1069290183513700693,1069290183513700900⟩,⟨(-17735065637850832290),(-17735065637850832079)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-2143694414495854748),(-2143694414495854591)⟩,⟨(-7745572807280024716),(-7745572807280024561)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-1633026032188570808),(-1633026032188570689)⟩,⟨(-2153134185217290317),(-2153134185217290200)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-617868344964709847),(-617868344964709731)⟩,⟨(-349074588591822720),(-349074588591822603)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-152989483520963468),(-152989483520963361)⟩,⟨(-16719796318846164),(-16719796318846054)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-28262963030183337),(-28262963030183221)⟩,⟨7392654097969155,7392654097969268⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-4397403475591145),(-4397403475591035)⟩,⟨2665037350382756,2665037350382862⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-657772915209794),(-657772915209682)⟩,⟨598563622767508,598563622767618⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-107426313004121),(-107426313004004)⟩,⟨119406262824035,119406262824157⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-20869359454694),(-20869359454576)⟩,⟨24583925716329,24583925716444⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-4963217485302),(-4963217485202)⟩,⟨5726793684451,5726793684549⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-1385339122964),(-1385339122891)⟩,⟨1531270961946,1531270962022⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-311612487779),(-311612487742)⟩,⟨334388286908,334388286942⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨189024559121456523714354,189024559121458238263385⟩,⟨(-272631362240750032787535),(-272631362240748318248181)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨393610147808219676171699,393610147808223297546915⟩,⟨(-743496116756703513322951),(-743496116756699891965859)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨248324905234856169833425,248324905234858993428047⟩,⟨(-971638156514828865815167),(-971638156514826042225940)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-84563154366644221716834),(-84563154366643101240051)⟩,⟨(-850396081031646887246447),(-850396081031645766753219)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-301315081860866398203138),(-301315081860866174173044)⟩,⟨(-490389603088093996915521),(-490389603088093772859277)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-284911537752933748856103),(-284911537752933713698176)⟩,⟨(-150289657391122953034622),(-150289657391122917867170)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-153729262677839128868743),(-153729262677839124873676)⟩,⟨15920262130077546698930,15920262130077550692418⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-48969445628791822704148),(-48969445628791822222632)⟩,⟨42740651545952492425208,42740651545952492903946⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-5761863881449007147555),(-5761863881449006997787)⟩,⟨23861540714545925770996,23861540714545925920309⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨3028080991395035995913,3028080991395036051982⟩,⟨8048600593930297120093,8048600593930297176326⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨2307292392626266709536,2307292392626266730462⟩,⟨1772175109087610743116,1772175109087610764158⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨979228792378654043080,979228792378654052274⟩,⟨159434481594879865279,159434481594879874488⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨342468389943248026327,342468389943248030364⟩,⟨(-87550825374438659041),(-87550825374438655006)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨112674289931548422392,112674289931548424156⟩,⟨(-71629687040531107773),(-71629687040531106012)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨36295277167095698956,36295277167095699708⟩,⟨(-35841570076441405190),(-35841570076441404446)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨8508742298506622812,8508742298506623031⟩,⟨(-10416410444655325309),(-10416410444655325092)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨55566642233985272222583384,55566642233987507098530955⟩,⟨(-62617977615564696505645400),(-62617977615562461630385199)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨131565262678013935269986310,131565262678021697401371424⟩,⟨(-190126021609450326101666671),(-190126021609442563968851264)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨118080716464044893868900355,118080716464060932794360628⟩,⟨(-302815617575955708318490946),(-302815617575939669381973614)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨12183306243461388152689367,12183306243487246844292147⟩,⟨(-349151270190959149599800836),(-349151270190933290883155480)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-121314696546266478835122852),(-121314696546224579511958577)⟩,⟨(-288299942194122185004549287),(-288299942194080285656628566)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-193368828162181891875104306),(-193368828162114460414316779)⟩,⟨(-147268852786590542697016047),(-147268852786523111230167799)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-169212075868428575057732736),(-169212075868362373303691164)⟩,⟨(-9873585924837486088091378),(-9873585924771284341680509)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-91337664227073780272130768),(-91337664227028056036501006)⟩,⟨59269048187131918968813057,59269048187177643196237110⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-22739223293886274279092307),(-22739223293854283808866828)⟩,⟨61422795910108005129318600,61422795910139995598742720⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨9636992023575917982959926,9636992023588369904128762⟩,⟨36003803145032454876093199,36003803145044906799123141⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨14917554394097442135497858,14917554394101631530971168⟩,⟨13679990674756810423335085,13679990674760999819785750⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨10289762831843862985700873,10289762831845273592445207⟩,⟨2524818259362819499218056,2524818259364230106005075⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨5313565218444538226655964,5313565218444893806105282⟩,⟨(-994481323931365365687963),(-994481323931009786420211)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨2330772821014267137671581,2330772821014349551925609⟩,⟨(-1349603794557871074237651),(-1349603794557788660133943)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨896737681373700516944590,896737681373727221488485⟩,⟨(-860664634838847113824049),(-860664634838820409338811)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨227186602826182717269039,227186602826189225989166⟩,⟨(-280348021163497728206422),(-280348021163491219500116)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨66320835920195571200667060,66320835920195571986588152⟩,⟨(-23411722803601718033713990),(-23411722803601717375639078)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨150990945861406731027504111,150990945861406733437777984⟩,⟨(-122173519641128180565888364),(-122173519641128178460441040)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨27527516923437760676200227,27527516923437764657187092⟩,⟨(-297519039183699234580140396),(-297519039183699230855709685)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-502100394012861619188110444),(-502100394012861613626298536)⟩,⟨(-376280566363625789782064959),(-376280566363625784188401581)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-1390639217197034683595780570),(-1390639217197034674872484131)⟩,⟨(-37554693985879601215627282),(-37554693985879592075774035)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-2143421579850974218372151701),(-2143421579850974205426315062)⟩,⟨886247711159746150356025069,886247711159746163950893840⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-2132136851826525843750186632),(-2132136851826525824484213190)⟩,⟨2090220898492746903410924826,2090220898492746922968233956⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-1218237669567807140996137988),(-1218237669567807114073493535)⟩,⟨2902919360746285816829988816,2902919360746285843660371102⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨65527815449157371568634381,65527815449157418434435477⟩,⟨2850663501260317694305993967,2850663501260317740926917990⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨1013886462962712114867179307,1013886462962712295039512505⟩,⟨2062683954403689910491680885,2062683954403690090554146124⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨1317086109333611410868410679,1317086109333612106093571290⟩,⟨1066223850888318498398190672,1066223850888319193635937231⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨1129421105284512962949782643,1129421105284514631856912197⟩,⟨304941260591797760152403427,304941260591799429103260326⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨763927753639100861433761705,763927753639103747589954033⟩,⟨(-88408453442694218882291021),(-88408453442691332692470796)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨434659438889139696863097919,434659438889144197069678807⟩,⟨(-198619985487049296211983417),(-198619985487044795994229572)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨207253785521051721570246352,207253785521055918055301115⟩,⟨(-157726179068196521268113566),(-157726179068192324780644405)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨59654753492058356266010004,59654753492060047527185931⟩,⟨(-57237997789874186207308154),(-57237997789872494945908088)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-397880771311547902382412477),(-397880771311491298979295498)⟩,⟨1603473972993821000222677871,1603473972993877603694095789⟩⟩
lemma checked : cachedMomentRuleBox density1 hk9_1_7 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 9 7) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk9_1_7 (tableDensity true) (fullFactor true 9 7) density1_contains hk9_1_7_contains
noncomputable def atomAnswer : CBox := ⟨⟨3329962652932276459679688685,3329962652932276473595115564⟩,⟨10638612819563516116664815408,10638612819563516130815329387⟩⟩
lemma atomChecked : tableAtomBox true ha9_1_7 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 9 7) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha9_1_7 9 7 ha9_1_7_contains
 def realAnswer : RBox := ⟨2932081881620728557197276208,2932081881620785174715820066⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 9 7) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm9_1_1_7
end SharpPlanar.CachedData

end OAI
