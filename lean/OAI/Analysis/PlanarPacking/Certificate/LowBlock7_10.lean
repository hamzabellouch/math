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
namespace hm7_0_1_2
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk7_1_2 j i k))
noncomputable def s0_0 : CBox := ⟨⟨25139293,25139351⟩,⟨51498119,51498177⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨18375299,18375440⟩,⟨119514771,119514911⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-45043832),(-45043614)⟩,⟨91076068,91076288⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-52677932),(-52677640)⟩,⟨9282647,9282944⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-9210862),(-9210488)⟩,⟨(-18257224),(-18256851)⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨5809405,5809810⟩,⟨(-2541114),(-2540709)⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨40650,41102⟩,⟨1776573,1777023⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-398082),(-397637)⟩,⟨(-307374),(-306926)⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨158728,159160⟩,⟨(-3550),(-3119)⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-50277),(-49865)⟩,⟨34322,34737⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨9501,9854⟩,⟨(-27755),(-27410)⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨7967,8258⟩,⟨15151,15437⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-11916),(-11691)⟩,⟨689,916⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-670),(-505)⟩,⟨(-8449),(-8285)⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨4390,4491⟩,⟨(-2849),(-2748)⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨1792,1838⟩,⟨(-53),(-8)⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨1357737082780706,1357737082780745⟩,⟨(-6074086802783991),(-6074086802783953)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨3462953734663997,3462953734664076⟩,⟨(-12964594594196841),(-12964594594196760)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨3994136221827513,3994136221827627⟩,⟨(-10896104101785329),(-10896104101785213)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨2987636956937974,2987636956938119⟩,⟨(-5386817286052153),(-5386817286052007)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨1520756776436859,1520756776437038⟩,⟨(-1641859426342414),(-1641859426342235)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨528771028611119,528771028611330⟩,⟨(-270800356355243),(-270800356355032)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨122481892570621,122481892570860⟩,⟨1203348691204,1203348691447⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨16798988643297,16798988643570⟩,⟨12583216527804,12583216528080⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨452372313548,452372313855⟩,⟨3195039969920,3195039970225⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-341898119196),(-341898118878)⟩,⟨342130213010,342130213322⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-74680884255),(-74680883950)⟩,⟨(-18107954571),(-18107954266)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-3814690980),(-3814690689)⟩,⟨(-13412564926),(-13412564633)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨2024702552,2024702793⟩,⟨(-2280767741),(-2280767499)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨816975636,816975821⟩,⟨10725925,10726108⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨202484341,202484465⟩,⟨150862280,150862403⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨34001958,34002012⟩,⟨49773655,49773709⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨5601515563302538037877,5601515563302538053878⟩,⟨1463302482453896818811,1463302482453896834339⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨13747160424304671816789,13747160424304671856466⟩,⟨2559660775561674276983,2559660775561674315402⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨15126000334799750505515,15126000334799750552158⟩,⟨706771328019926882933,706771328019926928010⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨11068130966183678738995,11068130966183678778060⟩,⟨(-1618750532419572644189),(-1618750532419572606244)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨5784006355157758247049,5784006355157758272214⟩,⟨(-2273618614789705350772),(-2273618614789705326070)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨2211458800305293812209,2211458800305293825064⟩,⟨(-1581038256979118808765),(-1581038256979118796037)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨629786333445453911553,629786333445453916918⟩,⟨(-735484272350706655060),(-735484272350706649711)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨136945269730584659946,136945269730584661890⟩,⟨(-256649987724561404005),(-256649987724561402057)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨23726161569026899278,23726161569026900012⟩,⟨(-73122151389388882344),(-73122151389388881610)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨3583534731873726442,3583534731873726825⟩,⟨(-18438013068532141856),(-18438013068532141474)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨584805188568136760,584805188568137089⟩,⟨(-4450547252708693338),(-4450547252708693011)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨140668714329687434,140668714329687723⟩,⟨(-1103211997008238970),(-1103211997008238681)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨50289149034455130,50289149034455377⟩,⟨(-296415871106671449),(-296415871106671198)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨21089966815698661,21089966815698845⟩,⟨(-88739455005361547),(-88739455005361361)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨8759011839272757,8759011839272873⟩,⟨(-28626057198296657),(-28626057198296540)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨2405098304388365,2405098304388414⟩,⟨(-6895868492004605),(-6895868492004559)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-3740090681917885661335562),(-3740090681917844066094346)⟩,⟨(-18802172905666996690748539),(-18802172905666955094399943)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-14108831029379787612608642),(-14108831029379699886625120)⟩,⟨(-48461526822796715040515740),(-48461526822796627312548046)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-28360117406099061612107176),(-28360117406098991951320164)⟩,⟨(-58235090349603445006122274),(-58235090349603375345142372)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-39444054141933595880022575),(-39444054141933566156810107)⟩,⟨(-46965687385465527068390525),(-46965687385465497348117750)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-39754085666317913577537750),(-39754085666317906569987410)⟩,⟨(-24984556311761001203221318),(-24984556311760994200663609)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-29682636343415740728675478),(-29682636343415739742488446)⟩,⟨(-5889729693399544712330379),(-5889729693399543730305233)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-16520536883016979635313757),(-16520536883016979482949625)⟩,⟨3498780915689621339781109,3498780915689621490888944⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-6740430950716969209581004),(-6740430950716969177359727)⟩,⟨4958862095538748715497513,4958862095538748747755703⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-1843604654724425626819316),(-1843604654724425613999970)⟩,⟨3295479744929535955498752,3295479744929535968616416⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-162336974514431048646865),(-162336974514431042675047)⟩,⟨1585901363606277603958582,1585901363606277610123204⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨173610591395471257237662,173610591395471260069165⟩,⟨624826822116557367359826,624826822116557370240111⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨147122886359919132152468,147122886359919133455599⟩,⟨216867423024893562349955,216867423024893563659052⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨82124861550325000073588,82124861550325000669017⟩,⟨70139947114471415464781,70139947114471416058048⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨40112465598729928996090,40112465598729929266396⟩,⟨22033975886552867414287,22033975886552867682249⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨17691312678315976857966,17691312678315976974367⟩,⟨6753256624227160569179,6753256624227160684239⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨4975952095993597004086,4975952095993597036598⟩,⟨1515029141798030737131,1515029141798030769228⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-1993787253149544243737860913),(-1993787253149522620553605989)⟩,⟨(-806597490387291061907326181),(-806597490387269438540541093)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-5643783700024393917991989362),(-5643783700024320238831060799)⟩,⟨(-1664087394804501055597327444),(-1664087394804427375850792457)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-8142913121322610543834214324),(-8142913121322461750220167372)⟩,⟨(-762276623264799085419626930),(-762276623264650290761440109)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-8637623793055524367444096127),(-8637623793055268835420177072)⟩,⟨1658626447872334253487987261,1658626447872589786876295066⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-6875671988933902085422839705),(-6875671988933397138440353078)⟩,⟨4217531498503612602701514964,4217531498504117550594887987⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-3707200217788823086938393244),(-3707200217788015007468310568)⟩,⟨5421584029771089664571362299,5421584029771897744304775461⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-658471861609176256269103234),(-658471861608271505212167421)⟩,⟨4803421045438983682335711074,4803421045439888433193105065⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨1140687126771743912468086166,1140687126772391793487616919⟩,⟨3090896878700334546773825360,3090896878700982427408691413⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨1576471801496378226643816474,1576471801496770386701460941⟩,⟨1376805756548240360581724422,1376805756548632520386224742⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨1231773135687953320695389734,1231773135688177471103818811⟩,⟨284030783654928999768211671,284030783655153150123104751⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨717839540818647027928675551,717839540818731470238613294⟩,⟨(-173981395214274207360364191),(-173981395214189765025335615)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨336088766450331536707525716,336088766450355160436483964⟩,⟨(-258385034429532294197104036),(-258385034429508670427931289)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨128425354666096512610190340,128425354666102489028337486⟩,⟨(-203175025097422040960166470),(-203175025097416064512792115)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨38173197458557289183467952,38173197458559333854345367⟩,⟨(-126932506560213863769942353),(-126932506560211819087167718)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨7148822370004856434923545,7148822370005540786305262⟩,⟨(-65734818472109324729924720),(-65734818472108640374381039)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨314330993430786638466306,314330993430950192094809⟩,⟨(-20005774790594361195291737),(-20005774790594197640679845)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-11125451522783768153926390808),(-11125451522783768137044211868)⟩,⟨8587519478487699673698421437,8587519478487699690055528525⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-28563874064785974044309653222),(-28563874064785973993342508428)⟩,⟨27691464020525298361123438958,27691464020525298411079304016⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-32860942663779327095472271593),(-32860942663779327010368074270)⟩,⟨49819726352495887482763611214,49819726352495887567715814040⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-20206688820229650654224813956),(-20206688820229650536869647488)⟩,⟨69934445627299060920917719788,69934445627299061040107966757⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨5764738724260925279759140169,5764738724260925425010537138⟩,⟨78716223963160711251224087363,78716223963160711400352370737⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨34357457082205441520573711081,34357457082205441684283611145⟩,⟨69458808180727971031753741308,69458808180727971200243303205⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨53183600798945573756364953895,53183600798945573940977470623⟩,⟨44478524728553704438058678431,44478524728553704625483975957⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨55529892630493461240765932734,55529892630493461466469586727⟩,⟨14438372117118484192973013322,14438372117118484419384799605⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨43846585678212910552660061120,43846585678212910993494964175⟩,⟨(-9077260570986817090556016041),(-9077260570986816650013932189)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨26464070480810450594523295802,26464070480810452011057048866⟩,⟨(-20549577193530886662949850371),(-20549577193530885246751810467)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨11215581977873093896791824820,11215581977873098991330222646⟩,⟨(-21564120077787332134595596873),(-21564120077787327040090778275)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨1656502272491497570679393462,1656502272491514532981408602⟩,⟨(-17055871345444067646276033623),(-17055871345444050683854175863)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-2536465735307694579953105794),(-2536465735307658887530683985)⟩,⟨(-11346716126699039732943797761),(-11346716126699004040421239596)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-3288105698625010736053508893),(-3288105698624962012681647365)⟩,⟨(-6612567346972582646205972872),(-6612567346972533922793826481)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-2371955705635702745088272656),(-2371955705635660348952194110)⟩,⟨(-3292109733945467385958347225),(-3292109733945424989818234200)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-837089043965949341388838478),(-837089043965932707168465779)⟩,⟨(-980662508788895301541922026),(-980662508788878667323739438)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨16594248296247139993479430030,16594248296247851179956902139⟩,⟨48204810084234766476848096012,48204810084235477665906612844⟩⟩
lemma checked : cachedMomentRuleBox density0 hk7_1_2 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 7 2) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk7_1_2 (tableDensity false) (fullFactor true 7 2) density0_contains hk7_1_2_contains
noncomputable def atomAnswer : CBox := ⟨⟨29054790763996813039916375051,29054790763996813064904497937⟩,⟨43624005156274762871846159876,43624005156274762897653750595⟩⟩
lemma atomChecked : tableAtomBox false ha7_1_2 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 7 2) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha7_1_2 7 2 ha7_1_2_contains
 def realAnswer : RBox := ⟨45649039060243953033295805081,45649039060244664244961400076⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 7 2) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm7_0_1_2
namespace hm7_1_1_2
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk7_1_2 j i k))
noncomputable def s0_0 : CBox := ⟨⟨3099237,3099261⟩,⟨9296246,9296268⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨261016,261057⟩,⟨20754563,20754600⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-10057485),(-10057435)⟩,⟨14277462,14277514⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-9097490),(-9097427)⟩,⟨41057,41121⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-980075),(-979996)⟩,⟨(-3240757),(-3240681)⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨979741,979822⟩,⟨(-261830),(-261751)⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-21607),(-21524)⟩,⟨277073,277158⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-60755),(-60669)⟩,⟨(-50642),(-50559)⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨25744,25827⟩,⟨(-1033),(-950)⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-8215),(-8134)⟩,⟨6241,6322⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨1345,1420⟩,⟨(-4998),(-4926)⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨1616,1679⟩,⟨2621,2685⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-2155),(-2103)⟩,⟨272,326⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-247),(-207)⟩,⟨(-1524),(-1484)⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨738,768⟩,⟨(-589),(-561)⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨315,335⟩,⟨(-46),(-27)⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨636938232351127,636938232351150⟩,⟨(-732688898340837),(-732688898340816)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨1401447879187004,1401447879187037⟩,⟨(-1519721398017747),(-1519721398017715)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨1267092851771193,1267092851771230⟩,⟨(-1205582258701021),(-1205582258700984)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨723173932955613,723173932955653⟩,⟨(-544448940578595),(-544448940578552)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨289299665495559,289299665495600⟩,⟨(-142614493756087),(-142614493756046)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨83942128350064,83942128350110⟩,⟨(-14217874218399),(-14217874218357)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨17132401508808,17132401508855⟩,⟨4521093110583,4521093110632⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨2063396791730,2063396791784⟩,⟨2310248619525,2310248619577⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-8283655821),(-8283655759)⟩,⟨489210434666,489210434724⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-59833874439),(-59833874377)⟩,⟨46639666758,46639666824⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-11850512738),(-11850512676)⟩,⟨(-4152628154),(-4152628091)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-448083106),(-448083041)⟩,⟨(-2340532620),(-2340532557)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨395730101,395730156⟩,⟨(-371947382),(-371947323)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨149079474,149079521⟩,⟨17093102,17093148⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨34491715,34491753⟩,⟨32306986,32307023⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨5256297,5256319⟩,⟨10092413,10092433⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨903941620558068315656,903941620558068320709⟩,⟨944092850231290742234,944092850231290747264⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨2334346951324255077991,2334346951324255090586⟩,⟨2131342452687390337688,2131342452687390350223⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨2793568044241414706384,2793568044241414720827⟩,⟨1965843057274940543422,1965843057274940557794⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨2253997308638533062132,2253997308638533073685⟩,⟨1055274687584740191673,1055274687584740203174⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨1305013166993526378104,1305013166993526385097⟩,⟨296632677992770528439,296632677992770535413⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨556863448757905699668,556863448757905702958⟩,⟨(-12160711030325067815),(-12160711030325064527)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨180323129916177874284,180323129916177875544⟩,⟨(-52844744896735525013),(-52844744896735523751)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨46277888572563531771,46277888572563532206⟩,⟨(-27913788331939504991),(-27913788331939504553)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨10058476463584444877,10058476463584445062⟩,⟨(-9644029856178726502),(-9644029856178726315)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨2038146954496998209,2038146954496998350⟩,⟨(-2690951655299876340),(-2690951655299876200)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨431554961737447458,431554961737447613⟩,⟨(-677648027883193090),(-677648027883192937)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨103905191590438206,103905191590438357⟩,⟨(-166817102872611004),(-166817102872610850)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨28986198423133944,28986198423134079⟩,⟨(-42851215724821788),(-42851215724821649)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨9180884501548050,9180884501548150⟩,⟨(-12080971225918837),(-12080971225918737)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨3109519667122541,3109519667122602⟩,⟨(-3707312888900959),(-3707312888900899)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨770632711078375,770632711078407⟩,⟨(-869922017455517),(-869922017455488)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨2754848860606813890309298,2754848860606848828816291⟩,⟨(-5786164064137192609691223),(-5786164064137157671300632)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨5858499228618746935448184,5858499228618820567639363⟩,⟨(-15559245223538277107082882),(-15559245223538203475101835)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨3968741524581326651977420,3968741524581385028170792⟩,⟨(-20361273195848123446593497),(-20361273195848065070424720)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-1060059473882680808295961),(-1060059473882655971442507)⟩,⟨(-18897846141040882780157114),(-18897846141040857943004410)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-5159965690044088635326989),(-5159965690044082817128324)⟩,⟨(-12969290890454008326562260),(-12969290890454002507857641)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-6019211566796605650430928),(-6019211566796604855604620)⟩,⟨(-6335678009345461816189718),(-6335678009345461020946165)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-4417486871362534118256652),(-4417486871362534009919783)⟩,⟨(-1837778834223280174629537),(-1837778834223280066168910)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-2334573016254089852269763),(-2334573016254089836414988)⟩,⟨84753441357434023577109,84753441357434039426460⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-928599584081277239737679),(-928599584081277234849307)⟩,⟨464482781100129989306276,464482781100129994164893⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-276865302801437017473262),(-276865302801437015310498)⟩,⟨331125160841687353221898,331125160841687355366012⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-54000251574546381695900),(-54000251574546380683615)⟩,⟨164894919161245123867654,164894919161245124875411⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨1280079371797561470099,1280079371797561934156⟩,⟨69792181810628536945775,69792181810628537409353⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨8391054167110734491272,8391054167110734704266⟩,⟨27607589897695497735280,27607589897695497948521⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨5961342953361107672507,5961342953361107770134⟩,⟨10777453001554193967862,10777453001554194065722⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨3088293165200093553821,3088293165200093596291⟩,⟨4101501692392120668813,4101501692392120711409⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨928985944568188415245,928985944568188427189⟩,⟨1069547511155924874114,1069547511155924886097⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-667776179832916819104543768),(-667776179832899049733872506)⟩,⟨(-231120849928857759312426628),(-231120849928839989968675754)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-1914252326363099012752630604),(-1914252326363038459978329578)⟩,⟨(-476891609133920880821201420),(-476891609133860328142120413)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-2826263386693398537968714565),(-2826263386693276234634134388)⟩,⟨(-205399840525412772381525021),(-205399840525290469234592031)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-3098645495642059890757689794),(-3098645495641849815125236322)⟩,⟨544275769983631395151760621,544275769983841470517709363⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-2593752442079004490096191081),(-2593752442078589309330772355)⟩,⟨1385856126891396008740482143,1385856126891811189310436519⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-1548006467932250320979934515),(-1548006467931585891411338589)⟩,⟨1848600855645124769316908467,1848600855645789198811332711⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-462476258059737411683404323),(-462476258058993644499700742)⟩,⟨1730722850023737479938121205,1730722850024481247149831463⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨250057467479051330199656984,250057467479583684683502609⟩,⟨1210934925912352412947733431,1210934925912884767509502506⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨498788242372973368367843829,498788242373295336766543061⟩,⟨631141359708610663574447023,631141359708932632026646024⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨445218278293736715011076511,445218278293920553493106042⟩,⟨221104768350763731898923948,221104768350947570392974180⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨292809834440730899725073535,292809834440800068827932930⟩,⟨17996629629540353172076212,17996629629609522270880175⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨159529242402130498501092800,159529242402149823222881928⟩,⟨(-47097644686686390479102311),(-47097644686667065764460330)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨76259603884655749061936789,76259603884660631331061084⟩,⟨(-50040753402869273783770240),(-50040753402864391519877582)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨33058190751135663590711440,33058190751137332069471779⟩,⟨(-35114886180048602262650339),(-35114886180046933785994595)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨12885849061304920740122146,12885849061305478733843297⟩,⟨(-19317696749537970183648017),(-19317696749537412190657569)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨3309337845469906927105752,3309337845470040226035444⟩,⟨(-6045557650940449139948125),(-6045557650940315841189149)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-318323266073428057476188026),(-318323266073428053022278615)⟩,⟨270735733575293963118241576,270735733575293967348415187⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-607972438674706922233588576),(-607972438674706909057675457)⟩,⟨988195391164021439301698049,988195391164021452120532538⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨346507603514335018241905735,346507603514335038974025011⟩,⟨1772576967818941405367955332,1772576967818941426404759829⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨3476040960274132769417262265,3476040960274132796218406903⟩,⟨1635387334211613489423222942,1635387334211613517933887867⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨8616224740548388765407853008,8616224740548388800770660804⟩,⟨(-658378179728141755739396837),(-658378179728141717106515626)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨13664612381395627625541197746,13664612381395627671495115309⟩,⟨(-5422792631468400626008311162),(-5422792631468400575867537092)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨15699795287510281629886180273,15699795287510281698303887653⟩,⟨(-11414940002952425196245465236),(-11414940002952425125289030793)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨13379760742562638270838348058,13379760742562638384718784404⟩,⟨(-16295617497548399704121950335),(-16295617497548399589748579274)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨7981114903252774913037142353,7981114903252775217694227617⟩,⟨(-18057637322807380331744193607),(-18057637322807380027749146141)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨2160519936155484134523426961,2160519936155485250225366297⟩,⟨(-16347352325453688095271759094),(-16347352325453686980522591046)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-1993297900475081938623910603),(-1993297900475077810298922745)⟩,⟨(-12448088845663523299328643355),(-12448088845663519171643976794)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-3874103371964903308414852060),(-3874103371964889480734945231)⟩,⟨(-8139153309007790371393226611),(-8139153309007776543875577888)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-3984839037686179658581892822),(-3984839037686150517024506714)⟩,⟨(-4640192193619651933483242850),(-4640192193619622791893828264)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-3133095433535146877994391929),(-3133095433535107065732960202)⟩,⟨(-2324578547907707567682025013),(-2324578547907667755349773429)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-1921883872128765675775127847),(-1921883872128731016817326173)⟩,⟨(-998975962923142097649881832),(-998975962923107438640797673)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-640134277250415345299989941),(-640134277250401743555854356)⟩,⟨(-268688264476328817473899976),(-268688264476315215712087426)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨6250671968662746732755429730,6250671968663330915097433879⟩,⟨(-14318412932276444425241166603),(-14318412932275860241401925665)⟩⟩
lemma checked : cachedMomentRuleBox density1 hk7_1_2 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 7 2) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk7_1_2 (tableDensity true) (fullFactor true 7 2) density1_contains hk7_1_2_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-37994726383688140161798189609),(-37994726383688140129121413528)⟩,⟨(-57046775973590074558470289239),(-57046775973590074524721901377)⟩⟩
lemma atomChecked : tableAtomBox true ha7_1_2 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 7 2) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha7_1_2 7 2 ha7_1_2_contains
 def realAnswer : RBox := ⟨(-31744054415025393429142759879),(-31744054415024809213923979649)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 7 2) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm7_1_1_2
namespace hm7_0_1_3
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk7_1_3 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-730357),(-730242)⟩,⟨(-162870593),(-162870476)⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨98502121,98502439⟩,⟨(-330319073),(-330318751)⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨225857424,225857950⟩,⟨(-183989954),(-183989429)⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨150470447,150471196⟩,⟨35563093,35563843⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨5283620,5284615⟩,⟨59468774,59469764⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-18678392),(-18677261)⟩,⟨1261313,1262445⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨1481452,1482764⟩,⟨(-5096699),(-5095387)⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨917552,918907⟩,⟨1207081,1208437⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-475600),(-474260)⟩,⟨(-95548),(-94205)⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨168821,170119⟩,⟨(-78635),(-77337)⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-40994),(-39886)⟩,⟨79867,80960⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-21188),(-20285)⟩,⟨(-49635),(-48742)⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨36113,36800⟩,⟨(-808),(-122)⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨816,1301⟩,⟨25559,26045⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-13888),(-13602)⟩,⟨8305,8580⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-5629),(-5526)⟩,⟨26,131⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-12656796278647997),(-12656796278647920)⟩,⟨7662767463813054,7662767463813134⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-27960942976039921),(-27960942976039718)⟩,⟨15594050050712064,15594050050712271⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-25355740045769893),(-25355740045769569)⟩,⟨11604012543511223,11604012543511544⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-14329844344174311),(-14329844344173873)⟩,⟨4278226083930525,4278226083930964⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-5491888648573974),(-5491888648573432)⟩,⟨386279340481439,386279340481978⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-1436395078983561),(-1436395078982943)⟩,⟨(-374222895429203),(-374222895428587)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-236354141851203),(-236354141850526)⟩,⟨(-202680681318432),(-202680681317754)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-14025411618614),(-14025411617878)⟩,⟨(-52487851335373),(-52487851334639)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨4016923664557,4016923665328⟩,⟨(-7498111618464),(-7498111617691)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨1274492434462,1274492435201⟩,⟨(-243098107735),(-243098106995)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨145845763311,145845763968⟩,⟨150311786230,150311786886⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-9643494418),(-9643493830)⟩,⟨37301842327,37301842913⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-8022125260),(-8022124754)⟩,⟨2868315102,2868315608⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-2028672111),(-2028671707)⟩,⟨(-1085664701),(-1085664301)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-322770300),(-322770032)⟩,⟨(-637806787),(-637806517)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-24841970),(-24841865)⟩,⟨(-169269264),(-169269154)⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-2806250121797579945105),(-2806250121797579921493)⟩,⟨(-10925429994222966033281),(-10925429994222966008761)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-8780028641871566735756),(-8780028641871566677063)⟩,⟨(-25892754716366927455474),(-25892754716366927394800)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-13564971160265485145832),(-13564971160265485076667)⟩,⟨(-26548412007840886978090),(-26548412007840886907282)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-13922458867516928291558),(-13922458867516928231837)⟩,⟨(-17353337197243922443276),(-17353337197243922382896)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-9969927762068672774758),(-9969927762068672733890)⟩,⟨(-7578779018111536011368),(-7578779018111535970527)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-5156029691643706306119),(-5156029691643706283772)⟩,⟨(-2091168151114632148785),(-2091168151114632126628)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-2001821662579566069756),(-2001821662579566059717)⟩,⟨(-245676003363369139779),(-245676003363369129865)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-613092854446319297540),(-613092854446319293631)⟩,⟨73398040747244672519,73398040747244676381⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-157936004252311212348),(-157936004252311210791)⟩,⟨52373982408545184441,52373982408545185988⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-37009910347828789072),(-37009910347828788232)⟩,⟨18667475972862329206,18667475972862330042⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-8585928993012236352),(-8585928993012235626)⟩,⟨5301231469554978132,5301231469554978859⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-2126420827181198801),(-2126420827181198162)⟩,⟨1393346903589215373,1393346903589216014⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-590975040240634566),(-590975040240634011)⟩,⟨369842802026643415,369842802026643973⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-186635274699539617),(-186635274699539199)⟩,⟨104497438447966793,104497438447967211⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-63443314234026272),(-63443314234026015)⟩,⟨31311068540532671,31311068540532926⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-15780772434902103),(-15780772434902010)⟩,⟨7158035277550894,7158035277550989⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-27075967871227989202443486),(-27075967871227919995086276)⟩,⟨15290729433526870867051572,15290729433526940074976294⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-67590411119164570024055753),(-67590411119164427208495212)⟩,⟨46655158812280302079673870,46655158812280444898310356⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-75380794738378967229533263),(-75380794738378858736764755)⟩,⟨74604161791874715186476829,74604161791874823687065918⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-51767331408754845910470680),(-51767331408754802863770453)⟩,⟨87123182787370278382578790,87123182787370321441568549⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-16617333572538947449860273),(-16617333572538937451704408)⟩,⟨76722081950568606150299531,76722081950568616159737519⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨8475788867668909955462359,8475788867668911944649107⟩,⟨50603173485204172249126418,50603173485204174242387542⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨16099104666567259145231631,16099104666567259421568073⟩,⟨24228032597840544274855414,24228032597840544551109908⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨12567090536410865830175423,12567090536410865883105159⟩,⟨7556112808899418592695311,7556112808899418644393838⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨6704681218020419804463494,6704681218020419825631339⟩,⟨650088984534174885362999,650088984534174905680585⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨2738967836333533671031107,2738967836333533681110403⟩,⟨(-937590430388177239768512),(-937590430388177229882206)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨900082838715565088337361,900082838715565092934086⟩,⟨(-790589949548956146770572),(-790589949548956142171922)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨239393120375768592444609,239393120375768594483099⟩,⟨(-429568537453772409818332),(-429568537453772407751332)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨46045143529608376446333,46045143529608377350338⟩,⟨(-200206387445000710901379),(-200206387445000709977190)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨867187156000727609649,867187156000728012619⟩,⟨(-87993607685328020179850),(-87993607685328019766802)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-4973075326742201978458),(-4973075326742201805352)⟩,⟨(-36346520208409812310058),(-36346520208409812133330)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-2101772263893997771155),(-2101772263893997722885)⟩,⟨(-9894836449841567398365),(-9894836449841567349191)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-628931686327293821550244713),(-628931686327266191631078973)⟩,⟨2906859169545711497477786926,2906859169545739127042363527⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-918931615143564833304870936),(-918931615143472135351582125)⟩,⟨8106910457041700458416986312,8106910457041793155282802741⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨973292841646628945093664503,973292841646812496933144687⟩,⟨11360241256748861834671404909,11360241256749045384717127296⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨4535773293826843892162929581,4535773293827240197540164537⟩,⟨11497023638358977536505410232,11497023638359373840238874802⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨7768481924998317909031902440,7768481924999098851795382319⟩,⟨8412705190126436791600795659,8412705190127217733544557434⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨8717885643393139246698403363,8717885643394320437796805809⟩,⟨3616535785586881743219269284,3616535785588062934373638900⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨7039651488442375002869378556,7039651488443610609465750542⟩,⟨(-584728433018535876253647380),(-584728433017300269044530327)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨4058687290324541043429212197,4058687290325424587405881877⟩,⟨(-2695606910372924271994754336),(-2695606910372040727342595239)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨1426498193661096945280701719,1426498193661768784517808607⟩,⟨(-2801353701584693368314005183),(-2801353701584021528842283596)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-66484743946678214420675132),(-66484743946328432648934216)⟩,⟨(-1927141248702390888339307579),(-1927141248702041106589245292)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-560874786887467548303594591),(-560874786887347407684804897)⟩,⟨(-996667411909147845064038453),(-996667411909027704544418116)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-538474611213794688052019190),(-538474611213762377636444032)⟩,⟨(-390962651480357690071541829),(-390962651480325379739081284)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-368409803247191148836183924),(-368409803247179903373826509)⟩,⟨(-100144571462222018324810726),(-100144571462210772893823206)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-212503241327237721865651139),(-212503241327234017264113238)⟩,⟨3152611413198079713307184,3152611413201784306543444⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-104488818605015157519905636),(-104488818605013977180292113)⟩,⟨21693660322964027242745240,21693660322965207581343238⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-30949290150412759958962851),(-30949290150412484660388796)⟩,⟨9588793686951542029125297,9588793686951817327867288⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨11046285389297252274364393335,11046285389297252294779383045⟩,⟨12855844331446660576918016759,12855844331446660597828965380⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨35309012210075164521211886777,35309012210075164583702413485⟩,⟨32652457625510164547366510586,32652457625510164610666629059⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨62743990181669991622997916152,62743990181669991729742431393⟩,⟨36290626064021845850777203681,36290626064021845957060466768⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨86938137368598708524295460028,86938137368598708675065653385⟩,⟨19124428333024036301112523463,19124428333024036448863658506⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨96339329088828841422049908253,96339329088828841612365338972⟩,⟨(-14124737850371779598608736441),(-14124737850371779413812082638)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨82811045103519551625440007778,82811045103519551845390226610⟩,⟨(-49751475383393760000560128726),(-49751475383393759786652523161)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨49711315739398072747781836727,49711315739398072997618800713⟩,⟨(-71961114116899641294361463686),(-71961114116899641047564660776)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨11047417494394675046665122349,11047417494394675348648989672⟩,⟨(-72474606928986079709782454357),(-72474606928986079408272148926)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-18171941186009391878458162262),(-18171941186009391310015967222)⟩,⟨(-55056346550576750901819968884),(-55056346550576750332755895979)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-31120049354420251926959141873),(-31120049354420250187175783513)⟩,⟨(-31055771863871535617042435267),(-31055771863871533876736871417)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-30428677586840846423978243644),(-30428677586840839037847773761)⟩,⟨(-10846022428265805043632493139),(-10846022428265797657483159065)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-23013017167971246666486951772),(-23013017167971222805341820322)⟩,⟨1161849731177983969413523083,1161849731178007830413093228⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-14690248070963939440627340247),(-14690248070963890702144379677)⟩,⟨5797099889103396231334354932,5797099889103444969723706045⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-8204627614755704876127350000),(-8204627614755640053218770614)⟩,⟨5910544717877090825423269354,5910544717877155648316182547⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-3924491421714542857503967398),(-3924491421714487630725867329)⟩,⟨3976537662207641148757893984,3976537662207696375554696602⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-1138950082695522498433898700),(-1138950082695501095113316332)⟩,⟨1368456728907964033294397252,1368456728907985436625999419⟩⟩
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
noncomputable def ans : CBox := ⟨⟨56025671376088147116858432366,56025671376089180012306131039⟩,⟨(-24885545726045925093239411622),(-24885545726044892201231744534)⟩⟩
lemma checked : cachedMomentRuleBox density0 hk7_1_3 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 7 3) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk7_1_3 (tableDensity false) (fullFactor true 7 3) density0_contains hk7_1_3_contains
noncomputable def atomAnswer : CBox := ⟨⟨51285844725786545210831126779,51285844725786545245143198903⟩,⟨(-38442077617219758672751764142),(-38442077617219758639433167071)⟩⟩
lemma atomChecked : tableAtomBox false ha7_1_3 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 7 3) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha7_1_3 7 3 ha7_1_3_contains
 def realAnswer : RBox := ⟨107311516101874692327589559145,107311516101875725257549329942⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 7 3) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm7_0_1_3
namespace hm7_1_1_3
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk7_1_3 j i k))
noncomputable def s0_0 : CBox := ⟨⟨3550943,3550979⟩,⟨(-27623465),(-27623431)⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨24654102,24654173⟩,⟨(-53787573),(-53787502)⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨43223802,43223910⟩,⟨(-25278330),(-25278222)⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨24200520,24200663⟩,⟨10290524,10290666⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-839615),(-839433)⟩,⟨9848466,9848649⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-2983124),(-2982927)⟩,⟨(-250613),(-250414)⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨310449,310666⟩,⟨(-769611),(-769388)⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨137094,137317⟩,⟨194984,195211⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-77454),(-77229)⟩,⟨(-14143),(-13917)⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨27894,28117⟩,⟨(-14802),(-14576)⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-6281),(-6078)⟩,⟨14509,14708⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-4425),(-4257)⟩,⟨(-8680),(-8514)⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨6534,6667⟩,⟨(-622),(-490)⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨517,611⟩,⟨4600,4695⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-2364),(-2300)⟩,⟨1716,1776⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-1012),(-983)⟩,⟨99,129⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-2305134508415362),(-2305134508415330)⟩,⟨112377368744967,112377368744997⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-4930482618876972),(-4930482618876918)⟩,⟨122400783788019,122400783788076⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-4200387260124902),(-4200387260124825)⟩,⟨(-124882603200014),(-124882603199938)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-2179202293315501),(-2179202293315410)⟩,⟨(-282561930081361),(-282561930081270)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-759004471696870),(-759004471696769)⟩,⟨(-230967102723792),(-230967102723691)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-180174032181311),(-180174032181209)⟩,⟨(-113034059419492),(-113034059419390)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-25942687109409),(-25942687109300)⟩,⟨(-36813418943102),(-36813418942992)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-499562004634),(-499562004514)⟩,⟨(-8001794650396),(-8001794650276)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨779769787196,779769787325⟩,⟨(-1027301204275),(-1027301204145)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨203073559024,203073559154⟩,⟨(-13214903926),(-13214903796)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨21287443549,21287443672⟩,⟨26798915836,26798915958⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-2201020334),(-2201020222)⟩,⟨6205848144,6205848256⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-1468852740),(-1468852639)⟩,⟨379865060,379865163⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-350587843),(-350587757)⟩,⟨(-235950381),(-235950293)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-46644287),(-46644222)⟩,⟨(-125394674),(-125394610)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-857954),(-857921)⟩,⟨(-32284800),(-32284766)⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨753020663795672080141,753020663795672087899⟩,⟨(-2432772676964004085889),(-2432772676964004078090)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨1402761551063272852128,1402761551063272871557⟩,⟨(-6019188104478947301461),(-6019188104478947281933)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨632340861114056131681,632340861114056154100⟩,⟨(-6695678827603484965117),(-6695678827603484942620)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-459693128603437066230),(-459693128603437047842)⟩,⟨(-4928653684477450818895),(-4928653684477450800475)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-855227620062667299509),(-855227620062667287860)⟩,⟨(-2557497339096350106943),(-2557497339096350095292)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-630946580682089005605),(-630946580682088999826)⟩,⟨(-949358944406450987657),(-949358944406450981882)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-299377131126881744320),(-299377131126881741982)⟩,⟨(-252034307635543538626),(-252034307635543536292)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-104790750908678136705),(-104790750908678135860)⟩,⟨(-46637958695559453196),(-46637958695559452358)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-29711152660062731544),(-29711152660062731186)⟩,⟨(-5174739988534284150),(-5174739988534283792)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-7448753460549720341),(-7448753460549720070)⟩,⟨81366848870436670,81366848870436937⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-1793664072046776330),(-1793664072046776028)⟩,⟨210316198628741288,210316198628741586⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-444207836122747388),(-444207836122747087)⟩,⟨67038931175599068,67038931175599365⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-118907357514622198),(-118907357514621945)⟩,⟨15844223008528904,15844223008529154⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-35425338568470172),(-35425338568469998)⟩,⟨3335728688933822,3335728688933997⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-11416431771089246),(-11416431771089143)⟩,⟨656649116088542,656649116088645⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-2755620762529835),(-2755620762529791)⟩,⟨100537425809008,100537425809055⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-10311563703831098764090205),(-10311563703831040632552785)⟩,⟨(-1312718897089300689740956),(-1312718897089242558260793)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-27031668901710294750512665),(-27031668901710174878934119)⟩,⟨(-1061882775463846082343694),(-1061882775463726211080123)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-33658283067592340940553661),(-33658283067592250021210246)⟩,⟨4554773807965315218203786,4554773807965406136743850⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-28900420725324457627935700),(-28900420725324421655546200)⟩,⟨11950661560398192247274288,11950661560398228218407258⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-17444073817369608878979433),(-17444073817369600575275755)⟩,⟨15499493496682978943037336,15499493496682987245604321⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-6433747974998950659170790),(-6433747974998949042187338)⟩,⟨13346650885889005284388708,13346650885889006900969313⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-135694722765824066101955),(-135694722765823865793325)⟩,⟨8240329141207011587713041,8240329141207011788033138⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨1711857800741039845599501,1711857800741039871281023⟩,⟨3718495865184926160433010,3718495865184926186236128⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨1424178298710602224983802,1424178298710602232687860⟩,⟨1184107035186806674274104,1184107035186806682059150⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨756518363257934828162716,756518363257934831736823⟩,⟨204968943034433103809106,204968943034433107400193⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨317686005985865859723409,317686005985865861359417⟩,⟨(-42578055530273408106092),(-42578055530273406470840)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨115903752985873403488141,115903752985873404220102⟩,⟨(-61026531842440781511335),(-61026531842440780782188)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨39177952724658456686528,39177952724658457015315⟩,⟨(-38438596164514255329388),(-38438596164514255002486)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨12840916025054729146085,12840916025054729294696⟩,⟨(-19898067500805795257898),(-19898067500805795110201)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨4098923880046587446034,4098923880046587510529⟩,⟨(-9062508189560590165251),(-9062508189560590101075)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨946677028051989883412,946677028051989901508⟩,⟨(-2587315911611563165924),(-2587315911611563147904)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-157463467127603137604504682),(-157463467127580432676037304)⟩,⟨964388501010079422281147454,964388501010102127268252186⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-192131922246214039754840333),(-192131922246137858477403518)⟩,⟨2728738334877731028400614191,2728738334877807209868265970⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨419009759479350517330217423,419009759479501387444723006⟩,⟨3928409276512386388153623119,3928409276512537258600557039⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨1557107459251944769745560156,1557107459252270575988055364⟩,⟨4137842007048806872618754457,4137842007049132679187048059⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨2644885521704991106872945508,2644885521705633217578994732⟩,⟨3230357819616232990375291630,3230357819616875101264597164⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨3056284169596975167694900100,3056284169597946381641396476⟩,⟨1632677260607486069932297849,1632677260608457283891072706⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨2607886360022754512523401266,2607886360023770267215500685⟩,⟨109662822775315058877755633,109662822776330813454368037⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨1657331080739009731365264792,1657331080739735714083234244⟩,⟨(-772858262353707125938249792),(-772858262352981143361117001)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨736184931527334905628430296,736184931527886499633107995⟩,⟨(-958170474979677343683222879),(-958170474979125749729010813)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨150573860913384597991271410,150573860913671476359063835⟩,⟨(-743259456521253857027745648),(-743259456520966978657191919)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-96174963563542862737053997),(-96174963563444451317842740)⟩,⟨(-443965139559664383163004779),(-443965139559565971725578934)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-141856387183304884588028822),(-141856387183278454857880829)⟩,⟨(-219209226408538886549787416),(-219209226408512456804448841)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-111561966486559422521316599),(-111561966486550235867790060)⟩,⟨(-92431043014205896099707851),(-92431043014196709440490116)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-69685326893446459794165224),(-69685326893443436755677166)⟩,⟨(-33517027849336112393082235),(-33517027849333089353098435)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-36066258804613807866467121),(-36066258804612845456360133)⟩,⟨(-10185633891870823646996575),(-10185633891869861236695738)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-10970943712794558834555317),(-10970943712794334460735105)⟩,⟨(-2049599843033579539666076),(-2049599843033355165868876)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨346201703338741470508989838,346201703338741475706693084⟩,⟨366243911811859860473877907,366243911811859865843730470⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨1232858811709548675747874965,1232858811709548691494549909⟩,⟨668524139218686013690832292,668524139218686029575304738⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨2123755152518644890248211048,2123755152518644916055210104⟩,⟨(-547291847602979183495286077),(-547291847602979158521257996)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨1718028941124951255532584479,1718028941124951290462937378⟩,⟨(-4373606967543286394809975019),(-4373606967543286362538361760)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-1585393586914045780135485833),(-1585393586914045732522424926)⟩,⟨(-10547758844524376083203990991),(-10547758844524376040192475847)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-8135716546608861491575220038),(-8135716546608861427151101369)⟩,⟨(-16434363081571768380464583895),(-16434363081571768321262632992)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-16168186674791656187645585363),(-16168186674791656093609145159)⟩,⟨(-18406828412921013468428079523),(-18406828412921013377012706949)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-22480294600320000712490522492),(-22480294600320000561931566046)⟩,⟨(-14868128273333574946678872048),(-14868128273333574796214528176)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-24418176628844189420471369991),(-24418176628844189033747826689)⟩,⟨(-7595252661554682822835793518),(-7595252661554682434862165064)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-21641748019964717114270523603),(-21641748019964715752906176693)⟩,⟨(-115072191034448545052553294),(-115072191034447182218048426)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-16028743747503764955687076267),(-16028743747503758970188496450)⟩,⟨4886117616046899068796457230,4886117616046905054980432599⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-10062629667553226374627475851),(-10062629667553206924144737052)⟩,⟨6758650988018944671304998054,6758650988018964121871961530⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-5385980914618148619772139745),(-5385980914618108828293966045)⟩,⟨6325828292180601033775625945,6325828292180640825130950161⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-2445378320784288283522256963),(-2445378320784235317785090716)⟩,⟨4749304335929132936949061759,4749304335929185902544461121⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-914687797551112611076636166),(-914687797551067464087632576)⟩,⟨2838702288982667087325986832,2838702288982712234221243082⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-216035575854342625285476640),(-216035575854325124224856822)⟩,⟨933989579402231227170763238,933989579402248728200076107⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-18694717901852342202043808467),(-18694717901851493755822542520)⟩,⟨(-5308063928183164751101731494),(-5308063928182316306844692748)⟩⟩
lemma checked : cachedMomentRuleBox density1 hk7_1_3 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 7 3) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk7_1_3 (tableDensity true) (fullFactor true 7 3) density1_contains hk7_1_3_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-67066104641413174551341106257),(-67066104641413174506471473481)⟩,⟨50270409191748915143874141555,50270409191748915187444614647⟩⟩
lemma atomChecked : tableAtomBox true ha7_1_3 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 7 3) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha7_1_3 7 3 ha7_1_3_contains
 def realAnswer : RBox := ⟨(-85760822543265516753484914724),(-85760822543264668262194016001)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 7 3) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm7_1_1_3
namespace hm7_0_1_4
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk7_1_4 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-149495590),(-149495363)⟩,⟨313340683,313340911⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-492623562),(-492622915)⟩,⟨548077512,548078159⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-606033483),(-606032479)⟩,⟨158439279,158440286⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-269137924),(-269136624)⟩,⟨(-199784704),(-199783409)⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨37371721,37373451⟩,⟨(-125270709),(-125268986)⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨39862824,39864970⟩,⟨11344939,11347074⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-6602950),(-6600283)⟩,⟨9881047,9883727⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-1297134),(-1294200)⟩,⟨(-3181834),(-3178898)⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨1010844,1013887⟩,⟨444754,447787⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-416269),(-413233)⟩,⟨108341,111377⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨115085,117712⟩,⟨(-173480),(-170886)⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨36602,38748⟩,⟨116475,118602⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-85003),(-83392)⟩,⟨(-4389),(-2772)⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-1268),(-149)⟩,⟨(-60171),(-59052)⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨31592,32232⟩,⟨(-19417),(-18800)⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨12741,12965⟩,⟨(-259),(-45)⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨25478522487077668,25478522487077776⟩,⟨6834618654876686,6834618654876796⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨54857109691665640,54857109691665935⟩,⟨16506929353078744,16506929353079034⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨47011691600134997,47011691600135436⟩,⟨17750507182267951,17750507182268388⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨24100912422100624,24100912422101228⟩,⟨12673575617044809,12673575617045414⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨7877881943248225,7877881943249021⟩,⟨6412005061335642,6412005061336438⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨1542477174833191,1542477174834190⟩,⟨2314552615399822,2314552615400821⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨96327569298511,96327569299729⟩,⟨585692118916644,585692118917858⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-41612783382717),(-41612783381262)⟩,⟨96910431743367,96910431744823⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-15167047250101),(-15167047248418)⟩,⟨7263196297343,7263196299029⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-2395224970083),(-2395224968327)⟩,⟨(-1037307514421),(-1037307512666)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-88321027979),(-88321026292)⟩,⟨(-418882280691),(-418882278998)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨56316870619,56316872212⟩,⟨(-56587163096),(-56587161506)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨17626130994,17626132273⟩,⟨2808130317,2808131591⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨2748723655,2748724587⟩,⟨4007554445,4007555372⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨9885668,9886249⟩,⟨1517671909,1517672489⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-110356470),(-110356257)⟩,⟨347047627,347047839⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-11966270356230432848997),(-11966270356230432804457)⟩,⟨11336138715656140579148,11336138715656140623622⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-26822192504301823701829),(-26822192504301823589866)⟩,⟨29800095946812792494088,29800095946812792606311⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-24101633359748440389834),(-24101633359748440254764)⟩,⟨36839334236907595437908,36839334236907595574146⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-11806383633888152692668),(-11806383633888152575988)⟩,⟨31016142760132287531867,31016142760132287650312⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-1958137229101422722966),(-1958137229101422645101)⟩,⟨18825289802687445210080,18825289802687445289492⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨1525388815178579398586,1525388815178579440320⟩,⟨8403406578611338812206,8403406578611338854758⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨1409903859783980166382,1409903859783980184990⟩,⟨2817551656094529173315,2817551656094529192133⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨654436028094050463601,654436028094050470744⟩,⟨733448881382394297579,733448881382394304760⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨220374749843060304082,220374749843060306877⟩,⟨156185723964474326634,156185723964474329433⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨61940628199948427804,61940628199948429290⟩,⟨29498134443652907339,29498134443652908823⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨16073158901406265193,16073158901406266480⟩,⟨5573844106803977652,5573844106803978937⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨4184103518286315451,4184103518286316595⟩,⟨1220396104433582480,1220396104433583624⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨1163759171932591525,1163759171932592523⟩,⟨340105304990931285,340105304990932278⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨357505056137051768,357505056137052508⟩,⟨117132201153662321,117132201153663057⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨117498436052007116,117498436052007558⟩,⟨43816791272060635,43816791272061073⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨28595581295002835,28595581295002989⟩,⟨11538950550782271,11538950550782422⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨27960865478970646445367149,27960865478970724326934149⟩,⟨25478551668147651683778266,25478551668147729561837857⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨80045727641923623884807667,80045727641923780496540699⟩,⟨60319059183417819740701850,60319059183417976341339285⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨116495691470998776299250742,116495691470998888638011889⟩,⟨58231347229561965187741620,58231347229562077507887184⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨123086827233511475070822065,123086827233511522722727785⟩,⟨24953756647992304832988289,24953756647992352466532867⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨97544708017371192720471749,97544708017371207875360436⟩,⟨(-13202598303930392549304535),(-13202598303930377402814199)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨56365068841427333759907806,56365068841427336491225431⟩,⟨(-32860932025110211819927469),(-32860932025110209088942669)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨21420249331778198758600778,21420249331778199083678361⟩,⟨(-30879158006017953574945285),(-30879158006017953246863412)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨2806115011798449041276753,2806115011798449095485203⟩,⟨(-19066743921015963227857066),(-19066743921015963171136835)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-2807527699925563508856345),(-2807527699925563484116495)⟩,⟨(-8563810228097434781351036),(-8563810228097434756005259)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-2721163095626816872076751),(-2721163095626816859210025)⟩,⟨(-2853384194483811070756491),(-2853384194483811057935054)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-1528579524074394136634499),(-1528579524074394130203871)⟩,⟨(-646844376456121358149381),(-646844376456121351851854)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-691504912779352148005780),(-691504912779352144891503)⟩,⟨(-29123257193541248719210),(-29123257193541245684201)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-283613300552720472442369),(-283613300552720470936483)⟩,⟨73858080292059959228996,73858080292059960711111⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-112406738557347472340707),(-112406738557347471626055)⟩,⟨58894184830394777619205,58894184830394778327852⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-42860628977837664138272),(-42860628977837663821221)⟩,⟨31687024744411591173363,31687024744411591489157⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-11149008049443703573067),(-11149008049443703483197)⟩,⟨9663709191949731693895,9663709191949731783596⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨3081818324907221743959258153,3081818324907247203793881361⟩,⟨128667264325051980695159894,128667264325077440992743089⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨8469067385773216603510117069,8469067385773301555064200403⟩,⟨(-517179196522382648104178345),(-517179196522297695185839691)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨11507794554098090105295875007,11507794554098297066164050731⟩,⟨(-3114127641274627042329406366),(-3114127641274420079772162260)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨11023301139522535748471266755,11023301139522998844582089037⟩,⟨(-6939349889138635608369976113),(-6939349889138172511025796237)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨7180676305849243964612702356,7180676305850111995054391446⟩,⟨(-9853079315218653057068376374),(-9853079315217785026286176302)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨1887985718974387941352043755,1887985718975628180782624839⟩,⟨(-9995631683165761632844017705),(-9995631683164521393936003543)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-2295924739098043309609276418),(-2295924739096844934457145133)⟩,⟨(-7369577725868495159146691072),(-7369577725867296784979773218)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-3947526246116169555728884936),(-3947526246115094220288050407)⟩,⟨(-3690612085370582953531697708),(-3690612085369507618701713454)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-3452668775814077243844471588),(-3452668775813272934713599299)⟩,⟨(-786811062736015417109588550),(-786811062735211108063253365)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-2110397829860463146386824712),(-2110397829860081000529089808)⟩,⟨642737228341007465405658746,642737228341389611404724000⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-937202199004173504092237938),(-937202199004052627265089634)⟩,⟨940976401782790112265842995,940976401782910989260827979⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-261697037299034454004680470),(-261697037298990609446113395)⟩,⟨738389433899838268255481491,738389433899882112884065445⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨14945838676501124378011726,14945838676515924316623541⟩,⟨454555084075435625440399965,454555084075450425392831468⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨80833697159584284508947609,80833697159588836218829982⟩,⟨242452396727969553348541955,242452396727974105054461024⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨63932158823196090725383976,63932158823197472528467683⟩,⟨112245272500520482594946292,112245272500521864392197217⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨22755498144995283348254687,22755498144995597253030863⟩,⟨32104843062817531271407479,32104843062817845173847404⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨11088242438163851763084085748,11088242438163851782447824578⟩,⟨(-10587750402132364767817016488),(-10587750402132364748774985241)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨27813943801129197672806635554,27813943801129197731569068926⟩,⟨(-33580194695800264760989654913),(-33580194695800264702581487422)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨29645552794620657756044297459,29645552794620657855211146825⟩,⟨(-58993666754565322228155574224),(-58993666754565322127979897624)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨12343086636024922341592031566,12343086636024922480469815957⟩,⟨(-80701507551425311266240645939),(-80701507551425311123897504181)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-19490270130543909554793100711),(-19490270130543909379454468109)⟩,⟨(-87957221983791475184997542211),(-87957221983791475003907111092)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-52678763835982963709416130202),(-52678763835982963499948990800)⟩,⟨(-73376535016954730412772735185),(-73376535016954730197873317402)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-72117582032735296151242215805),(-72117582032735295906461402237)⟩,⟨(-40580357361125861767247204598),(-40580357361125861520105577385)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-70173723438905662886275907540),(-70173723438905662587739031967)⟩,⟨(-3380125665311371363256102971),(-3380125665311371064686144364)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-51095892640691150483392550176),(-51095892640691149939798950897)⟩,⟨23649926012253494041324044788,23649926012253494584085882566⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-26464802151497955465363125192),(-26464802151497953727530972602)⟩,⟨34229419000481292269842325314,34229419000481294007121695120⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-6560449582107754372949191928),(-6560449582107746489980286347)⟩,⟨31524260395678264366364213283,31524260395678272249337426105⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨4564852953245738071627962090,4564852953245762671374820646⟩,⟨22785424356404522700340644779,22785424356404547300207133115⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨8158396516247905234811612423,8158396516247953933746585365⟩,⟨13866561690854332073680112235,13866561690854380772660168269⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨7355481242566466108006203021,7355481242566528964743350139⟩,⟨7330158177262271452069929493,7330158177262334308780231413⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨4725181903838616822429425393,4725181903838669000328133813⟩,⟨3310779009807602285578129719,3310779009807654463432512497⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨1596461462610810011595259207,1596461462610829915875543172⟩,⟨922620976604485254818321656,922620976604505159079188908⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-26740856096941292452637569740),(-26740856096940166664029177017)⟩,⟨(-48408542716410305996017983618),(-48408542716409180204195681458)⟩⟩
lemma checked : cachedMomentRuleBox density0 hk7_1_4 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 7 4) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk7_1_4 (tableDensity false) (fullFactor true 7 4) density0_contains hk7_1_4_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-37972438921062993942484099572),(-37972438921062993908870799292)⟩,⟨(-44971359138062014876813942784),(-44971359138062014842304584219)⟩⟩
lemma atomChecked : tableAtomBox false ha7_1_4 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 7 4) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha7_1_4 7 4 ha7_1_4_contains
 def realAnswer : RBox := ⟨(-64713295018004286395221669312),(-64713295018003160572799976309)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 7 4) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm7_0_1_4
namespace hm7_1_1_4
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk7_1_4 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-32409636),(-32409583)⟩,⟨49739157,49739210⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-96862204),(-96862077)⟩,⟨81363609,81363736⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-107120972),(-107120783)⟩,⟨10887102,10887291⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-39366468),(-39366230)⟩,⟨(-41236060),(-41235823)⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨9678552,9678857⟩,⟨(-19356101),(-19355794)⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨6026995,6027357⟩,⟨2753564,2753926⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-1181894),(-1181459)⟩,⟨1433260,1433697⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-185306),(-184831)⟩,⟨(-507286),(-506811)⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨165318,165814⟩,⟨69203,69698⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-69497),(-68989)⟩,⟨22001,22510⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨18242,18699⟩,⟨(-31851),(-31401)⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨8041,8423⟩,⟨20501,20878⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-15449),(-15159)⟩,⟨293,583⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-1090),(-887)⟩,⟨(-10860),(-10658)⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨5361,5479⟩,⟨(-4022),(-3906)⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨2274,2325⟩,⟨(-283),(-234)⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨2988801746867324,2988801746867363⟩,⟨2828046516328446,2828046516328486⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨6297165676769391,6297165676769480⟩,⟨6182571831468797,6182571831468882⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨5166317750426336,5166317750426455⟩,⟨5536271250576390,5536271250576508⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨2476924898080400,2476924898080531⟩,⟨3141776660300701,3141776660300834⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨729820266423418,729820266423560⟩,⟨1268621729622736,1268621729622879⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨111085628424165,111085628424323⟩,⟨382715449329662,382715449329820⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-7283476381736),(-7283476381552)⟩,⟨85537877145071,85537877145257⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-8841499032201),(-8841499031975)⟩,⟨12807232333873,12807232334099⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-2443661302847),(-2443661302578)⟩,⟨727340639073,727340639341⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-352804987963),(-352804987673)⟩,⟨(-207685465812),(-207685465522)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-7602837292),(-7602837001)⟩,⟨(-69542849949),(-69542849656)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨10435722286,10435722576⟩,⟨(-8790761556),(-8790761269)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨3081223939,3081224181⟩,⟨781014602,781014842⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨428084312,428084497⟩,⟨783210197,783210382⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-30010230),(-30010109)⟩,⟨282471935,282472054⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-28472576),(-28472520)⟩,⟨62573358,62573413⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-3642098362849731574435),(-3642098362849731560124)⟩,⟨763975973175432158653,763975973175432172960⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-8705124387822893580445),(-8705124387822893544117)⟩,⟨2522559144903136240779,2522559144903136277116⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-9048020964819911471559),(-9048020964819911428571)⟩,⟨4093896950369903236401,4093896950369903279438⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-5992865756810204869949),(-5992865756810204834576)⟩,⟨4313716660712002900710,4313716660712002936156⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-2631142589438569637364),(-2631142589438569615479)⟩,⟨3112230622632734783053,3112230622632734804999⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-712509374621952131478),(-712509374621952120840)⟩,⟨1597946168835875439860,1597946168835875450528⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-69358371357220517126),(-69358371357220512821)⟩,⟨607308055987693659283,607308055987693663602⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨34595328834658952347,34595328834658953894⟩,⟨179262895992481856484,179262895992481858033⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨21803327995817324514,21803327995817325176⟩,⟨43827750421499293831,43827750421499294491⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨7657174035984759090,7657174035984759590⟩,⟨9662214994963835867,9662214994963836368⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨2185308314510175127,2185308314510175693⟩,⟨2119954135617526587,2119954135617527156⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨581988362984121209,581988362984121788⟩,⟨504404834827624784,504404834827625367⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨158055146155916402,158055146155916904⟩,⟨136152109665078453,136152109665078953⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨46499982296425431,46499982296425796⟩,⟨41879787326758866,41879787326759231⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨14719995092562178,14719995092562391⟩,⟨13933344752271706,13933344752271918⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨3512772117278998,3512772117279074⟩,⟨3426104575226837,3426104575226916⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨2401935236496883528248219,2401935236496948944320006⟩,⟨12415285355115395757274242,12415285355115461173709773⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨9173991815674863470545999,9173991815674994915478417⟩,⟨31713753384943223853709200,31713753384943355299793198⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨18573434424565982406919738,18573434424566076534273691⟩,⟨37344682256714059507881699,37344682256714153637158792⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨25792099695279447437293445,25792099695279487240564571⟩,⟨28926235943284157247571176,28926235943284197052723210⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨25725321142474875678153606,25725321142474888270282838⟩,⟨13938788658911846444675639,13938788658911859037641917⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨18768221677307347228825020,18768221677307349457106396⟩,⟨1643081091842302093219153,1643081091842304321520566⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨9959433404247925606452421,9959433404247925846929506⟩,⟨(-3764212549887161424575789),(-3764212549887161184401913)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨3644129421909712680084823,3644129421909712707741922⟩,⟨(-3957833992940573107031819),(-3957833992940573079617964)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨685225186499041623061991,685225186499041632717713⟩,⟨(-2381284133916166438212886),(-2381284133916166428610165)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-177726322554347981360872),(-177726322554347976730642)⟩,⟨(-1052577633377497611532496),(-1052577633377497606894761)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-244472527483359489749536),(-244472527483359487499033)⟩,⟨(-370725849555136527306264),(-370725849555136525042433)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-150059123913171649072441),(-150059123913171647986862)⟩,⟨(-107085859562199165666384),(-107085859562199164573351)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-74469511180055165003576),(-74469511180055164469113)⟩,⟨(-24191171298593149507840),(-24191171298593148971283)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-34040282140132442112774),(-34040282140132441854426)⟩,⟨(-2749960328242382821540),(-2749960328242382562715)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-14410092022216119697509),(-14410092022216119581189)⟩,⟨1095598645924774222435,1095598645924774338836⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-3970831135499878974675),(-3970831135499878941422)⟩,⟨616765864176196540254,616765864176196573513⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨1013382152650894763948065933,1013382152650915685622942884⟩,⟨(-9628975831555483129749950),(-9628975831534561536109908)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨2829599093484979174690775112,2829599093485048989886464433⟩,⟨(-294114690309445526208403781),(-294114690309375711261307581)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨3964242116273504175577431188,3964242116273674289610345129⟩,⟨(-1161745748406393519231176657),(-1161745748406223405518163937)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨3982273103027614955956527826,3982273103027995673913802751⟩,⟨(-2419540558327823558014528139),(-2419540558327442840306802163)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨2827416706307480924168384606,2827416706308194641246572826⟩,⟨(-3430386576697317535035010819),(-3430386576696603818042095858)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨1046855552447984533667437435,1046855552449004298721593835⟩,⟨(-3584969566226171557273043844),(-3584969566225151792128319259)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-502502649685534701148830053),(-502502649684549552914502008)⟩,⟨(-2807737713196033757921699027),(-2807737713195048609485743536)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-1258151700520240301191329474),(-1258151700519356739473029254)⟩,⟨(-1591020610575136327790199446),(-1591020610574252765941181201)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-1249396724303699251364006801),(-1249396724303038891771797278)⟩,⟨(-540373848448331254718597487),(-540373848447670895107001945)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-866072998861187177732314338),(-866072998860873752459701829)⟩,⟨53083111297580321805390645,53083111297893747050636968⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-465959877385081424637994656),(-465959877384982410821314862)⟩,⟨247388339297245813518111129,247388339297344827302931985⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-200173645743510079191989152),(-200173645743474214808766229)⟩,⟨233293991001881803835550101,233293991001917668205583426⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-66203332910208542828886529),(-66203332910196452217401250)⟩,⟨159386879848824488688160304,159386879848836579297015168⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-13102766166696025772430437),(-13102766166692311419094302)⟩,⟨92060079535559445160264516,92060079535563159514250015⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨1713359263598343867959175,1713359263599470554406678⟩,⟨45331234176895671696123064,45331234176896798383564532⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨1776837116230620417578815,1776837116230876256772782⟩,⟨13438036039545058465092246,13438036039545314304679314⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨314386822626066440828357122,314386822626066445670710948⟩,⟨(-330091047943708739261016996),(-330091047943708734485548315)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨544083573829313351734237709,544083573829313366054070560⟩,⟨(-1149117488843929132638860876),(-1149117488843929118177076269)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-611926409475794828818711051),(-611926409475794806334701735)⟩,⟨(-1901263820870637270623059084),(-1901263820870637246961194210)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-4106845146626009972322197586),(-4106845146626009943307225216)⟩,⟨(-1310285500206508083824227186),(-1310285500206508051859547870)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-9631640563763473398552255342),(-9631640563763473359527549772)⟩,⟨2175364433385002354765155186,2175364433385002398551322884⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-14700541017351991297682897509),(-14700541017351991239743318315)⟩,⟨8843528407922137630841490284,8843528407922137693407986485⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-15942748056601667229794422648),(-15942748056601667139184661445)⟩,⟨16842566829528257500578193414,16842566829528257593103346263⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-11959570184911596384162852076),(-11959570184911596236739619081)⟩,⟨22905321797193343244450657830,22905321797193343391456447070⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-4616862478790850131269669207),(-4616862478790849765893259457)⟩,⟨24409395465861804306316332262,24409395465861804670113789429⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨2567055111042034188721110013,2567055111042035547280636099⟩,⟨21148323001796121059905763874,21148323001796122416941682150⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨7009630363014278104246208481,7009630363014284494185550733⟩,⟨15163377266285553178069028788,15163377266285559567511663380⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨8231466998645587100190548875,8231466998645607152024391501⟩,⟨9039115797979151089349480190,9039115797979171141225299907⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨7218372471847619158150107699,7218372471847658915485714512⟩,⟨4419633167944046528103745074,4419633167944086285637336968⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨5219915395972244089303495313,5219915395972295446556074092⟩,⟨1687339779535994950000085803,1687339779536046307438545364⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨3048024934673046352560275640,3048024934673089005757669523⟩,⟨442208396688405904655606365,442208396688448557970531510⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨991200675721436297217089521,991200675721452572057842393⟩,⟨56766691043111080193876067,56766691043127355073211910⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-2544384729315956992435026765),(-2544384729315032230536071279)⟩,⟨17926831114267925389191324086,17926831114268850153000611399⟩⟩
lemma checked : cachedMomentRuleBox density1 hk7_1_4 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 7 4) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk7_1_4 (tableDensity true) (fullFactor true 7 4) density1_contains hk7_1_4_contains
noncomputable def atomAnswer : CBox := ⟨⟨49656266281390068957754122152,49656266281390069001709976363⟩,⟨58808700411311865563013687056,58808700411311865608141309794⟩⟩
lemma atomChecked : tableAtomBox true ha7_1_4 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 7 4) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha7_1_4 7 4 ha7_1_4_contains
 def realAnswer : RBox := ⟨47111881552074111965219095387,47111881552075036771273905084⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 7 4) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm7_1_1_4
namespace hm7_0_1_5
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk7_1_5 j i k))
noncomputable def s0_0 : CBox := ⟨⟨461834235,461834676⟩,⟨(-370414476),(-370414034)⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨1162714128,1162715426⟩,⟨(-486507582),(-486506282)⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨1061586970,1061589068⟩,⟨184573722,184575818⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨291743771,291746624⟩,⟨502755702,502758555⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-141905238),(-141901730)⟩,⟨179696113,179699609⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-59661041),(-59657514)⟩,⟨(-42767785),(-42764279)⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨16603631,16607554⟩,⟨(-13322558),(-13318583)⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨765510,770274⟩,⟨6167698,6172461⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-1632419),(-1627107)⟩,⟨(-1198647),(-1193364)⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨783548,789099⟩,⟨(-71104),(-65555)⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-256389),(-251473)⟩,⟨285414,290300⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-52171),(-48106)⟩,⟨(-224733),(-220696)⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨153551,156605⟩,⟨13673,16726⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-2941),(-855)⟩,⟨109043,111130⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-59846),(-58668)⟩,⟨34012,35147⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-23890),(-23491)⟩,⟨33,417⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-18112364595861219),(-18112364595861045)⟩,⟨(-32978950862795274),(-32978950862795102)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-37684884723110278),(-37684884723109775)⟩,⟨(-72832779472619390),(-72832779472618888)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-29511569458461796),(-29511569458460980)⟩,⟨(-66161679804983555),(-66161679804982740)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-12193142738088453),(-12193142738087321)⟩,⟨(-37743284348282456),(-37743284348281325)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-2007118225649495),(-2007118225648066)⟩,⟨(-14857013436410407),(-14857013436408974)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨582597129631105,582597129632761⟩,⟨(-4128545519257840),(-4128545519256186)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨462164116350340,462164116352151⟩,⟨(-778323999400556),(-778323999398747)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨143841223764889,143841223766790⟩,⟨(-78320675457199),(-78320675455294)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨26137609796955,26137609798941⟩,⟨4909304331820,4909304333805⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨2249208138408,2249208140738⟩,⟨3547719290010,3547719292342⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-243059864407),(-243059861884)⟩,⟨656421996502,656421999027⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-127962331766),(-127962329156)⟩,⟨33744811063,33744813677⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-23643478416),(-23643476161)⟩,⟨(-18324069323),(-18324067070)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-1007269509),(-1007267785)⟩,⟨(-8148803539),(-8148801814)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨1133913491,1133914604⟩,⟨(-2315080675),(-2315079560)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨427892818,427893222⟩,⟨(-448877809),(-448877403)⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨18377181715328150910682,18377181715328150964961⟩,⟨5795441984597179301706,5795441984597179354542⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨45882519301538325621634,45882519301538325757516⟩,⟨10348457434572983878486,10348457434572984010381⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨51910010768568479911424,51910010768568480073837⟩,⟨3131612496388234476380,3131612496388234633507⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨39051367746656462629048,39051367746656462768139⟩,⟨(-6593002744641310881724),(-6593002744641310746512)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨20677038146661849690346,20677038146661849782056⟩,⟨(-9803363991694731295177),(-9803363991694731204985)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨7713196458877966883014,7713196458877966930703⟩,⟨(-7106611428759493683674),(-7106611428759493636291)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨1958713704931211674769,1958713704931211694812⟩,⟨(-3415582578724350498302),(-3415582578724350478227)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨288821526344823306528,288821526344823313702⟩,⟨(-1218062558666191611542),(-1218062558666191604319)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-6155182362081653587),(-6155182362081650823)⟩,⟨(-350716557670682000704),(-350716557670681997936)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-19362847480593864003),(-19362847480593862372)⟩,⟨(-88750117240310215362),(-88750117240310213726)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-7870139451572958867),(-7870139451572957391)⟩,⟨(-21552680987704453972),(-21552680987704452494)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-2454794463718620516),(-2454794463718619145)⟩,⟨(-5450288191001769882),(-5450288191001768513)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-723039575037994114),(-723039575037992863)⟩,⟨(-1524003966681396269),(-1524003966681395015)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-219300674150462027),(-219300674150461036)⟩,⟨(-481765958558110335),(-481765958558109343)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-68995054921199669),(-68995054921199045)⟩,⟨(-163888874573068197),(-163888874573067573)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-16196401486655357),(-16196401486655142)⟩,⟨(-40801203325525526),(-40801203325525310)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨15053714030527835257869603,15053714030527897320077237⟩,⟨(-33596637449193862141386487),(-33596637449193800073361038)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨31236890953716983799191250,31236890953717109768811418⟩,⟨(-92733321472333411584728139),(-92733321472333285599097534)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨17408405834025587389213158,17408405834025700437887775⟩,⟨(-126757780240326683834198438),(-126757780240326570768382070)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-16894924016728558074541048),(-16894924016728500672087798)⟩,⟨(-123361346627087577101208144),(-123361346627087519688586464)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-45806513486843541760749554),(-45806513486843525301074306)⟩,⟨(-87475315611655574124279914),(-87475315611655557663564149)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-51565861680997977613614134),(-51565861680997974955136773)⟩,⟨(-41789680327319730357808384),(-41789680327319727704118603)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-37831505137226598429027350),(-37831505137226598124909418)⟩,⟨(-8801714832715148583437468),(-8801714832715148284449594)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-19637252441413583932838754),(-19637252441413583859114503)⟩,⟨4996450469812459805149814,4996450469812459877387993⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-7186000389968204078018030),(-7186000389968204045227077)⟩,⟨6434795451191075860618835,6434795451191075893546627⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-1582285645734496917887133),(-1582285645734496901562051)⟩,⟨3994088615213011862321998,3994088615213011879040500⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨90996480134019709736313,90996480134019717799284⟩,⟨1837462902700372246463409,1837462902700372254725180⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨320793476855314456840047,320793476855314460782427⟩,⟨710174706077600723250189,710174706077600727233080⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨224446652491681648026256,224446652491681649911109⟩,⟨247991566843914166547877,247991566843914168433465⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨121184803562664303029584,121184803562664303914437⟩,⟨82143979619930067769894,82143979619930068649528⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨56224701983310999263102,56224701983310999652442⟩,⟨26026422186479586935434,26026422186479587321070⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨16161664541908895664700,16161664541908895774557⟩,⟨5932236486676181025972,5932236486676181134604⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-330805876397251327740721712),(-330805876397230612305823797)⟩,⟨(-2537716783329680827215793057),(-2537716783329660112170381929)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-1642667675571472369322352885),(-1642667675571393858256198585)⟩,⟨(-6865328423248217820652553568),(-6865328423248139310552682877)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-4275522479527194629586232617),(-4275522479527001229224199611)⟩,⟨(-9009161537558345857935477860),(-9009161537558152458620701586)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-7469241964448888827560832229),(-7469241964448473572454442698)⟩,⟨(-8051140926642314850380027215),(-8051140926641899595859368234)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-9420622145626095498667622168),(-9420622145625353245929701525)⟩,⟨(-4370149102293527377800474288),(-4370149102292785124891507667)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-8769145660336509723622171389),(-8769145660335514373910301023)⟩,⟨174506216498799760515518159,174506216499795111055162321⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-5851895067110565104836372931),(-5851895067109559114011700731)⟩,⟨3359763237093929590742557752,3359763237094935582511271478⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-2378327735487607671967870091),(-2378327735486546064779337715)⟩,⟨4163668351001408393117809681,4163668351002470000623946330⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨73118990652452598365650107,73118990653176344921976593⟩,⟨3190371976240578995145297086,3190371976241302741611367640⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨1067096537149810953891088170,1067096537150120849698998151⟩,⟨1714149571573213776527426887,1714149571573523672108436531⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨1077676510672641435905281918,1077676510672759966077276948⟩,⟨600728091513014771938687421,600728091513133301975368433⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨736763517447158819300932861,736763517447204683811887220⟩,⟨39219541765427137201472026,39219541765473001684339672⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨409880750195267154570602784,409880750195281355117427001⟩,⟨(-140930361226965811527016131),(-140930361226951610969726658)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨198843485507301109495844011,198843485507305173083008384⟩,⟨(-144613617061763040743612049),(-144613617061758977139538592)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨84346048117253334005065610,84346048117254496720837248⟩,⟨(-92373376918354904017430188),(-92373376918353741289695191)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨22773434939735958872023857,22773434939736213766069204⟩,⟨(-30712469937793995343796921),(-30712469937793740445626608)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-8071765621019969664522823672),(-8071765621019969650360976827)⟩,⟨(-7610695535348708103208519054),(-7610695535348708088907357829)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-25420674455364671409150191816),(-25420674455364671365630016046)⟩,⟨(-18815271169689245407042534245),(-18815271169689245363543800077)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-44182729533363612467734581717),(-44182729533363612392821013664)⟩,⟨(-19042662404429593739771332862),(-19042662404429593666020605399)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-59673109126877188438293867020),(-59673109126877188331276408471)⟩,⟨(-5204971060984086104662212144),(-5204971060984086000685799704)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-63889875519585102449429931365),(-63889875519585102312223885136)⟩,⟨19104929277938575304823560428,19104929277938575437350073716⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-51488388636532371216966313917),(-51488388636532371049557548066)⟩,⟨43750787537687142915074019464,43750787537687143078785656888⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-25570119777797148650544029928),(-25570119777797148456849429222)⟩,⟨57177875405222754801768579893,57177875405222754994088789508⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨2962520822339406232516528028,2962520822339406466089526905⟩,⟨53779328214891153184841718976,53779328214891153418713996735⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨22796778807510269922865878867,22796778807510270331723333365⟩,⟨37332545320026016470433760126,37332545320026016880105987614⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨29357645723652456726979834556,29357645723652458181394280310⟩,⟨17277302151896866672327645610,17277302151896868127159985944⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨25617472265990950391592775804,25617472265990956973773356330⟩,⟨1743022222274861575147219964,1743022222274868157311033477⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨17643731676608491289560068353,17643731676608511134590930870⟩,⟨(-6341075018053993215513606919),(-6341075018053973370549614142)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨10131124922668466532210291438,10131124922668504472650106524⟩,⟨(-8323656236139057584240880488),(-8323656236139019643792700216)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨4962710165225679603927690939,4962710165225726819771893977⟩,⟨(-6939339224977674024521631385),(-6939339224977626808619364012)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨2045503150714077509020327412,2045503150714115440237820951⟩,⟨(-4305377513916600261544376574),(-4305377513916562330270355938)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨529472286894713300494135069,529472286894728397628724057⟩,⟨(-1433009164551281056318102481),(-1433009164551265959162590696)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-33138870313513334878130759050),(-33138870313512351773817017497)⟩,⟨22275637188180833016535933046,22275637188181816118621217141⟩⟩
lemma checked : cachedMomentRuleBox density0 hk7_1_5 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 7 5) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk7_1_5 (tableDensity false) (fullFactor true 7 5) density0_contains hk7_1_5_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-31320315995287418707029390559),(-31320315995287418678988008140)⟩,⟨29884733131464193175421830127,29884733131464193202826540612⟩⟩
lemma atomChecked : tableAtomBox false ha7_1_5 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 7 5) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha7_1_5 7 5 ha7_1_5_contains
 def realAnswer : RBox := ⟨(-64459186308800753585260149609),(-64459186308799770452705025637)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 7 5) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm7_0_1_5
namespace hm7_1_1_5
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk7_1_5 j i k))
noncomputable def s0_0 : CBox := ⟨⟨86639732,86639820⟩,⟨(-52366372),(-52366285)⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨209291908,209292148⟩,⟨(-54850329),(-54850090)⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨175429302,175429684⟩,⟨59420899,59421279⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨34431479,34431989⟩,⟨92677337,92677849⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-28280915),(-28280306)⟩,⟨25234505,25235110⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-8397232),(-8396642)⟩,⟨(-8195818),(-8195230)⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨2790301,2790939⟩,⟨(-1811490),(-1810847)⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨84655,85418⟩,⟨972979,973740⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-268387),(-267529)⟩,⟨(-189626),(-188774)⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨132046,132964⟩,⟨(-18993),(-18074)⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-41724),(-40884)⟩,⟨53150,53984⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-12132),(-11422)⟩,⟨(-39815),(-39108)⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨28031,28570⟩,⟨483,1022⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨1061,1431⟩,⟨19731,20100⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-10185),(-9972)⟩,⟨7094,7297⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-4281),(-4202)⟩,⟨429,508⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-38422106221584),(-38422106221532)⟩,⟨(-5868752674438546),(-5868752674438498)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨81451729725558,81451729725674⟩,⟨(-12632046927061218),(-12632046927061098)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨429578012078903,429578012079076⟩,⟨(-10907731803852484),(-10907731803852312)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨619867957604421,619867957604638⟩,⟨(-5793934815647878),(-5793934815647666)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨495019255076565,495019255076805⟩,⟨(-2102393941745167),(-2102393941744923)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨257353053894534,257353053894791⟩,⟨(-539021287043239),(-539021287042984)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨92406444705116,92406444705384⟩,⟨(-92724359187093),(-92724359186822)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨23085984468335,23085984468627⟩,⟨(-7143812827741),(-7143812827451)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨3797310113822,3797310114133⟩,⟨1355414962292,1355414962603⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨281707454053,281707454431⟩,⟨595576825872,595576826251⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-50106920404),(-50106919977)⟩,⟨102832297990,102832298419⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-22292329074),(-22292328614)⟩,⟨3831082792,3831083255⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-3899850149),(-3899849731)⟩,⟨(-3629591695),(-3629591275)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-33225241),(-33224907)⟩,⟨(-1507765047),(-1507764718)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨259474121,259474344⟩,⟨(-406782885),(-406782662)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨90275882,90275970⟩,⟨(-74534943),(-74534850)⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨2847925066487354857215,2847925066487354874353⟩,⟨3288604382708648318111,3288604382708648335182⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨7575794597942694697736,7575794597942694740905⟩,⟨7460380797775161991622,7460380797775162034598⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨9501466689205845245524,9501466689205845295805⟩,⟨6881480078182817515724,6881480078182817565762⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨8060182983059445761114,8060182983059445802239⟩,⟨3560614827873101864180,3560614827873101905134⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨4867658479248194748105,4867658479248194773631⟩,⟨763236460637897427797,763236460637897453261⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨2125627934982975649995,2125627934982975662244⟩,⟨(-311297187911158772193),(-311297187911158759958)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨680141883289890776689,680141883289890781402⟩,⟨(-347535530933024842560),(-347535530933024837844)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨161951726593366098970,161951726593366100566⟩,⟨(-166783362940139617159),(-166783362940139615561)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨29071426314033379029,29071426314033379705⟩,⟨(-56525422881124502026),(-56525422881124501353)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨3901512222903872777,3901512222903873307⟩,⟨(-15849405031079035828),(-15849405031079035297)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨353933285535780039,353933285535780626⟩,⟨(-4090954334759993313),(-4090954334759992726)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨7553484026409589,7553484026410200⟩,⟨(-1056204225220603391),(-1056204225220602781)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-4698027655770159),(-4698027655769622)⟩,⟨(-290184386432925884),(-290184386432925342)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-932671012410605),(-932671012410203)⟩,⟨(-88042464264351995),(-88042464264351595)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨73355143749373,73355143749617⟩,⟨(-28740032985212944),(-28740032985212702)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨80250641537694,80250641537783⟩,⟨(-6985040716327280),(-6985040716327194)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨10747712780675798299952179,10747712780675850432638487⟩,⟨(-5995396784056032813362177),(-5995396784055980681281393)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨26557145859802783967867883,26557145859802889704461080⟩,⟨(-18264140621687579403058438),(-18264140621687473668132721)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨28881215994873234572478350,28881215994873329316542592⟩,⟨(-29064224809214972268423264),(-29064224809214877526138686)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨18639097229296959010859447,18639097229297006991256637⟩,⟨(-33596838812614539246726871),(-33596838812614491267374897)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨4348555701182231536594101,4348555701182245221391893⟩,⟨(-29025132626914017456327054),(-29025132626914003771621828)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-5196380592300892262552085),(-5196380592300890100753714)⟩,⟨(-18447074056342830814247426),(-18447074056342828651958800)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-7413489166436987627962140),(-7413489166436987414544080)⟩,⟨(-8131705592413733500274166),(-8131705592413733286344802)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-5315626762314334475570961),(-5315626762314334440030353)⟩,⟨(-1933733469914057609884316),(-1933733469914057574203531)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-2628562228294388072893776),(-2628562228294388060439239)⟩,⟨352475842999938815665894,352475842999938828102490⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-960456100994691897252161),(-960456100994691891346169)⟩,⟨655926298298305214550420,655926298298305220416888⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-252217730969251955475152),(-252217730969251952587475)⟩,⟨422665567859409194402675,422665567859409197271410⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-31722038689460112230523),(-31722038689460110822802)⟩,⟨205122190131771934427225,205122190131771935831340⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨14833358842867700020262,14833358842867700696092⟩,⟨88122832442585863389921,88122832442585864065832⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨15772900387360302745808,15772900387360303065935⟩,⟨36104259788126113474935,36104259788126113795606⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨9157042837811664118568,9157042837811664260775⟩,⟨14082863230964703370510,14082863230964703513080⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨2870961462812790847568,2870961462812790887941⟩,⟨3707240803193727918485,3707240803193727958975⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-151239965545769834321431247),(-151239965545752811802969824)⟩,⟨(-827120803496156191468331022),(-827120803496139168878732448)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-648262267389631669409607519),(-648262267389567147535871616)⟩,⟨(-2276344574517200690236234873),(-2276344574517136168180262867)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-1546146272159186044165399837),(-1546146272159027076648672268)⟩,⟨(-3090375068332225301032825998),(-3090375068332066333311455187)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-2626035782109814658540281059),(-2626035782109473271610056187)⟩,⟨(-2922366269111213961515942024),(-2922366269110872574462626678)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-3334089782830977627647180540),(-3334089782830367328315540379)⟩,⟨(-1795268687411436307405714679),(-1795268687410826008099182890)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-3210585222951394398944872331),(-3210585222950575989571173979)⟩,⟨(-249527986092814609161331467),(-249527986091996199952980152)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-2300371173109624289436729085),(-2300371173108797303513649712)⟩,⟨962427417561927669660141846,962427417562754655380390721⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-1116187935640292175029215968),(-1116187935639419886844415703)⟩,⟨1412013246375222808081158201,1412013246376095096194083402⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-196983265047701697282855934),(-196983265047107477025810228)⟩,⟨1210901175519111292884460929,1210901175519705513159087572⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨251611318828606378539226645,251611318828860549163332812⟩,⟨753336194176840416604846194,753336194177094587274580538⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨338687074033165440235445271,338687074033262527704005079⟩,⟨354310968931857622050680086,354310968931954709545887741⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨264148311377016310688883746,264148311377053827965391125⟩,⟨118535030156166877408837205,118535030156204394691172862⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨163732431752456993602868559,163732431752468594727496131⟩,⟨15676239657104783947117067,15676239657116385070063287⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨88233330260860011137419178,88233330260863327225164463⟩,⟨(-14743363288685873842513650),(-14743363288682557757702779)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨41252539033362547121938106,41252539033363495190024594⟩,⟨(-15096085756072035801162358),(-15096085756071087735142620)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨11872772395437497326190281,11872772395437705074284739⟩,⟨(-5700331494588758005722128),(-5700331494588550258328965)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-250462528197261729842143319),(-250462528197261726342360488)⟩,⟨(-214648478144343122988497008),(-214648478144343119504754852)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-853720248737863676800204547),(-853720248737863666207387924)⟩,⟨(-348467851424110829850910530),(-348467851424110819554383533)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-1356408554032396131113565688),(-1356408554032396113816882058)⟩,⟨526971136532670321747023482,526971136532670337882896316⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-762399049428652569903092827),(-762399049428652546599102925)⟩,⟨3070552455443109128659744438,3070552455443109149433209334⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨2126717096275674578007877162,2126717096275674610139381664⟩,⟨6996788133090996543463722976,6996788133090996571739821664⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨7496837756822285716599348847,7496837756822285765384141486⟩,⟨10423707021075720029991010120,10423707021075720075678181377⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨13811269876798888809307873155,13811269876798888881458151312⟩,⟨10848843626139655179650548623,10848843626139655250785999083⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨18419079804786509064962722611,18419079804786509178570369441⟩,⟨7314724257930021081748534564,7314724257930021196058429067⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨19256093894766098122729092699,19256093894766098392406821374⟩,⟨1394268732051719339796819004,1394268732051719610968281963⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨16267474114026053661025138994,16267474114026054798715382717⟩,⟨(-4100558413567757413266803072),(-4100558413567756274449511933)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨11215393228843543343866517580,11215393228843548679915229217⟩,⟨(-7191291682377856536507132009),(-7191291682377851200210939812)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨6239972711017318909240634104,6239972711017335084704778555⟩,⟨(-7639647584625729995472498205),(-7639647584625713820137069012)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨2644648341761456204641915466,2644648341761487177538849477⟩,⟨(-6371033880205988061699486319),(-6371033880205957089015983804)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨672624291002845360250769837,672624291002883936687002355⟩,⟨(-4456495254998788871922301271),(-4456495254998750295666586056)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-59963893270169417637155067),(-59963893270138411484500818)⟩,⟨(-2543798204341747089470132393),(-2543798204341716083428538719)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-92663889573452880779880375),(-92663889573440536722464376)⟩,⟨(-817339328639758507068195928),(-817339328639746163044619187)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨13478597137507837561515719309,13478597137508645129317726557⟩,⟨63428799644105128438390696,63428799644912694762321957⟩⟩
lemma checked : cachedMomentRuleBox density1 hk7_1_5 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 7 5) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk7_1_5 (tableDensity true) (fullFactor true 7 5) density1_contains hk7_1_5_contains
noncomputable def atomAnswer : CBox := ⟨⟨40957336301529701349445856799,40957336301529701386115356884⟩,⟨(-39080035633453175726773168493),(-39080035633453175690936239397)⟩⟩
lemma atomChecked : tableAtomBox true ha7_1_5 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 7 5) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha7_1_5 7 5 ha7_1_5_contains
 def realAnswer : RBox := ⟨54435933439037538910861576108,54435933439038346515533083441⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 7 5) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm7_1_1_5
namespace hm7_0_1_6
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk7_1_6 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-819846229),(-819845642)⟩,⟨188803627,188804213⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-1794487201),(-1794485415)⟩,⟨(-82698329),(-82696541)⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-1274783510),(-1274780492)⟩,⟨(-872096128),(-872093113)⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-100068681),(-100064337)⟩,⟨(-834015766),(-834011419)⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨289350299,289356016⟩,⟨(-167200992),(-167195277)⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨61544762,61550972⟩,⟨89136300,89142490⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-29621359),(-29614911)⟩,⟨11497693,11504220⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨1297466,1303591⟩,⟨(-9292126),(-9286004)⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨2025447,2032816⟩,⟨2310168,2317474⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-1209446),(-1201212)⟩,⟨(-107397),(-99167)⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨440463,448023⟩,⟨(-393077),(-385524)⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨43351,49737⟩,⟨345549,351896⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-239671),(-234864)⟩,⟨(-38973),(-34165)⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨6219,9488⟩,⟨(-170894),(-167628)⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨90775,92588⟩,⟨(-52999),(-51246)⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨36086,36690⟩,⟨(-557),28⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-13397266892141274),(-13397266892141097)⟩,⟨42667703026576511,42667703026576689⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-31099496653941145),(-31099496653940649)⟩,⟨92747477051288717,92747477051289216⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-31522643133862750),(-31522643133861990)⟩,⟨81124468104678396,81124468104679156⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-21447343220566346),(-21447343220565267)⟩,⟨43104451063228731,43104451063229807⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-10698727007197147),(-10698727007195643)⟩,⟨15017824778239856,15017824778241360⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-3974561315062326),(-3974561315060347)⟩,⟨3365810094412927,3365810094414906⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-1085932961726422),(-1085932961723929)⟩,⟨379481070205767,379481070208263⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-208958834423498),(-208958834420469)⟩,⟨(-35418155296913),(-35418155293886)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-23965121223174),(-23965121219698)⟩,⟨(-25572571678019),(-25572571674538)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨179903869650,179903873149⟩,⟨(-5630250819226),(-5630250815724)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨757037665155,757037668297⟩,⟨(-580080691378),(-580080688234)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨176072042359,176072045120⟩,⟨49118226476,49118229245⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨16659281407,16659283959⟩,⟨38310029609,38310032170⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-4020467475),(-4020465351)⟩,⟨10838923844,10838925976⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-2897218633),(-2897217191)⟩,⟨2218017357,2218018795⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-824943537),(-824943001)⟩,⟨306500046,306500581⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-3756180602921921819080),(-3756180602921921777730)⟩,⟨(-18392271346461496110125),(-18392271346461496067139)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-13113380218141741618859),(-13113380218141741515659)⟩,⟨(-44072661796655032943559),(-44072661796655032836790)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-22674813643665297539999),(-22674813643665297417712)⟩,⟨(-45898436059927274785258),(-45898436059927274660049)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-25319325192387443029523),(-25319325192387442919684)⟩,⟨(-30167225596507062496778),(-30167225596507062385910)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-19264150597724911762644),(-19264150597724911681959)⟩,⟨(-12666838382613251011551),(-12666838382613250931158)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-10368113435143916816543),(-10368113435143916769140)⟩,⟨(-2772864936064610347011),(-2772864936064610300161)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-4091582371785098382335),(-4091582371785098359570)⟩,⟨268531102342527418249,268531102342527440673⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-1235354311673401209146),(-1235354311673401199701)⟩,⟨488707617473369305875,488707617473369315213⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-301788191186257663372),(-301788191186257659400)⟩,⟨230246373133834622063,230246373133834626018⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-64310768332028716133),(-64310768332028713897)⟩,⟨76872377352673761274,76872377352673763506⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-13185347241338361387),(-13185347241338359370)⟩,⟨22161956935006029473,22161956935006031488⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-2913471576030093042),(-2913471576030091191)⟩,⟨6179359893895769492,6179359893895771339⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-762394500535637881),(-762394500535636239)⟩,⟨1800929528377770550,1800929528377772195⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-241587670481974163),(-241587670481972925)⟩,⟨571699262793975562,571699262793976802⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-85087072222716866),(-85087072222716123)⟩,⟨192123371003837970,192123371003838713⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-21780559613320280),(-21780559613320034)⟩,⟨47304973611359368,47304973611359617⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-29697769691539817992250501),(-29697769691539760746811714)⟩,⟨(-3085281924737007267347479),(-3085281924736950025615567)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-79611062572551068408149590),(-79611062572550942236360824)⟩,⟨(-321646651585275578628455),(-321646651585149415175037)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-102850808485708140910220599),(-102850808485708032754736740)⟩,⟨19842132070721416187212079,19842132070721524335927915⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-91610431823387142134983222),(-91610431823387091438602627)⟩,⟨46795381102201776734820471,46795381102201827430691229⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-55690175553989624639373891),(-55690175553989611440462677)⟩,⟨60927042246229686862223032,60927042246229700066761733⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-17652413181476663437204554),(-17652413181476661526226683)⟩,⟨53427214041500675951252749,53427214041500677869726025⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨4977472437325533701600287,4977472437325533993244772⟩,⟨33081623632722229679877798,33081623632722229974396447⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨10666170391147664483918913,10666170391147664553340188⟩,⟨14192656773985072162359055,14192656773985072231667841⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨7831283417799913599309430,7831283417799913629651067⟩,⟨3562550030686548213228823,3562550030686548242760343⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨3894882695414345462577844,3894882695414345477754212⟩,⟨(-213601135261382326306531),(-213601135261382311556961)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨1491788666611410019099435,1491788666611410026465389⟩,⟨(-813666364392788956628293),(-813666364392788949325550)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨459811885758781411686857,459811885758781415095574⟩,⟨(-568471794275968453686696),(-568471794275968450256971)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨110371537401144043524011,110371537401144045076576⟩,⟨(-298350879437052509839515),(-298350879437052508261869)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨14499593157511507138489,14499593157511507840025⟩,⟨(-139999961207273369373554),(-139999961207273368656442)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-4025192054173088147956),(-4025192054173087845030)⟩,⟨(-59878097660910498682961),(-59878097660910498373613)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-2552413644108286613566),(-2552413644108286528724)⟩,⟨(-16544701519290543486901),(-16544701519290543400448)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-1689906470094844817858814763),(-1689906470094828600263341864)⟩,⟨524557188193089368081457590,524557188193105585884791060⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-4490999437571138565099644113),(-4490999437571078123831576439)⟩,⟨1945102764348487847226927200,1945102764348548288985867211⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-5649682756543831867205347300),(-5649682756543687220341681905)⟩,⟨4049838249786016522032094558,4049838249786161169348327207⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-4588124047807810356816855734),(-4588124047807511266885181658)⟩,⟨6203964852282190610215160159,6203964852282489700226459709⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-1744281100619391227090463685),(-1744281100618882476702196319)⟩,⟨7162044104829525538345293309,7162044104830034288291321088⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨1415267358877537541737526212,1415267358878173206732207578⟩,⟨6141112837304163382166396346,6141112837304799046328061310⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨3316000357566115566223533630,3316000357566928319985671931⟩,⟨3628814903109620000887408555,3628814903110432754112069975⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨3401424852334106662652422099,3401424852334928790402776925⟩,⟨1000786335136395433755202574,1000786335137217561449291618⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨2309747986433300781865273717,2309747986433810570861905165⟩,⟨(-639056215701386753421188519),(-639056215700876964235972375)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨1052865919535341411604814670,1052865919535560639083789388⟩,⟨(-1123934577808122772112437946),(-1123934577807903544434879402)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨221141437404774613726045398,221141437404879520917089726⟩,⟨(-929229575595015963255495081),(-929229575594911056006958549)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-134416219051527422362138635),(-134416219051490779348317814)⟩,⟨(-563244785373975289444685851),(-563244785373938646440709566)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-202655304266393605531765163),(-202655304266383243146471852)⟩,⟨(-278245710669363098584380789),(-278245710669352736225690041)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-158689366237813143423177650),(-158689366237810430845368589)⟩,⟨(-116923359317495833065275898),(-116923359317493120510192592)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-91880462548275138647581996),(-91880462548274272196920515)⟩,⟨(-41800542806828904617304818),(-41800542806828038177826976)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-29367931527433227032469739),(-29367931527433007600229571)⟩,⟨(-9793725256209691373896085),(-9793725256209471944656872)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-4327710777819073592259337861),(-4327710777819073583483152333)⟩,⟨5101397428934924331968773069,5101397428934924340718127939⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-10517412894297724108038716133),(-10517412894297724081288707037)⟩,⟨15962658028317599200514183014,15962658028317599227446637873⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-9969050475696467131010175018),(-9969050475696467085463126871)⟩,⟨27462634003250777858151129099,27462634003250777904662330488⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-814033844368921688196542830),(-814033844368921623594811288)⟩,⟨36614929732747865285992143864,36614929732747865352749173418⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨14608897017473485862399189617,14608897017473485945986655082⟩,⟨38452111223697415148340617414,38452111223697415234951890350⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨29799857893897022120330575311,29799857893897022226191330798⟩,⟨29762286460668053196249795529,29762286460668053304153666169⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨37395214503333458428950810862,37395214503333458553723174173⟩,⟨12745697128323113074387185491,12745697128323113199754821872⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨33980552201454347169284682207,33980552201454347320354521895⟩,⟨(-5421655537436763822266511970),(-5421655537436763671594289686)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨22321200677182245193281611459,22321200677182245449324298978⟩,⟨(-17429297677590069482355892699),(-17429297677590069226937898062)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨8819833580754929362740604814,8819833580754930386854639735⟩,⟨(-20535250263907953419233079955),(-20535250263907952395348690238)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-1182007851738529933129159182),(-1182007851738525445564375320)⟩,⟨(-17021681864981496886390929622),(-17021681864981492398809228389)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-5958361672494058145842109346),(-5958361672494045097714349806)⟩,⟨(-11108256319083176450106968127),(-11108256319083163401958358944)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-6653276918293187740412840681),(-6653276918293163792836725707)⟩,⟨(-5918948906177205089457938899),(-5918948906177181141919835866)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-5238887919468410559570934513),(-5238887919468381621846483561)⟩,⟨(-2582371859407009715570406842),(-2582371859406980777909079252)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-3157504290010633320721105955),(-3157504290010605536444817277)⟩,⟨(-893922642058185614928575448),(-893922642058157830694246198)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-1037000612538949070170466686),(-1037000612538937144946219668)⟩,⟨(-192804837605632728547484318),(-192804837605620803336639873)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨15109830044773342710098892791,15109830044774058843348259565⟩,⟨18696279187305396981913722151,18696279187306113116378946980⟩⟩
lemma checked : cachedMomentRuleBox density0 hk7_1_6 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 7 6) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk7_1_6 (tableDensity false) (fullFactor true 7 6) density0_contains hk7_1_6_contains
noncomputable def atomAnswer : CBox := ⟨⟨19523665010221977673440687137,19523665010221977692276297177⟩,⟨18005225816604129401583587255,18005225816604129420784525110⟩⟩
lemma atomChecked : tableAtomBox false ha7_1_6 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 7 6) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha7_1_6 7 6 ha7_1_6_contains
 def realAnswer : RBox := ⟨34633495054995320383439579928,34633495054996036535724556742⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 7 6) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm7_0_1_6
namespace hm7_1_1_6
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk7_1_6 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-143226573),(-143226459)⟩,⟨13505289,13505406⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-303053421),(-303053098)⟩,⟨(-57035738),(-57035416)⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-193463184),(-193462639)⟩,⟨(-181841540),(-181840997)⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨7244427,7245195⟩,⟨(-142690029),(-142689260)⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨51960340,51961325⟩,⟨(-18969871),(-18968888)⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨7575376,7576405⟩,⟨15565973,15567004⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-4784669),(-4783630)⟩,⟨1324028,1325076⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨256884,257863⟩,⟨(-1451483),(-1450510)⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨335544,336729⟩,⟨368645,369821⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-205632),(-204273)⟩,⟨(-7434),(-6075)⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨72934,74222⟩,⟨(-74271),(-72987)⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨12136,13246⟩,⟨61634,62737⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-43888),(-43050)⟩,⟨(-3984),(-3142)⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-1307),(-739)⟩,⟨(-30975),(-30406)⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨15457,15773⟩,⟨(-11038),(-10733)⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨6459,6574⟩,⟨(-759),(-651)⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-5003762789939564),(-5003762789939506)⟩,⟨4860381407317474,4860381407317530⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-10887680241209364),(-10887680241209230)⟩,⟨10417401030255178,10417401030255315⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-9672981243273937),(-9672981243273752)⟩,⟨8854441644175992,8854441644176185⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-5454231573583078),(-5454231573582852)⟩,⟨4502086574662188,4502086574662412⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-2212542612781719),(-2212542612781462)⟩,⟨1469644917651082,1469644917651338⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-687865703391437),(-687865703391139)⟩,⟨288793244596908,288793244597206⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-165691096090756),(-165691096090390)⟩,⟨14696128658821,14696128659186⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-29195316231984),(-29195316231532)⟩,⟨(-11199155578090),(-11199155577638)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-2982085670712),(-2982085670176)⟩,⟨(-4397380256371),(-4397380255835)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨136419637289,136419637849⟩,⟨(-872914359598),(-872914359036)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨132454200304,132454200831⟩,⟨(-82152483794),(-82152483265)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨29246526400,29246526889⟩,⟨10995015400,10995015890⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨2340909447,2340909919⟩,⟨7062834563,7062835035⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-935327544),(-935327137)⟩,⟨1906380566,1906380970⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-585396169),(-585395884)⟩,⟨351738435,351738721⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-161503546),(-161503429)⟩,⟨38938521,38938636⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨1453787882584619780349,1453787882584619793878⟩,⟨(-3980902737742091115899),(-3980902737742091102294)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨2739436952334371588232,2739436952334371622292⟩,⟨(-10027050311465564867713),(-10027050311465564833478)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨1241736091030362566121,1241736091030362605677⟩,⟨(-11481989086895351869652),(-11481989086895351829955)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-1005292234632238798192),(-1005292234632238764485)⟩,⟨(-8704873861846588707220),(-8704873861846588673461)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-1890974312218978383893),(-1890974312218978361052)⟩,⟨(-4589739209064529686675),(-4589739209064529663839)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-1433384435418219167053),(-1433384435418219154938)⟩,⟨(-1666568454692651395967),(-1666568454692651383871)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-693230402049513345979),(-693230402049513340783)⟩,⟨(-389804829702881410433),(-389804829702881405246)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-243483569085615869857),(-243483569085615867854)⟩,⟨(-39587339686087421237),(-39587339686087419240)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-67908937149563059458),(-67908937149563058542)⟩,⟨10902544066568589027,10902544066568589940⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-16457961469767743185),(-16457961469767742453)⟩,⟨7310228560924646175,7310228560924646907⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-3814880122434543035),(-3814880122434542174)⟩,⟨2596928114862068020,2596928114862068880⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-923374411550561242),(-923374411550560326)⟩,⟨777515619369277509,777515619369278426⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-247671181111663100),(-247671181111662288)⟩,⟨227740552973421552,227740552973422363⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-75225701108847796),(-75225701108847201)⟩,⟨70697318516280503,70697318516281096⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-24782160964243028),(-24782160964242683)⟩,⟨23219446139411500,23219446139411847⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-6064002955372836),(-6064002955372713)⟩,⟨5648441850339822,5648441850339941⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-7342135038391834347646981),(-7342135038391786266985149)⟩,⟨(-6761214764015847660688090),(-6761214764015799579639097)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-20915197360527630715784704),(-20915197360527524821800474)⟩,⟨(-15817283917356895869009743),(-15817283917356789974152863)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-30127801128845347267628425),(-30127801128845256637394235)⟩,⟨(-14747088574787786317760239),(-14747088574787695686817937)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-31281609578733252253733169),(-31281609578733209888952506)⟩,⟨(-5382269816567851162647637),(-5382269816567808797811258)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-24048065787402951358444361),(-24048065787402940390780541)⟩,⟨4853517326891918034624845,4853517326891929001714493⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-13064832285467010243368907),(-13064832285467008695275289)⟩,⟨9656743093745299955052190,9656743093745301502392488⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-4153345636009296239131664),(-4153345636009296031368634)⟩,⟨8518561779456144361941244,8518561779456144569420499⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨229906046183192582200208,229906046183192616065213⟩,⟨4950562050351828526606450,4950562050351828560486397⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨1229990042386994794569400,1229990042386994805725603⟩,⟨2020475022922149480958829,2020475022922149492194806⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨905928322885438049071083,905928322885438054368437⟩,⟨542618493962785661443656,542618493962785666781495⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨452845383144950726557473,452845383144950729154401⟩,⟨40030097770249936365112,40030097770249938967482⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨185282713895714008120561,185282713895714009337027⟩,⟨(-59960544404622500852763),(-59960544404622499638488)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨67779811135830112316323,67779811135830112878699⟩,⟨(-51274984191731140156209),(-51274984191731139596214)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨23414958210121588950532,23414958210121589208685⟩,⟨(-29774024257419224944187),(-29774024257419224687454)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨7709455090009821822485,7709455090009821935279⟩,⟨(-14329047734772123646841),(-14329047734772123534620)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨1804839636418172736165,1804839636418172767954⟩,⟨(-4186969101801466699049),(-4186969101801466667400)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-545674841333336113607217774),(-545674841333322786610078018)⟩,⟨200551604221896090761446691,200551604221909417718528014⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-1476679170439949604501953595),(-1476679170439899931520823658)⟩,⟨715700424064826824665259171,715700424064876497548655390⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-1928193611522743454625756182),(-1928193611522624559301684669)⟩,⟨1443806195056249954522107751,1443806195056368849752204148⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-1676558371763141275386918984),(-1676558371762895388790038590)⟩,⟨2193202736955396866056236745,2193202736955642752631503088⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-790552463960018427979244632),(-790552463959600120597537597)⟩,⟨2569118263976458403128059179,2569118263976876710597088889⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨297692512744105123309100495,297692512744627787190732017⟩,⟨2294694386331412012382863612,2294694386331934676440291667⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨1048765057184333962570995799,1048765057185002094073855847⟩,⟨1483317034970300010248200176,1483317034970968141875185676⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨1206408831495771436468283086,1206408831496446956114375820⟩,⟨562213681208178204870322652,562213681208853724534024556⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨918006183220912006335560954,918006183221330564207228072⟩,⟨(-78889867452698454225946224),(-78889867452279896393133929)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨505593697557882014675755948,505593697558061813933599747⟩,⟨(-333794571411679983556714556),(-333794571411500184339904294)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨192869527026967505052094836,192869527027053435467922520⟩,⟨(-326826118639118699173696276),(-326826118639032768770077369)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨30461674538259298941252870,30461674538289273305989710⟩,⟨(-225189949970492693474695200),(-225189949970462719108738453)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-26309257438724540770572254),(-26309257438716075252629912)⟩,⟨(-127951566500688738493377996),(-127951566500680272970773781)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-32640325797055283503205174),(-32640325797053069989353649)⟩,⟨(-63857912434620389482132660),(-63857912434618175964291470)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-21841175154165206247166683),(-21841175154164499801449640)⟩,⟨(-27920077316183595068426373),(-27920077316182888620764108)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-7375575060192837845810788),(-7375575060192659009973964)⟩,⟨(-7701715947133550111582063),(-7701715947133371275230835)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-121332714820583957534975074),(-121332714820583955452180723)⟩,⟨157613130112108184127721972,157613130112108186259037480⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-182095545738605272612920536),(-182095545738605266462032049)⟩,⟨526708501357370898452242239,526708501357370904898573262⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨368093815559034814337520602,368093815559034823952002024⟩,⟨803165338159352203076750685,803165338159352213577434552⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨1904439719381817570300432486,1904439719381817582634603041⟩,⟨342410178265723622493778625,342410178265723636592793887⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨4211016367028575690703709449,4211016367028575708083355952⟩,⟨(-1623854455925071959195372453),(-1623854455925071939337085296)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨6096621067254429675861459179,6096621067254429705671809803⟩,⟨(-5192118132708366126464222099),(-5192118132708366094972403644)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨6015470919542486277214877047,6015470919542486323323931426⟩,⟨(-9308977960410463061496300071),(-9308977960410463015024294707)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨3437648826448626447037607481,3437648826448626520120931480⟩,⟨(-12191507617837630336922351606),(-12191507617837630264524867399)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-529992286442074761532332278),(-529992286442074594482435414)⟩,⟨(-12492444153237620104724894681),(-12492444153237619938791579799)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-4012814190052858809176955143),(-4012814190052858005562330898)⟩,⟨(-10251993737026096180731335045),(-10251993737026095377729834588)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-5753772115316387672660379778),(-5753772115316384034021509267)⟩,⟨(-6730318701449220149734191688),(-6730318701449216511162225654)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-5696717698747208079573713390),(-5696717698747197444772796737)⟩,⟨(-3396549896152813493377109328),(-3396549896152802858431621416)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-4553486900576876000117734672),(-4553486900576856451620785089)⟩,⟨(-1102308474137773211726030931),(-1102308474137753663054182798)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-3085366850340703718268188147),(-3085366850340680076599783597)⟩,⟨40279350480246269958499912,40279350480269911763438440⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-1719869229742791362963917841),(-1719869229742768650733366613)⟩,⟨332930768674326442699100533,332930768674349154994854183⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-545343910779591795514207047),(-545343910779582044668488713)⟩,⟨158582691197174302314554429,158582691197184053177489001⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-1100226047030609215552000529),(-1100226047030020944852993343)⟩,⟨(-8278372726145814475154138715),(-8278372726145226203514082220)⟩⟩
lemma checked : cachedMomentRuleBox density1 hk7_1_6 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 7 6) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk7_1_6 (tableDensity true) (fullFactor true 7 6) density1_contains hk7_1_6_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-25530946551828740059130542462),(-25530946551828740034499360103)⟩,⟨(-23545295298636169242564378990),(-23545295298636169217455460257)⟩⟩
lemma atomChecked : tableAtomBox true ha7_1_6 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 7 6) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha7_1_6 7 6 ha7_1_6_contains
 def realAnswer : RBox := ⟨(-26631172598859349274782542991),(-26631172598858760979252353446)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 7 6) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm7_1_1_6
namespace hm7_0_1_7
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk7_1_7 j i k))
noncomputable def s0_0 : CBox := ⟨⟨999305963,999306506⟩,⟨226926449,226926988⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨1937984589,1937986282⟩,⟨1029673385,1029675075⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨980530314,980533380⟩,⟨1624711612,1624714671⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-294455516),(-294450717)⟩,⟨997871430,997876236⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-413619600),(-413612680)⟩,⟨60651495,60658418⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-35202971),(-35194740)⟩,⟨(-132409889),(-132401654)⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨40551497,40560868⟩,⟨(-2637306),(-2627872)⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-4747792),(-4739041)⟩,⟨11155809,11164557⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-1937212),(-1928823)⟩,⟨(-3523335),(-3515044)⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨1531516,1541689⟩,⟨399644,409810⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-651640),(-641815)⟩,⟨429297,439150⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-24689),(-16166)⟩,⟨(-468460),(-459964)⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨306932,313402⟩,⟨62261,68736⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-19044),(-14667)⟩,⟨220679,225057⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-122767),(-120362)⟩,⟨66140,68467⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-48307),(-47515)⟩,⟨(-141),621⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨40824752465857938,40824752465858145⟩,⟨(-20230434291712618),(-20230434291712412)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨90226009020432202,90226009020432812⟩,⟨(-43168383505833083),(-43168383505832470)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨82193382212939128,82193382212940134⟩,⟨(-35725794258530846),(-35725794258529837)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨47307051962971970,47307051962973392⟩,⟨(-16466694903373052),(-16466694903371630)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨19056361126452850,19056361126454677⟩,⟨(-3834500027028544),(-3834500027026720)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨5574467419471645,5574467419473759⟩,⟨140640687423816,140640687425929⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨1171528389576288,1171528389578525⟩,⟨444305749497067,444305749499305⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨157889705622494,157889705625096⟩,⟨174145178602052,174145178604646⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨4773594747375,4773594750970⟩,⟨39296364614834,39296364618429⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-3808338627322),(-3808338623082)⟩,⟨5236128488311,5236128492547⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-1109105486734),(-1109105482339)⟩,⟨101826452949,101826457340⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-150483267508),(-150483263230)⟩,⟨(-155526050145),(-155526045868)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨4547165110,4547168533⟩,⟨(-49798576787),(-49798573354)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨10326617783,10326620204⟩,⟨(-9380777878),(-9380775447)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨4345838946,4345840410⟩,⟨(-842297579),(-842296121)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨1065322964,1065323474⟩,⟨104583270,104583780⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-11903516444550646641416),(-11903516444550646598936)⟩,⟨10198365244911535798535,10198365244911535840832⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-26838357323338203923273),(-26838357323338203814812)⟩,⟨27646706083136578741609,27646706083136578850089⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-24133957264796978011578),(-24133957264796977876902)⟩,⟨35825810742588808010557,35825810742588808146282⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-11243577800567551064445),(-11243577800567550943619)⟩,⟨31631841964335071101409,31631841964335071224129⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-700654279738734502526),(-700654279738734418469)⟩,⟨19898081535802548567378,19898081535802548653235⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨2815272281036854612215,2815272281036854659534⟩,⟨8982837974987908982203,8982837974987909030329⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨2220325207526371975790,2220325207526371997616⟩,⟨2909702125352393431108,2909702125352393453099⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨1007833143735405013057,1007833143735405021575⟩,⟨666787592497103394248,666787592497103402777⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨337905801953241996666,337905801953241999973⟩,⟨98927163057587073067,98927163057587076379⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨94718671781665837006,94718671781665838726⟩,⟨3530326983404549374,3530326983404551088⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨24572896753938487284,24572896753938488858⟩,⟨(-3647079074964446471),(-3647079074964444901)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨6456139991353924214,6456139991353925753⟩,⟨(-1762561195431763903),(-1762561195431762362)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨1840466944034050628,1840466944034052095⟩,⟨(-624095403321710967),(-624095403321709506)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨587208840275039598,587208840275040784⟩,⟨(-210370714935738048),(-210370714935736863)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨200743515929559653,200743515929560409⟩,⟨(-70673560235888114),(-70673560235887362)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨50100307344965176,50100307344965436⟩,⟨(-17156709656032012),(-17156709656031755)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨4412236718086419693208504,4412236718086464912401824⟩,⟨20281315732143569236882706,20281315732143614457191181⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨17297057455898554782634050,17297057455898651673552721⟩,⟨52754607125522930015792731,52754607125523026908460826⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨36372511775824309647137983,36372511775824388453381868⟩,⟨63873146043011147855889431,63873146043011226661235004⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨52683757052818436586206869,52683757052818470805045626⟩,⟨50311704257482814442564635,50311704257482848656101362⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨54644861000393874856269461,54644861000393882872344691⟩,⟨22628764542870087377914595,22628764542870095385960758⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨40848990793419636100417264,40848990793419637584253306⟩,⟨(-1752622920657637514401583),(-1752622920657636034769375)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨21342350517101966620265015,21342350517101966855470074⟩,⟨(-12428029814415978533296804),(-12428029814415978298329783)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨6751169197810464081858309,6751169197810464129675036⟩,⟨(-11497644485242951504688150),(-11497644485242951455727041)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨87579356088299807852975,87579356088299827719389⟩,⟨(-6576876247321717050439736),(-6576876247321717029787423)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-1420179183843558019189380),(-1420179183843558009285632)⟩,⟨(-2683111561505257035579061),(-2683111561505257025554557)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-1093680653965781359977944),(-1093680653965781355277554)⟩,⟨(-783395440809523561749435),(-783395440809523557105157)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-574636243429043214575380),(-574636243429043212124241)⟩,⟨(-124690735289444648795318),(-124690735289444646405017)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-257249783201055592916370),(-257249783201055591645633)⟩,⟨32734428343331649144669,32734428343331650389691⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-107304589277626879294815),(-107304589277626878655719)⟩,⟨44021778344040595790034,44021778344040596421952⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-42008646011857467055769),(-42008646011857466761415)⟩,⟨26794809777909434776895,26794809777909435069517⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-11040162257511957040834),(-11040162257511956955879)⟩,⟨8531635602461408236010,8531635602461408320669⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨477089671255548695118065934,477089671255559147892258183⟩,⟨933826354982747284413540554,933826354982757737104562216⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨1600167232969199126084442536,1600167232969237532195016671⟩,⟨2428631388736042831860472741,2428631388736081237794459572⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨2981581609125337548910878173,2981581609125427088943814663⟩,⟨2891330401221107518606830147,2891330401221197058543423347⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨4183004844241886621192820061,4183004844242064914384263341⟩,⟨2024074521162074213987307031,2024074521162252507331687848⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨4480645887240474263608794575,4480645887240760910815216057⟩,⟨194684622046016027880202275,194684622046302675539774058⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨3522894569142652839471439991,3522894569143035896338627934⟩,⟨(-1629062075005997261544395537),(-1629062075005614204131728809)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨1761357456003909194629160596,1761357456004467352948789041⟩,⟨(-2513823373817279928416507013),(-2513823373816721769905268515)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨119683043874546798888698475,119683043875063296589412070⟩,⟨(-2243999013656991353908329058),(-2243999013656474856286584260)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-762449029873224676380485624),(-762449029872934297940050171)⟩,⟨(-1341039668327725543121633126),(-1341039668327435164869170142)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-887638898078738748327555662),(-887638898078577299508907526)⟩,⟨(-475175002052843483921231498),(-475175002052682035197195979)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-633301716588162472720050390),(-633301716588089342839349439)⟩,⟨26161011286854949519848041,26161011286928079396934379⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-337720529566570070363218100),(-337720529566546997065440291)⟩,⟨194145175820520548083789539,194145175820543621409327461⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-140493945217533104190820469),(-140493945217527136119648550)⟩,⟨187532208149440151870273731,187532208149446119969297716⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-43634869525827282893563060),(-43634869525825244459794849)⟩,⟨128228614573883599808544224,128228614573885638255227058⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-7935883678388834966838878),(-7935883678388114607702032)⟩,⟨69367708702141605935480354,69367708702142326299088453⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-123098233072659651659121),(-123098233072483548842316)⟩,⟨21484875918011596159335640,21484875918011772263176960⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨2750447323448818310161325214,2750447323448818314780692616⟩,⟨2095465609055660064204321191,2095465609055660068807682372⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨8554990392283095539032371678,8554990392283095553273118426⟩,⟨4989628774322030394758798388,4989628774322030408816883475⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨14574358251672342986347519641,14574358251672343011011387771⟩,⟨4340925194419474395502481837,4340925194419474419531582727⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨19176393869258166983676445848,19176393869258167019221308302⟩,⟨(-816572398679168361944648012),(-816572398679168327679167153)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨19717097164472283827811545043,19717097164472283874669729344⟩,⟨(-9176904342157311087602742148),(-9176904342157311042345434111)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨14549143770915333453905868936,14549143770915333513092157967⟩,⟨(-17166743473736166615011920863),(-17166743473736166556767823804)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨5003215505691679574914019926,5003215505691679643872015528⟩,⟨(-20765721032219814506195379218),(-20765721032219814437407627175)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-4870323556648631797939712698),(-4870323556648631715487199302)⟩,⟨(-18203136901342346646432113829),(-18203136901342346563650627618)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-11026987916988074261175079624),(-11026987916988074118719165135)⟩,⟨(-11197711053586388431615048009),(-11197711053586388288783846226)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-12080990713894021141916370243),(-12080990713894020534592810298)⟩,⟨(-3466006565253656409257782030),(-3466006565253655801833932748)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-9512011588336911956355665275),(-9512011588336909384375138192)⟩,⟨1993802950084196008399926294,1993802950084198580369116818⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-5828149070475081095081659989),(-5828149070475073910754078488)⟩,⟨4336285791238246474137806582,4336285791238253658469085602⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-2802101116913372331747841861),(-2802101116913359785934047343)⟩,⟨4361366277454305756698824469,4361366277454318302553900557⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-996871319953046404782114483),(-996871319953028421811349620)⟩,⟨3279342433974792200087548736,3279342433974810183101063050⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-209208747921775006586568676),(-209208747921756697099863714)⟩,⟨1925169766596126083699946241,1925169766596144393210181208⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-8568750865665134788754867),(-8568750865657392478458571)⟩,⟨624154988625951203487771086,624154988625958945805162393⟩⟩
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
noncomputable def ans : CBox := ⟨⟨8922404323904782479556261996,8922404323905230091849357610⟩,⟨(-8629338854363002705997993139),(-8629338854362555094243653298)⟩⟩
lemma checked : cachedMomentRuleBox density0 hk7_1_7 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 7 7) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk7_1_7 (tableDensity false) (fullFactor true 7 7) density0_contains hk7_1_7_contains
noncomputable def atomAnswer : CBox := ⟨⟨8760515359270327482004480142,8760515359270327493414349961⟩,⟨(-10889332908024463427752406975),(-10889332908024463416518339258)⟩⟩
lemma atomChecked : tableAtomBox false ha7_1_7 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 7 7) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha7_1_7 7 7 ha7_1_7_contains
 def realAnswer : RBox := ⟨17682919683175109961460742138,17682919683175557585363707571⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 7 7) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm7_0_1_7
namespace hm7_1_1_7
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk7_1_7 j i k))
noncomputable def s0_0 : CBox := ⟨⟨164266075,164266181⟩,⟨61011395,61011499⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨304769616,304769926⟩,⟨221445873,221446181⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨123578083,123578633⟩,⟨301904267,301904817⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-78108571),(-78107719)⟩,⟨158792810,158793660⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-69162797),(-69161608)⟩,⟨(-1965698),(-1964508)⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-2369598),(-2368237)⟩,⟨(-21764046),(-21762686)⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨6343482,6344985⟩,⟨223809,225322⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-808787),(-807397)⟩,⟨1724189,1725575⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-324967),(-323621)⟩,⟨(-565574),(-564240)⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨262882,264561⟩,⟨53935,55613⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-109484),(-107817)⟩,⟨83066,84740⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-10162),(-8685)⟩,⟨(-84030),(-82557)⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨56487,57615⟩,⟨7299,8425⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-206),549⟩,⟨40123,40883⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-20944),(-20528)⟩,⟨13909,14308⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-8656),(-8510)⟩,⟨838,975⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨7102365319688172,7102365319688230⟩,⟨253058206717896,253058206717954⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨15396018506525638,15396018506525779⟩,⟨580458713776220,580458713776362⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨13486681972540375,13486681972540584⟩,⟨660280105620194,660280105620405⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨7331375089409732,7331375089410001⟩,⟨617781194407086,617781194407355⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨2760867253533486,2760867253533790⟩,⟨465017353941060,465017353941362⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨755472782464732,755472782465053⟩,⟨259021210792053,259021210792377⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨148479846284479,148479846284811⟩,⟨103797662997944,103797662998275⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨17777030446953,17777030447346⟩,⟨29776314953954,29776314954342⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-216181509035),(-216181508478)⟩,⟨5997054213196,5997054213750⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-693506694859),(-693506694182)⟩,⟨741784369405,741784370080⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-182017011027),(-182017010294)⟩,⟨(-1269733943),(-1269733209)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-23303107816),(-23303107066)⟩,⟨(-28730262966),(-28730262215)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨1604623830,1604624458⟩,⟨(-8761294676),(-8761294045)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨2060806453,2060806915⟩,⟨(-1523305734),(-1523305274)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨825970306,825970593⟩,⟨(-65478574),(-65478289)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨197335655,197335763⟩,⟨43508039,43508151⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-3495424848280703758312),(-3495424848280703744681)⟩,⟨552627243538320525130,552627243538320538751⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-8451478391851364352141),(-8451478391851364316987)⟩,⟨2107095987372167135830,2107095987372167170979⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-8931851120645781014988),(-8931851120645780972172)⟩,⟨3896714121430225776018,3896714121430225818883⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-5964347638668254374862),(-5964347638668254338289)⟩,⟨4496184297722684358598,4496184297722684395257⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-2537959916622818580665),(-2537959916622818557107)⟩,⟨3454636915638197105922,3454636915638197129552⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-561478271440457885503),(-561478271440457873433)⟩,⟨1844321661220107241149,1844321661220107253252⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨52474762532927997570,52474762532928002634⟩,⟨707871292641731832715,707871292641731837786⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨97267800773691405878,97267800773691407736⟩,⟨202174372281929963236,202174372281929965092⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨45468488908336257076,45468488908336257868⟩,⟨44739527559724339394,44739527559724340191⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨14998857346658664202,14998857346658664804⟩,⟨8065100913177007151,8065100913177007755⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨4261098922380095218,4261098922380095912⟩,⟨1267259587246434015,1267259587246434709⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨1166627131250588060,1166627131250588787⟩,⟨192926824524218801,192926824524219531⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨332671709851887382,332671709851888039⟩,⟨33361577263304529,33361577263305184⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨103471950232928696,103471950232929191⟩,⟨7527180691698848,7527180691699344⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨34328526203574406,34328526203574708⟩,⟨2149284732599329,2149284732599629⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨8411999302146566,8411999302146674⟩,⟨500611755089908,500611755090017⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-2870317535779170392732598),(-2870317535779132410730278)⟩,⟨6316827902709303420963117,6316827902709341402847945⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-5867306694594601906862856),(-5867306694594520583746208)⟩,⟨17319666974572919859907558,17319666974573001182837732⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-3008078128002088521469487),(-3008078128002022484380023)⟩,⟨23344561382463534404413379,23344561382463600441590342⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨3708486196723982114983148,3708486196724010703670647⟩,⟨22168759211195920900923866,22168759211195949490152218⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨9143228621604119812603363,9143228621604126461776047⟩,⟨15012397583432885249641268,15012397583432891899624958⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨9923649000640569214764023,9923649000640570413254965⟩,⟨6393066472591247573212243,6393066472591248772121698⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨6976181847995595473525108,6976181847995595642569806⟩,⟨529003035683037686939785,529003035683037856005452⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨3364507239648362861970802,3364507239648362885650482⟩,⟨(-1591212823193026149427605),(-1591212823193026125860869)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨1036477524031010851662636,1036477524031010859274818⟩,⟨(-1481818354350045720888750),(-1481818354350045713350629)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨88294550797995335381243,88294550797995338976365⟩,⟨(-817065389970110578558128),(-817065389970110574972332)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-127366319566132317518928),(-127366319566132315856363)⟩,⟨(-336617207015805701158027),(-336617207015805699489366)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-110080279497151210342448),(-110080279497151209485845)⟩,⟨(-111401980369049826576512),(-111401980369049825714112)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-62617643395600996974338),(-62617643395600996524735)⟩,⟨(-29651123939645815542833),(-29651123939645815090910)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-30742730369360816015455),(-30742730369360815784833)⟩,⟨(-5400245098560484472552),(-5400245098560484241333)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-13509153617356021097297),(-13509153617356020989431)⟩,⟨95303593263507513695,95303593263507621689⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-3781921676363861880636),(-3781921676363861849233)⟩,⟨371295662311371726999,371295662311371758423⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨172256348005573592773412147,172256348005582182472860785⟩,⟨298385243571967408826453284,298385243571975998543537560⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨570721548242557151835521717,570721548242588715525344308⟩,⟨790737452270330038623124629,790737452270361602352243862⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨1053863218620905706633720838,1053863218620979305972664469⟩,⟨980273368503999629206113668,980273368504073228570212706⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨1484906788468209265337414606,1484906788468355843278719968⟩,⟨747906570760457512793565277,747906570760604090708108980⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨1626820222317335159202446757,1626820222317570848087483956⟩,⟨168285735598878794206100764,168285735599114482997359772⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨1345639131845013603866741603,1345639131845328565307952356⟩,⟨(-469368230051712710990538972),(-469368230051397749670288474)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨761667562162441783112090291,761667562162900624635135024⟩,⟨(-840654925316145069353234713),(-840654925315686227882467843)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨170281524450044185131039926,170281524450468579349221407⟩,⟨(-826257459236846925311451023),(-826257459236422531080960726)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-193747288847990505706543602),(-193747288847752092315347434)⟩,⟨(-560609106630699207871119972),(-560609106630460794440620196)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-296206245285793449890428850),(-296206245285661039582712827)⟩,⟨(-262995458964798266904949104),(-262995458964665856577130145)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-243489763232554801404438039),(-243489763232494899532446197)⟩,⟨(-64327410420761346260553901),(-64327410420701444387099341)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-151092244305889797219826231),(-151092244305870922913933369)⟩,⟨23287493008275434691466183,23287493008294308992550735⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-77992021458016165898050877),(-77992021458011290383443738)⟩,⟨42714056370841544928237458,42714056370846420437873551⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-35052163400492935468460510),(-35052163400491272098700943)⟩,⟨34639964240648178002428274,34639964240649841369902760⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-13721062409774570503993290),(-13721062409773983155915533)⟩,⟨20319979470576053835633977,20319979470576641182925181⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-3488688196866152008573411),(-3488688196866008483014017)⟩,⟨6526917958497425908497176,6526917958497569433878057⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨84642292945076824344884304,84642292945076825454301693⟩,⟨58352137237724257900588787,58352137237724258964908336⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨277603059254387807669599425,277603059254387811022169714⟩,⟨79280342389154628529895268,79280342389154631669557891⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨405909767834045869569778871,405909767834045875015399231⟩,⟨(-215946583018394790529343503),(-215946583018394785637785490)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨113784899102940561641629898,113784899102940568921807434⟩,⟨(-1007972941459162334471319461),(-1007972941459162328226303390)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-1019165872592310407005274819),(-1019165872592310396367938317)⟩,⟨(-2159072069562839536621544684),(-2159072069562839527289208096)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-3033169077211677572505588686),(-3033169077211677555209404967)⟩,⟨(-3021020645184455791525566393),(-3021020645184455774989201732)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-5313572699867892699909064811),(-5313572699867892674469504824)⟩,⟨(-2776689927378374203471138554),(-2776689927378374178077568406)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-6837545243560125585056441147),(-6837545243560125545928245620)⟩,⟨(-1185101391326654792742102985),(-1185101391326654753113523829)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-6855593475251132895667101418),(-6855593475251132803240919272)⟩,⟨1086002817553674907057613602,1086002817553675000137421211⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-5436794090272858948600580970),(-5436794090272858471159018524)⟩,⟨2964986176765427220139268236,2964986176765427697845193694⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-3349751335808670685716877971),(-3349751335808668600029370946)⟩,⟨3771299766092480590229742971,3771299766092482675901170862⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-1454564569304358158232230041),(-1454564569304352302900347143)⟩,⟨3534860712290292589673792327,3534860712290298444892599768⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-222170292446381094110111591),(-222170292446370853464968670)⟩,⟨2718302466029346784757786265,2718302466029357025287138716⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨316897560229272825765290547,316897560229287518443449086⟩,⟨1782796312719643448991239386,1782796312719658141601854799⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨363064546903209683585293541,363064546903224651266268347⟩,⟨967901725893845778778703192,967901725893860746433855583⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨147127395951503404762596782,147127395951509735558223563⟩,⟨302190034255538350816113382,302190034255544681605492421⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-4269968828153665828444481773),(-4269968828153298134988828248)⟩,⟨1179293670400990842672815371,1179293670401358535622740167⟩⟩
lemma checked : cachedMomentRuleBox density1 hk7_1_7 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 7 7) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk7_1_7 (tableDensity true) (fullFactor true 7 7) density1_contains hk7_1_7_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-11456058546738120568311073026),(-11456058546738120553390474032)⟩,⟨14239896879724298313908597492,14239896879724298328599301429⟩⟩
lemma atomChecked : tableAtomBox true ha7_1_7 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 7 7) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha7_1_7 7 7 ha7_1_7_contains
 def realAnswer : RBox := ⟨(-15726027374891786396855554799),(-15726027374891418688279302280)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 7 7) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm7_1_1_7
end SharpPlanar.CachedData

end OAI
