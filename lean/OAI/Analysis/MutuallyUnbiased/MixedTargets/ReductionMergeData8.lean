import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData8
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData9
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData7

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge256 : Integer.Sparse Master := [(Sum.inl 0, -93615485239019520000), (Sum.inl 1, -1317424463073331200000), (Sum.inl 2, 98634551826585600000), (Sum.inl 3, 954893949404774400000), (Sum.inl 5, 115789421854310400000), (Sum.inl 6, -5324919264000000000), (Sum.inl 7, 1721682323420774400000), (Sum.inl 8, -12977965537689600000), (Sum.inl 12, -340794832896000000000), (Sum.inl 13, -596390957568000000000), (Sum.inl 34, -85198708224000000000), (Sum.inl 35, -85198708224000000000), (Sum.inl 51, -989950545793843200000), (Sum.inl 52, -255596124672000000000), (Sum.inl 54, -1245546670465843200000), (Sum.inl 64, -1245546670465843200000)]

def originalMerge256 : Integer.Sparse OriginalKey := originalMerge254 ++ originalMerge255

theorem reducedMerge256Check : reducedMerge256 = Integer.Sparse.mergeBy masterLess reducedMerge254 reducedMerge255 := by decide +kernel

def reducedMerge257 : Integer.Sparse Master := [(Sum.inl 0, -139941643682211840000), (Sum.inl 1, -1118129247970560000000), (Sum.inl 2, 302987143855872000000), (Sum.inl 3, 1650559615436390400000), (Sum.inl 4, 231888555343872000000), (Sum.inl 5, 175063827739852800000), (Sum.inl 6, -37564730196940800000), (Sum.inl 7, 1721682323420774400000), (Sum.inl 8, -12977965537689600000), (Sum.inl 12, -340794832896000000000), (Sum.inl 13, -364502402224128000000), (Sum.inl 26, 984823153813094400000), (Sum.inl 34, 667735890245222400000), (Sum.inl 35, 146689847119872000000), (Sum.inl 51, -989950545793843200000), (Sum.inl 52, -255596124672000000000), (Sum.inl 54, -1245546670465843200000), (Sum.inl 64, -1245546670465843200000), (Sum.inl 67, 521046043125350400000)]

def originalMerge257 : Integer.Sparse OriginalKey := originalMerge253 ++ originalMerge256

theorem reducedMerge257Check : reducedMerge257 = Integer.Sparse.mergeBy masterLess reducedMerge253 reducedMerge256 := by decide +kernel

def reducedMerge258 : Integer.Sparse Master := [(Sum.inl 0, 173283228037785600000), (Sum.inl 1, -419245476314112000000), (Sum.inl 2, 411278523134976000000), (Sum.inl 3, 1341716248793088000000), (Sum.inl 4, 170397416448000000000), (Sum.inl 5, 250230353974272000000), (Sum.inl 6, -62557588493568000000), (Sum.inl 12, 170397416448000000000), (Sum.inl 13, 170397416448000000000), (Sum.inl 25, -2491571998347264000000), (Sum.inl 26, 915722707673088000000), (Sum.inl 31, -511192249344000000000), (Sum.inl 33, -511192249344000000000), (Sum.inl 34, 85198708224000000000), (Sum.inl 51, -511192249344000000000), (Sum.inl 52, 85198708224000000000), (Sum.inl 64, -2491571998347264000000), (Sum.inl 123, -2747168123019264000000)]

def originalMerge258 : Integer.Sparse OriginalKey := originalTerm261 ++ originalTerm262

theorem reducedMerge258Check : reducedMerge258 = Integer.Sparse.mergeBy masterLess reducedTerm261 reducedTerm262 := by decide +kernel

def reducedMerge259 : Integer.Sparse Master := [(Sum.inl 0, -77190903611136000000), (Sum.inl 1, 161048169160704000000), (Sum.inl 2, 10649838528000000000), (Sum.inl 5, 21299677056000000000), (Sum.inl 6, -51907749965568000000), (Sum.inl 31, -255596124672000000000), (Sum.inl 33, -255596124672000000000), (Sum.inl 51, -255596124672000000000), (Sum.inl 123, -2491571998347264000000)]

def originalMerge259 : Integer.Sparse OriginalKey := originalTerm263 ++ originalTerm264

theorem reducedMerge259Check : reducedMerge259 = Integer.Sparse.mergeBy masterLess reducedTerm263 reducedTerm264 := by decide +kernel

def reducedMerge260 : Integer.Sparse Master := [(Sum.inl 0, 96092324426649600000), (Sum.inl 1, -258197307153408000000), (Sum.inl 2, 421928361662976000000), (Sum.inl 3, 1341716248793088000000), (Sum.inl 4, 170397416448000000000), (Sum.inl 5, 271530031030272000000), (Sum.inl 6, -114465338459136000000), (Sum.inl 12, 170397416448000000000), (Sum.inl 13, 170397416448000000000), (Sum.inl 25, -2491571998347264000000), (Sum.inl 26, 915722707673088000000), (Sum.inl 31, -766788374016000000000), (Sum.inl 33, -766788374016000000000), (Sum.inl 34, 85198708224000000000), (Sum.inl 51, -766788374016000000000), (Sum.inl 52, 85198708224000000000), (Sum.inl 64, -2491571998347264000000), (Sum.inl 123, -5238740121366528000000)]

def originalMerge260 : Integer.Sparse OriginalKey := originalMerge258 ++ originalMerge259

theorem reducedMerge260Check : reducedMerge260 = Integer.Sparse.mergeBy masterLess reducedMerge258 reducedMerge259 := by decide +kernel

def reducedMerge261 : Integer.Sparse Master := [(Sum.inl 0, -1834272353894400000), (Sum.inl 1, -7337089415577600000), (Sum.inl 2, 64199532386304000000), (Sum.inl 3, 322831934285414400000), (Sum.inl 4, 117393430649241600000), (Sum.inl 5, 29348357662310400000), (Sum.inl 6, -7337089415577600000), (Sum.inl 12, 88045072986931200000), (Sum.inl 13, 58696715324620800000), (Sum.inl 51, -352180291947724800000), (Sum.inl 52, 117393430649241600000)]

def originalMerge261 : Integer.Sparse OriginalKey := originalTerm265 ++ originalTerm266

theorem reducedMerge261Check : reducedMerge261 = Integer.Sparse.mergeBy masterLess reducedTerm265 reducedTerm266 := by decide +kernel

def reducedMerge262 : Integer.Sparse Master := [(Sum.inl 0, -303089446422282240000), (Sum.inl 1, 557999680237977600000), (Sum.inl 2, -439077182423040000000), (Sum.inl 3, -1756308729692160000000), (Sum.inl 5, -207334321599283200000), (Sum.inl 6, 54884647802880000000), (Sum.inl 12, -878154364846080000000), (Sum.inl 13, -878154364846080000000), (Sum.inl 51, 2634463094538240000000), (Sum.inl 52, -878154364846080000000), (Sum.inl 64, -146451235346841600000)]

def originalMerge262 : Integer.Sparse OriginalKey := originalTerm267 ++ originalTerm268

theorem reducedMerge262Check : reducedMerge262 = Integer.Sparse.mergeBy masterLess reducedTerm267 reducedTerm268 := by decide +kernel

def reducedMerge263 : Integer.Sparse Master := [(Sum.inl 0, -304923718776176640000), (Sum.inl 1, 550662590822400000000), (Sum.inl 2, -374877650036736000000), (Sum.inl 3, -1433476795406745600000), (Sum.inl 4, 117393430649241600000), (Sum.inl 5, -177985963936972800000), (Sum.inl 6, 47547558387302400000), (Sum.inl 12, -790109291859148800000), (Sum.inl 13, -819457649521459200000), (Sum.inl 51, 2282282802590515200000), (Sum.inl 52, -760760934196838400000), (Sum.inl 64, -146451235346841600000)]

def originalMerge263 : Integer.Sparse OriginalKey := originalMerge261 ++ originalMerge262

theorem reducedMerge263Check : reducedMerge263 = Integer.Sparse.mergeBy masterLess reducedMerge261 reducedMerge262 := by decide +kernel

def reducedMerge264 : Integer.Sparse Master := [(Sum.inl 0, -208831394349527040000), (Sum.inl 1, 292465283668992000000), (Sum.inl 2, 47050711626240000000), (Sum.inl 3, -91760546613657600000), (Sum.inl 4, 287790847097241600000), (Sum.inl 5, 93544067093299200000), (Sum.inl 6, -66917780071833600000), (Sum.inl 12, -619711875411148800000), (Sum.inl 13, -649060233073459200000), (Sum.inl 25, -2491571998347264000000), (Sum.inl 26, 915722707673088000000), (Sum.inl 31, -766788374016000000000), (Sum.inl 33, -766788374016000000000), (Sum.inl 34, 85198708224000000000), (Sum.inl 51, 1515494428574515200000), (Sum.inl 52, -675562225972838400000), (Sum.inl 64, -2638023233694105600000), (Sum.inl 123, -5238740121366528000000)]

def originalMerge264 : Integer.Sparse OriginalKey := originalMerge260 ++ originalMerge263

theorem reducedMerge264Check : reducedMerge264 = Integer.Sparse.mergeBy masterLess reducedMerge260 reducedMerge263 := by decide +kernel

def reducedMerge265 : Integer.Sparse Master := [(Sum.inl 0, -348773038031738880000), (Sum.inl 1, -825663964301568000000), (Sum.inl 2, 350037855482112000000), (Sum.inl 3, 1558799068822732800000), (Sum.inl 4, 519679402441113600000), (Sum.inl 5, 268607894833152000000), (Sum.inl 6, -104482510268774400000), (Sum.inl 7, 1721682323420774400000), (Sum.inl 8, -12977965537689600000), (Sum.inl 12, -960506708307148800000), (Sum.inl 13, -1013562635297587200000), (Sum.inl 25, -2491571998347264000000), (Sum.inl 26, 1900545861486182400000), (Sum.inl 31, -766788374016000000000), (Sum.inl 33, -766788374016000000000), (Sum.inl 34, 752934598469222400000), (Sum.inl 35, 146689847119872000000), (Sum.inl 51, 525543882780672000000), (Sum.inl 52, -931158350644838400000), (Sum.inl 54, -1245546670465843200000), (Sum.inl 64, -3883569904159948800000), (Sum.inl 67, 521046043125350400000), (Sum.inl 123, -5238740121366528000000)]

def originalMerge265 : Integer.Sparse OriginalKey := originalMerge257 ++ originalMerge264

theorem reducedMerge265Check : reducedMerge265 = Integer.Sparse.mergeBy masterLess reducedMerge257 reducedMerge264 := by decide +kernel

def reducedMerge266 : Integer.Sparse Master := [(Sum.inl 0, 160494579051448320000), (Sum.inl 1, -638033950497484800000), (Sum.inl 2, 335609016219187200000), (Sum.inl 3, 2237774217773875200000), (Sum.inl 4, 1299853433320243200000), (Sum.inl 5, 762392578422988800000), (Sum.inl 6, -219877514280345600000), (Sum.inl 7, 2501554685711155200000), (Sum.inl 8, -297706694403686400000), (Sum.inl 12, -1123521239302963200000), (Sum.inl 13, -2559639832694784000000), (Sum.inl 25, -2491571998347264000000), (Sum.inl 26, 2393601843599769600000), (Sum.inl 31, -766788374016000000000), (Sum.inl 33, -1277980623360000000000), (Sum.inl 34, -352747753124659200000), (Sum.inl 35, 126487223422156800000), (Sum.inl 51, 566216281387008000000), (Sum.inl 52, -1504588989741465600000), (Sum.inl 54, -1245546670465843200000), (Sum.inl 64, -3437730225222451200000), (Sum.inl 67, 72598711527014400000), (Sum.inl 81, -511192249344000000000), (Sum.inl 123, -5238740121366528000000)]

def originalMerge266 : Integer.Sparse OriginalKey := originalMerge251 ++ originalMerge265

theorem reducedMerge266Check : reducedMerge266 = Integer.Sparse.mergeBy masterLess reducedMerge251 reducedMerge265 := by decide +kernel

def reducedMerge267 : Integer.Sparse Master := [(Sum.inl 0, -6962110798970880000), (Sum.inl 1, 46483649152819200000), (Sum.inl 2, -60160268657664000000), (Sum.inl 3, -170888084088422400000), (Sum.inl 5, 86161959191347200000), (Sum.inl 7, -40377882643660800000), (Sum.inl 12, -45066159400550400000), (Sum.inl 13, -166199807331532800000), (Sum.inl 23, -335271283251609600000), (Sum.inl 25, -228202465591296000000), (Sum.inl 26, -85444042044211200000), (Sum.inl 27, -144384644778393600000), (Sum.inl 33, -228202465591296000000), (Sum.inl 34, -80755765287321600000), (Sum.inl 35, -45066159400550400000), (Sum.inl 54, -456404931182592000000), (Sum.inl 55, -214137635320627200000), (Sum.inl 63, -335271283251609600000), (Sum.inl 64, -228202465591296000000), (Sum.inl 65, -335271283251609600000), (Sum.inl 67, -40377882643660800000), (Sum.inl 68, -228202465591296000000), (Sum.inl 125, -228202465591296000000), (Sum.inl 196, -228202465591296000000), (Sum.inl 264, -228202465591296000000), (Sum.inl 266, -228202465591296000000)]

def originalMerge267 : Integer.Sparse OriginalKey := originalTerm270 ++ originalTerm271

theorem reducedMerge267Check : reducedMerge267 = Integer.Sparse.mergeBy masterLess reducedTerm270 reducedTerm271 := by decide +kernel

def reducedMerge268 : Integer.Sparse Master := [(Sum.inl 0, 298912309869035520000), (Sum.inl 1, -281238944420044800000), (Sum.inl 2, 267562324915200000000), (Sum.inl 3, -170888084088422400000), (Sum.inl 5, -350801498905804800000), (Sum.inl 7, -40377882643660800000), (Sum.inl 12, -45066159400550400000), (Sum.inl 13, -166199807331532800000), (Sum.inl 23, -335271283251609600000), (Sum.inl 25, -228202465591296000000), (Sum.inl 26, -85444042044211200000), (Sum.inl 27, -144384644778393600000), (Sum.inl 33, -228202465591296000000), (Sum.inl 34, -80755765287321600000), (Sum.inl 35, -45066159400550400000), (Sum.inl 51, 5243561497165824000000), (Sum.inl 54, -456404931182592000000), (Sum.inl 55, -214137635320627200000), (Sum.inl 63, -335271283251609600000), (Sum.inl 64, -228202465591296000000), (Sum.inl 65, -335271283251609600000), (Sum.inl 67, -40377882643660800000), (Sum.inl 68, -228202465591296000000), (Sum.inl 125, -228202465591296000000), (Sum.inl 196, -228202465591296000000), (Sum.inl 264, -228202465591296000000), (Sum.inl 266, -228202465591296000000)]

def originalMerge268 : Integer.Sparse OriginalKey := originalTerm269 ++ originalMerge267

theorem reducedMerge268Check : reducedMerge268 = Integer.Sparse.mergeBy masterLess reducedTerm269 reducedMerge267 := by decide +kernel

def reducedMerge269 : Integer.Sparse Master := [(Sum.inl 0, 58043776921804800000), (Sum.inl 1, -223482654155980800000), (Sum.inl 2, 23252410860134400000), (Sum.inl 3, -639238695085670400000), (Sum.inl 4, 159299274748723200000), (Sum.inl 5, -139642064916480000000), (Sum.inl 7, 39824818687180800000), (Sum.inl 12, -306004141965312000000), (Sum.inl 13, -478918622291558400000), (Sum.inl 24, -119474456061542400000), (Sum.inl 25, 518743440978739200000), (Sum.inl 26, 66034431796838400000), (Sum.inl 27, 418926194749440000000), (Sum.inl 33, 1436755866874675200000), (Sum.inl 34, 79649637374361600000), (Sum.inl 35, -93264842951884800000), (Sum.inl 55, 679063513772851200000), (Sum.inl 63, 518743440978739200000), (Sum.inl 64, 918012425895936000000), (Sum.inl 66, -119474456061542400000), (Sum.inl 67, 39824818687180800000)]

def originalMerge269 : Integer.Sparse OriginalKey := originalTerm272 ++ originalTerm273

theorem reducedMerge269Check : reducedMerge269 = Integer.Sparse.mergeBy masterLess reducedTerm272 reducedTerm273 := by decide +kernel

def reducedMerge270 : Integer.Sparse Master := [(Sum.inl 0, -132631842569748480000), (Sum.inl 1, 178402019152896000000), (Sum.inl 2, 101949994408550400000), (Sum.inl 3, 344237842051891200000), (Sum.inl 4, 434897289746841600000), (Sum.inl 5, -11332430961868800000), (Sum.inl 12, -45329723847475200000), (Sum.inl 13, -117812605471948800000), (Sum.inl 26, 172118921025945600000), (Sum.inl 27, 33997292885606400000), (Sum.inl 35, -45329723847475200000), (Sum.inl 55, 135989171542425600000)]

def originalMerge270 : Integer.Sparse OriginalKey := originalTerm274 ++ originalTerm275

theorem reducedMerge270Check : reducedMerge270 = Integer.Sparse.mergeBy masterLess reducedTerm274 reducedTerm275 := by decide +kernel

def reducedMerge271 : Integer.Sparse Master := [(Sum.inl 0, -74588065647943680000), (Sum.inl 1, -45080635003084800000), (Sum.inl 2, 125202405268684800000), (Sum.inl 3, -295000853033779200000), (Sum.inl 4, 594196564495564800000), (Sum.inl 5, -150974495878348800000), (Sum.inl 7, 39824818687180800000), (Sum.inl 12, -351333865812787200000), (Sum.inl 13, -596731227763507200000), (Sum.inl 24, -119474456061542400000), (Sum.inl 25, 518743440978739200000), (Sum.inl 26, 238153352822784000000), (Sum.inl 27, 452923487635046400000), (Sum.inl 33, 1436755866874675200000), (Sum.inl 34, 79649637374361600000), (Sum.inl 35, -138594566799360000000), (Sum.inl 55, 815052685315276800000), (Sum.inl 63, 518743440978739200000), (Sum.inl 64, 918012425895936000000), (Sum.inl 66, -119474456061542400000), (Sum.inl 67, 39824818687180800000)]

def originalMerge271 : Integer.Sparse OriginalKey := originalMerge269 ++ originalMerge270

theorem reducedMerge271Check : reducedMerge271 = Integer.Sparse.mergeBy masterLess reducedMerge269 reducedMerge270 := by decide +kernel

def reducedMerge272 : Integer.Sparse Master := [(Sum.inl 0, 224324244221091840000), (Sum.inl 1, -326319579423129600000), (Sum.inl 2, 392764730183884800000), (Sum.inl 3, -465888937122201600000), (Sum.inl 4, 594196564495564800000), (Sum.inl 5, -501775994784153600000), (Sum.inl 7, -553063956480000000), (Sum.inl 12, -396400025213337600000), (Sum.inl 13, -762931035095040000000), (Sum.inl 23, -335271283251609600000), (Sum.inl 24, -119474456061542400000), (Sum.inl 25, 290540975387443200000), (Sum.inl 26, 152709310778572800000), (Sum.inl 27, 308538842856652800000), (Sum.inl 33, 1208553401283379200000), (Sum.inl 34, -1106127912960000000), (Sum.inl 35, -183660726199910400000), (Sum.inl 51, 5243561497165824000000), (Sum.inl 54, -456404931182592000000), (Sum.inl 55, 600915049994649600000), (Sum.inl 63, 183472157727129600000), (Sum.inl 64, 689809960304640000000), (Sum.inl 65, -335271283251609600000), (Sum.inl 66, -119474456061542400000), (Sum.inl 67, -553063956480000000), (Sum.inl 68, -228202465591296000000), (Sum.inl 125, -228202465591296000000), (Sum.inl 196, -228202465591296000000), (Sum.inl 264, -228202465591296000000), (Sum.inl 266, -228202465591296000000)]

def originalMerge272 : Integer.Sparse OriginalKey := originalMerge268 ++ originalMerge271

theorem reducedMerge272Check : reducedMerge272 = Integer.Sparse.mergeBy masterLess reducedMerge268 reducedMerge271 := by decide +kernel

def reducedMerge273 : Integer.Sparse Master := [(Sum.inl 0, -46672608281886720000), (Sum.inl 1, -97506605216563200000), (Sum.inl 2, 189165581195673600000), (Sum.inl 3, -946508387844096000000), (Sum.inl 4, -171622693483315200000), (Sum.inl 5, -65004403477708800000), (Sum.inl 7, -85811346741657600000), (Sum.inl 12, -85811346741657600000), (Sum.inl 13, -85811346741657600000), (Sum.inl 23, 257434040224972800000), (Sum.inl 25, 514868080449945600000), (Sum.inl 26, -343245386966630400000), (Sum.inl 27, 195013210433126400000), (Sum.inl 33, 1552354962407424000000), (Sum.inl 34, -171622693483315200000), (Sum.inl 35, -85811346741657600000), (Sum.inl 55, 1294920922182451200000), (Sum.inl 63, 514868080449945600000), (Sum.inl 64, 1552354962407424000000), (Sum.inl 65, 257434040224972800000), (Sum.inl 67, -85811346741657600000)]

def originalMerge273 : Integer.Sparse OriginalKey := originalTerm276 ++ originalTerm277

theorem reducedMerge273Check : reducedMerge273 = Integer.Sparse.mergeBy masterLess reducedTerm276 reducedTerm277 := by decide +kernel

def reducedMerge274 : Integer.Sparse Master := [(Sum.inl 0, -155149002138009600000), (Sum.inl 1, 351539726417510400000), (Sum.inl 2, 142384099995648000000), (Sum.inl 5, -1473507857203200000), (Sum.inl 23, 1673245011374899200000), (Sum.inl 25, 17682094286438400000), (Sum.inl 27, -832201982115840000000), (Sum.inl 33, 17682094286438400000), (Sum.inl 55, 1673245011374899200000), (Sum.inl 63, 1690927105661337600000), (Sum.inl 64, 17682094286438400000), (Sum.inl 65, 1673245011374899200000)]

def originalMerge274 : Integer.Sparse OriginalKey := originalTerm278 ++ originalTerm279

theorem reducedMerge274Check : reducedMerge274 = Integer.Sparse.mergeBy masterLess reducedTerm278 reducedTerm279 := by decide +kernel

def reducedMerge275 : Integer.Sparse Master := [(Sum.inl 0, -201821610419896320000), (Sum.inl 1, 254033121200947200000), (Sum.inl 2, 331549681191321600000), (Sum.inl 3, -946508387844096000000), (Sum.inl 4, -171622693483315200000), (Sum.inl 5, -66477911334912000000), (Sum.inl 7, -85811346741657600000), (Sum.inl 12, -85811346741657600000), (Sum.inl 13, -85811346741657600000), (Sum.inl 23, 1930679051599872000000), (Sum.inl 25, 532550174736384000000), (Sum.inl 26, -343245386966630400000), (Sum.inl 27, -637188771682713600000), (Sum.inl 33, 1570037056693862400000), (Sum.inl 34, -171622693483315200000), (Sum.inl 35, -85811346741657600000), (Sum.inl 55, 2968165933557350400000), (Sum.inl 63, 2205795186111283200000), (Sum.inl 64, 1570037056693862400000), (Sum.inl 65, 1930679051599872000000), (Sum.inl 67, -85811346741657600000)]

def originalMerge275 : Integer.Sparse OriginalKey := originalMerge273 ++ originalMerge274

theorem reducedMerge275Check : reducedMerge275 = Integer.Sparse.mergeBy masterLess reducedMerge273 reducedMerge274 := by decide +kernel

def reducedMerge276 : Integer.Sparse Master := [(Sum.inl 0, -70776042229186560000), (Sum.inl 1, 100546237196697600000), (Sum.inl 2, -454426448342630400000), (Sum.inl 24, -119474456061542400000), (Sum.inl 27, -364328511057100800000), (Sum.inl 55, -238948912123084800000), (Sum.inl 63, -1696262956351488000000), (Sum.inl 66, -119474456061542400000)]

def originalMerge276 : Integer.Sparse OriginalKey := originalTerm280 ++ originalTerm281

theorem reducedMerge276Check : reducedMerge276 = Integer.Sparse.mergeBy masterLess reducedTerm280 reducedTerm281 := by decide +kernel

def reducedMerge277 : Integer.Sparse Master := [(Sum.inl 0, 102417404518195200000), (Sum.inl 1, -169197268707532800000), (Sum.inl 2, -82917618300518400000), (Sum.inl 3, 161377541111808000000), (Sum.inl 4, 107585027407872000000), (Sum.inl 5, 13448128425984000000), (Sum.inl 26, 107585027407872000000), (Sum.inl 27, 291326087924121600000), (Sum.inl 35, 53792513703936000000), (Sum.inl 55, 1165304351696486400000)]

def originalMerge277 : Integer.Sparse OriginalKey := originalTerm282 ++ originalTerm283

theorem reducedMerge277Check : reducedMerge277 = Integer.Sparse.mergeBy masterLess reducedTerm282 reducedTerm283 := by decide +kernel

def reducedMerge278 : Integer.Sparse Master := [(Sum.inl 0, 31641362289008640000), (Sum.inl 1, -68651031510835200000), (Sum.inl 2, -537344066643148800000), (Sum.inl 3, 161377541111808000000), (Sum.inl 4, 107585027407872000000), (Sum.inl 5, 13448128425984000000), (Sum.inl 24, -119474456061542400000), (Sum.inl 26, 107585027407872000000), (Sum.inl 27, -73002423132979200000), (Sum.inl 35, 53792513703936000000), (Sum.inl 55, 926355439573401600000), (Sum.inl 63, -1696262956351488000000), (Sum.inl 66, -119474456061542400000)]

def originalMerge278 : Integer.Sparse OriginalKey := originalMerge276 ++ originalMerge277

theorem reducedMerge278Check : reducedMerge278 = Integer.Sparse.mergeBy masterLess reducedMerge276 reducedMerge277 := by decide +kernel

def reducedMerge279 : Integer.Sparse Master := [(Sum.inl 0, -170180248130887680000), (Sum.inl 1, 185382089690112000000), (Sum.inl 2, -205794385451827200000), (Sum.inl 3, -785130846732288000000), (Sum.inl 4, -64037666075443200000), (Sum.inl 5, -53029782908928000000), (Sum.inl 7, -85811346741657600000), (Sum.inl 12, -85811346741657600000), (Sum.inl 13, -85811346741657600000), (Sum.inl 23, 1930679051599872000000), (Sum.inl 24, -119474456061542400000), (Sum.inl 25, 532550174736384000000), (Sum.inl 26, -235660359558758400000), (Sum.inl 27, -710191194815692800000), (Sum.inl 33, 1570037056693862400000), (Sum.inl 34, -171622693483315200000), (Sum.inl 35, -32018833037721600000), (Sum.inl 55, 3894521373130752000000), (Sum.inl 63, 509532229759795200000), (Sum.inl 64, 1570037056693862400000), (Sum.inl 65, 1930679051599872000000), (Sum.inl 66, -119474456061542400000), (Sum.inl 67, -85811346741657600000)]

def originalMerge279 : Integer.Sparse OriginalKey := originalMerge275 ++ originalMerge278

theorem reducedMerge279Check : reducedMerge279 = Integer.Sparse.mergeBy masterLess reducedMerge275 reducedMerge278 := by decide +kernel

def reducedMerge280 : Integer.Sparse Master := [(Sum.inl 0, 54143996090204160000), (Sum.inl 1, -140937489733017600000), (Sum.inl 2, 186970344732057600000), (Sum.inl 3, -1251019783854489600000), (Sum.inl 4, 530158898420121600000), (Sum.inl 5, -554805777693081600000), (Sum.inl 7, -86364410698137600000), (Sum.inl 12, -482211371954995200000), (Sum.inl 13, -848742381836697600000), (Sum.inl 23, 1595407768348262400000), (Sum.inl 24, -238948912123084800000), (Sum.inl 25, 823091150123827200000), (Sum.inl 26, -82951048780185600000), (Sum.inl 27, -401652351959040000000), (Sum.inl 33, 2778590457977241600000), (Sum.inl 34, -172728821396275200000), (Sum.inl 35, -215679559237632000000), (Sum.inl 51, 5243561497165824000000), (Sum.inl 54, -456404931182592000000), (Sum.inl 55, 4495436423125401600000), (Sum.inl 63, 693004387486924800000), (Sum.inl 64, 2259847016998502400000), (Sum.inl 65, 1595407768348262400000), (Sum.inl 66, -238948912123084800000), (Sum.inl 67, -86364410698137600000), (Sum.inl 68, -228202465591296000000), (Sum.inl 125, -228202465591296000000), (Sum.inl 196, -228202465591296000000), (Sum.inl 264, -228202465591296000000), (Sum.inl 266, -228202465591296000000)]

def originalMerge280 : Integer.Sparse OriginalKey := originalMerge272 ++ originalMerge279

theorem reducedMerge280Check : reducedMerge280 = Integer.Sparse.mergeBy masterLess reducedMerge272 reducedMerge279 := by decide +kernel

def reducedMerge281 : Integer.Sparse Master := [(Sum.inl 0, -24172973117798400000), (Sum.inl 1, -92691793132646400000), (Sum.inl 2, -46380530472192000000), (Sum.inl 3, 130761212217753600000), (Sum.inl 12, 87174141478502400000), (Sum.inl 13, -145659664126771200000), (Sum.inl 26, 87174141478502400000), (Sum.inl 34, 87174141478502400000)]

def originalMerge281 : Integer.Sparse OriginalKey := originalTerm285 ++ originalTerm286

theorem reducedMerge281Check : reducedMerge281 = Integer.Sparse.mergeBy masterLess reducedTerm285 reducedTerm286 := by decide +kernel

def reducedMerge282 : Integer.Sparse Master := [(Sum.inl 0, -303154644270643200000), (Sum.inl 1, -1726727295599308800000), (Sum.inl 2, -365216726075443200000), (Sum.inl 3, 4594467950663270400000), (Sum.inl 4, 2550689564826009600000), (Sum.inl 5, 159418097801625600000), (Sum.inl 12, 87174141478502400000), (Sum.inl 13, -145659664126771200000), (Sum.inl 26, 2637863706304512000000), (Sum.inl 27, -478254293404876800000), (Sum.inl 34, 87174141478502400000), (Sum.inl 35, 637672391206502400000), (Sum.inl 55, -1913017173619507200000)]

def originalMerge282 : Integer.Sparse OriginalKey := originalTerm284 ++ originalMerge281

theorem reducedMerge282Check : reducedMerge282 = Integer.Sparse.mergeBy masterLess reducedTerm284 reducedMerge281 := by decide +kernel

def reducedMerge283 : Integer.Sparse Master := [(Sum.inl 0, -38196356146421760000), (Sum.inl 1, -494305785424281600000), (Sum.inl 2, 33702667188019200000), (Sum.inl 3, 898737791680512000000), (Sum.inl 4, 359495116672204800000), (Sum.inl 26, 359495116672204800000)]

def originalMerge283 : Integer.Sparse OriginalKey := originalTerm287 ++ originalTerm288

theorem reducedMerge283Check : reducedMerge283 = Integer.Sparse.mergeBy masterLess reducedTerm287 reducedTerm288 := by decide +kernel

def reducedMerge284 : Integer.Sparse Master := [(Sum.inl 0, 191147490691153920000), (Sum.inl 1, -143403340850380800000), (Sum.inl 2, -234669607977369600000), (Sum.inl 3, 513479559669350400000), (Sum.inl 26, 80178404976230400000)]

def originalMerge284 : Integer.Sparse OriginalKey := originalTerm289 ++ originalTerm290

theorem reducedMerge284Check : reducedMerge284 = Integer.Sparse.mergeBy masterLess reducedTerm289 reducedTerm290 := by decide +kernel

def reducedMerge285 : Integer.Sparse Master := [(Sum.inl 0, 152951134544732160000), (Sum.inl 1, -637709126274662400000), (Sum.inl 2, -200966940789350400000), (Sum.inl 3, 1412217351349862400000), (Sum.inl 4, 359495116672204800000), (Sum.inl 26, 439673521648435200000)]

def originalMerge285 : Integer.Sparse OriginalKey := originalMerge283 ++ originalMerge284

theorem reducedMerge285Check : reducedMerge285 = Integer.Sparse.mergeBy masterLess reducedMerge283 reducedMerge284 := by decide +kernel

def reducedMerge286 : Integer.Sparse Master := [(Sum.inl 0, -150203509725911040000), (Sum.inl 1, -2364436421873971200000), (Sum.inl 2, -566183666864793600000), (Sum.inl 3, 6006685302013132800000), (Sum.inl 4, 2910184681498214400000), (Sum.inl 5, 159418097801625600000), (Sum.inl 12, 87174141478502400000), (Sum.inl 13, -145659664126771200000), (Sum.inl 26, 3077537227952947200000), (Sum.inl 27, -478254293404876800000), (Sum.inl 34, 87174141478502400000), (Sum.inl 35, 637672391206502400000), (Sum.inl 55, -1913017173619507200000)]

def originalMerge286 : Integer.Sparse OriginalKey := originalMerge282 ++ originalMerge285

theorem reducedMerge286Check : reducedMerge286 = Integer.Sparse.mergeBy masterLess reducedMerge282 reducedMerge285 := by decide +kernel

def reducedMerge287 : Integer.Sparse Master := [(Sum.inl 0, -74948919813734400000), (Sum.inl 1, -260874624761856000000), (Sum.inl 2, 45553407492096000000), (Sum.inl 3, 3014551219470336000000), (Sum.inl 4, 927554221375488000000), (Sum.inl 5, 115944277671936000000), (Sum.inl 6, -14493034708992000000), (Sum.inl 12, 927554221375488000000), (Sum.inl 13, 1391331332063232000000), (Sum.inl 26, 1391331332063232000000), (Sum.inl 27, -173916416507904000000), (Sum.inl 33, -1391331332063232000000), (Sum.inl 34, 927554221375488000000), (Sum.inl 35, 231888555343872000000), (Sum.inl 54, -695665666031616000000), (Sum.inl 65, -695665666031616000000), (Sum.inl 67, 231888555343872000000)]

def originalMerge287 : Integer.Sparse OriginalKey := originalTerm291 ++ originalTerm292

theorem reducedMerge287Check : reducedMerge287 = Integer.Sparse.mergeBy masterLess reducedTerm291 reducedTerm292 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
