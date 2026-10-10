import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData11
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData12
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData10
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData9

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge352 : Integer.Sparse Master := [(Sum.inl 0, 409967815066951680000), (Sum.inl 1, 989187992664883200000), (Sum.inl 2, -2905017550848000000), (Sum.inl 3, -416436157012377600000), (Sum.inl 4, -297154098649497600000), (Sum.inl 5, -67506010409779200000), (Sum.inl 6, 9710031640780800000), (Sum.inl 7, 772347519575654400000), (Sum.inl 12, -705408838660915200000), (Sum.inl 13, -466081518757478400000), (Sum.inl 23, 3681665592075878400000), (Sum.inl 24, 1865376018667929600000), (Sum.inl 25, 2805984355339468800000), (Sum.inl 26, -155360506252492800000), (Sum.inl 27, 1350522605072793600000), (Sum.inl 35, -155360506252492800000), (Sum.inl 51, 466081518757478400000), (Sum.inl 52, -155360506252492800000), (Sum.inl 54, 2805984355339468800000), (Sum.inl 55, 466081518757478400000), (Sum.inl 195, 1222065418420224000000)]

def originalMerge352 : Integer.Sparse OriginalKey := originalMerge348 ++ originalMerge351

theorem reducedMerge352Check : reducedMerge352 = Integer.Sparse.mergeBy masterLess reducedMerge348 reducedMerge351 := by decide +kernel

def reducedMerge353 : Integer.Sparse Master := [(Sum.inl 0, -488781616874987520000), (Sum.inl 1, 1689161086332518400000), (Sum.inl 2, -249477744918528000000), (Sum.inl 3, 5995402324918272000000), (Sum.inl 4, 619459071256166400000), (Sum.inl 5, -114656982644736000000), (Sum.inl 6, 9710031640780800000), (Sum.inl 7, 2101251433571942400000), (Sum.inl 12, 2145904855931289600000), (Sum.inl 13, -466081518757478400000), (Sum.inl 23, -4678165142500147200000), (Sum.inl 24, 1437280136390246400000), (Sum.inl 25, -5695553153551564800000), (Sum.inl 26, 1553411845472256000000), (Sum.inl 27, 1680443013357158400000), (Sum.inl 31, -477226723147776000000), (Sum.inl 33, -7890046220618956800000), (Sum.inl 35, -155360506252492800000), (Sum.inl 51, 1494281842370150400000), (Sum.inl 52, -155360506252492800000), (Sum.inl 54, -6307044441823641600000), (Sum.inl 55, 168977467588608000000), (Sum.inl 63, -3191825047722393600000), (Sum.inl 64, -2763729165444710400000), (Sum.inl 65, -4373118992587161600000), (Sum.inl 68, -611491288272076800000), (Sum.inl 124, -611491288272076800000), (Sum.inl 125, -1222982576544153600000), (Sum.inl 195, 3584653308149760000000), (Sum.inl 196, -611491288272076800000)]

def originalMerge353 : Integer.Sparse OriginalKey := originalMerge345 ++ originalMerge352

theorem reducedMerge353Check : reducedMerge353 = Integer.Sparse.mergeBy masterLess reducedMerge345 reducedMerge352 := by decide +kernel

def reducedMerge354 : Integer.Sparse Master := [(Sum.inl 0, 520296560434667520000), (Sum.inl 1, 4774289838900019200000), (Sum.inl 2, 258434248517222400000), (Sum.inl 3, 1374387124587724800000), (Sum.inl 4, -1158603712229376000000), (Sum.inl 5, -1150106051753164800000), (Sum.inl 6, 9710031640780800000), (Sum.inl 7, 1468982832552345600000), (Sum.inl 8, -137268216594432000000), (Sum.inl 12, -5368884966169804800000), (Sum.inl 13, -7692900934002278400000), (Sum.inl 23, 6668134970344243200000), (Sum.inl 24, 9473490651237580800000), (Sum.inl 25, -1905451634928844800000), (Sum.inl 26, 1553411845472256000000), (Sum.inl 27, -1436370379624857600000), (Sum.inl 30, 480011920625664000000), (Sum.inl 31, -222427211231232000000), (Sum.inl 33, 782137077674803200000), (Sum.inl 34, -1706152492361318400000), (Sum.inl 35, -155360506252492800000), (Sum.inl 51, 7082473091987865600000), (Sum.inl 52, -155360506252492800000), (Sum.inl 54, -2516942923200921600000), (Sum.inl 55, 12316863835629158400000), (Sum.inl 59, 4336091649146880000000), (Sum.inl 61, 4336091649146880000000), (Sum.inl 63, -3191825047722393600000), (Sum.inl 64, -2763729165444710400000), (Sum.inl 65, -4373118992587161600000), (Sum.inl 68, 4175910318904934400000), (Sum.inl 124, 130212675610214400000), (Sum.inl 125, -480481999906406400000), (Sum.inl 126, 740907351126835200000), (Sum.inl 194, -15476971187994624000000), (Sum.inl 195, -3995549729095680000000), (Sum.inl 196, -611491288272076800000), (Sum.inl 197, 742500576637747200000), (Sum.inl 236, -796612755456000000), (Sum.inl 263, -7580203037245440000000), (Sum.inl 486, -511192249344000000000), (Sum.inl 487, -8091395286589440000000)]

def originalMerge354 : Integer.Sparse OriginalKey := originalMerge339 ++ originalMerge353

theorem reducedMerge354Check : reducedMerge354 = Integer.Sparse.mergeBy masterLess reducedMerge339 reducedMerge353 := by decide +kernel

def reducedMerge355 : Integer.Sparse Master := [(Sum.inl 0, -315269594350018560000), (Sum.inl 1, 1005829238421504000000), (Sum.inl 2, 1348902524119449600000), (Sum.inl 3, 18601941822853939200000), (Sum.inl 4, 2051548268352307200000), (Sum.inl 5, -1158781200611328000000), (Sum.inl 6, 9710031640780800000), (Sum.inl 7, 1468982832552345600000), (Sum.inl 8, -137268216594432000000), (Sum.inl 12, -736156646004326400000), (Sum.inl 13, -3580983385310822400000), (Sum.inl 23, 6668134970344243200000), (Sum.inl 24, 9473490651237580800000), (Sum.inl 25, -1905451634928844800000), (Sum.inl 26, 10705809146631782400000), (Sum.inl 27, -1332713189025792000000), (Sum.inl 30, 480011920625664000000), (Sum.inl 31, -222427211231232000000), (Sum.inl 33, -9216088427866521600000), (Sum.inl 34, 1123950876217344000000), (Sum.inl 35, -155360506252492800000), (Sum.inl 51, 7082473091987865600000), (Sum.inl 52, -155360506252492800000), (Sum.inl 54, -2516942923200921600000), (Sum.inl 55, 12718262856705638400000), (Sum.inl 59, 4336091649146880000000), (Sum.inl 61, 4737490670223360000000), (Sum.inl 63, -3191825047722393600000), (Sum.inl 64, -2763729165444710400000), (Sum.inl 65, -4523616047539814400000), (Sum.inl 66, 163726796272435200000), (Sum.inl 67, 99099078259507200000), (Sum.inl 68, 4175910318904934400000), (Sum.inl 124, 130212675610214400000), (Sum.inl 125, -480481999906406400000), (Sum.inl 126, 740907351126835200000), (Sum.inl 194, -15476971187994624000000), (Sum.inl 195, -3995549729095680000000), (Sum.inl 196, -611491288272076800000), (Sum.inl 197, 742500576637747200000), (Sum.inl 236, -796612755456000000), (Sum.inl 263, -7580203037245440000000), (Sum.inl 486, -511192249344000000000), (Sum.inl 487, -8091395286589440000000)]

def originalMerge355 : Integer.Sparse OriginalKey := originalMerge325 ++ originalMerge354

theorem reducedMerge355Check : reducedMerge355 = Integer.Sparse.mergeBy masterLess reducedMerge325 reducedMerge354 := by decide +kernel

def reducedMerge356 : Integer.Sparse Master := [(Sum.inl 0, -308217491883141120000), (Sum.inl 1, -1951858241899776000000), (Sum.inl 2, 1246379487207321600000), (Sum.inl 3, 27114829412261068800000), (Sum.inl 4, 7391420113880678400000), (Sum.inl 5, -703278882973900800000), (Sum.inl 6, -224660517348556800000), (Sum.inl 7, 3884173107565363200000), (Sum.inl 8, -434974910998118400000), (Sum.inl 12, -2471053767288422400000), (Sum.inl 13, -6856745912974540800000), (Sum.inl 23, 8263542738692505600000), (Sum.inl 24, 9234541739114496000000), (Sum.inl 25, -3573932483152281600000), (Sum.inl 26, 17668263748217241600000), (Sum.inl 27, -2304195675199488000000), (Sum.inl 30, 480011920625664000000), (Sum.inl 31, -989215585247232000000), (Sum.inl 33, -7142445591669964800000), (Sum.inl 34, 1934358636684902400000), (Sum.inl 35, 625008104482406400000), (Sum.inl 51, 12892250870540697600000), (Sum.inl 52, -1659949495993958400000), (Sum.inl 54, -4585197888088473600000), (Sum.inl 55, 15300682106211532800000), (Sum.inl 59, 4336091649146880000000), (Sum.inl 61, 4737490670223360000000), (Sum.inl 63, -2498820660235468800000), (Sum.inl 64, -3941612373668659200000), (Sum.inl 65, -3294511642430668800000), (Sum.inl 66, -75222115850649600000), (Sum.inl 67, 317221934432256000000), (Sum.inl 68, 3947707853313638400000), (Sum.inl 81, -511192249344000000000), (Sum.inl 123, -5238740121366528000000), (Sum.inl 124, 130212675610214400000), (Sum.inl 125, -708684465497702400000), (Sum.inl 126, 740907351126835200000), (Sum.inl 194, -15476971187994624000000), (Sum.inl 195, -3995549729095680000000), (Sum.inl 196, -839693753863372800000), (Sum.inl 197, 742500576637747200000), (Sum.inl 236, -796612755456000000), (Sum.inl 263, -7580203037245440000000), (Sum.inl 264, -228202465591296000000), (Sum.inl 266, -228202465591296000000), (Sum.inl 486, -511192249344000000000), (Sum.inl 487, -8091395286589440000000)]

def originalMerge356 : Integer.Sparse OriginalKey := originalMerge296 ++ originalMerge355

theorem reducedMerge356Check : reducedMerge356 = Integer.Sparse.mergeBy masterLess reducedMerge296 reducedMerge355 := by decide +kernel

def reducedMerge357 : Integer.Sparse Master := [(Sum.inl 0, -498546586306621440000), (Sum.inl 1, -634872323080396800000), (Sum.inl 2, -6337611295948800000), (Sum.inl 3, 8704355885619609600000), (Sum.inl 4, 2188764193996800000000), (Sum.inl 5, 534515825907302400000), (Sum.inl 6, -66814478238412800000), (Sum.inl 7, -25350445183795200000), (Sum.inl 12, 5446560039808204800000), (Sum.inl 13, 2112712858445414400000), (Sum.inl 23, -3207094955443814400000), (Sum.inl 25, -6490241246439014400000), (Sum.inl 27, -801773738860953600000), (Sum.inl 31, -3283146290995200000000), (Sum.inl 33, -13132585163980800000000), (Sum.inl 35, -25350445183795200000), (Sum.inl 54, -6490241246439014400000), (Sum.inl 62, -3283146290995200000000)]

def originalMerge357 : Integer.Sparse OriginalKey := originalTerm360 ++ originalTerm361

theorem reducedMerge357Check : reducedMerge357 = Integer.Sparse.mergeBy masterLess reducedTerm360 reducedTerm361 := by decide +kernel

def reducedMerge358 : Integer.Sparse Master := [(Sum.inl 0, -474595174926028800000), (Sum.inl 1, -641345677507584000000), (Sum.inl 2, 6609097558425600000), (Sum.inl 3, 8238274366862131200000), (Sum.inl 4, 1981616852326809600000), (Sum.inl 5, 508622408198553600000), (Sum.inl 6, -63577801024819200000), (Sum.inl 7, -77137280601292800000), (Sum.inl 12, 5342986368973209600000), (Sum.inl 13, 2112712858445414400000), (Sum.inl 23, -3051734449191321600000), (Sum.inl 25, -6179520233934028800000), (Sum.inl 26, -207147341669990400000), (Sum.inl 27, -762933612297830400000), (Sum.inl 31, -3283146290995200000000), (Sum.inl 33, -13132585163980800000000), (Sum.inl 35, -77137280601292800000), (Sum.inl 54, -6334880740186521600000), (Sum.inl 62, -3283146290995200000000)]

def originalMerge358 : Integer.Sparse OriginalKey := originalTerm359 ++ originalMerge357

theorem reducedMerge358Check : reducedMerge358 = Integer.Sparse.mergeBy masterLess reducedTerm359 reducedMerge357 := by decide +kernel

def reducedMerge359 : Integer.Sparse Master := [(Sum.inl 0, 14617302494699520000), (Sum.inl 1, 86553812372428800000), (Sum.inl 2, -18688884670310400000), (Sum.inl 3, -487794533783961600000), (Sum.inl 4, -36749925221990400000), (Sum.inl 12, -243897266891980800000), (Sum.inl 13, -225522304280985600000)]

def originalMerge359 : Integer.Sparse OriginalKey := originalTerm362 ++ originalTerm363

theorem reducedMerge359Check : reducedMerge359 = Integer.Sparse.mergeBy masterLess reducedTerm362 reducedTerm363 := by decide +kernel

def reducedMerge360 : Integer.Sparse Master := [(Sum.inl 0, -555506660324044800000), (Sum.inl 1, -1666519980972134400000), (Sum.inl 3, 17776213130369433600000), (Sum.inl 4, 2962702188394905600000), (Sum.inl 12, 8888106565184716800000), (Sum.inl 13, 17776213130369433600000), (Sum.inl 32, 1481351094197452800000)]

def originalMerge360 : Integer.Sparse OriginalKey := originalTerm364 ++ originalTerm365

theorem reducedMerge360Check : reducedMerge360 = Integer.Sparse.mergeBy masterLess reducedTerm364 reducedTerm365 := by decide +kernel

def reducedMerge361 : Integer.Sparse Master := [(Sum.inl 0, -540889357829345280000), (Sum.inl 1, -1579966168599705600000), (Sum.inl 2, -18688884670310400000), (Sum.inl 3, 17288418596585472000000), (Sum.inl 4, 2925952263172915200000), (Sum.inl 12, 8644209298292736000000), (Sum.inl 13, 17550690826088448000000), (Sum.inl 32, 1481351094197452800000)]

def originalMerge361 : Integer.Sparse OriginalKey := originalMerge359 ++ originalMerge360

theorem reducedMerge361Check : reducedMerge361 = Integer.Sparse.mergeBy masterLess reducedMerge359 reducedMerge360 := by decide +kernel

def reducedMerge362 : Integer.Sparse Master := [(Sum.inl 0, -1015484532755374080000), (Sum.inl 1, -2221311846107289600000), (Sum.inl 2, -12079787111884800000), (Sum.inl 3, 25526692963447603200000), (Sum.inl 4, 4907569115499724800000), (Sum.inl 5, 508622408198553600000), (Sum.inl 6, -63577801024819200000), (Sum.inl 7, -77137280601292800000), (Sum.inl 12, 13987195667265945600000), (Sum.inl 13, 19663403684533862400000), (Sum.inl 23, -3051734449191321600000), (Sum.inl 25, -6179520233934028800000), (Sum.inl 26, -207147341669990400000), (Sum.inl 27, -762933612297830400000), (Sum.inl 31, -3283146290995200000000), (Sum.inl 32, 1481351094197452800000), (Sum.inl 33, -13132585163980800000000), (Sum.inl 35, -77137280601292800000), (Sum.inl 54, -6334880740186521600000), (Sum.inl 62, -3283146290995200000000)]

def originalMerge362 : Integer.Sparse OriginalKey := originalMerge358 ++ originalMerge361

theorem reducedMerge362Check : reducedMerge362 = Integer.Sparse.mergeBy masterLess reducedMerge358 reducedMerge361 := by decide +kernel

def reducedMerge363 : Integer.Sparse Master := []

def originalMerge363 : Integer.Sparse OriginalKey := originalTerm366 ++ originalTerm367

theorem reducedMerge363Check : reducedMerge363 = Integer.Sparse.mergeBy masterLess reducedTerm366 reducedTerm367 := by decide +kernel

def reducedMerge364 : Integer.Sparse Master := [(Sum.inl 0, 871627901874186240000), (Sum.inl 1, -2893644399263385600000), (Sum.inl 2, 1131507134121369600000), (Sum.inl 3, 9052057072970956800000), (Sum.inl 4, 2347656301360742400000), (Sum.inl 12, 4695312602721484800000), (Sum.inl 13, 4356744470249472000000)]

def originalMerge364 : Integer.Sparse OriginalKey := originalTerm368 ++ originalTerm369

theorem reducedMerge364Check : reducedMerge364 = Integer.Sparse.mergeBy masterLess reducedTerm368 reducedTerm369 := by decide +kernel

def reducedMerge365 : Integer.Sparse Master := [(Sum.inl 0, 871627901874186240000), (Sum.inl 1, -2893644399263385600000), (Sum.inl 2, 1131507134121369600000), (Sum.inl 3, 9052057072970956800000), (Sum.inl 4, 2347656301360742400000), (Sum.inl 12, 4695312602721484800000), (Sum.inl 13, 4356744470249472000000)]

def originalMerge365 : Integer.Sparse OriginalKey := originalMerge363 ++ originalMerge364

theorem reducedMerge365Check : reducedMerge365 = Integer.Sparse.mergeBy masterLess reducedMerge363 reducedMerge364 := by decide +kernel

def reducedMerge366 : Integer.Sparse Master := [(Sum.inl 0, -29819547878400000000), (Sum.inl 1, -111823304544000000000), (Sum.inl 2, 53249192640000000000), (Sum.inl 3, 766788374016000000000), (Sum.inl 4, 255596124672000000000), (Sum.inl 5, 42599354112000000000), (Sum.inl 6, -5324919264000000000), (Sum.inl 12, 340794832896000000000), (Sum.inl 26, 170397416448000000000), (Sum.inl 27, -63899031168000000000), (Sum.inl 33, -766788374016000000000), (Sum.inl 81, -255596124672000000000), (Sum.inl 195, 511192249344000000000)]

def originalMerge366 : Integer.Sparse OriginalKey := originalTerm370 ++ originalTerm371

theorem reducedMerge366Check : reducedMerge366 = Integer.Sparse.mergeBy masterLess reducedTerm370 reducedTerm371 := by decide +kernel

def reducedMerge367 : Integer.Sparse Master := [(Sum.inl 0, -143604706713108480000), (Sum.inl 1, -1030584292628889600000), (Sum.inl 2, -143722535672217600000), (Sum.inl 3, 1187246769124147200000), (Sum.inl 4, -185385633605222400000), (Sum.inl 5, 68409622020096000000), (Sum.inl 6, -17102405505024000000), (Sum.inl 7, 639969792963379200000), (Sum.inl 8, -92692816802611200000), (Sum.inl 12, 732662609765990400000), (Sum.inl 23, -1098993914648985600000), (Sum.inl 24, 278078450407833600000), (Sum.inl 27, -205228866060288000000)]

def originalMerge367 : Integer.Sparse OriginalKey := originalTerm372 ++ originalTerm373

theorem reducedMerge367Check : reducedMerge367 = Integer.Sparse.mergeBy masterLess reducedTerm372 reducedTerm373 := by decide +kernel

def reducedMerge368 : Integer.Sparse Master := [(Sum.inl 0, -173424254591508480000), (Sum.inl 1, -1142407597172889600000), (Sum.inl 2, -90473343032217600000), (Sum.inl 3, 1954035143140147200000), (Sum.inl 4, 70210491066777600000), (Sum.inl 5, 111008976132096000000), (Sum.inl 6, -22427324769024000000), (Sum.inl 7, 639969792963379200000), (Sum.inl 8, -92692816802611200000), (Sum.inl 12, 1073457442661990400000), (Sum.inl 23, -1098993914648985600000), (Sum.inl 24, 278078450407833600000), (Sum.inl 26, 170397416448000000000), (Sum.inl 27, -269127897228288000000), (Sum.inl 33, -766788374016000000000), (Sum.inl 81, -255596124672000000000), (Sum.inl 195, 511192249344000000000)]

def originalMerge368 : Integer.Sparse OriginalKey := originalMerge366 ++ originalMerge367

theorem reducedMerge368Check : reducedMerge368 = Integer.Sparse.mergeBy masterLess reducedMerge366 reducedMerge367 := by decide +kernel

def reducedMerge369 : Integer.Sparse Master := [(Sum.inl 0, 698203647282677760000), (Sum.inl 1, -4036051996436275200000), (Sum.inl 2, 1041033791089152000000), (Sum.inl 3, 11006092216111104000000), (Sum.inl 4, 2417866792427520000000), (Sum.inl 5, 111008976132096000000), (Sum.inl 6, -22427324769024000000), (Sum.inl 7, 639969792963379200000), (Sum.inl 8, -92692816802611200000), (Sum.inl 12, 5768770045383475200000), (Sum.inl 13, 4356744470249472000000), (Sum.inl 23, -1098993914648985600000), (Sum.inl 24, 278078450407833600000), (Sum.inl 26, 170397416448000000000), (Sum.inl 27, -269127897228288000000), (Sum.inl 33, -766788374016000000000), (Sum.inl 81, -255596124672000000000), (Sum.inl 195, 511192249344000000000)]

def originalMerge369 : Integer.Sparse OriginalKey := originalMerge365 ++ originalMerge368

theorem reducedMerge369Check : reducedMerge369 = Integer.Sparse.mergeBy masterLess reducedMerge365 reducedMerge368 := by decide +kernel

def reducedMerge370 : Integer.Sparse Master := [(Sum.inl 0, -317280885472696320000), (Sum.inl 1, -6257363842543564800000), (Sum.inl 2, 1028954003977267200000), (Sum.inl 3, 36532785179558707200000), (Sum.inl 4, 7325435907927244800000), (Sum.inl 5, 619631384330649600000), (Sum.inl 6, -86005125793843200000), (Sum.inl 7, 562832512362086400000), (Sum.inl 8, -92692816802611200000), (Sum.inl 12, 19755965712649420800000), (Sum.inl 13, 24020148154783334400000), (Sum.inl 23, -4150728363840307200000), (Sum.inl 24, 278078450407833600000), (Sum.inl 25, -6179520233934028800000), (Sum.inl 26, -36749925221990400000), (Sum.inl 27, -1032061509526118400000), (Sum.inl 31, -3283146290995200000000), (Sum.inl 32, 1481351094197452800000), (Sum.inl 33, -13899373537996800000000), (Sum.inl 35, -77137280601292800000), (Sum.inl 54, -6334880740186521600000), (Sum.inl 62, -3283146290995200000000), (Sum.inl 81, -255596124672000000000), (Sum.inl 195, 511192249344000000000)]

def originalMerge370 : Integer.Sparse OriginalKey := originalMerge362 ++ originalMerge369

theorem reducedMerge370Check : reducedMerge370 = Integer.Sparse.mergeBy masterLess reducedMerge362 reducedMerge369 := by decide +kernel

def reducedMerge371 : Integer.Sparse Master := [(Sum.inl 0, 108079205259110400000), (Sum.inl 1, -138447900864000000000), (Sum.inl 2, 280345449323520000000), (Sum.inl 3, -1061501984944128000000), (Sum.inl 4, -573350346584064000000), (Sum.inl 5, 42599354112000000000), (Sum.inl 6, -5324919264000000000), (Sum.inl 12, 255596124672000000000), (Sum.inl 25, 732227457540096000000), (Sum.inl 26, -743747763032064000000), (Sum.inl 27, -63899031168000000000), (Sum.inl 31, -511192249344000000000), (Sum.inl 33, -766788374016000000000), (Sum.inl 51, -255596124672000000000), (Sum.inl 55, -255596124672000000000), (Sum.inl 64, -255596124672000000000), (Sum.inl 123, -255596124672000000000)]

def originalMerge371 : Integer.Sparse OriginalKey := originalTerm375 ++ originalTerm376

theorem reducedMerge371Check : reducedMerge371 = Integer.Sparse.mergeBy masterLess reducedTerm375 reducedTerm376 := by decide +kernel

def reducedMerge372 : Integer.Sparse Master := [(Sum.inl 0, -117020684406528000000), (Sum.inl 1, 142926961218048000000), (Sum.inl 2, 245173591563264000000), (Sum.inl 3, 1189496911712256000000), (Sum.inl 4, 552149101744128000000), (Sum.inl 5, 323974216194048000000), (Sum.inl 6, -40496777024256000000), (Sum.inl 12, 255596124672000000000), (Sum.inl 25, -2644270887444480000000), (Sum.inl 26, 381751685296128000000), (Sum.inl 27, -485961324291072000000), (Sum.inl 31, -2199441421836288000000), (Sum.inl 33, -4143286719000576000000), (Sum.inl 51, -255596124672000000000), (Sum.inl 55, -255596124672000000000), (Sum.inl 63, -1688249172492288000000), (Sum.inl 64, -3632094469656576000000), (Sum.inl 123, -1943845297164288000000)]

def originalMerge372 : Integer.Sparse OriginalKey := originalTerm374 ++ originalMerge371

theorem reducedMerge372Check : reducedMerge372 = Integer.Sparse.mergeBy masterLess reducedTerm374 reducedMerge371 := by decide +kernel

def reducedMerge373 : Integer.Sparse Master := [(Sum.inl 0, -116702256056924160000), (Sum.inl 1, -700173508024166400000), (Sum.inl 2, 272612147899392000000), (Sum.inl 3, 4987195179724800000000), (Sum.inl 4, 1244397095888486400000), (Sum.inl 12, 2495198722557542400000), (Sum.inl 13, 2501603253338112000000), (Sum.inl 26, 622198547944243200000), (Sum.inl 33, -3752404880007168000000), (Sum.inl 34, 625400813334528000000)]

def originalMerge373 : Integer.Sparse OriginalKey := originalTerm377 ++ originalTerm378

theorem reducedMerge373Check : reducedMerge373 = Integer.Sparse.mergeBy masterLess reducedTerm377 reducedTerm378 := by decide +kernel

def reducedMerge374 : Integer.Sparse Master := [(Sum.inl 0, -102521110594129920000), (Sum.inl 1, -419404543339622400000), (Sum.inl 3, 4473648462289305600000), (Sum.inl 12, 2236824231144652800000), (Sum.inl 13, 4473648462289305600000), (Sum.inl 34, 745608077048217600000)]

def originalMerge374 : Integer.Sparse OriginalKey := originalTerm379 ++ originalTerm380

theorem reducedMerge374Check : reducedMerge374 = Integer.Sparse.mergeBy masterLess reducedTerm379 reducedTerm380 := by decide +kernel

def reducedMerge375 : Integer.Sparse Master := [(Sum.inl 0, -219223366651054080000), (Sum.inl 1, -1119578051363788800000), (Sum.inl 2, 272612147899392000000), (Sum.inl 3, 9460843642014105600000), (Sum.inl 4, 1244397095888486400000), (Sum.inl 12, 4732022953702195200000), (Sum.inl 13, 6975251715627417600000), (Sum.inl 26, 622198547944243200000), (Sum.inl 33, -3752404880007168000000), (Sum.inl 34, 1371008890382745600000)]

def originalMerge375 : Integer.Sparse OriginalKey := originalMerge373 ++ originalMerge374

theorem reducedMerge375Check : reducedMerge375 = Integer.Sparse.mergeBy masterLess reducedMerge373 reducedMerge374 := by decide +kernel

def reducedMerge376 : Integer.Sparse Master := [(Sum.inl 0, -336244051057582080000), (Sum.inl 1, -976651090145740800000), (Sum.inl 2, 517785739462656000000), (Sum.inl 3, 10650340553726361600000), (Sum.inl 4, 1796546197632614400000), (Sum.inl 5, 323974216194048000000), (Sum.inl 6, -40496777024256000000), (Sum.inl 12, 4987619078374195200000), (Sum.inl 13, 6975251715627417600000), (Sum.inl 25, -2644270887444480000000), (Sum.inl 26, 1003950233240371200000), (Sum.inl 27, -485961324291072000000), (Sum.inl 31, -2199441421836288000000), (Sum.inl 33, -7895691599007744000000), (Sum.inl 34, 1371008890382745600000), (Sum.inl 51, -255596124672000000000), (Sum.inl 55, -255596124672000000000), (Sum.inl 63, -1688249172492288000000), (Sum.inl 64, -3632094469656576000000), (Sum.inl 123, -1943845297164288000000)]

def originalMerge376 : Integer.Sparse OriginalKey := originalMerge372 ++ originalMerge375

theorem reducedMerge376Check : reducedMerge376 = Integer.Sparse.mergeBy masterLess reducedMerge372 reducedMerge375 := by decide +kernel

def reducedMerge377 : Integer.Sparse Master := [(Sum.inl 0, -417040697441894400000), (Sum.inl 1, 814679031059712000000), (Sum.inl 2, -601950718252800000000), (Sum.inl 3, -1552215971819520000000), (Sum.inl 4, 299221061271552000000), (Sum.inl 12, -888315883886592000000), (Sum.inl 25, -448831591907328000000), (Sum.inl 26, 74805265317888000000), (Sum.inl 31, -448831591907328000000), (Sum.inl 33, -673247387860992000000)]

def originalMerge377 : Integer.Sparse OriginalKey := originalTerm381 ++ originalTerm382

theorem reducedMerge377Check : reducedMerge377 = Integer.Sparse.mergeBy masterLess reducedTerm381 reducedTerm382 := by decide +kernel

def reducedMerge378 : Integer.Sparse Master := [(Sum.inl 0, 6519821153126400000), (Sum.inl 1, 773010677956608000000), (Sum.inl 2, -175200943341312000000), (Sum.inl 3, -2632817677012992000000), (Sum.inl 4, -1471216090595328000000), (Sum.inl 12, -980810727063552000000), (Sum.inl 13, -170397416448000000000), (Sum.inl 25, 991204169969664000000), (Sum.inl 26, -831200196427776000000), (Sum.inl 31, 511192249344000000000), (Sum.inl 33, 511192249344000000000), (Sum.inl 34, -170397416448000000000)]

def originalMerge378 : Integer.Sparse OriginalKey := originalTerm383 ++ originalTerm384

theorem reducedMerge378Check : reducedMerge378 = Integer.Sparse.mergeBy masterLess reducedTerm383 reducedTerm384 := by decide +kernel

def reducedMerge379 : Integer.Sparse Master := [(Sum.inl 0, -410520876288768000000), (Sum.inl 1, 1587689709016320000000), (Sum.inl 2, -777151661594112000000), (Sum.inl 3, -4185033648832512000000), (Sum.inl 4, -1171995029323776000000), (Sum.inl 12, -1869126610950144000000), (Sum.inl 13, -170397416448000000000), (Sum.inl 25, 542372578062336000000), (Sum.inl 26, -756394931109888000000), (Sum.inl 31, 62360657436672000000), (Sum.inl 33, -162055138516992000000), (Sum.inl 34, -170397416448000000000)]

def originalMerge379 : Integer.Sparse OriginalKey := originalMerge377 ++ originalMerge378

theorem reducedMerge379Check : reducedMerge379 = Integer.Sparse.mergeBy masterLess reducedMerge377 reducedMerge378 := by decide +kernel

def reducedMerge380 : Integer.Sparse Master := [(Sum.inl 0, 539672229290557440000), (Sum.inl 1, -1298598950947737600000), (Sum.inl 2, 768731428678348800000), (Sum.inl 3, 4099900952951193600000), (Sum.inl 4, 2096296884876902400000), (Sum.inl 12, 185385633605222400000), (Sum.inl 25, -5732733753815040000000), (Sum.inl 26, 1910911251271680000000)]

def originalMerge380 : Integer.Sparse OriginalKey := originalTerm385 ++ originalTerm386

theorem reducedMerge380Check : reducedMerge380 = Integer.Sparse.mergeBy masterLess reducedTerm385 reducedTerm386 := by decide +kernel

def reducedMerge381 : Integer.Sparse Master := [(Sum.inl 0, -216685718854778880000), (Sum.inl 1, 987302876468428800000), (Sum.inl 2, -120607639378329600000), (Sum.inl 3, -981182396075212800000), (Sum.inl 4, 10880854032384000000), (Sum.inl 12, -992063250107596800000)]

def originalMerge381 : Integer.Sparse OriginalKey := originalTerm387 ++ originalTerm388

theorem reducedMerge381Check : reducedMerge381 = Integer.Sparse.mergeBy masterLess reducedTerm387 reducedTerm388 := by decide +kernel

def reducedMerge382 : Integer.Sparse Master := [(Sum.inl 0, 322986510435778560000), (Sum.inl 1, -311296074479308800000), (Sum.inl 2, 648123789300019200000), (Sum.inl 3, 3118718556875980800000), (Sum.inl 4, 2107177738909286400000), (Sum.inl 12, -806677616502374400000), (Sum.inl 25, -5732733753815040000000), (Sum.inl 26, 1910911251271680000000)]

def originalMerge382 : Integer.Sparse OriginalKey := originalMerge380 ++ originalMerge381

theorem reducedMerge382Check : reducedMerge382 = Integer.Sparse.mergeBy masterLess reducedMerge380 reducedMerge381 := by decide +kernel

def reducedMerge383 : Integer.Sparse Master := [(Sum.inl 0, -87534365852989440000), (Sum.inl 1, 1276393634537011200000), (Sum.inl 2, -129027872294092800000), (Sum.inl 3, -1066315091956531200000), (Sum.inl 4, 935182709585510400000), (Sum.inl 12, -2675804227452518400000), (Sum.inl 13, -170397416448000000000), (Sum.inl 25, -5190361175752704000000), (Sum.inl 26, 1154516320161792000000), (Sum.inl 31, 62360657436672000000), (Sum.inl 33, -162055138516992000000), (Sum.inl 34, -170397416448000000000)]

def originalMerge383 : Integer.Sparse OriginalKey := originalMerge379 ++ originalMerge382

theorem reducedMerge383Check : reducedMerge383 = Integer.Sparse.mergeBy masterLess reducedMerge379 reducedMerge382 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
