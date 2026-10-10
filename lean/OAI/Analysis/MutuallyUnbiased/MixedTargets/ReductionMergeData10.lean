import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData10
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData11
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData9

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge320 : Integer.Sparse Master := [(Sum.inl 0, -35354062026178560000), (Sum.inl 1, 35766600081408000000), (Sum.inl 2, -38869008791961600000), (Sum.inl 3, 231557201893785600000), (Sum.inl 4, 231557201893785600000), (Sum.inl 26, 231557201893785600000), (Sum.inl 27, 13643899689369600000), (Sum.inl 66, 54575598757478400000)]

def originalMerge320 : Integer.Sparse OriginalKey := originalTerm325 ++ originalTerm326

theorem reducedMerge320Check : reducedMerge320 = Integer.Sparse.mergeBy masterLess reducedTerm325 reducedTerm326 := by decide +kernel

def reducedMerge321 : Integer.Sparse Master := [(Sum.inl 0, -498275509616640000000), (Sum.inl 1, -3447334958376960000000), (Sum.inl 2, -275981579274240000000), (Sum.inl 3, 2367502508851200000000), (Sum.inl 26, 1024101379768320000000)]

def originalMerge321 : Integer.Sparse OriginalKey := originalTerm327 ++ originalTerm328

theorem reducedMerge321Check : reducedMerge321 = Integer.Sparse.mergeBy masterLess reducedTerm327 reducedTerm328 := by decide +kernel

def reducedMerge322 : Integer.Sparse Master := [(Sum.inl 0, -533629571642818560000), (Sum.inl 1, -3411568358295552000000), (Sum.inl 2, -314850588066201600000), (Sum.inl 3, 2599059710744985600000), (Sum.inl 4, 231557201893785600000), (Sum.inl 26, 1255658581662105600000), (Sum.inl 27, 13643899689369600000), (Sum.inl 66, 54575598757478400000)]

def originalMerge322 : Integer.Sparse OriginalKey := originalMerge320 ++ originalMerge321

theorem reducedMerge322Check : reducedMerge322 = Integer.Sparse.mergeBy masterLess reducedMerge320 reducedMerge321 := by decide +kernel

def reducedMerge323 : Integer.Sparse Master := [(Sum.inl 0, -871364503945635840000), (Sum.inl 1, -3803943320261683200000), (Sum.inl 2, 750270279919104000000), (Sum.inl 3, 9375145993182412800000), (Sum.inl 4, 1365109644629606400000), (Sum.inl 12, 4508981396965785600000), (Sum.inl 13, 4289903056967270400000), (Sum.inl 26, 2389211024397926400000), (Sum.inl 27, 13643899689369600000), (Sum.inl 33, -9040331700449280000000), (Sum.inl 34, 1133552442735820800000), (Sum.inl 66, 54575598757478400000)]

def originalMerge323 : Integer.Sparse OriginalKey := originalMerge319 ++ originalMerge322

theorem reducedMerge323Check : reducedMerge323 = Integer.Sparse.mergeBy masterLess reducedMerge319 reducedMerge322 := by decide +kernel

def reducedMerge324 : Integer.Sparse Master := [(Sum.inl 0, -1266975881067939840000), (Sum.inl 1, -3684703117929523200000), (Sum.inl 2, 65775574629273600000), (Sum.inl 3, 11828815231035801600000), (Sum.inl 4, 1365109644629606400000), (Sum.inl 12, 4508981396965785600000), (Sum.inl 13, 4289903056967270400000), (Sum.inl 26, 6587277139744358400000), (Sum.inl 27, 77631744024576000000), (Sum.inl 33, -9040331700449280000000), (Sum.inl 34, 3109571451747532800000), (Sum.inl 65, 255951377340825600000), (Sum.inl 66, 54575598757478400000)]

def originalMerge324 : Integer.Sparse OriginalKey := originalMerge316 ++ originalMerge323

theorem reducedMerge324Check : reducedMerge324 = Integer.Sparse.mergeBy masterLess reducedMerge316 reducedMerge323 := by decide +kernel

def reducedMerge325 : Integer.Sparse Master := [(Sum.inl 0, -835566154784686080000), (Sum.inl 1, -3768460600478515200000), (Sum.inl 2, 1090468275602227200000), (Sum.inl 3, 17227554698266214400000), (Sum.inl 4, 3210151980581683200000), (Sum.inl 5, -8675148858163200000), (Sum.inl 12, 4632728320165478400000), (Sum.inl 13, 4111917548691456000000), (Sum.inl 26, 9152397301159526400000), (Sum.inl 27, 103657190599065600000), (Sum.inl 33, -9998225505541324800000), (Sum.inl 34, 2830103368578662400000), (Sum.inl 55, 401399021076480000000), (Sum.inl 61, 401399021076480000000), (Sum.inl 65, -150497054952652800000), (Sum.inl 66, 163726796272435200000), (Sum.inl 67, 99099078259507200000)]

def originalMerge325 : Integer.Sparse OriginalKey := originalMerge310 ++ originalMerge324

theorem reducedMerge325Check : reducedMerge325 = Integer.Sparse.mergeBy masterLess reducedMerge310 reducedMerge324 := by decide +kernel

def reducedMerge326 : Integer.Sparse Master := []

def originalMerge326 : Integer.Sparse OriginalKey := originalTerm330 ++ originalTerm331

theorem reducedMerge326Check : reducedMerge326 = Integer.Sparse.mergeBy masterLess reducedTerm330 reducedTerm331 := by decide +kernel

def reducedMerge327 : Integer.Sparse Master := []

def originalMerge327 : Integer.Sparse OriginalKey := originalTerm329 ++ originalMerge326

theorem reducedMerge327Check : reducedMerge327 = Integer.Sparse.mergeBy masterLess reducedTerm329 reducedMerge326 := by decide +kernel

def reducedMerge328 : Integer.Sparse Master := [(Sum.inl 0, 435448749692436480000), (Sum.inl 1, 1361416340938752000000), (Sum.inl 2, -200852781992755200000), (Sum.inl 3, 8332101988968038400000), (Sum.inl 34, -1706152492361318400000)]

def originalMerge328 : Integer.Sparse OriginalKey := originalTerm332 ++ originalTerm333

theorem reducedMerge328Check : reducedMerge328 = Integer.Sparse.mergeBy masterLess reducedTerm332 reducedTerm333 := by decide +kernel

def reducedMerge329 : Integer.Sparse Master := [(Sum.inl 0, -119491913318400000), (Sum.inl 1, -33192198144000000), (Sum.inl 2, -99576594432000000), (Sum.inl 5, 132768792576000000), (Sum.inl 31, -796612755456000000), (Sum.inl 51, -1593225510912000000), (Sum.inl 68, -796612755456000000), (Sum.inl 124, -796612755456000000), (Sum.inl 126, -1593225510912000000), (Sum.inl 236, -796612755456000000)]

def originalMerge329 : Integer.Sparse OriginalKey := originalTerm334 ++ originalTerm335

theorem reducedMerge329Check : reducedMerge329 = Integer.Sparse.mergeBy masterLess reducedTerm334 reducedTerm335 := by decide +kernel

def reducedMerge330 : Integer.Sparse Master := [(Sum.inl 0, 435329257779118080000), (Sum.inl 1, 1361383148740608000000), (Sum.inl 2, -200952358587187200000), (Sum.inl 3, 8332101988968038400000), (Sum.inl 5, 132768792576000000), (Sum.inl 31, -796612755456000000), (Sum.inl 34, -1706152492361318400000), (Sum.inl 51, -1593225510912000000), (Sum.inl 68, -796612755456000000), (Sum.inl 124, -796612755456000000), (Sum.inl 126, -1593225510912000000), (Sum.inl 236, -796612755456000000)]

def originalMerge330 : Integer.Sparse OriginalKey := originalMerge328 ++ originalMerge329

theorem reducedMerge330Check : reducedMerge330 = Integer.Sparse.mergeBy masterLess reducedMerge328 reducedMerge329 := by decide +kernel

def reducedMerge331 : Integer.Sparse Master := [(Sum.inl 0, 435329257779118080000), (Sum.inl 1, 1361383148740608000000), (Sum.inl 2, -200952358587187200000), (Sum.inl 3, 8332101988968038400000), (Sum.inl 5, 132768792576000000), (Sum.inl 31, -796612755456000000), (Sum.inl 34, -1706152492361318400000), (Sum.inl 51, -1593225510912000000), (Sum.inl 68, -796612755456000000), (Sum.inl 124, -796612755456000000), (Sum.inl 126, -1593225510912000000), (Sum.inl 236, -796612755456000000)]

def originalMerge331 : Integer.Sparse OriginalKey := originalMerge327 ++ originalMerge330

theorem reducedMerge331Check : reducedMerge331 = Integer.Sparse.mergeBy masterLess reducedMerge327 reducedMerge330 := by decide +kernel

def reducedMerge332 : Integer.Sparse Master := [(Sum.inl 0, 99506072663746560000), (Sum.inl 1, 105486393722572800000), (Sum.inl 2, 187143131495577600000), (Sum.inl 3, -1160398185298329600000), (Sum.inl 4, -332698900436582400000), (Sum.inl 5, -270823852383436800000), (Sum.inl 7, -495000384425164800000), (Sum.inl 12, -332698900436582400000), (Sum.inl 23, 1485001153275494400000), (Sum.inl 24, 1485001153275494400000), (Sum.inl 27, 63899031168000000000), (Sum.inl 31, 255596124672000000000), (Sum.inl 51, 1253692825981747200000), (Sum.inl 55, 1740597277947494400000), (Sum.inl 68, 998096701309747200000), (Sum.inl 124, 742500576637747200000), (Sum.inl 125, 742500576637747200000), (Sum.inl 126, 742500576637747200000), (Sum.inl 194, -511192249344000000000), (Sum.inl 197, 742500576637747200000), (Sum.inl 486, -511192249344000000000), (Sum.inl 487, -511192249344000000000)]

def originalMerge332 : Integer.Sparse OriginalKey := originalTerm336 ++ originalTerm337

theorem reducedMerge332Check : reducedMerge332 = Integer.Sparse.mergeBy masterLess reducedTerm336 reducedTerm337 := by decide +kernel

def reducedMerge333 : Integer.Sparse Master := [(Sum.inl 0, 298257961581619200000), (Sum.inl 1, -116878364757504000000), (Sum.inl 2, 1134405482837760000000), (Sum.inl 3, -1263367172874240000000), (Sum.inl 5, -1263367172874240000000), (Sum.inl 12, -1263367172874240000000), (Sum.inl 23, 8060214957871104000000), (Sum.inl 24, 4750125359874048000000), (Sum.inl 25, 3790101518622720000000), (Sum.inl 27, 707519419342848000000), (Sum.inl 30, 480011920625664000000), (Sum.inl 54, 3790101518622720000000), (Sum.inl 55, 4270113439248384000000), (Sum.inl 68, 3790101518622720000000), (Sum.inl 194, -480011920625664000000), (Sum.inl 195, -7580203037245440000000), (Sum.inl 263, -7580203037245440000000), (Sum.inl 487, -7580203037245440000000)]

def originalMerge333 : Integer.Sparse OriginalKey := originalTerm338 ++ originalTerm339

theorem reducedMerge333Check : reducedMerge333 = Integer.Sparse.mergeBy masterLess reducedTerm338 reducedTerm339 := by decide +kernel

def reducedMerge334 : Integer.Sparse Master := [(Sum.inl 0, 397764034245365760000), (Sum.inl 1, -11391971034931200000), (Sum.inl 2, 1321548614333337600000), (Sum.inl 3, -2423765358172569600000), (Sum.inl 4, -332698900436582400000), (Sum.inl 5, -1534191025257676800000), (Sum.inl 7, -495000384425164800000), (Sum.inl 12, -1596066073310822400000), (Sum.inl 23, 9545216111146598400000), (Sum.inl 24, 6235126513149542400000), (Sum.inl 25, 3790101518622720000000), (Sum.inl 27, 771418450510848000000), (Sum.inl 30, 480011920625664000000), (Sum.inl 31, 255596124672000000000), (Sum.inl 51, 1253692825981747200000), (Sum.inl 54, 3790101518622720000000), (Sum.inl 55, 6010710717195878400000), (Sum.inl 68, 4788198219932467200000), (Sum.inl 124, 742500576637747200000), (Sum.inl 125, 742500576637747200000), (Sum.inl 126, 742500576637747200000), (Sum.inl 194, -991204169969664000000), (Sum.inl 195, -7580203037245440000000), (Sum.inl 197, 742500576637747200000), (Sum.inl 263, -7580203037245440000000), (Sum.inl 486, -511192249344000000000), (Sum.inl 487, -8091395286589440000000)]

def originalMerge334 : Integer.Sparse OriginalKey := originalMerge332 ++ originalMerge333

theorem reducedMerge334Check : reducedMerge334 = Integer.Sparse.mergeBy masterLess reducedMerge332 reducedMerge333 := by decide +kernel

def reducedMerge335 : Integer.Sparse Master := [(Sum.inl 0, -87659818793164800000), (Sum.inl 1, 347319837978624000000), (Sum.inl 2, -189781121940480000000), (Sum.inl 3, -411804649783296000000), (Sum.inl 5, 137268216594432000000), (Sum.inl 7, -137268216594432000000), (Sum.inl 8, -137268216594432000000), (Sum.inl 12, -137268216594432000000), (Sum.inl 23, 1801084001697792000000), (Sum.inl 24, 1801084001697792000000), (Sum.inl 27, -1350813001273344000000), (Sum.inl 55, 1801084001697792000000)]

def originalMerge335 : Integer.Sparse OriginalKey := originalTerm340 ++ originalTerm341

theorem reducedMerge335Check : reducedMerge335 = Integer.Sparse.mergeBy masterLess reducedTerm340 reducedTerm341 := by decide +kernel

def reducedMerge336 : Integer.Sparse Master := [(Sum.inl 0, 263644704078336000000), (Sum.inl 1, 1387817736883200000000), (Sum.inl 2, -422903140369920000000), (Sum.inl 3, -10117547181342720000000), (Sum.inl 4, -1445363883048960000000), (Sum.inl 5, 361340970762240000000), (Sum.inl 12, -5781455532195840000000), (Sum.inl 13, -7226819415244800000000), (Sum.inl 27, -2537418842219520000000), (Sum.inl 33, 8672183298293760000000), (Sum.inl 51, 4336091649146880000000), (Sum.inl 55, 4336091649146880000000), (Sum.inl 59, 4336091649146880000000), (Sum.inl 61, 4336091649146880000000), (Sum.inl 194, -14485767018024960000000)]

def originalMerge336 : Integer.Sparse OriginalKey := originalTerm342 ++ originalTerm343

theorem reducedMerge336Check : reducedMerge336 = Integer.Sparse.mergeBy masterLess reducedTerm342 reducedTerm343 := by decide +kernel

def reducedMerge337 : Integer.Sparse Master := [(Sum.inl 0, 175984885285171200000), (Sum.inl 1, 1735137574861824000000), (Sum.inl 2, -612684262310400000000), (Sum.inl 3, -10529351831126016000000), (Sum.inl 4, -1445363883048960000000), (Sum.inl 5, 498609187356672000000), (Sum.inl 7, -137268216594432000000), (Sum.inl 8, -137268216594432000000), (Sum.inl 12, -5918723748790272000000), (Sum.inl 13, -7226819415244800000000), (Sum.inl 23, 1801084001697792000000), (Sum.inl 24, 1801084001697792000000), (Sum.inl 27, -3888231843492864000000), (Sum.inl 33, 8672183298293760000000), (Sum.inl 51, 4336091649146880000000), (Sum.inl 55, 6137175650844672000000), (Sum.inl 59, 4336091649146880000000), (Sum.inl 61, 4336091649146880000000), (Sum.inl 194, -14485767018024960000000)]

def originalMerge337 : Integer.Sparse OriginalKey := originalMerge335 ++ originalMerge336

theorem reducedMerge337Check : reducedMerge337 = Integer.Sparse.mergeBy masterLess reducedMerge335 reducedMerge336 := by decide +kernel

def reducedMerge338 : Integer.Sparse Master := [(Sum.inl 0, 573748919530536960000), (Sum.inl 1, 1723745603826892800000), (Sum.inl 2, 708864352022937600000), (Sum.inl 3, -12953117189298585600000), (Sum.inl 4, -1778062783485542400000), (Sum.inl 5, -1035581837901004800000), (Sum.inl 7, -632268601019596800000), (Sum.inl 8, -137268216594432000000), (Sum.inl 12, -7514789822101094400000), (Sum.inl 13, -7226819415244800000000), (Sum.inl 23, 11346300112844390400000), (Sum.inl 24, 8036210514847334400000), (Sum.inl 25, 3790101518622720000000), (Sum.inl 27, -3116813392982016000000), (Sum.inl 30, 480011920625664000000), (Sum.inl 31, 255596124672000000000), (Sum.inl 33, 8672183298293760000000), (Sum.inl 51, 5589784475128627200000), (Sum.inl 54, 3790101518622720000000), (Sum.inl 55, 12147886368040550400000), (Sum.inl 59, 4336091649146880000000), (Sum.inl 61, 4336091649146880000000), (Sum.inl 68, 4788198219932467200000), (Sum.inl 124, 742500576637747200000), (Sum.inl 125, 742500576637747200000), (Sum.inl 126, 742500576637747200000), (Sum.inl 194, -15476971187994624000000), (Sum.inl 195, -7580203037245440000000), (Sum.inl 197, 742500576637747200000), (Sum.inl 263, -7580203037245440000000), (Sum.inl 486, -511192249344000000000), (Sum.inl 487, -8091395286589440000000)]

def originalMerge338 : Integer.Sparse OriginalKey := originalMerge334 ++ originalMerge337

theorem reducedMerge338Check : reducedMerge338 = Integer.Sparse.mergeBy masterLess reducedMerge334 reducedMerge337 := by decide +kernel

def reducedMerge339 : Integer.Sparse Master := [(Sum.inl 0, 1009078177309655040000), (Sum.inl 1, 3085128752567500800000), (Sum.inl 2, 507911993435750400000), (Sum.inl 3, -4621015200330547200000), (Sum.inl 4, -1778062783485542400000), (Sum.inl 5, -1035449069108428800000), (Sum.inl 7, -632268601019596800000), (Sum.inl 8, -137268216594432000000), (Sum.inl 12, -7514789822101094400000), (Sum.inl 13, -7226819415244800000000), (Sum.inl 23, 11346300112844390400000), (Sum.inl 24, 8036210514847334400000), (Sum.inl 25, 3790101518622720000000), (Sum.inl 27, -3116813392982016000000), (Sum.inl 30, 480011920625664000000), (Sum.inl 31, 254799511916544000000), (Sum.inl 33, 8672183298293760000000), (Sum.inl 34, -1706152492361318400000), (Sum.inl 51, 5588191249617715200000), (Sum.inl 54, 3790101518622720000000), (Sum.inl 55, 12147886368040550400000), (Sum.inl 59, 4336091649146880000000), (Sum.inl 61, 4336091649146880000000), (Sum.inl 68, 4787401607177011200000), (Sum.inl 124, 741703963882291200000), (Sum.inl 125, 742500576637747200000), (Sum.inl 126, 740907351126835200000), (Sum.inl 194, -15476971187994624000000), (Sum.inl 195, -7580203037245440000000), (Sum.inl 197, 742500576637747200000), (Sum.inl 236, -796612755456000000), (Sum.inl 263, -7580203037245440000000), (Sum.inl 486, -511192249344000000000), (Sum.inl 487, -8091395286589440000000)]

def originalMerge339 : Integer.Sparse OriginalKey := originalMerge331 ++ originalMerge338

theorem reducedMerge339Check : reducedMerge339 = Integer.Sparse.mergeBy masterLess reducedMerge331 reducedMerge338 := by decide +kernel

def reducedMerge340 : Integer.Sparse Master := [(Sum.inl 0, -394398639338618880000), (Sum.inl 1, 929896244482867200000), (Sum.inl 2, 123782636165529600000), (Sum.inl 3, -2058574844893593600000), (Sum.inl 4, -1029287422446796800000), (Sum.inl 5, -276835022172979200000), (Sum.inl 12, -1029287422446796800000), (Sum.inl 27, 771965566835097600000), (Sum.inl 31, 234157998735360000000), (Sum.inl 51, 3322020266075750400000), (Sum.inl 55, 3087862267340390400000)]

def originalMerge340 : Integer.Sparse OriginalKey := originalTerm345 ++ originalTerm346

theorem reducedMerge340Check : reducedMerge340 = Integer.Sparse.mergeBy masterLess reducedTerm345 reducedTerm346 := by decide +kernel

def reducedMerge341 : Integer.Sparse Master := [(Sum.inl 0, -357197492519239680000), (Sum.inl 1, 929896244482867200000), (Sum.inl 2, 172731513559449600000), (Sum.inl 3, -2293529456384409600000), (Sum.inl 4, -1185923830107340800000), (Sum.inl 5, -315994124088115200000), (Sum.inl 12, -1107605626277068800000), (Sum.inl 27, 830704219707801600000), (Sum.inl 31, 704067221716992000000), (Sum.inl 51, 3791929489057382400000), (Sum.inl 55, 3322816878831206400000)]

def originalMerge341 : Integer.Sparse OriginalKey := originalTerm344 ++ originalMerge340

theorem reducedMerge341Check : reducedMerge341 = Integer.Sparse.mergeBy masterLess reducedTerm344 reducedMerge340 := by decide +kernel

def reducedMerge342 : Integer.Sparse Master := [(Sum.inl 0, -73126548994867200000), (Sum.inl 1, -262429512029798400000), (Sum.inl 2, -149052084443136000000), (Sum.inl 3, 815321717696102400000), (Sum.inl 5, 203830429424025600000), (Sum.inl 7, 407660858848051200000), (Sum.inl 12, 407660858848051200000), (Sum.inl 23, -1651078458821836800000), (Sum.inl 24, -428095882277683200000), (Sum.inl 25, -611491288272076800000), (Sum.inl 27, -305745644136038400000), (Sum.inl 54, -1222982576544153600000), (Sum.inl 55, -856191764555366400000), (Sum.inl 63, -428095882277683200000), (Sum.inl 65, -428095882277683200000), (Sum.inl 68, -611491288272076800000), (Sum.inl 124, -611491288272076800000), (Sum.inl 125, -1222982576544153600000), (Sum.inl 196, -611491288272076800000)]

def originalMerge342 : Integer.Sparse OriginalKey := originalTerm347 ++ originalTerm348

theorem reducedMerge342Check : reducedMerge342 = Integer.Sparse.mergeBy masterLess reducedTerm347 reducedTerm348 := by decide +kernel

def reducedMerge343 : Integer.Sparse Master := [(Sum.inl 0, -468425390427832320000), (Sum.inl 1, 32506361214566400000), (Sum.inl 2, -270252156483993600000), (Sum.inl 3, 7890046220618956800000), (Sum.inl 4, 2102537000013004800000), (Sum.inl 5, 65012722429132800000), (Sum.inl 7, 921243055148236800000), (Sum.inl 12, 3551258462021222400000), (Sum.inl 23, -6708752275754188800000), (Sum.inl 25, -7890046220618956800000), (Sum.inl 26, 1708772351724748800000), (Sum.inl 27, -195038167287398400000), (Sum.inl 31, -1181293944864768000000), (Sum.inl 33, -7890046220618956800000), (Sum.inl 51, -2763729165444710400000), (Sum.inl 54, -7890046220618956800000), (Sum.inl 55, -2763729165444710400000), (Sum.inl 63, -2763729165444710400000), (Sum.inl 64, -2763729165444710400000), (Sum.inl 65, -3945023110309478400000), (Sum.inl 195, 2362587889729536000000)]

def originalMerge343 : Integer.Sparse OriginalKey := originalTerm349 ++ originalTerm350

theorem reducedMerge343Check : reducedMerge343 = Integer.Sparse.mergeBy masterLess reducedTerm349 reducedTerm350 := by decide +kernel

def reducedMerge344 : Integer.Sparse Master := [(Sum.inl 0, -541551939422699520000), (Sum.inl 1, -229923150815232000000), (Sum.inl 2, -419304240927129600000), (Sum.inl 3, 8705367938315059200000), (Sum.inl 4, 2102537000013004800000), (Sum.inl 5, 268843151853158400000), (Sum.inl 7, 1328903913996288000000), (Sum.inl 12, 3958919320869273600000), (Sum.inl 23, -8359830734576025600000), (Sum.inl 24, -428095882277683200000), (Sum.inl 25, -8501537508891033600000), (Sum.inl 26, 1708772351724748800000), (Sum.inl 27, -500783811423436800000), (Sum.inl 31, -1181293944864768000000), (Sum.inl 33, -7890046220618956800000), (Sum.inl 51, -2763729165444710400000), (Sum.inl 54, -9113028797163110400000), (Sum.inl 55, -3619920930000076800000), (Sum.inl 63, -3191825047722393600000), (Sum.inl 64, -2763729165444710400000), (Sum.inl 65, -4373118992587161600000), (Sum.inl 68, -611491288272076800000), (Sum.inl 124, -611491288272076800000), (Sum.inl 125, -1222982576544153600000), (Sum.inl 195, 2362587889729536000000), (Sum.inl 196, -611491288272076800000)]

def originalMerge344 : Integer.Sparse OriginalKey := originalMerge342 ++ originalMerge343

theorem reducedMerge344Check : reducedMerge344 = Integer.Sparse.mergeBy masterLess reducedMerge342 reducedMerge343 := by decide +kernel

def reducedMerge345 : Integer.Sparse Master := [(Sum.inl 0, -898749431941939200000), (Sum.inl 1, 699973093667635200000), (Sum.inl 2, -246572727367680000000), (Sum.inl 3, 6411838481930649600000), (Sum.inl 4, 916613169905664000000), (Sum.inl 5, -47150972234956800000), (Sum.inl 7, 1328903913996288000000), (Sum.inl 12, 2851313694592204800000), (Sum.inl 23, -8359830734576025600000), (Sum.inl 24, -428095882277683200000), (Sum.inl 25, -8501537508891033600000), (Sum.inl 26, 1708772351724748800000), (Sum.inl 27, 329920408284364800000), (Sum.inl 31, -477226723147776000000), (Sum.inl 33, -7890046220618956800000), (Sum.inl 51, 1028200323612672000000), (Sum.inl 54, -9113028797163110400000), (Sum.inl 55, -297104051168870400000), (Sum.inl 63, -3191825047722393600000), (Sum.inl 64, -2763729165444710400000), (Sum.inl 65, -4373118992587161600000), (Sum.inl 68, -611491288272076800000), (Sum.inl 124, -611491288272076800000), (Sum.inl 125, -1222982576544153600000), (Sum.inl 195, 2362587889729536000000), (Sum.inl 196, -611491288272076800000)]

def originalMerge345 : Integer.Sparse OriginalKey := originalMerge341 ++ originalMerge344

theorem reducedMerge345Check : reducedMerge345 = Integer.Sparse.mergeBy masterLess reducedMerge341 reducedMerge344 := by decide +kernel

def reducedMerge346 : Integer.Sparse Master := [(Sum.inl 0, -212895502375772160000), (Sum.inl 1, -1187081229306470400000), (Sum.inl 2, 116916014805811200000), (Sum.inl 3, -935328118446489600000), (Sum.inl 5, -182912637177446400000), (Sum.inl 12, -935328118446489600000), (Sum.inl 23, 2805984355339468800000), (Sum.inl 25, 2805984355339468800000), (Sum.inl 27, 548737911532339200000), (Sum.inl 54, 2805984355339468800000), (Sum.inl 195, 1222065418420224000000)]

def originalMerge346 : Integer.Sparse OriginalKey := originalTerm351 ++ originalTerm352

theorem reducedMerge346Check : reducedMerge346 = Integer.Sparse.mergeBy masterLess reducedTerm351 reducedTerm352 := by decide +kernel

def reducedMerge347 : Integer.Sparse Master := [(Sum.inl 0, 223196513997864960000), (Sum.inl 1, 947562969611059200000), (Sum.inl 2, -94715158074163200000), (Sum.inl 3, 1515442529186611200000), (Sum.inl 4, 123440932100505600000), (Sum.inl 5, 181715257892044800000), (Sum.inl 7, 726861031568179200000), (Sum.inl 12, 696000798543052800000), (Sum.inl 23, -1995421696553779200000), (Sum.inl 24, -185161398150758400000), (Sum.inl 27, -545145773676134400000)]

def originalMerge347 : Integer.Sparse OriginalKey := originalTerm353 ++ originalTerm354

theorem reducedMerge347Check : reducedMerge347 = Integer.Sparse.mergeBy masterLess reducedTerm353 reducedTerm354 := by decide +kernel

def reducedMerge348 : Integer.Sparse Master := [(Sum.inl 0, 10301011622092800000), (Sum.inl 1, -239518259695411200000), (Sum.inl 2, 22200856731648000000), (Sum.inl 3, 580114410740121600000), (Sum.inl 4, 123440932100505600000), (Sum.inl 5, -1197379285401600000), (Sum.inl 7, 726861031568179200000), (Sum.inl 12, -239327319903436800000), (Sum.inl 23, 810562658785689600000), (Sum.inl 24, -185161398150758400000), (Sum.inl 25, 2805984355339468800000), (Sum.inl 27, 3592137856204800000), (Sum.inl 54, 2805984355339468800000), (Sum.inl 195, 1222065418420224000000)]

def originalMerge348 : Integer.Sparse OriginalKey := originalMerge346 ++ originalMerge347

theorem reducedMerge348Check : reducedMerge348 = Integer.Sparse.mergeBy masterLess reducedMerge346 reducedMerge347 := by decide +kernel

def reducedMerge349 : Integer.Sparse Master := [(Sum.inl 0, 165729809568153600000), (Sum.inl 1, 1375850451135283200000), (Sum.inl 2, -5685811000934400000), (Sum.inl 3, 90972976014950400000), (Sum.inl 4, 45486488007475200000), (Sum.inl 5, 11371622001868800000), (Sum.inl 7, 45486488007475200000), (Sum.inl 23, 2871102933290188800000), (Sum.inl 24, -136459464022425600000), (Sum.inl 27, 683660867316940800000)]

def originalMerge349 : Integer.Sparse OriginalKey := originalTerm355 ++ originalTerm356

theorem reducedMerge349Check : reducedMerge349 = Integer.Sparse.mergeBy masterLess reducedTerm355 reducedTerm356 := by decide +kernel

def reducedMerge350 : Integer.Sparse Master := [(Sum.inl 0, 233936993876705280000), (Sum.inl 1, -147144198774988800000), (Sum.inl 2, -19420063281561600000), (Sum.inl 3, -1087523543767449600000), (Sum.inl 4, -466081518757478400000), (Sum.inl 5, -77680253126246400000), (Sum.inl 6, 9710031640780800000), (Sum.inl 12, -466081518757478400000), (Sum.inl 13, -466081518757478400000), (Sum.inl 24, 2186996880841113600000), (Sum.inl 26, -155360506252492800000), (Sum.inl 27, 663269599899648000000), (Sum.inl 35, -155360506252492800000), (Sum.inl 51, 466081518757478400000), (Sum.inl 52, -155360506252492800000), (Sum.inl 55, 466081518757478400000)]

def originalMerge350 : Integer.Sparse OriginalKey := originalTerm357 ++ originalTerm358

theorem reducedMerge350Check : reducedMerge350 = Integer.Sparse.mergeBy masterLess reducedTerm357 reducedTerm358 := by decide +kernel

def reducedMerge351 : Integer.Sparse Master := [(Sum.inl 0, 399666803444858880000), (Sum.inl 1, 1228706252360294400000), (Sum.inl 2, -25105874282496000000), (Sum.inl 3, -996550567752499200000), (Sum.inl 4, -420595030750003200000), (Sum.inl 5, -66308631124377600000), (Sum.inl 6, 9710031640780800000), (Sum.inl 7, 45486488007475200000), (Sum.inl 12, -466081518757478400000), (Sum.inl 13, -466081518757478400000), (Sum.inl 23, 2871102933290188800000), (Sum.inl 24, 2050537416818688000000), (Sum.inl 26, -155360506252492800000), (Sum.inl 27, 1346930467216588800000), (Sum.inl 35, -155360506252492800000), (Sum.inl 51, 466081518757478400000), (Sum.inl 52, -155360506252492800000), (Sum.inl 55, 466081518757478400000)]

def originalMerge351 : Integer.Sparse OriginalKey := originalMerge349 ++ originalMerge350

theorem reducedMerge351Check : reducedMerge351 = Integer.Sparse.mergeBy masterLess reducedMerge349 reducedMerge350 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
