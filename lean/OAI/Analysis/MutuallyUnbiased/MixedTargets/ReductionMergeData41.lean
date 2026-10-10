import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData41
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData42
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData39
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData40

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge1312 : Integer.Sparse Master := [(Sum.inr 3475, -4633408883520700416000), (Sum.inr 3476, 1856913308405858304000), (Sum.inr 3480, -4726817018446086144000), (Sum.inr 3488, -416003421044736000000), (Sum.inr 3493, 4958849630270914560000), (Sum.inr 3496, -8093713655448207360000), (Sum.inr 3497, -416003421044736000000), (Sum.inr 3505, 7799955337720627200000), (Sum.inr 3506, -3146577964923617280000), (Sum.inr 3508, -1421726643557498880000), (Sum.inr 3509, 7390298065975050240000), (Sum.inr 3510, -1331003266183987200000), (Sum.inr 3511, -270860476671590400000), (Sum.inr 3512, -3141806478252244992000), (Sum.inr 3516, 1646462429022781440000)]

def originalMerge1312 : Integer.Sparse OriginalKey := originalMerge1304 ++ originalMerge1311

theorem reducedMerge1312Check : reducedMerge1312 = Integer.Sparse.mergeBy masterLess reducedMerge1304 reducedMerge1311 := by decide +kernel

def reducedMerge1313 : Integer.Sparse Master := [(Sum.inr 3415, -1559990074286407680000), (Sum.inr 3418, -354715844131160064000), (Sum.inr 3419, 814999240525381632000), (Sum.inr 3451, 744619799330684928000), (Sum.inr 3452, 4783674936826920960000), (Sum.inr 3454, 5808432531870646272000), (Sum.inr 3458, 23220776228880384000), (Sum.inr 3461, 2229127337632333824000), (Sum.inr 3462, -2370794412740640768000), (Sum.inr 3463, -3066113985645182976000), (Sum.inr 3464, 3058373744961454080000), (Sum.inr 3465, -722635406229897216000), (Sum.inr 3466, -3632663000341315584000), (Sum.inr 3472, 506711554922151936000), (Sum.inr 3474, -1835451633733337088000), (Sum.inr 3475, -4633408883520700416000), (Sum.inr 3476, 1856913308405858304000), (Sum.inr 3480, -4726817018446086144000), (Sum.inr 3488, -416003421044736000000), (Sum.inr 3493, 4958849630270914560000), (Sum.inr 3496, -8093713655448207360000), (Sum.inr 3497, -416003421044736000000), (Sum.inr 3505, 7799955337720627200000), (Sum.inr 3506, -3146577964923617280000), (Sum.inr 3508, -1421726643557498880000), (Sum.inr 3509, 7390298065975050240000), (Sum.inr 3510, -1331003266183987200000), (Sum.inr 3511, -270860476671590400000), (Sum.inr 3512, -3141806478252244992000), (Sum.inr 3516, 1646462429022781440000)]

def originalMerge1313 : Integer.Sparse OriginalKey := originalMerge1298 ++ originalMerge1312

theorem reducedMerge1313Check : reducedMerge1313 = Integer.Sparse.mergeBy masterLess reducedMerge1298 reducedMerge1312 := by decide +kernel

def reducedMerge1314 : Integer.Sparse Master := [(Sum.inr 3289, 2654462499211837440000), (Sum.inr 3290, 1619043489526579200000), (Sum.inr 3291, -1521451825330913280000), (Sum.inr 3294, -8946502007384309760000), (Sum.inr 3295, -3789395265230733312000), (Sum.inr 3296, -9536788940949946368000), (Sum.inr 3297, -1889903966198169600000), (Sum.inr 3298, 752859079780663296000), (Sum.inr 3302, -1389583379072286720000), (Sum.inr 3303, -565455270900989952000), (Sum.inr 3306, -186994987012915200000), (Sum.inr 3365, 4501291376384409600000), (Sum.inr 3375, 654308882759024640000), (Sum.inr 3376, -4735033992735621120000), (Sum.inr 3378, 4935862034835701760000), (Sum.inr 3379, -379671498467573760000), (Sum.inr 3380, 2452540759969628160000), (Sum.inr 3388, 28541892592926720000), (Sum.inr 3390, -2426340427298242560000), (Sum.inr 3391, -3915341740423249920000), (Sum.inr 3392, -57083785185853440000), (Sum.inr 3394, 6542432374534963200000), (Sum.inr 3395, 16453451164259450880000), (Sum.inr 3396, 10440815232685178880000), (Sum.inr 3397, -684291540819640320000), (Sum.inr 3406, 652996879610019840000), (Sum.inr 3407, 3344441963460820992000), (Sum.inr 3408, -1985415998552211456000), (Sum.inr 3413, -2989726119329660928000), (Sum.inr 3414, 355417517501448192000), (Sum.inr 3415, -1559990074286407680000), (Sum.inr 3418, -354715844131160064000), (Sum.inr 3419, 814999240525381632000), (Sum.inr 3451, 744619799330684928000), (Sum.inr 3452, 4783674936826920960000), (Sum.inr 3454, 5808432531870646272000), (Sum.inr 3458, 23220776228880384000), (Sum.inr 3461, 2229127337632333824000), (Sum.inr 3462, -2370794412740640768000), (Sum.inr 3463, -3066113985645182976000), (Sum.inr 3464, 3058373744961454080000), (Sum.inr 3465, -722635406229897216000), (Sum.inr 3466, -3632663000341315584000), (Sum.inr 3472, 506711554922151936000), (Sum.inr 3474, -1835451633733337088000), (Sum.inr 3475, -4633408883520700416000), (Sum.inr 3476, 1856913308405858304000), (Sum.inr 3480, -4726817018446086144000), (Sum.inr 3488, -416003421044736000000), (Sum.inr 3493, 4958849630270914560000), (Sum.inr 3496, -8093713655448207360000), (Sum.inr 3497, -416003421044736000000), (Sum.inr 3505, 7799955337720627200000), (Sum.inr 3506, -3146577964923617280000), (Sum.inr 3508, -1421726643557498880000), (Sum.inr 3509, 7390298065975050240000), (Sum.inr 3510, -1331003266183987200000), (Sum.inr 3511, -270860476671590400000), (Sum.inr 3512, -3141806478252244992000), (Sum.inr 3516, 1646462429022781440000)]

def originalMerge1314 : Integer.Sparse OriginalKey := originalMerge1284 ++ originalMerge1313

theorem reducedMerge1314Check : reducedMerge1314 = Integer.Sparse.mergeBy masterLess reducedMerge1284 reducedMerge1313 := by decide +kernel

def reducedMerge1315 : Integer.Sparse Master := [(Sum.inl 0, -117343595247530803200), (Sum.inl 1, 361420713534246912000), (Sum.inl 2, 96476820425330688000), (Sum.inl 3, 96957509274501120000), (Sum.inl 4, 477168826924597248000), (Sum.inl 12, -40555765569650688000), (Sum.inl 13, -212621157529288704000), (Sum.inl 26, 573455482913488896000), (Sum.inr 3118, 6748651458342420480000), (Sum.inr 3127, -2711226786498478080000), (Sum.inr 3128, -814591422450892800000), (Sum.inr 3129, -6439173843973570560000), (Sum.inr 3130, -2879161744832593920000), (Sum.inr 3131, -16011049661961338880000), (Sum.inr 3132, 814591422450892800000), (Sum.inr 3133, -616542244556636160000), (Sum.inr 3134, 9470910448608215040000), (Sum.inr 3136, 6932067331465543680000), (Sum.inr 3137, 5023829814312960000000), (Sum.inr 3138, 8259752936279900160000), (Sum.inr 3155, 2995585454962114560000), (Sum.inr 3156, -4348786044622602240000), (Sum.inr 3158, -2995585454962114560000), (Sum.inr 3161, 519512794327941120000), (Sum.inr 3162, -6260504027114373120000), (Sum.inr 3163, 10736042127096545280000), (Sum.inr 3164, -9579839035999518720000), (Sum.inr 3170, 6664563524103045120000), (Sum.inr 3172, 9579839035999518720000), (Sum.inr 3174, -10880841765483970560000), (Sum.inr 3179, -8772590858152181760000), (Sum.inr 3180, -8754560341097840640000), (Sum.inr 3189, -1174798139719680000000), (Sum.inr 3196, 6466249688175083520000), (Sum.inr 3197, 1899117244195799040000), (Sum.inr 3198, 419312052798750720000), (Sum.inr 3199, 6894774206306058240000), (Sum.inr 3202, 11475455859405619200000), (Sum.inr 3221, -12951213345010483200000), (Sum.inr 3222, -12438782405973245952000), (Sum.inr 3255, 1331003266183987200000), (Sum.inr 3257, 5933039869919232000000), (Sum.inr 3258, -1531997227471011840000), (Sum.inr 3259, 9156607353476481024000), (Sum.inr 3260, 1182595905074626560000), (Sum.inr 3261, 270860476671590400000), (Sum.inr 3262, 1979586319187312640000), (Sum.inr 3266, 3863114615263002624000), (Sum.inr 3267, 53914691091824640000), (Sum.inr 3268, -2204937138861047808000), (Sum.inr 3271, -2066297949707894784000), (Sum.inr 3272, -992147345927700480000), (Sum.inr 3288, 305084947161415680000), (Sum.inr 3289, 2654462499211837440000), (Sum.inr 3290, 1619043489526579200000), (Sum.inr 3291, -1521451825330913280000), (Sum.inr 3294, -8946502007384309760000), (Sum.inr 3295, -3789395265230733312000), (Sum.inr 3296, -9536788940949946368000), (Sum.inr 3297, -1889903966198169600000), (Sum.inr 3298, 752859079780663296000), (Sum.inr 3302, -1389583379072286720000), (Sum.inr 3303, -565455270900989952000), (Sum.inr 3306, -186994987012915200000), (Sum.inr 3365, 4501291376384409600000), (Sum.inr 3375, 654308882759024640000), (Sum.inr 3376, -4735033992735621120000), (Sum.inr 3378, 4935862034835701760000), (Sum.inr 3379, -379671498467573760000), (Sum.inr 3380, 2452540759969628160000), (Sum.inr 3388, 28541892592926720000), (Sum.inr 3390, -2426340427298242560000), (Sum.inr 3391, -3915341740423249920000), (Sum.inr 3392, -57083785185853440000), (Sum.inr 3394, 6542432374534963200000), (Sum.inr 3395, 16453451164259450880000), (Sum.inr 3396, 10440815232685178880000), (Sum.inr 3397, -684291540819640320000), (Sum.inr 3406, 652996879610019840000), (Sum.inr 3407, 3344441963460820992000), (Sum.inr 3408, -1985415998552211456000), (Sum.inr 3413, -2989726119329660928000), (Sum.inr 3414, 355417517501448192000), (Sum.inr 3415, -1559990074286407680000), (Sum.inr 3418, -354715844131160064000), (Sum.inr 3419, 814999240525381632000), (Sum.inr 3451, 744619799330684928000), (Sum.inr 3452, 4783674936826920960000), (Sum.inr 3454, 5808432531870646272000), (Sum.inr 3458, 23220776228880384000), (Sum.inr 3461, 2229127337632333824000), (Sum.inr 3462, -2370794412740640768000), (Sum.inr 3463, -3066113985645182976000), (Sum.inr 3464, 3058373744961454080000), (Sum.inr 3465, -722635406229897216000), (Sum.inr 3466, -3632663000341315584000), (Sum.inr 3472, 506711554922151936000), (Sum.inr 3474, -1835451633733337088000), (Sum.inr 3475, -4633408883520700416000), (Sum.inr 3476, 1856913308405858304000), (Sum.inr 3480, -4726817018446086144000), (Sum.inr 3488, -416003421044736000000), (Sum.inr 3493, 4958849630270914560000), (Sum.inr 3496, -8093713655448207360000), (Sum.inr 3497, -416003421044736000000), (Sum.inr 3505, 7799955337720627200000), (Sum.inr 3506, -3146577964923617280000), (Sum.inr 3508, -1421726643557498880000), (Sum.inr 3509, 7390298065975050240000), (Sum.inr 3510, -1331003266183987200000), (Sum.inr 3511, -270860476671590400000), (Sum.inr 3512, -3141806478252244992000), (Sum.inr 3516, 1646462429022781440000)]

def originalMerge1315 : Integer.Sparse OriginalKey := originalMerge1255 ++ originalMerge1314

theorem reducedMerge1315Check : reducedMerge1315 = Integer.Sparse.mergeBy masterLess reducedMerge1255 reducedMerge1314 := by decide +kernel

def reducedMerge1316 : Integer.Sparse Master := [(Sum.inr 3519, -500927005576101888000), (Sum.inr 3523, -12294580299389337600000)]

def originalMerge1316 : Integer.Sparse OriginalKey := originalTerm1320 ++ originalTerm1321

theorem reducedMerge1316Check : reducedMerge1316 = Integer.Sparse.mergeBy masterLess reducedTerm1320 reducedTerm1321 := by decide +kernel

def reducedMerge1317 : Integer.Sparse Master := [(Sum.inr 3517, 3031883170345451520000), (Sum.inr 3519, -500927005576101888000), (Sum.inr 3523, -12294580299389337600000)]

def originalMerge1317 : Integer.Sparse OriginalKey := originalTerm1319 ++ originalMerge1316

theorem reducedMerge1317Check : reducedMerge1317 = Integer.Sparse.mergeBy masterLess reducedTerm1319 reducedMerge1316 := by decide +kernel

def reducedMerge1318 : Integer.Sparse Master := [(Sum.inr 3524, -1072771597873446912000)]

def originalMerge1318 : Integer.Sparse OriginalKey := originalTerm1322 ++ originalTerm1323

theorem reducedMerge1318Check : reducedMerge1318 = Integer.Sparse.mergeBy masterLess reducedTerm1322 reducedTerm1323 := by decide +kernel

def reducedMerge1319 : Integer.Sparse Master := [(Sum.inr 3526, -8846701964077694976000), (Sum.inr 3529, 2431584286271078400000)]

def originalMerge1319 : Integer.Sparse OriginalKey := originalTerm1324 ++ originalTerm1325

theorem reducedMerge1319Check : reducedMerge1319 = Integer.Sparse.mergeBy masterLess reducedTerm1324 reducedTerm1325 := by decide +kernel

def reducedMerge1320 : Integer.Sparse Master := [(Sum.inr 3524, -1072771597873446912000), (Sum.inr 3526, -8846701964077694976000), (Sum.inr 3529, 2431584286271078400000)]

def originalMerge1320 : Integer.Sparse OriginalKey := originalMerge1318 ++ originalMerge1319

theorem reducedMerge1320Check : reducedMerge1320 = Integer.Sparse.mergeBy masterLess reducedMerge1318 reducedMerge1319 := by decide +kernel

def reducedMerge1321 : Integer.Sparse Master := [(Sum.inr 3517, 3031883170345451520000), (Sum.inr 3519, -500927005576101888000), (Sum.inr 3523, -12294580299389337600000), (Sum.inr 3524, -1072771597873446912000), (Sum.inr 3526, -8846701964077694976000), (Sum.inr 3529, 2431584286271078400000)]

def originalMerge1321 : Integer.Sparse OriginalKey := originalMerge1317 ++ originalMerge1320

theorem reducedMerge1321Check : reducedMerge1321 = Integer.Sparse.mergeBy masterLess reducedMerge1317 reducedMerge1320 := by decide +kernel

def reducedMerge1322 : Integer.Sparse Master := [(Sum.inr 3530, 6558674437762449408000), (Sum.inr 3532, -1598770106249379840000)]

def originalMerge1322 : Integer.Sparse OriginalKey := originalTerm1326 ++ originalTerm1327

theorem reducedMerge1322Check : reducedMerge1322 = Integer.Sparse.mergeBy masterLess reducedTerm1326 reducedTerm1327 := by decide +kernel

def reducedMerge1323 : Integer.Sparse Master := [(Sum.inr 3533, -1975281871324446720000), (Sum.inr 3534, 26110149656309268480000)]

def originalMerge1323 : Integer.Sparse OriginalKey := originalTerm1328 ++ originalTerm1329

theorem reducedMerge1323Check : reducedMerge1323 = Integer.Sparse.mergeBy masterLess reducedTerm1328 reducedTerm1329 := by decide +kernel

def reducedMerge1324 : Integer.Sparse Master := [(Sum.inr 3530, 6558674437762449408000), (Sum.inr 3532, -1598770106249379840000), (Sum.inr 3533, -1975281871324446720000), (Sum.inr 3534, 26110149656309268480000)]

def originalMerge1324 : Integer.Sparse OriginalKey := originalMerge1322 ++ originalMerge1323

theorem reducedMerge1324Check : reducedMerge1324 = Integer.Sparse.mergeBy masterLess reducedMerge1322 reducedMerge1323 := by decide +kernel

def reducedMerge1325 : Integer.Sparse Master := [(Sum.inr 3535, 4491472530225364992000), (Sum.inr 3537, 7698731041103413248000)]

def originalMerge1325 : Integer.Sparse OriginalKey := originalTerm1330 ++ originalTerm1331

theorem reducedMerge1325Check : reducedMerge1325 = Integer.Sparse.mergeBy masterLess reducedTerm1330 reducedTerm1331 := by decide +kernel

def reducedMerge1326 : Integer.Sparse Master := [(Sum.inr 3538, 1252704393088598016000), (Sum.inr 3539, 6590198986965909504000)]

def originalMerge1326 : Integer.Sparse OriginalKey := originalTerm1332 ++ originalTerm1333

theorem reducedMerge1326Check : reducedMerge1326 = Integer.Sparse.mergeBy masterLess reducedTerm1332 reducedTerm1333 := by decide +kernel

def reducedMerge1327 : Integer.Sparse Master := [(Sum.inr 3535, 4491472530225364992000), (Sum.inr 3537, 7698731041103413248000), (Sum.inr 3538, 1252704393088598016000), (Sum.inr 3539, 6590198986965909504000)]

def originalMerge1327 : Integer.Sparse OriginalKey := originalMerge1325 ++ originalMerge1326

theorem reducedMerge1327Check : reducedMerge1327 = Integer.Sparse.mergeBy masterLess reducedMerge1325 reducedMerge1326 := by decide +kernel

def reducedMerge1328 : Integer.Sparse Master := [(Sum.inr 3530, 6558674437762449408000), (Sum.inr 3532, -1598770106249379840000), (Sum.inr 3533, -1975281871324446720000), (Sum.inr 3534, 26110149656309268480000), (Sum.inr 3535, 4491472530225364992000), (Sum.inr 3537, 7698731041103413248000), (Sum.inr 3538, 1252704393088598016000), (Sum.inr 3539, 6590198986965909504000)]

def originalMerge1328 : Integer.Sparse OriginalKey := originalMerge1324 ++ originalMerge1327

theorem reducedMerge1328Check : reducedMerge1328 = Integer.Sparse.mergeBy masterLess reducedMerge1324 reducedMerge1327 := by decide +kernel

def reducedMerge1329 : Integer.Sparse Master := [(Sum.inr 3517, 3031883170345451520000), (Sum.inr 3519, -500927005576101888000), (Sum.inr 3523, -12294580299389337600000), (Sum.inr 3524, -1072771597873446912000), (Sum.inr 3526, -8846701964077694976000), (Sum.inr 3529, 2431584286271078400000), (Sum.inr 3530, 6558674437762449408000), (Sum.inr 3532, -1598770106249379840000), (Sum.inr 3533, -1975281871324446720000), (Sum.inr 3534, 26110149656309268480000), (Sum.inr 3535, 4491472530225364992000), (Sum.inr 3537, 7698731041103413248000), (Sum.inr 3538, 1252704393088598016000), (Sum.inr 3539, 6590198986965909504000)]

def originalMerge1329 : Integer.Sparse OriginalKey := originalMerge1321 ++ originalMerge1328

theorem reducedMerge1329Check : reducedMerge1329 = Integer.Sparse.mergeBy masterLess reducedMerge1321 reducedMerge1328 := by decide +kernel

def reducedMerge1330 : Integer.Sparse Master := [(Sum.inr 3541, -2683554743866687488000), (Sum.inr 3542, -1438088403369590784000)]

def originalMerge1330 : Integer.Sparse OriginalKey := originalTerm1335 ++ originalTerm1336

theorem reducedMerge1330Check : reducedMerge1330 = Integer.Sparse.mergeBy masterLess reducedTerm1335 reducedTerm1336 := by decide +kernel

def reducedMerge1331 : Integer.Sparse Master := [(Sum.inr 3540, 442881254805405696000), (Sum.inr 3541, -2683554743866687488000), (Sum.inr 3542, -1438088403369590784000)]

def originalMerge1331 : Integer.Sparse OriginalKey := originalTerm1334 ++ originalMerge1330

theorem reducedMerge1331Check : reducedMerge1331 = Integer.Sparse.mergeBy masterLess reducedTerm1334 reducedMerge1330 := by decide +kernel

def reducedMerge1332 : Integer.Sparse Master := [(Sum.inr 3543, -3946797413223727104000), (Sum.inr 3544, -2488508247260528640000)]

def originalMerge1332 : Integer.Sparse OriginalKey := originalTerm1337 ++ originalTerm1338

theorem reducedMerge1332Check : reducedMerge1332 = Integer.Sparse.mergeBy masterLess reducedTerm1337 reducedTerm1338 := by decide +kernel

def reducedMerge1333 : Integer.Sparse Master := [(Sum.inr 3548, -1028860950356951040000)]

def originalMerge1333 : Integer.Sparse OriginalKey := originalTerm1339 ++ originalTerm1340

theorem reducedMerge1333Check : reducedMerge1333 = Integer.Sparse.mergeBy masterLess reducedTerm1339 reducedTerm1340 := by decide +kernel

def reducedMerge1334 : Integer.Sparse Master := [(Sum.inr 3543, -3946797413223727104000), (Sum.inr 3544, -2488508247260528640000), (Sum.inr 3548, -1028860950356951040000)]

def originalMerge1334 : Integer.Sparse OriginalKey := originalMerge1332 ++ originalMerge1333

theorem reducedMerge1334Check : reducedMerge1334 = Integer.Sparse.mergeBy masterLess reducedMerge1332 reducedMerge1333 := by decide +kernel

def reducedMerge1335 : Integer.Sparse Master := [(Sum.inr 3540, 442881254805405696000), (Sum.inr 3541, -2683554743866687488000), (Sum.inr 3542, -1438088403369590784000), (Sum.inr 3543, -3946797413223727104000), (Sum.inr 3544, -2488508247260528640000), (Sum.inr 3548, -1028860950356951040000)]

def originalMerge1335 : Integer.Sparse OriginalKey := originalMerge1331 ++ originalMerge1334

theorem reducedMerge1335Check : reducedMerge1335 = Integer.Sparse.mergeBy masterLess reducedMerge1331 reducedMerge1334 := by decide +kernel

def reducedMerge1336 : Integer.Sparse Master := [(Sum.inr 3549, 1255758373127946240000), (Sum.inr 3553, -1133832859511095296000)]

def originalMerge1336 : Integer.Sparse OriginalKey := originalTerm1341 ++ originalTerm1342

theorem reducedMerge1336Check : reducedMerge1336 = Integer.Sparse.mergeBy masterLess reducedTerm1341 reducedTerm1342 := by decide +kernel

def reducedMerge1337 : Integer.Sparse Master := [(Sum.inr 3554, -5933039869919232000000), (Sum.inr 3555, -5743947411554107392000)]

def originalMerge1337 : Integer.Sparse OriginalKey := originalTerm1343 ++ originalTerm1344

theorem reducedMerge1337Check : reducedMerge1337 = Integer.Sparse.mergeBy masterLess reducedTerm1343 reducedTerm1344 := by decide +kernel

def reducedMerge1338 : Integer.Sparse Master := [(Sum.inr 3549, 1255758373127946240000), (Sum.inr 3553, -1133832859511095296000), (Sum.inr 3554, -5933039869919232000000), (Sum.inr 3555, -5743947411554107392000)]

def originalMerge1338 : Integer.Sparse OriginalKey := originalMerge1336 ++ originalMerge1337

theorem reducedMerge1338Check : reducedMerge1338 = Integer.Sparse.mergeBy masterLess reducedMerge1336 reducedMerge1337 := by decide +kernel

def reducedMerge1339 : Integer.Sparse Master := [(Sum.inr 3556, -1645301575619444736000), (Sum.inr 3557, 900394580334477312000)]

def originalMerge1339 : Integer.Sparse OriginalKey := originalTerm1345 ++ originalTerm1346

theorem reducedMerge1339Check : reducedMerge1339 = Integer.Sparse.mergeBy masterLess reducedTerm1345 reducedTerm1346 := by decide +kernel

def reducedMerge1340 : Integer.Sparse Master := [(Sum.inr 3558, 8704054146298871808000), (Sum.inr 3562, 2987270009704415232000)]

def originalMerge1340 : Integer.Sparse OriginalKey := originalTerm1347 ++ originalTerm1348

theorem reducedMerge1340Check : reducedMerge1340 = Integer.Sparse.mergeBy masterLess reducedTerm1347 reducedTerm1348 := by decide +kernel

def reducedMerge1341 : Integer.Sparse Master := [(Sum.inr 3556, -1645301575619444736000), (Sum.inr 3557, 900394580334477312000), (Sum.inr 3558, 8704054146298871808000), (Sum.inr 3562, 2987270009704415232000)]

def originalMerge1341 : Integer.Sparse OriginalKey := originalMerge1339 ++ originalMerge1340

theorem reducedMerge1341Check : reducedMerge1341 = Integer.Sparse.mergeBy masterLess reducedMerge1339 reducedMerge1340 := by decide +kernel

def reducedMerge1342 : Integer.Sparse Master := [(Sum.inr 3549, 1255758373127946240000), (Sum.inr 3553, -1133832859511095296000), (Sum.inr 3554, -5933039869919232000000), (Sum.inr 3555, -5743947411554107392000), (Sum.inr 3556, -1645301575619444736000), (Sum.inr 3557, 900394580334477312000), (Sum.inr 3558, 8704054146298871808000), (Sum.inr 3562, 2987270009704415232000)]

def originalMerge1342 : Integer.Sparse OriginalKey := originalMerge1338 ++ originalMerge1341

theorem reducedMerge1342Check : reducedMerge1342 = Integer.Sparse.mergeBy masterLess reducedMerge1338 reducedMerge1341 := by decide +kernel

def reducedMerge1343 : Integer.Sparse Master := [(Sum.inr 3540, 442881254805405696000), (Sum.inr 3541, -2683554743866687488000), (Sum.inr 3542, -1438088403369590784000), (Sum.inr 3543, -3946797413223727104000), (Sum.inr 3544, -2488508247260528640000), (Sum.inr 3548, -1028860950356951040000), (Sum.inr 3549, 1255758373127946240000), (Sum.inr 3553, -1133832859511095296000), (Sum.inr 3554, -5933039869919232000000), (Sum.inr 3555, -5743947411554107392000), (Sum.inr 3556, -1645301575619444736000), (Sum.inr 3557, 900394580334477312000), (Sum.inr 3558, 8704054146298871808000), (Sum.inr 3562, 2987270009704415232000)]

def originalMerge1343 : Integer.Sparse OriginalKey := originalMerge1335 ++ originalMerge1342

theorem reducedMerge1343Check : reducedMerge1343 = Integer.Sparse.mergeBy masterLess reducedMerge1335 reducedMerge1342 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
