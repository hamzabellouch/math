import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData39
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData40
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData38

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge1248 : Integer.Sparse Master := [(Sum.inr 3261, 270860476671590400000), (Sum.inr 3262, 1979586319187312640000), (Sum.inr 3266, 3863114615263002624000), (Sum.inr 3267, 53914691091824640000)]

def originalMerge1248 : Integer.Sparse OriginalKey := originalMerge1246 ++ originalMerge1247

theorem reducedMerge1248Check : reducedMerge1248 = Integer.Sparse.mergeBy masterLess reducedMerge1246 reducedMerge1247 := by decide +kernel

def reducedMerge1249 : Integer.Sparse Master := [(Sum.inr 3268, -2204937138861047808000), (Sum.inr 3271, -2066297949707894784000)]

def originalMerge1249 : Integer.Sparse OriginalKey := originalTerm1255 ++ originalTerm1256

theorem reducedMerge1249Check : reducedMerge1249 = Integer.Sparse.mergeBy masterLess reducedTerm1255 reducedTerm1256 := by decide +kernel

def reducedMerge1250 : Integer.Sparse Master := [(Sum.inr 3272, -992147345927700480000), (Sum.inr 3288, 305084947161415680000)]

def originalMerge1250 : Integer.Sparse OriginalKey := originalTerm1257 ++ originalTerm1258

theorem reducedMerge1250Check : reducedMerge1250 = Integer.Sparse.mergeBy masterLess reducedTerm1257 reducedTerm1258 := by decide +kernel

def reducedMerge1251 : Integer.Sparse Master := [(Sum.inr 3268, -2204937138861047808000), (Sum.inr 3271, -2066297949707894784000), (Sum.inr 3272, -992147345927700480000), (Sum.inr 3288, 305084947161415680000)]

def originalMerge1251 : Integer.Sparse OriginalKey := originalMerge1249 ++ originalMerge1250

theorem reducedMerge1251Check : reducedMerge1251 = Integer.Sparse.mergeBy masterLess reducedMerge1249 reducedMerge1250 := by decide +kernel

def reducedMerge1252 : Integer.Sparse Master := [(Sum.inr 3261, 270860476671590400000), (Sum.inr 3262, 1979586319187312640000), (Sum.inr 3266, 3863114615263002624000), (Sum.inr 3267, 53914691091824640000), (Sum.inr 3268, -2204937138861047808000), (Sum.inr 3271, -2066297949707894784000), (Sum.inr 3272, -992147345927700480000), (Sum.inr 3288, 305084947161415680000)]

def originalMerge1252 : Integer.Sparse OriginalKey := originalMerge1248 ++ originalMerge1251

theorem reducedMerge1252Check : reducedMerge1252 = Integer.Sparse.mergeBy masterLess reducedMerge1248 reducedMerge1251 := by decide +kernel

def reducedMerge1253 : Integer.Sparse Master := [(Sum.inr 3255, 1331003266183987200000), (Sum.inr 3257, 5933039869919232000000), (Sum.inr 3258, -1531997227471011840000), (Sum.inr 3259, 9156607353476481024000), (Sum.inr 3260, 1182595905074626560000), (Sum.inr 3261, 270860476671590400000), (Sum.inr 3262, 1979586319187312640000), (Sum.inr 3266, 3863114615263002624000), (Sum.inr 3267, 53914691091824640000), (Sum.inr 3268, -2204937138861047808000), (Sum.inr 3271, -2066297949707894784000), (Sum.inr 3272, -992147345927700480000), (Sum.inr 3288, 305084947161415680000)]

def originalMerge1253 : Integer.Sparse OriginalKey := originalMerge1245 ++ originalMerge1252

theorem reducedMerge1253Check : reducedMerge1253 = Integer.Sparse.mergeBy masterLess reducedMerge1245 reducedMerge1252 := by decide +kernel

def reducedMerge1254 : Integer.Sparse Master := [(Sum.inl 0, -4353477099658444800), (Sum.inl 1, 267993233451675648000), (Sum.inl 2, 146146682757390336000), (Sum.inl 3, -380211317650096128000), (Sum.inl 12, -40555765569650688000), (Sum.inl 13, -212621157529288704000), (Sum.inr 3189, -1174798139719680000000), (Sum.inr 3196, 6466249688175083520000), (Sum.inr 3197, 1899117244195799040000), (Sum.inr 3198, 419312052798750720000), (Sum.inr 3199, 6894774206306058240000), (Sum.inr 3202, 11475455859405619200000), (Sum.inr 3221, -12951213345010483200000), (Sum.inr 3222, -12438782405973245952000), (Sum.inr 3255, 1331003266183987200000), (Sum.inr 3257, 5933039869919232000000), (Sum.inr 3258, -1531997227471011840000), (Sum.inr 3259, 9156607353476481024000), (Sum.inr 3260, 1182595905074626560000), (Sum.inr 3261, 270860476671590400000), (Sum.inr 3262, 1979586319187312640000), (Sum.inr 3266, 3863114615263002624000), (Sum.inr 3267, 53914691091824640000), (Sum.inr 3268, -2204937138861047808000), (Sum.inr 3271, -2066297949707894784000), (Sum.inr 3272, -992147345927700480000), (Sum.inr 3288, 305084947161415680000)]

def originalMerge1254 : Integer.Sparse OriginalKey := originalMerge1239 ++ originalMerge1253

theorem reducedMerge1254Check : reducedMerge1254 = Integer.Sparse.mergeBy masterLess reducedMerge1239 reducedMerge1253 := by decide +kernel

def reducedMerge1255 : Integer.Sparse Master := [(Sum.inl 0, -117343595247530803200), (Sum.inl 1, 361420713534246912000), (Sum.inl 2, 96476820425330688000), (Sum.inl 3, 96957509274501120000), (Sum.inl 4, 477168826924597248000), (Sum.inl 12, -40555765569650688000), (Sum.inl 13, -212621157529288704000), (Sum.inl 26, 573455482913488896000), (Sum.inr 3118, 6748651458342420480000), (Sum.inr 3127, -2711226786498478080000), (Sum.inr 3128, -814591422450892800000), (Sum.inr 3129, -6439173843973570560000), (Sum.inr 3130, -2879161744832593920000), (Sum.inr 3131, -16011049661961338880000), (Sum.inr 3132, 814591422450892800000), (Sum.inr 3133, -616542244556636160000), (Sum.inr 3134, 9470910448608215040000), (Sum.inr 3136, 6932067331465543680000), (Sum.inr 3137, 5023829814312960000000), (Sum.inr 3138, 8259752936279900160000), (Sum.inr 3155, 2995585454962114560000), (Sum.inr 3156, -4348786044622602240000), (Sum.inr 3158, -2995585454962114560000), (Sum.inr 3161, 519512794327941120000), (Sum.inr 3162, -6260504027114373120000), (Sum.inr 3163, 10736042127096545280000), (Sum.inr 3164, -9579839035999518720000), (Sum.inr 3170, 6664563524103045120000), (Sum.inr 3172, 9579839035999518720000), (Sum.inr 3174, -10880841765483970560000), (Sum.inr 3179, -8772590858152181760000), (Sum.inr 3180, -8754560341097840640000), (Sum.inr 3189, -1174798139719680000000), (Sum.inr 3196, 6466249688175083520000), (Sum.inr 3197, 1899117244195799040000), (Sum.inr 3198, 419312052798750720000), (Sum.inr 3199, 6894774206306058240000), (Sum.inr 3202, 11475455859405619200000), (Sum.inr 3221, -12951213345010483200000), (Sum.inr 3222, -12438782405973245952000), (Sum.inr 3255, 1331003266183987200000), (Sum.inr 3257, 5933039869919232000000), (Sum.inr 3258, -1531997227471011840000), (Sum.inr 3259, 9156607353476481024000), (Sum.inr 3260, 1182595905074626560000), (Sum.inr 3261, 270860476671590400000), (Sum.inr 3262, 1979586319187312640000), (Sum.inr 3266, 3863114615263002624000), (Sum.inr 3267, 53914691091824640000), (Sum.inr 3268, -2204937138861047808000), (Sum.inr 3271, -2066297949707894784000), (Sum.inr 3272, -992147345927700480000), (Sum.inr 3288, 305084947161415680000)]

def originalMerge1255 : Integer.Sparse OriginalKey := originalMerge1225 ++ originalMerge1254

theorem reducedMerge1255Check : reducedMerge1255 = Integer.Sparse.mergeBy masterLess reducedMerge1225 reducedMerge1254 := by decide +kernel

def reducedMerge1256 : Integer.Sparse Master := [(Sum.inr 3290, 1619043489526579200000), (Sum.inr 3291, -1521451825330913280000)]

def originalMerge1256 : Integer.Sparse OriginalKey := originalTerm1260 ++ originalTerm1261

theorem reducedMerge1256Check : reducedMerge1256 = Integer.Sparse.mergeBy masterLess reducedTerm1260 reducedTerm1261 := by decide +kernel

def reducedMerge1257 : Integer.Sparse Master := [(Sum.inr 3289, 2654462499211837440000), (Sum.inr 3290, 1619043489526579200000), (Sum.inr 3291, -1521451825330913280000)]

def originalMerge1257 : Integer.Sparse OriginalKey := originalTerm1259 ++ originalMerge1256

theorem reducedMerge1257Check : reducedMerge1257 = Integer.Sparse.mergeBy masterLess reducedTerm1259 reducedMerge1256 := by decide +kernel

def reducedMerge1258 : Integer.Sparse Master := [(Sum.inr 3294, -8946502007384309760000), (Sum.inr 3295, -3789395265230733312000)]

def originalMerge1258 : Integer.Sparse OriginalKey := originalTerm1262 ++ originalTerm1263

theorem reducedMerge1258Check : reducedMerge1258 = Integer.Sparse.mergeBy masterLess reducedTerm1262 reducedTerm1263 := by decide +kernel

def reducedMerge1259 : Integer.Sparse Master := [(Sum.inr 3296, -9536788940949946368000), (Sum.inr 3297, -1889903966198169600000)]

def originalMerge1259 : Integer.Sparse OriginalKey := originalTerm1264 ++ originalTerm1265

theorem reducedMerge1259Check : reducedMerge1259 = Integer.Sparse.mergeBy masterLess reducedTerm1264 reducedTerm1265 := by decide +kernel

def reducedMerge1260 : Integer.Sparse Master := [(Sum.inr 3294, -8946502007384309760000), (Sum.inr 3295, -3789395265230733312000), (Sum.inr 3296, -9536788940949946368000), (Sum.inr 3297, -1889903966198169600000)]

def originalMerge1260 : Integer.Sparse OriginalKey := originalMerge1258 ++ originalMerge1259

theorem reducedMerge1260Check : reducedMerge1260 = Integer.Sparse.mergeBy masterLess reducedMerge1258 reducedMerge1259 := by decide +kernel

def reducedMerge1261 : Integer.Sparse Master := [(Sum.inr 3289, 2654462499211837440000), (Sum.inr 3290, 1619043489526579200000), (Sum.inr 3291, -1521451825330913280000), (Sum.inr 3294, -8946502007384309760000), (Sum.inr 3295, -3789395265230733312000), (Sum.inr 3296, -9536788940949946368000), (Sum.inr 3297, -1889903966198169600000)]

def originalMerge1261 : Integer.Sparse OriginalKey := originalMerge1257 ++ originalMerge1260

theorem reducedMerge1261Check : reducedMerge1261 = Integer.Sparse.mergeBy masterLess reducedMerge1257 reducedMerge1260 := by decide +kernel

def reducedMerge1262 : Integer.Sparse Master := [(Sum.inr 3298, 752859079780663296000), (Sum.inr 3302, -1389583379072286720000)]

def originalMerge1262 : Integer.Sparse OriginalKey := originalTerm1266 ++ originalTerm1267

theorem reducedMerge1262Check : reducedMerge1262 = Integer.Sparse.mergeBy masterLess reducedTerm1266 reducedTerm1267 := by decide +kernel

def reducedMerge1263 : Integer.Sparse Master := [(Sum.inr 3303, -565455270900989952000), (Sum.inr 3306, -186994987012915200000)]

def originalMerge1263 : Integer.Sparse OriginalKey := originalTerm1268 ++ originalTerm1269

theorem reducedMerge1263Check : reducedMerge1263 = Integer.Sparse.mergeBy masterLess reducedTerm1268 reducedTerm1269 := by decide +kernel

def reducedMerge1264 : Integer.Sparse Master := [(Sum.inr 3298, 752859079780663296000), (Sum.inr 3302, -1389583379072286720000), (Sum.inr 3303, -565455270900989952000), (Sum.inr 3306, -186994987012915200000)]

def originalMerge1264 : Integer.Sparse OriginalKey := originalMerge1262 ++ originalMerge1263

theorem reducedMerge1264Check : reducedMerge1264 = Integer.Sparse.mergeBy masterLess reducedMerge1262 reducedMerge1263 := by decide +kernel

def reducedMerge1265 : Integer.Sparse Master := [(Sum.inr 3365, 4501291376384409600000), (Sum.inr 3375, 654308882759024640000)]

def originalMerge1265 : Integer.Sparse OriginalKey := originalTerm1270 ++ originalTerm1271

theorem reducedMerge1265Check : reducedMerge1265 = Integer.Sparse.mergeBy masterLess reducedTerm1270 reducedTerm1271 := by decide +kernel

def reducedMerge1266 : Integer.Sparse Master := [(Sum.inr 3376, -4735033992735621120000), (Sum.inr 3378, 4935862034835701760000)]

def originalMerge1266 : Integer.Sparse OriginalKey := originalTerm1272 ++ originalTerm1273

theorem reducedMerge1266Check : reducedMerge1266 = Integer.Sparse.mergeBy masterLess reducedTerm1272 reducedTerm1273 := by decide +kernel

def reducedMerge1267 : Integer.Sparse Master := [(Sum.inr 3365, 4501291376384409600000), (Sum.inr 3375, 654308882759024640000), (Sum.inr 3376, -4735033992735621120000), (Sum.inr 3378, 4935862034835701760000)]

def originalMerge1267 : Integer.Sparse OriginalKey := originalMerge1265 ++ originalMerge1266

theorem reducedMerge1267Check : reducedMerge1267 = Integer.Sparse.mergeBy masterLess reducedMerge1265 reducedMerge1266 := by decide +kernel

def reducedMerge1268 : Integer.Sparse Master := [(Sum.inr 3298, 752859079780663296000), (Sum.inr 3302, -1389583379072286720000), (Sum.inr 3303, -565455270900989952000), (Sum.inr 3306, -186994987012915200000), (Sum.inr 3365, 4501291376384409600000), (Sum.inr 3375, 654308882759024640000), (Sum.inr 3376, -4735033992735621120000), (Sum.inr 3378, 4935862034835701760000)]

def originalMerge1268 : Integer.Sparse OriginalKey := originalMerge1264 ++ originalMerge1267

theorem reducedMerge1268Check : reducedMerge1268 = Integer.Sparse.mergeBy masterLess reducedMerge1264 reducedMerge1267 := by decide +kernel

def reducedMerge1269 : Integer.Sparse Master := [(Sum.inr 3289, 2654462499211837440000), (Sum.inr 3290, 1619043489526579200000), (Sum.inr 3291, -1521451825330913280000), (Sum.inr 3294, -8946502007384309760000), (Sum.inr 3295, -3789395265230733312000), (Sum.inr 3296, -9536788940949946368000), (Sum.inr 3297, -1889903966198169600000), (Sum.inr 3298, 752859079780663296000), (Sum.inr 3302, -1389583379072286720000), (Sum.inr 3303, -565455270900989952000), (Sum.inr 3306, -186994987012915200000), (Sum.inr 3365, 4501291376384409600000), (Sum.inr 3375, 654308882759024640000), (Sum.inr 3376, -4735033992735621120000), (Sum.inr 3378, 4935862034835701760000)]

def originalMerge1269 : Integer.Sparse OriginalKey := originalMerge1261 ++ originalMerge1268

theorem reducedMerge1269Check : reducedMerge1269 = Integer.Sparse.mergeBy masterLess reducedMerge1261 reducedMerge1268 := by decide +kernel

def reducedMerge1270 : Integer.Sparse Master := [(Sum.inr 3380, 2452540759969628160000), (Sum.inr 3388, 28541892592926720000)]

def originalMerge1270 : Integer.Sparse OriginalKey := originalTerm1275 ++ originalTerm1276

theorem reducedMerge1270Check : reducedMerge1270 = Integer.Sparse.mergeBy masterLess reducedTerm1275 reducedTerm1276 := by decide +kernel

def reducedMerge1271 : Integer.Sparse Master := [(Sum.inr 3379, -379671498467573760000), (Sum.inr 3380, 2452540759969628160000), (Sum.inr 3388, 28541892592926720000)]

def originalMerge1271 : Integer.Sparse OriginalKey := originalTerm1274 ++ originalMerge1270

theorem reducedMerge1271Check : reducedMerge1271 = Integer.Sparse.mergeBy masterLess reducedTerm1274 reducedMerge1270 := by decide +kernel

def reducedMerge1272 : Integer.Sparse Master := [(Sum.inr 3390, -2426340427298242560000), (Sum.inr 3391, -3915341740423249920000)]

def originalMerge1272 : Integer.Sparse OriginalKey := originalTerm1277 ++ originalTerm1278

theorem reducedMerge1272Check : reducedMerge1272 = Integer.Sparse.mergeBy masterLess reducedTerm1277 reducedTerm1278 := by decide +kernel

def reducedMerge1273 : Integer.Sparse Master := [(Sum.inr 3392, -57083785185853440000), (Sum.inr 3394, 6542432374534963200000)]

def originalMerge1273 : Integer.Sparse OriginalKey := originalTerm1279 ++ originalTerm1280

theorem reducedMerge1273Check : reducedMerge1273 = Integer.Sparse.mergeBy masterLess reducedTerm1279 reducedTerm1280 := by decide +kernel

def reducedMerge1274 : Integer.Sparse Master := [(Sum.inr 3390, -2426340427298242560000), (Sum.inr 3391, -3915341740423249920000), (Sum.inr 3392, -57083785185853440000), (Sum.inr 3394, 6542432374534963200000)]

def originalMerge1274 : Integer.Sparse OriginalKey := originalMerge1272 ++ originalMerge1273

theorem reducedMerge1274Check : reducedMerge1274 = Integer.Sparse.mergeBy masterLess reducedMerge1272 reducedMerge1273 := by decide +kernel

def reducedMerge1275 : Integer.Sparse Master := [(Sum.inr 3379, -379671498467573760000), (Sum.inr 3380, 2452540759969628160000), (Sum.inr 3388, 28541892592926720000), (Sum.inr 3390, -2426340427298242560000), (Sum.inr 3391, -3915341740423249920000), (Sum.inr 3392, -57083785185853440000), (Sum.inr 3394, 6542432374534963200000)]

def originalMerge1275 : Integer.Sparse OriginalKey := originalMerge1271 ++ originalMerge1274

theorem reducedMerge1275Check : reducedMerge1275 = Integer.Sparse.mergeBy masterLess reducedMerge1271 reducedMerge1274 := by decide +kernel

def reducedMerge1276 : Integer.Sparse Master := [(Sum.inr 3395, 16453451164259450880000), (Sum.inr 3396, 10440815232685178880000)]

def originalMerge1276 : Integer.Sparse OriginalKey := originalTerm1281 ++ originalTerm1282

theorem reducedMerge1276Check : reducedMerge1276 = Integer.Sparse.mergeBy masterLess reducedTerm1281 reducedTerm1282 := by decide +kernel

def reducedMerge1277 : Integer.Sparse Master := [(Sum.inr 3397, -684291540819640320000), (Sum.inr 3406, 652996879610019840000)]

def originalMerge1277 : Integer.Sparse OriginalKey := originalTerm1283 ++ originalTerm1284

theorem reducedMerge1277Check : reducedMerge1277 = Integer.Sparse.mergeBy masterLess reducedTerm1283 reducedTerm1284 := by decide +kernel

def reducedMerge1278 : Integer.Sparse Master := [(Sum.inr 3395, 16453451164259450880000), (Sum.inr 3396, 10440815232685178880000), (Sum.inr 3397, -684291540819640320000), (Sum.inr 3406, 652996879610019840000)]

def originalMerge1278 : Integer.Sparse OriginalKey := originalMerge1276 ++ originalMerge1277

theorem reducedMerge1278Check : reducedMerge1278 = Integer.Sparse.mergeBy masterLess reducedMerge1276 reducedMerge1277 := by decide +kernel

def reducedMerge1279 : Integer.Sparse Master := [(Sum.inr 3407, 3344441963460820992000), (Sum.inr 3408, -1985415998552211456000)]

def originalMerge1279 : Integer.Sparse OriginalKey := originalTerm1285 ++ originalTerm1286

theorem reducedMerge1279Check : reducedMerge1279 = Integer.Sparse.mergeBy masterLess reducedTerm1285 reducedTerm1286 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
