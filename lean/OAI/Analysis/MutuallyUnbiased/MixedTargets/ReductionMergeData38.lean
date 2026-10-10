import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData38
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData39
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData37

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge1216 : Integer.Sparse Master := [(Sum.inr 3136, 6932067331465543680000), (Sum.inr 3137, 5023829814312960000000), (Sum.inr 3138, 8259752936279900160000), (Sum.inr 3155, 2995585454962114560000), (Sum.inr 3156, -4348786044622602240000), (Sum.inr 3158, -2995585454962114560000), (Sum.inr 3161, 519512794327941120000)]

def originalMerge1216 : Integer.Sparse OriginalKey := originalMerge1212 ++ originalMerge1215

theorem reducedMerge1216Check : reducedMerge1216 = Integer.Sparse.mergeBy masterLess reducedMerge1212 reducedMerge1215 := by decide +kernel

def reducedMerge1217 : Integer.Sparse Master := [(Sum.inr 3162, -6260504027114373120000), (Sum.inr 3163, 10736042127096545280000)]

def originalMerge1217 : Integer.Sparse OriginalKey := originalTerm1221 ++ originalTerm1222

theorem reducedMerge1217Check : reducedMerge1217 = Integer.Sparse.mergeBy masterLess reducedTerm1221 reducedTerm1222 := by decide +kernel

def reducedMerge1218 : Integer.Sparse Master := [(Sum.inr 3164, -9579839035999518720000), (Sum.inr 3170, 6664563524103045120000)]

def originalMerge1218 : Integer.Sparse OriginalKey := originalTerm1223 ++ originalTerm1224

theorem reducedMerge1218Check : reducedMerge1218 = Integer.Sparse.mergeBy masterLess reducedTerm1223 reducedTerm1224 := by decide +kernel

def reducedMerge1219 : Integer.Sparse Master := [(Sum.inr 3162, -6260504027114373120000), (Sum.inr 3163, 10736042127096545280000), (Sum.inr 3164, -9579839035999518720000), (Sum.inr 3170, 6664563524103045120000)]

def originalMerge1219 : Integer.Sparse OriginalKey := originalMerge1217 ++ originalMerge1218

theorem reducedMerge1219Check : reducedMerge1219 = Integer.Sparse.mergeBy masterLess reducedMerge1217 reducedMerge1218 := by decide +kernel

def reducedMerge1220 : Integer.Sparse Master := [(Sum.inr 3172, 9579839035999518720000), (Sum.inr 3174, -10880841765483970560000)]

def originalMerge1220 : Integer.Sparse OriginalKey := originalTerm1225 ++ originalTerm1226

theorem reducedMerge1220Check : reducedMerge1220 = Integer.Sparse.mergeBy masterLess reducedTerm1225 reducedTerm1226 := by decide +kernel

def reducedMerge1221 : Integer.Sparse Master := [(Sum.inr 3179, -8772590858152181760000), (Sum.inr 3180, -8754560341097840640000)]

def originalMerge1221 : Integer.Sparse OriginalKey := originalTerm1227 ++ originalTerm1228

theorem reducedMerge1221Check : reducedMerge1221 = Integer.Sparse.mergeBy masterLess reducedTerm1227 reducedTerm1228 := by decide +kernel

def reducedMerge1222 : Integer.Sparse Master := [(Sum.inr 3172, 9579839035999518720000), (Sum.inr 3174, -10880841765483970560000), (Sum.inr 3179, -8772590858152181760000), (Sum.inr 3180, -8754560341097840640000)]

def originalMerge1222 : Integer.Sparse OriginalKey := originalMerge1220 ++ originalMerge1221

theorem reducedMerge1222Check : reducedMerge1222 = Integer.Sparse.mergeBy masterLess reducedMerge1220 reducedMerge1221 := by decide +kernel

def reducedMerge1223 : Integer.Sparse Master := [(Sum.inr 3162, -6260504027114373120000), (Sum.inr 3163, 10736042127096545280000), (Sum.inr 3164, -9579839035999518720000), (Sum.inr 3170, 6664563524103045120000), (Sum.inr 3172, 9579839035999518720000), (Sum.inr 3174, -10880841765483970560000), (Sum.inr 3179, -8772590858152181760000), (Sum.inr 3180, -8754560341097840640000)]

def originalMerge1223 : Integer.Sparse OriginalKey := originalMerge1219 ++ originalMerge1222

theorem reducedMerge1223Check : reducedMerge1223 = Integer.Sparse.mergeBy masterLess reducedMerge1219 reducedMerge1222 := by decide +kernel

def reducedMerge1224 : Integer.Sparse Master := [(Sum.inr 3136, 6932067331465543680000), (Sum.inr 3137, 5023829814312960000000), (Sum.inr 3138, 8259752936279900160000), (Sum.inr 3155, 2995585454962114560000), (Sum.inr 3156, -4348786044622602240000), (Sum.inr 3158, -2995585454962114560000), (Sum.inr 3161, 519512794327941120000), (Sum.inr 3162, -6260504027114373120000), (Sum.inr 3163, 10736042127096545280000), (Sum.inr 3164, -9579839035999518720000), (Sum.inr 3170, 6664563524103045120000), (Sum.inr 3172, 9579839035999518720000), (Sum.inr 3174, -10880841765483970560000), (Sum.inr 3179, -8772590858152181760000), (Sum.inr 3180, -8754560341097840640000)]

def originalMerge1224 : Integer.Sparse OriginalKey := originalMerge1216 ++ originalMerge1223

theorem reducedMerge1224Check : reducedMerge1224 = Integer.Sparse.mergeBy masterLess reducedMerge1216 reducedMerge1223 := by decide +kernel

def reducedMerge1225 : Integer.Sparse Master := [(Sum.inl 0, -112990118147872358400), (Sum.inl 1, 93427480082571264000), (Sum.inl 2, -49669862332059648000), (Sum.inl 3, 477168826924597248000), (Sum.inl 4, 477168826924597248000), (Sum.inl 26, 573455482913488896000), (Sum.inr 3118, 6748651458342420480000), (Sum.inr 3127, -2711226786498478080000), (Sum.inr 3128, -814591422450892800000), (Sum.inr 3129, -6439173843973570560000), (Sum.inr 3130, -2879161744832593920000), (Sum.inr 3131, -16011049661961338880000), (Sum.inr 3132, 814591422450892800000), (Sum.inr 3133, -616542244556636160000), (Sum.inr 3134, 9470910448608215040000), (Sum.inr 3136, 6932067331465543680000), (Sum.inr 3137, 5023829814312960000000), (Sum.inr 3138, 8259752936279900160000), (Sum.inr 3155, 2995585454962114560000), (Sum.inr 3156, -4348786044622602240000), (Sum.inr 3158, -2995585454962114560000), (Sum.inr 3161, 519512794327941120000), (Sum.inr 3162, -6260504027114373120000), (Sum.inr 3163, 10736042127096545280000), (Sum.inr 3164, -9579839035999518720000), (Sum.inr 3170, 6664563524103045120000), (Sum.inr 3172, 9579839035999518720000), (Sum.inr 3174, -10880841765483970560000), (Sum.inr 3179, -8772590858152181760000), (Sum.inr 3180, -8754560341097840640000)]

def originalMerge1225 : Integer.Sparse OriginalKey := originalMerge1210 ++ originalMerge1224

theorem reducedMerge1225Check : reducedMerge1225 = Integer.Sparse.mergeBy masterLess reducedMerge1210 reducedMerge1224 := by decide +kernel

def reducedMerge1226 : Integer.Sparse Master := [(Sum.inr 3196, 6466249688175083520000), (Sum.inr 3197, 1899117244195799040000)]

def originalMerge1226 : Integer.Sparse OriginalKey := originalTerm1230 ++ originalTerm1231

theorem reducedMerge1226Check : reducedMerge1226 = Integer.Sparse.mergeBy masterLess reducedTerm1230 reducedTerm1231 := by decide +kernel

def reducedMerge1227 : Integer.Sparse Master := [(Sum.inr 3189, -1174798139719680000000), (Sum.inr 3196, 6466249688175083520000), (Sum.inr 3197, 1899117244195799040000)]

def originalMerge1227 : Integer.Sparse OriginalKey := originalTerm1229 ++ originalMerge1226

theorem reducedMerge1227Check : reducedMerge1227 = Integer.Sparse.mergeBy masterLess reducedTerm1229 reducedMerge1226 := by decide +kernel

def reducedMerge1228 : Integer.Sparse Master := [(Sum.inr 3198, 419312052798750720000), (Sum.inr 3199, 6894774206306058240000)]

def originalMerge1228 : Integer.Sparse OriginalKey := originalTerm1232 ++ originalTerm1233

theorem reducedMerge1228Check : reducedMerge1228 = Integer.Sparse.mergeBy masterLess reducedTerm1232 reducedTerm1233 := by decide +kernel

def reducedMerge1229 : Integer.Sparse Master := [(Sum.inr 3202, 11475455859405619200000), (Sum.inr 3221, -12951213345010483200000)]

def originalMerge1229 : Integer.Sparse OriginalKey := originalTerm1234 ++ originalTerm1235

theorem reducedMerge1229Check : reducedMerge1229 = Integer.Sparse.mergeBy masterLess reducedTerm1234 reducedTerm1235 := by decide +kernel

def reducedMerge1230 : Integer.Sparse Master := [(Sum.inr 3198, 419312052798750720000), (Sum.inr 3199, 6894774206306058240000), (Sum.inr 3202, 11475455859405619200000), (Sum.inr 3221, -12951213345010483200000)]

def originalMerge1230 : Integer.Sparse OriginalKey := originalMerge1228 ++ originalMerge1229

theorem reducedMerge1230Check : reducedMerge1230 = Integer.Sparse.mergeBy masterLess reducedMerge1228 reducedMerge1229 := by decide +kernel

def reducedMerge1231 : Integer.Sparse Master := [(Sum.inr 3189, -1174798139719680000000), (Sum.inr 3196, 6466249688175083520000), (Sum.inr 3197, 1899117244195799040000), (Sum.inr 3198, 419312052798750720000), (Sum.inr 3199, 6894774206306058240000), (Sum.inr 3202, 11475455859405619200000), (Sum.inr 3221, -12951213345010483200000)]

def originalMerge1231 : Integer.Sparse OriginalKey := originalMerge1227 ++ originalMerge1230

theorem reducedMerge1231Check : reducedMerge1231 = Integer.Sparse.mergeBy masterLess reducedMerge1227 reducedMerge1230 := by decide +kernel

def reducedMerge1232 : Integer.Sparse Master := [(Sum.inl 0, -24418675486369382400), (Sum.inl 1, 23479495659970560000), (Sum.inl 2, -4695899131994112000), (Sum.inl 3, -150268772223811584000), (Sum.inl 12, -75134386111905792000), (Sum.inl 13, -225403158335717376000), (Sum.inr 3222, -12438782405973245952000)]

def originalMerge1232 : Integer.Sparse OriginalKey := originalTerm1236 ++ originalTerm1237

theorem reducedMerge1232Check : reducedMerge1232 = Integer.Sparse.mergeBy masterLess reducedTerm1236 reducedTerm1237 := by decide +kernel

def reducedMerge1233 : Integer.Sparse Master := [(Sum.inl 0, -30165864245998387200), (Sum.inl 1, -1651933730635776000), (Sum.inl 2, 77408247828086784000), (Sum.inl 3, 63794790818906112000), (Sum.inl 12, 121362273116356608000), (Sum.inl 13, 306519337051619328000)]

def originalMerge1233 : Integer.Sparse OriginalKey := originalTerm1238 ++ originalTerm1239

theorem reducedMerge1233Check : reducedMerge1233 = Integer.Sparse.mergeBy masterLess reducedTerm1238 reducedTerm1239 := by decide +kernel

def reducedMerge1234 : Integer.Sparse Master := [(Sum.inl 0, -54584539732367769600), (Sum.inl 1, 21827561929334784000), (Sum.inl 2, 72712348696092672000), (Sum.inl 3, -86473981404905472000), (Sum.inl 12, 46227887004450816000), (Sum.inl 13, 81116178715901952000), (Sum.inr 3222, -12438782405973245952000)]

def originalMerge1234 : Integer.Sparse OriginalKey := originalMerge1232 ++ originalMerge1233

theorem reducedMerge1234Check : reducedMerge1234 = Integer.Sparse.mergeBy masterLess reducedMerge1232 reducedMerge1233 := by decide +kernel

def reducedMerge1235 : Integer.Sparse Master := [(Sum.inl 0, 50231062632709324800), (Sum.inl 1, 246165671522340864000), (Sum.inl 2, 73434334061297664000), (Sum.inl 3, -293737336245190656000), (Sum.inl 12, -86783652574101504000), (Sum.inl 13, -293737336245190656000)]

def originalMerge1235 : Integer.Sparse OriginalKey := originalTerm1240 ++ originalTerm1241

theorem reducedMerge1235Check : reducedMerge1235 = Integer.Sparse.mergeBy masterLess reducedTerm1240 reducedTerm1241 := by decide +kernel

def reducedMerge1236 : Integer.Sparse Master := []

def originalMerge1236 : Integer.Sparse OriginalKey := originalTerm1242 ++ originalTerm1243

theorem reducedMerge1236Check : reducedMerge1236 = Integer.Sparse.mergeBy masterLess reducedTerm1242 reducedTerm1243 := by decide +kernel

def reducedMerge1237 : Integer.Sparse Master := [(Sum.inl 0, 50231062632709324800), (Sum.inl 1, 246165671522340864000), (Sum.inl 2, 73434334061297664000), (Sum.inl 3, -293737336245190656000), (Sum.inl 12, -86783652574101504000), (Sum.inl 13, -293737336245190656000)]

def originalMerge1237 : Integer.Sparse OriginalKey := originalMerge1235 ++ originalMerge1236

theorem reducedMerge1237Check : reducedMerge1237 = Integer.Sparse.mergeBy masterLess reducedMerge1235 reducedMerge1236 := by decide +kernel

def reducedMerge1238 : Integer.Sparse Master := [(Sum.inl 0, -4353477099658444800), (Sum.inl 1, 267993233451675648000), (Sum.inl 2, 146146682757390336000), (Sum.inl 3, -380211317650096128000), (Sum.inl 12, -40555765569650688000), (Sum.inl 13, -212621157529288704000), (Sum.inr 3222, -12438782405973245952000)]

def originalMerge1238 : Integer.Sparse OriginalKey := originalMerge1234 ++ originalMerge1237

theorem reducedMerge1238Check : reducedMerge1238 = Integer.Sparse.mergeBy masterLess reducedMerge1234 reducedMerge1237 := by decide +kernel

def reducedMerge1239 : Integer.Sparse Master := [(Sum.inl 0, -4353477099658444800), (Sum.inl 1, 267993233451675648000), (Sum.inl 2, 146146682757390336000), (Sum.inl 3, -380211317650096128000), (Sum.inl 12, -40555765569650688000), (Sum.inl 13, -212621157529288704000), (Sum.inr 3189, -1174798139719680000000), (Sum.inr 3196, 6466249688175083520000), (Sum.inr 3197, 1899117244195799040000), (Sum.inr 3198, 419312052798750720000), (Sum.inr 3199, 6894774206306058240000), (Sum.inr 3202, 11475455859405619200000), (Sum.inr 3221, -12951213345010483200000), (Sum.inr 3222, -12438782405973245952000)]

def originalMerge1239 : Integer.Sparse OriginalKey := originalMerge1231 ++ originalMerge1238

theorem reducedMerge1239Check : reducedMerge1239 = Integer.Sparse.mergeBy masterLess reducedMerge1231 reducedMerge1238 := by decide +kernel

def reducedMerge1240 : Integer.Sparse Master := [(Sum.inr 3255, 1331003266183987200000)]

def originalMerge1240 : Integer.Sparse OriginalKey := originalTerm1245 ++ originalTerm1246

theorem reducedMerge1240Check : reducedMerge1240 = Integer.Sparse.mergeBy masterLess reducedTerm1245 reducedTerm1246 := by decide +kernel

def reducedMerge1241 : Integer.Sparse Master := [(Sum.inr 3255, 1331003266183987200000)]

def originalMerge1241 : Integer.Sparse OriginalKey := originalTerm1244 ++ originalMerge1240

theorem reducedMerge1241Check : reducedMerge1241 = Integer.Sparse.mergeBy masterLess reducedTerm1244 reducedMerge1240 := by decide +kernel

def reducedMerge1242 : Integer.Sparse Master := [(Sum.inr 3257, 5933039869919232000000), (Sum.inr 3258, -1531997227471011840000)]

def originalMerge1242 : Integer.Sparse OriginalKey := originalTerm1247 ++ originalTerm1248

theorem reducedMerge1242Check : reducedMerge1242 = Integer.Sparse.mergeBy masterLess reducedTerm1247 reducedTerm1248 := by decide +kernel

def reducedMerge1243 : Integer.Sparse Master := [(Sum.inr 3259, 9156607353476481024000), (Sum.inr 3260, 1182595905074626560000)]

def originalMerge1243 : Integer.Sparse OriginalKey := originalTerm1249 ++ originalTerm1250

theorem reducedMerge1243Check : reducedMerge1243 = Integer.Sparse.mergeBy masterLess reducedTerm1249 reducedTerm1250 := by decide +kernel

def reducedMerge1244 : Integer.Sparse Master := [(Sum.inr 3257, 5933039869919232000000), (Sum.inr 3258, -1531997227471011840000), (Sum.inr 3259, 9156607353476481024000), (Sum.inr 3260, 1182595905074626560000)]

def originalMerge1244 : Integer.Sparse OriginalKey := originalMerge1242 ++ originalMerge1243

theorem reducedMerge1244Check : reducedMerge1244 = Integer.Sparse.mergeBy masterLess reducedMerge1242 reducedMerge1243 := by decide +kernel

def reducedMerge1245 : Integer.Sparse Master := [(Sum.inr 3255, 1331003266183987200000), (Sum.inr 3257, 5933039869919232000000), (Sum.inr 3258, -1531997227471011840000), (Sum.inr 3259, 9156607353476481024000), (Sum.inr 3260, 1182595905074626560000)]

def originalMerge1245 : Integer.Sparse OriginalKey := originalMerge1241 ++ originalMerge1244

theorem reducedMerge1245Check : reducedMerge1245 = Integer.Sparse.mergeBy masterLess reducedMerge1241 reducedMerge1244 := by decide +kernel

def reducedMerge1246 : Integer.Sparse Master := [(Sum.inr 3261, 270860476671590400000), (Sum.inr 3262, 1979586319187312640000)]

def originalMerge1246 : Integer.Sparse OriginalKey := originalTerm1251 ++ originalTerm1252

theorem reducedMerge1246Check : reducedMerge1246 = Integer.Sparse.mergeBy masterLess reducedTerm1251 reducedTerm1252 := by decide +kernel

def reducedMerge1247 : Integer.Sparse Master := [(Sum.inr 3266, 3863114615263002624000), (Sum.inr 3267, 53914691091824640000)]

def originalMerge1247 : Integer.Sparse OriginalKey := originalTerm1253 ++ originalTerm1254

theorem reducedMerge1247Check : reducedMerge1247 = Integer.Sparse.mergeBy masterLess reducedTerm1253 reducedTerm1254 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
