import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock38 : Integer.Sparse (Fin 2886) := [(1216, 20210904000), (1217, -60504474240), (1218, -90704725440), (1219, 37611000000), (1220, -22127928000), (1221, 10987226880), (1222, -56876813760), (1223, 33608041920), (1224, -7891734240), (1225, 22104192000), (1226, 15341940000), (1227, 65343541440), (1228, -9891735360), (1229, -10987226880), (1230, 19265813760), (1231, 3561901440), (1232, -13716326400), (1233, -31734372480), (1234, 11830790400), (1235, 112785109280), (1236, -33383971440), (1237, 25763754240), (1238, 36762840000), (1239, -123451736000), (1240, -189998147200), (1241, -69810220960), (1242, 60239702800), (1243, 24022892160), (1244, 11396067600), (1245, 3560809200), (1246, 86879699200), (1247, 68743742400)]

def originalBlock38 : Integer.Sparse OriginalKey := [(Sum.inl 2277, 54936134400), (Sum.inl 2278, -54936134400), (Sum.inl 2281, -39458671200), (Sum.inl 2293, -68581632000), (Sum.inl 2743, -158671862400), (Sum.inl 3054, 76709700000), (Sum.inl 3055, 59153952000), (Sum.inl 3078, 183814200000), (Sum.inl 3584, 128818771200), (Sum.inl 3633, 110520960000), (Sum.inl 3812, 168040209600), (Sum.inl 3813, 17809507200), (Sum.inl 3814, -302522371200), (Sum.inl 3817, 563925546400), (Sum.inl 3845, -617258680000), (Sum.inl 3877, 120114460800), (Sum.inl 3884, 301198514000), (Sum.inl 3901, -284384068800), (Sum.inl 3903, -453523627200), (Sum.inl 3904, 188055000000), (Sum.inl 3906, -110639640000), (Sum.inl 3907, -49458676800), (Sum.inl 3908, 101054520000), (Sum.inl 3910, 96329068800), (Sum.inl 3913, 326717707200), (Sum.inl 3953, 434398496000), (Sum.inl 3954, 343718712000), (Sum.inl 3958, -949990736000), (Sum.inl 3959, -349051104800), (Sum.inl 3961, 56980338000), (Sum.inl 3962, 17804046000), (Sum.inl 3963, -166919857200)]

theorem originalBlockCheck38 : originalBlock38 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock38 keyMomentRows) := by decide +kernel

theorem originalBlockEval38 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock38 x =
      Integer.Sparse.eval keyPolynomialBlock38 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck38, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
