import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock73 : Integer.Sparse (Fin 2886) := [(2336, 27036763920), (2337, -121147853760), (2338, -31378885680), (2339, -16312046640), (2340, 68642441640), (2341, -42708115440), (2342, 14341033920), (2343, -47280171000), (2344, -3525346560), (2345, 20512214240), (2346, 10132584400), (2347, -4546412160), (2348, 13639726320), (2349, -2610481920), (2350, -67065433960), (2351, 49078791360), (2352, 7161813520), (2353, 4332624480), (2354, 126626353200), (2355, 179046816960), (2356, 709566437880), (2357, -29606574240), (2358, 94694929440), (2359, -118232166400), (2360, 70240364800), (2361, 17100179040), (2362, -82568679560), (2363, 17250203520), (2364, 90512788240), (2365, 284801434440), (2366, -39662974560), (2367, 8053488080)]

def originalBlock73 : Integer.Sparse OriginalKey := [(Sum.inl 1, 126626353200), (Sum.inl 3, 284801434440), (Sum.inl 4, 709566437880), (Sum.inl 2753, 17250203520), (Sum.inl 2776, 94694929440), (Sum.inl 3037, -42708115440), (Sum.inl 3038, -31378885680), (Sum.inl 3039, -121147853760), (Sum.inl 3051, 13639726320), (Sum.inl 3052, 7161813520), (Sum.inl 3055, -4546412160), (Sum.inl 3064, -3525346560), (Sum.inl 3065, 14341033920), (Sum.inl 3074, 49078791360), (Sum.inl 3075, 4332624480), (Sum.inl 3078, -2610481920), (Sum.inl 3087, -47280171000), (Sum.inl 3088, -16312046640), (Sum.inl 3099, -67065433960), (Sum.inl 3103, 20512214240), (Sum.inl 3109, 27036763920), (Sum.inl 3111, 68642441640), (Sum.inl 3112, 179046816960), (Sum.inl 3119, 10132584400), (Sum.inl 3847, -39662974560), (Sum.inl 3856, -82568679560), (Sum.inl 3883, 17100179040), (Sum.inl 3977, 8053488080), (Sum.inl 3996, 160753153040), (Sum.inl 4006, -29606574240), (Sum.inl 4035, -118232166400), (Sum.inl 4084, 506505412800), (Sum.inl 4091, 1139205737760), (Sum.inl 4092, 2838265751520), (Sum.inl 5250, 57364135680), (Sum.inl 5251, -14101386240), (Sum.inl 5257, -189120684000), (Sum.inl 5259, -65248186560), (Sum.inl 5265, -170832461760), (Sum.inl 5266, -484591415040), (Sum.inl 5267, -125515542720), (Sum.inl 5270, 17330497920), (Sum.inl 5271, 108147055680), (Sum.inl 5273, 274569766560), (Sum.inl 5274, 716187267840), (Sum.inl 5276, 28647254080), (Sum.inl 5281, 196315165440), (Sum.inl 5282, -10441927680), (Sum.inl 5284, 69000814080), (Sum.inl 5290, -268261735840), (Sum.inl 5291, 82048856960), (Sum.inl 5299, 54558905280), (Sum.inl 5300, -18185648640), (Sum.inl 5302, 378779717760), (Sum.inl 5304, 40530337600), (Sum.inl 5405, 32213952320), (Sum.inl 5406, -158651898240), (Sum.inl 5409, -472928665600), (Sum.inl 5410, 643012612160), (Sum.inl 5411, 68400716160), (Sum.inl 5412, -330274718240), (Sum.inl 5413, -118426296960)]

theorem originalBlockCheck73 : originalBlock73 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock73 keyMomentRows) := by decide +kernel

theorem originalBlockEval73 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock73 x =
      Integer.Sparse.eval keyPolynomialBlock73 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck73, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
