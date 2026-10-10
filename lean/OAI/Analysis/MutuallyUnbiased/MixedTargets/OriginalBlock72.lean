import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock72 : Integer.Sparse (Fin 2886) := [(2304, -40972413840), (2305, -77676135840), (2306, 36844286400), (2307, 25195671720), (2308, -12603127200), (2309, 7954347360), (2310, 11445253440), (2311, 23602894080), (2312, -19191440400), (2313, 116784693840), (2314, 34694184720), (2315, 55110368040), (2316, -1135962080), (2317, -2048698800), (2318, -16433028000), (2319, -10159945920), (2320, 28138372240), (2321, 28477512240), (2322, -11229504000), (2323, 19651632000), (2324, -20746041600), (2325, 28493753680), (2326, 24670783920), (2327, 36305572800), (2328, 2446403760), (2329, 2199785280), (2330, 65612752640), (2331, 13749933600), (2332, 63950874000), (2333, 68274009600), (2334, -27617621760), (2335, 10138864800)]

def originalBlock72 : Integer.Sparse OriginalKey := [(Sum.inl 1501, -11229504000), (Sum.inl 1504, -20746041600), (Sum.inl 1505, 19651632000), (Sum.inl 1510, -10159945920), (Sum.inl 1511, -16433028000), (Sum.inl 1514, 24670783920), (Sum.inl 1515, 36305572800), (Sum.inl 1516, 28493753680), (Sum.inl 1522, 28477512240), (Sum.inl 1523, 28138372240), (Sum.inl 1528, -2048698800), (Sum.inl 1529, -1135962080), (Sum.inl 1532, 13645038720), (Sum.inl 1533, 65612752640), (Sum.inl 1534, 2446403760), (Sum.inl 1540, 7954347360), (Sum.inl 1670, 25195671720), (Sum.inl 1688, 34694184720), (Sum.inl 1689, 55110368040), (Sum.inl 1695, 23602894080), (Sum.inl 1720, -40972413840), (Sum.inl 1721, 36844286400), (Sum.inl 1723, -77676135840), (Sum.inl 1748, 116784693840), (Sum.inl 1749, -19191440400), (Sum.inl 1757, -12603127200), (Sum.inl 2734, -27617621760), (Sum.inl 3089, 10138864800), (Sum.inl 3110, 68274009600), (Sum.inl 3112, 63950874000), (Sum.inl 3114, 13749933600), (Sum.inl 4149, -44918016000), (Sum.inl 4150, -82984166400), (Sum.inl 4151, 78606528000), (Sum.inl 4152, -40639783680), (Sum.inl 4153, 98683135680), (Sum.inl 4154, -65732112000), (Sum.inl 4155, 145222291200), (Sum.inl 4156, 113975014720), (Sum.inl 4157, -8194795200), (Sum.inl 4158, 113910048960), (Sum.inl 4159, 54580154880), (Sum.inl 4160, 112553488960), (Sum.inl 4161, 262451010560), (Sum.inl 4162, -4543848320), (Sum.inl 4163, 9785615040), (Sum.inl 4189, 31817389440), (Sum.inl 4327, 100782686880), (Sum.inl 4333, 138776738880), (Sum.inl 4335, 220441472160), (Sum.inl 4358, 94411576320), (Sum.inl 4367, -163889655360), (Sum.inl 4369, 147377145600), (Sum.inl 4374, 467138775360), (Sum.inl 4440, -310704543360), (Sum.inl 4445, -76765761600), (Sum.inl 4481, -50412508800), (Sum.inl 4897, 54999734400), (Sum.inl 5258, 40555459200), (Sum.inl 5268, -110470487040), (Sum.inl 5274, 255803496000), (Sum.inl 5275, 273096038400)]

theorem originalBlockCheck72 : originalBlock72 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock72 keyMomentRows) := by decide +kernel

theorem originalBlockEval72 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock72 x =
      Integer.Sparse.eval keyPolynomialBlock72 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck72, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
