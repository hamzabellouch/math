import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock74 : Integer.Sparse (Fin 2886) := [(2368, -65205723240), (2369, -49374989440), (2370, 22604714640), (2371, -144898064640), (2372, -246620576520), (2373, 120897845280), (2374, -77627280960), (2375, -201403157520), (2376, -56208224160), (2377, -156245208240), (2378, -33567760200), (2379, -10938011520), (2380, 10255934320), (2381, 48045374040), (2382, -34148752320), (2383, -45145603680), (2384, -232946023840), (2385, 40053479760), (2386, 2851571760), (2387, -6312192000), (2388, 149837521040), (2389, -16009994800), (2390, -35794478480), (2391, -166129114320), (2392, 18535552720), (2393, 118855596480), (2394, 7836927760), (2395, 57340892880), (2396, 29474272080), (2397, -2890879280), (2398, -111359264160), (2399, 97266550160)]

def originalBlock74 : Integer.Sparse OriginalKey := [(Sum.inl 2710, -10938011520), (Sum.inl 2724, -6312192000), (Sum.inl 2732, -77627280960), (Sum.inl 2744, -45145603680), (Sum.inl 3089, -144898064640), (Sum.inl 3103, -34148752320), (Sum.inl 3230, 22604714640), (Sum.inl 3526, -16009994800), (Sum.inl 3541, 2851571760), (Sum.inl 3573, 40053479760), (Sum.inl 3839, 48009824800), (Sum.inl 3841, -33567760200), (Sum.inl 3847, -49374989440), (Sum.inl 3872, -156245208240), (Sum.inl 3877, 57340892880), (Sum.inl 3954, -2890879280), (Sum.inl 3972, -35794478480), (Sum.inl 3990, -45952289840), (Sum.inl 3993, 157674448800), (Sum.inl 4003, 120897845280), (Sum.inl 4026, -277488378480), (Sum.inl 4027, -114090427360), (Sum.inl 4030, 97266550160), (Sum.inl 4032, -201403157520), (Sum.inl 4034, 48045374040), (Sum.inl 4035, -246620576520), (Sum.inl 4038, -65205723240), (Sum.inl 4894, 90418858560), (Sum.inl 5251, -43752046080), (Sum.inl 5258, -579592258560), (Sum.inl 5260, -25248768000), (Sum.inl 5265, -64039979200), (Sum.inl 5267, -299102836800), (Sum.inl 5276, -180582414720), (Sum.inl 5291, -136595009280), (Sum.inl 5299, 160213919040), (Sum.inl 5406, -197499957760), (Sum.inl 5408, -260822892960), (Sum.inl 5409, -986482306080), (Sum.inl 5423, -805612630080), (Sum.inl 5424, -183809159360), (Sum.inl 5425, -432941533760), (Sum.inl 5426, -134271040800), (Sum.inl 5427, 192181496160), (Sum.inl 5428, 483591381120), (Sum.inl 5429, -11563517120), (Sum.inl 5430, -143177913920), (Sum.inl 5431, -1109953513920), (Sum.inl 5432, -456361709440), (Sum.inl 5436, 229363571520), (Sum.inl 5438, 630697795200), (Sum.inl 5449, 389066200640)]

theorem originalBlockCheck74 : originalBlock74 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock74 keyMomentRows) := by decide +kernel

theorem originalBlockEval74 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock74 x =
      Integer.Sparse.eval keyPolynomialBlock74 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck74, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
