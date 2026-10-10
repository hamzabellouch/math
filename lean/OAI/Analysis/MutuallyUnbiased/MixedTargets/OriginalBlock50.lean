import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock50 : Integer.Sparse (Fin 2886) := [(1600, -3560809200), (1601, 69175999680), (1602, -44642664000), (1603, 2243173600), (1604, -140745038400), (1605, 11793018560), (1606, -34926888800), (1607, -17842504800), (1608, -11104874400), (1609, -3560809200), (1610, -27656481600), (1611, -30092011200), (1612, -2243173600), (1613, 9353676160), (1614, 132673632800), (1615, 104070986400), (1616, 11104874400), (1617, 3560809200), (1618, 21563601600), (1619, 17699832000), (1620, -144826954560), (1621, -26340278400), (1622, 37160467200), (1623, -24276918720), (1624, -39575993280), (1625, 72853920000), (1626, 80803207200), (1627, -27614989920), (1628, -2243173600), (1629, -18261313760), (1630, 88281461600), (1631, 57501607200)]

def originalBlock50 : Integer.Sparse OriginalKey := [(Sum.inl 1217, 520354932000), (Sum.inl 1243, 46768380800), (Sum.inl 1790, -121384593600), (Sum.inl 1808, -131701392000), (Sum.inl 1825, 88499160000), (Sum.inl 1973, 185802336000), (Sum.inl 2090, -724134772800), (Sum.inl 2134, 107818008000), (Sum.inl 2558, 55524372000), (Sum.inl 2618, 663368164000), (Sum.inl 2712, 17804046000), (Sum.inl 2734, -11215868000), (Sum.inl 2754, -138282408000), (Sum.inl 2759, -197879966400), (Sum.inl 2777, 345879998400), (Sum.inl 2797, 287508036000), (Sum.inl 2811, -91306568800), (Sum.inl 2848, -138074949600), (Sum.inl 2861, -55524372000), (Sum.inl 2865, -150460056000), (Sum.inl 2867, 58965092800), (Sum.inl 2900, 441407308000), (Sum.inl 2902, 364269600000), (Sum.inl 2916, -89212524000), (Sum.inl 2933, -174634444000), (Sum.inl 2942, -223213320000), (Sum.inl 2979, -11215868000), (Sum.inl 2984, 404016036000), (Sum.inl 3038, 11215868000), (Sum.inl 3064, -17804046000), (Sum.inl 3078, -17804046000), (Sum.inl 3086, -703725192000)]

theorem originalBlockCheck50 : originalBlock50 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock50 keyMomentRows) := by decide +kernel

theorem originalBlockEval50 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock50 x =
      Integer.Sparse.eval keyPolynomialBlock50 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck50, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
