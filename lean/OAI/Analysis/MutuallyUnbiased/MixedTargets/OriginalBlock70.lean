import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock70 : Integer.Sparse (Fin 2886) := [(2240, 387034596480), (2241, -317340480), (2242, 65403264000), (2243, -14236499520), (2244, -22459008000), (2245, 31022502720), (2246, -34636753920), (2247, 65283607200), (2248, -7593210720), (2249, -20547720000), (2250, -77691031680), (2251, -53975601840), (2252, -81358596480), (2253, -26794424880), (2254, 9476558400), (2255, -17825395200), (2256, -46727562960), (2257, -3888915600), (2258, -14076578880), (2259, -23975871120), (2260, -41492083200), (2261, -29704458240), (2262, -646280640), (2263, -25185862720), (2264, -4758454560), (2265, -3924651520), (2266, -3210480000), (2267, -48398638560), (2268, 37284743040), (2269, -1027497360), (2270, 20981767680), (2271, 18184504880)]

def originalBlock70 : Integer.Sparse OriginalKey := [(Sum.inl 1528, -1027497360), (Sum.inl 1529, -3924651520), (Sum.inl 1530, -4758454560), (Sum.inl 1531, -646280640), (Sum.inl 1686, 20981767680), (Sum.inl 1687, -3210480000), (Sum.inl 1744, 18184504880), (Sum.inl 1745, -48398638560), (Sum.inl 1746, -25185862720), (Sum.inl 1747, -29704458240), (Sum.inl 2140, -22459008000), (Sum.inl 2147, -23975871120), (Sum.inl 2148, -41492083200), (Sum.inl 2149, -53975601840), (Sum.inl 2172, -17825395200), (Sum.inl 2189, -14236499520), (Sum.inl 2192, 65403264000), (Sum.inl 2198, -46727562960), (Sum.inl 2199, -14076578880), (Sum.inl 2200, -77691031680), (Sum.inl 2201, -3888915600), (Sum.inl 2207, -20547720000), (Sum.inl 2238, 31022502720), (Sum.inl 2239, -317340480), (Sum.inl 2240, -34636753920), (Sum.inl 2246, 387034596480), (Sum.inl 2256, -81358596480), (Sum.inl 2257, 9476558400), (Sum.inl 2258, -7593210720), (Sum.inl 2259, -26794424880), (Sum.inl 2267, 65283607200), (Sum.inl 2286, 37284743040), (Sum.inl 4157, -4109989440), (Sum.inl 4162, -15698606080), (Sum.inl 4184, -19033818240), (Sum.inl 4193, -2585122560), (Sum.inl 4353, 83927070720), (Sum.inl 4362, -12841920000), (Sum.inl 4442, 72738019520), (Sum.inl 4464, -193594554240), (Sum.inl 4478, -100743450880), (Sum.inl 4508, -118817832960), (Sum.inl 4532, -71301580800), (Sum.inl 4536, -215902407360), (Sum.inl 4552, -310764126720), (Sum.inl 4560, -30372842880), (Sum.inl 4663, -89836032000), (Sum.inl 4664, -95903484480), (Sum.inl 4666, -165968332800), (Sum.inl 4696, 124090010880), (Sum.inl 4697, -1269361920), (Sum.inl 4699, -325434385920), (Sum.inl 4701, 37906233600), (Sum.inl 4705, 149138972160), (Sum.inl 4771, -56945998080), (Sum.inl 4772, -186910251840), (Sum.inl 4774, -56306315520), (Sum.inl 4792, -15555662400), (Sum.inl 4815, 261613056000), (Sum.inl 4817, -82190880000), (Sum.inl 4851, -138547015680), (Sum.inl 4853, -107177699520), (Sum.inl 4879, 1548138385920), (Sum.inl 4881, 261134428800)]

theorem originalBlockCheck70 : originalBlock70 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock70 keyMomentRows) := by decide +kernel

theorem originalBlockEval70 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock70 x =
      Integer.Sparse.eval keyPolynomialBlock70 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck70, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
