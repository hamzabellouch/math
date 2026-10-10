import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock20 : Integer.Sparse (Fin 2886) := [(640, -1966368000), (641, -1557131520), (642, 233002560), (643, -7007091840), (644, -233002560), (645, -4511577600), (646, -983184000), (647, 242702400), (648, -4496332800), (649, -15244800), (650, 21533016000), (651, -21533016000), (652, -242702400), (653, 4496332800), (654, 15244800), (655, 10259016000), (656, -9767424000), (657, 11667543040), (658, -9275832000), (659, 9767424000), (660, -2282120640), (661, 2282120640), (662, 9775883520), (663, 5844191040), (664, 12577524480), (665, 5844191040), (666, -19551767040), (667, -5844191040), (668, -12577524480), (669, 286883520), (670, -12577524480), (671, 239069600)]

def originalBlock20 : Integer.Sparse OriginalKey := [(Sum.inl 0, 48879417600), (Sum.inl 3, 29220955200), (Sum.inl 111, -11410603200), (Sum.inl 112, 11410603200), (Sum.inl 265, -97758835200), (Sum.inl 310, -48837120000), (Sum.inl 312, 48837120000), (Sum.inl 355, -1213512000), (Sum.inl 382, -62887622400), (Sum.inl 386, -62887622400), (Sum.inl 387, 51295080000), (Sum.inl 390, -46379160000), (Sum.inl 411, 62887622400), (Sum.inl 420, 58337715200), (Sum.inl 436, -76224000), (Sum.inl 437, 76224000), (Sum.inl 438, 1213512000), (Sum.inl 464, -29220955200), (Sum.inl 479, -9831840000), (Sum.inl 483, -4915920000), (Sum.inl 488, 1195348000), (Sum.inl 492, 29220955200), (Sum.inl 496, -35035459200), (Sum.inl 502, -1165012800), (Sum.inl 503, -107665080000), (Sum.inl 514, -45039552000), (Sum.inl 516, 22481664000), (Sum.inl 528, 1165012800), (Sum.inl 530, 107665080000), (Sum.inr 5, -7785657600), (Sum.inr 7, 1434417600)]

theorem originalBlockCheck20 : originalBlock20 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock20 keyMomentRows) := by decide +kernel

theorem originalBlockEval20 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock20 x =
      Integer.Sparse.eval keyPolynomialBlock20 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck20, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
