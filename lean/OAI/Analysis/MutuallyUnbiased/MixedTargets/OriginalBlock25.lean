import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock25 : Integer.Sparse (Fin 2886) := [(800, -20352852480), (801, 12345523200), (802, 11306956800), (803, -4204656000), (804, -9098248320), (805, -680195520), (806, 60162984000), (807, -11927064960), (808, -60162984000), (809, 7801056000), (810, -9767424000), (811, 957741600), (812, -778348800), (813, -1147534080), (814, -2873224800), (815, -7801056000), (816, 9767424000), (817, -519043840), (818, 4204656000), (819, -75577280), (820, 943747200), (821, -10184246400), (822, -2282120640), (823, -2810002560), (824, 5365171200), (825, 2276884800), (826, -12784148160), (827, 11306956800), (828, 21533016000), (829, -12345523200), (830, 24691046400), (831, -21533016000)]

def originalBlock25 : Integer.Sparse OriginalKey := [(Sum.inl 28, 21023280000), (Sum.inl 63, 56534784000), (Sum.inl 68, -50921232000), (Sum.inl 70, -14050012800), (Sum.inl 71, 4718736000), (Sum.inl 72, -11410603200), (Sum.inl 93, -101764262400), (Sum.inl 94, -377886400), (Sum.inl 158, -2595219200), (Sum.inl 161, -107665080000), (Sum.inl 175, -45491241600), (Sum.inl 183, 11384424000), (Sum.inl 210, 56534784000), (Sum.inl 222, -3400977600), (Sum.inl 227, -63920740800), (Sum.inl 247, -21023280000), (Sum.inl 252, 26825856000), (Sum.inl 285, -300814920000), (Sum.inl 291, 48837120000), (Sum.inl 293, -48837120000), (Sum.inl 294, -3891744000), (Sum.inl 303, -39005280000), (Sum.inl 321, -5737670400), (Sum.inl 325, 39005280000), (Sum.inl 332, 300814920000), (Sum.inl 339, 4788708000), (Sum.inl 341, -14366124000), (Sum.inl 343, -59635324800), (Sum.inl 452, 107665080000), (Sum.inl 508, -61727616000), (Sum.inl 509, 185182848000)]

theorem originalBlockCheck25 : originalBlock25 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock25 keyMomentRows) := by decide +kernel

theorem originalBlockEval25 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock25 x =
      Integer.Sparse.eval keyPolynomialBlock25 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck25, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
