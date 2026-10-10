import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock23 : Integer.Sparse (Fin 2886) := [(736, -10360464480), (737, 7801056000), (738, -9767424000), (739, 12466367040), (740, 2810002560), (741, -965890800), (742, -9927207360), (743, -9927207360), (744, -1545425280), (745, 9927207360), (746, -573767040), (747, 9927207360), (748, 772712640), (749, 965890800), (750, 113365920), (751, -4161320640), (752, 15086390400), (753, -23154986880), (754, -4003565760), (755, 906927360), (756, 778565760), (757, -1398015360), (758, 6228526080), (759, -1165012800), (760, 4511577600), (761, 1966368000), (762, 2873224800), (763, 5321594880), (764, -2632325760), (765, -25302504960), (766, 28474176960), (767, 4788708000)]

def originalBlock23 : Integer.Sparse OriginalKey := [(Sum.inl 8, -7727126400), (Sum.inl 9, 4829454000), (Sum.inl 21, -49636036800), (Sum.inl 24, 49636036800), (Sum.inl 98, 62331835200), (Sum.inl 100, 14050012800), (Sum.inl 163, 3863563200), (Sum.inl 171, 75431952000), (Sum.inl 172, 49636036800), (Sum.inl 207, -13161628800), (Sum.inl 220, 4534636800), (Sum.inl 232, -115774934400), (Sum.inl 242, -49636036800), (Sum.inl 243, -20806603200), (Sum.inl 257, -4829454000), (Sum.inl 259, -20017828800), (Sum.inl 260, 566829600), (Sum.inl 303, -48837120000), (Sum.inl 321, -2868835200), (Sum.inl 339, 23943540000), (Sum.inl 371, -126512524800), (Sum.inl 379, 39005280000), (Sum.inl 407, -51802322400), (Sum.inl 429, 9831840000), (Sum.inl 436, 22557888000), (Sum.inl 448, -5825064000), (Sum.inl 449, 31142630400), (Sum.inl 502, -6990076800), (Sum.inl 504, 14366124000), (Sum.inl 505, 3892828800), (Sum.inl 525, 26607974400), (Sum.inl 531, 142370884800)]

theorem originalBlockCheck23 : originalBlock23 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock23 keyMomentRows) := by decide +kernel

theorem originalBlockEval23 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock23 x =
      Integer.Sparse.eval keyPolynomialBlock23 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck23, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
