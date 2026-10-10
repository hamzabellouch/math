import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock8 : Integer.Sparse (Fin 2886) := [(256, -3563376000), (257, -6703008000), (258, -4318654080), (259, -5946276480), (260, -4206891360), (261, -20247005320), (262, -10913104800), (263, 4761687360), (264, 17523425800), (265, 10913104800), (266, 1342258080), (267, -4891350000), (268, -4593000600), (269, 4891350000), (270, 4593000600), (271, 983184000), (272, -983184000), (273, -3130436800), (274, 10341905320), (275, 10913104800), (276, -4761687360), (277, -39193252800), (278, -22606454400), (279, -10229534400), (280, 4891350000), (281, 6124000800), (282, -983184000), (283, 9831840000), (284, 29155563400), (285, -8357064000), (286, 31096581600), (287, 19727107800)]

def originalBlock8 : Integer.Sparse OriginalKey := [(Sum.inl 145, 98635539000), (Sum.inl 150, 155482908000), (Sum.inl 268, -49167224000), (Sum.inl 272, -21034456800), (Sum.inl 381, -23808436800), (Sum.inl 387, -41785320000), (Sum.inl 409, 145777817000), (Sum.inl 410, 23808436800), (Sum.inl 443, -51147672000), (Sum.inl 444, -113032272000), (Sum.inl 467, 21978144200), (Sum.inl 469, -101235026600), (Sum.inl 479, 49159200000), (Sum.inl 480, -195966264000), (Sum.inl 483, 87617129000), (Sum.inl 485, 24456750000), (Sum.inl 489, -4915920000), (Sum.inl 491, 6711290400), (Sum.inl 496, -17816880000), (Sum.inl 498, 109131048000), (Sum.inl 499, 30620004000), (Sum.inl 504, -21593270400), (Sum.inl 512, 24456750000), (Sum.inl 513, 22965003000), (Sum.inl 514, -24456750000), (Sum.inl 515, -22965003000), (Sum.inl 516, -54565524000), (Sum.inl 521, -4915920000), (Sum.inr 4, 4915920000)]

theorem originalBlockCheck8 : originalBlock8 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock8 keyMomentRows) := by decide +kernel

theorem originalBlockEval8 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock8 x =
      Integer.Sparse.eval keyPolynomialBlock8 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck8, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
