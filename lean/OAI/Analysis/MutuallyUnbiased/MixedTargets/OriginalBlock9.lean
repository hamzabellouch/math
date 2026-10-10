import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock9 : Integer.Sparse (Fin 2886) := [(288, -4891350000), (289, -6736400880), (290, 14068899600), (291, 11693349600), (292, -4891350000), (293, -4593000600), (294, -6882288000), (295, -30098402800), (296, 7373880000), (297, -31096581600), (298, 4891350000), (299, 5817800760), (300, 14476542480), (301, -14809605760), (302, 31525516800), (303, -5851062720), (304, 6062232000), (305, -96702295200), (306, -11702125440), (307, 50415792000), (308, 30096136800), (309, 1675752000), (310, 2973138240), (311, 1455396480), (312, -4922282880), (313, 1455396480), (314, 1557131520), (315, -10881866880), (316, 4922282880), (317, 21031476480), (318, -2910792960), (319, 13477086080)]

def originalBlock9 : Integer.Sparse OriginalKey := [(Sum.inl 147, -74048028800), (Sum.inl 153, -155482908000), (Sum.inl 244, 8378760000), (Sum.inl 248, -24611414400), (Sum.inl 249, 24611414400), (Sum.inl 330, -24456750000), (Sum.inl 333, 24456750000), (Sum.inl 337, -14553964800), (Sum.inl 346, 72382712400), (Sum.inl 390, 36869400000), (Sum.inl 394, -33682004400), (Sum.inl 395, 29089003800), (Sum.inl 402, 30311160000), (Sum.inl 410, -150492014000), (Sum.inl 420, 225013014400), (Sum.inl 446, -58510627200), (Sum.inl 447, 58466748000), (Sum.inl 456, 14865691200), (Sum.inl 459, 7276982400), (Sum.inl 470, -24456750000), (Sum.inl 483, -34411440000), (Sum.inl 484, -22965003000), (Sum.inl 487, 150480684000), (Sum.inl 491, 70344498000), (Sum.inl 493, 252078960000), (Sum.inl 494, 112434364800), (Sum.inl 496, -83664648000), (Sum.inl 503, -483511476000), (Sum.inr 5, 7785657600)]

theorem originalBlockCheck9 : originalBlock9 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock9 keyMomentRows) := by decide +kernel

theorem originalBlockEval9 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock9 x =
      Integer.Sparse.eval keyPolynomialBlock9 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck9, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
