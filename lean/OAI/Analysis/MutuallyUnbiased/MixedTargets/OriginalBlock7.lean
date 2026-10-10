import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock7 : Integer.Sparse (Fin 2886) := [(224, 39552482400), (225, -14861740000), (226, 41434694400), (227, 18209881120), (228, 4891350000), (229, 5817800760), (230, 15152615600), (231, 41434694400), (232, 4891350000), (233, 3368200440), (234, -27352549000), (235, 13247688000), (236, -41434694400), (237, -4891350000), (238, -4593000600), (239, 18041921120), (240, -10516170720), (241, -5851062720), (242, -6062232000), (243, -3563376000), (244, -11702125440), (245, 5946276480), (246, 5177428000), (247, 6703008000), (248, 5946276480), (249, 42004716480), (250, 7373970720), (251, 6062232000), (252, 21755694240), (253, -5851062720), (254, -5946276480), (255, -17437040160)]

def originalBlock7 : Integer.Sparse OriginalKey := [(Sum.inl 5, 108778471200), (Sum.inl 6, 210023582400), (Sum.inl 261, 33515040000), (Sum.inl 384, 181259011200), (Sum.inl 385, -52580853600), (Sum.inl 405, -30311160000), (Sum.inl 409, 207173472000), (Sum.inl 410, -207173472000), (Sum.inl 412, -29255313600), (Sum.inl 420, 30311160000), (Sum.inl 462, 29731382400), (Sum.inl 468, -58510627200), (Sum.inl 484, 24456750000), (Sum.inl 485, 24456750000), (Sum.inl 486, 45930006000), (Sum.inl 487, 273525490000), (Sum.inl 489, 29731382400), (Sum.inl 490, -48421560000), (Sum.inl 491, 207173472000), (Sum.inl 495, -29255313600), (Sum.inl 496, 66238440000), (Sum.inl 498, -24456750000), (Sum.inl 500, -22965003000), (Sum.inl 501, -136762745000), (Sum.inl 503, -29731382400), (Sum.inl 506, -87185200800), (Sum.inl 507, 36869853600), (Sum.inr 3, -17816880000)]

theorem originalBlockCheck7 : originalBlock7 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock7 keyMomentRows) := by decide +kernel

theorem originalBlockEval7 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock7 x =
      Integer.Sparse.eval keyPolynomialBlock7 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck7, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
