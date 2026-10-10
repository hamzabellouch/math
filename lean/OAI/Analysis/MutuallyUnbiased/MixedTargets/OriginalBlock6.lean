import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock6 : Integer.Sparse (Fin 2886) := [(192, 6472454400), (193, 10729172160), (194, 10027419840), (195, -3178736640), (196, 12092544000), (197, -14184489600), (198, -16599544320), (199, 6052872960), (200, -1471699200), (201, 6346624320), (202, -6052872960), (203, 23375734560), (204, 115439281240), (205, 73742764800), (206, -394570560), (207, -59013377800), (208, -73742764800), (209, 8667519600), (210, 4891350000), (211, 4593000600), (212, -4891350000), (213, -4593000600), (214, -23375734560), (215, -107829550840), (216, -73742764800), (217, 394570560), (218, 31660828800), (219, 32308070400), (220, -11573959920), (221, -4891350000), (222, -4593000600), (223, 3563376000)]

def originalBlock6 : Integer.Sparse OriginalKey := [(Sum.inl 1, 116878672800), (Sum.inl 3, 22965003000), (Sum.inl 4, 577196406200), (Sum.inl 266, -116878672800), (Sum.inl 270, -15893683200), (Sum.inl 384, 1972852800), (Sum.inl 396, -30264364800), (Sum.inl 397, 31733121600), (Sum.inl 404, -82997721600), (Sum.inl 405, -7358496000), (Sum.inl 412, -72895300800), (Sum.inl 417, 30264364800), (Sum.inl 418, 53645860800), (Sum.inl 419, 60462720000), (Sum.inl 420, 50137099200), (Sum.inl 422, 32362272000), (Sum.inl 461, -24456750000), (Sum.inl 464, -22965003000), (Sum.inl 465, -834214643200), (Sum.inl 466, 24456750000), (Sum.inl 467, -368713824000), (Sum.inl 468, 43337598000), (Sum.inl 469, 368713824000), (Sum.inl 478, 158304144000), (Sum.inl 479, -24456750000), (Sum.inl 480, 161540352000), (Sum.inl 481, -57869799600), (Sum.inl 482, -22965003000), (Sum.inl 483, -368713824000), (Sum.inr 3, 17816880000)]

theorem originalBlockCheck6 : originalBlock6 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock6 keyMomentRows) := by decide +kernel

theorem originalBlockEval6 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock6 x =
      Integer.Sparse.eval keyPolynomialBlock6 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck6, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
