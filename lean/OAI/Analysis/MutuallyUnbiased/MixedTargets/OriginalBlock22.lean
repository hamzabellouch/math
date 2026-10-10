import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock22 : Integer.Sparse (Fin 2886) := [(704, -63478552320), (705, -5321594880), (706, 778348800), (707, -5166365760), (708, 1290975840), (709, 12944257600), (710, -5321594880), (711, 4511577600), (712, -25363775600), (713, 3113416000), (714, -9795297600), (715, -63023193600), (716, 28415707200), (717, 4496332800), (718, 15244800), (719, -5321594880), (720, 2685520880), (721, 9080424000), (722, 5321594880), (723, -16939689600), (724, -4496332800), (725, 17511888960), (726, -5815324800), (727, -15244800), (728, -60162984000), (729, 60162984000), (730, -10259016000), (731, 9767424000), (732, 143441760), (733, 7776671360), (734, 778348800), (735, 1195348000)]

def originalBlock22 : Integer.Sparse OriginalKey := [(Sum.inl 149, -84698448000), (Sum.inl 301, 48837120000), (Sum.inl 305, 3891744000), (Sum.inl 306, 300814920000), (Sum.inl 325, -76224000), (Sum.inl 326, 3891744000), (Sum.inl 376, 717208800), (Sum.inl 377, -35728000000), (Sum.inl 378, 5976740000), (Sum.inl 387, 22557888000), (Sum.inl 390, -22481664000), (Sum.inl 402, -300814920000), (Sum.inl 403, -26607974400), (Sum.inl 404, 26607974400), (Sum.inl 405, 103604644800), (Sum.inl 429, 76224000), (Sum.inl 432, 142078536000), (Sum.inl 479, 6454879200), (Sum.inl 483, 22481664000), (Sum.inl 488, -26607974400), (Sum.inl 489, -26607974400), (Sum.inl 496, -315115968000), (Sum.inl 520, -3574368000), (Sum.inl 521, -29076624000), (Sum.inl 526, -113391273600), (Sum.inl 527, 87559444800), (Sum.inl 532, -317392761600), (Sum.inl 533, -25831828800)]

theorem originalBlockCheck22 : originalBlock22 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock22 keyMomentRows) := by decide +kernel

theorem originalBlockEval22 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock22 x =
      Integer.Sparse.eval keyPolynomialBlock22 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck22, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
