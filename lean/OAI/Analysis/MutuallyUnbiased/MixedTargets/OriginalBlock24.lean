import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock24 : Integer.Sparse (Fin 2886) := [(768, 5321594880), (769, -4511577600), (770, 20892408000), (771, -1966368000), (772, -932010240), (773, -4161320640), (774, 4838744640), (775, -4864653120), (776, -2276884800), (777, -13063399680), (778, 23154986880), (779, 15521053760), (780, -1203850560), (781, -11092952640), (782, 63023193600), (783, 17182392000), (784, -20368003200), (785, 1398015360), (786, -45598099200), (787, -4496332800), (788, -15244800), (789, 5321594880), (790, 14846243520), (791, -5321594880), (792, 16939689600), (793, 4496332800), (794, -24042087360), (795, -12345523200), (796, 15244800), (797, 22465026240), (798, 1327024320), (799, 4030504320)]

def originalBlock24 : Integer.Sparse OriginalKey := [(Sum.inl 22, -20806603200), (Sum.inl 26, 20152521600), (Sum.inl 30, 6635121600), (Sum.inl 91, 24193723200), (Sum.inl 124, 84698448000), (Sum.inl 155, -4660051200), (Sum.inl 157, 112325131200), (Sum.inl 174, -6019252800), (Sum.inl 178, -65316998400), (Sum.inl 221, -55464763200), (Sum.inl 234, 115774934400), (Sum.inl 245, -11384424000), (Sum.inl 260, 77605268800), (Sum.inl 268, -24323265600), (Sum.inl 289, -227990496000), (Sum.inl 293, 76224000), (Sum.inl 301, -9831840000), (Sum.inl 310, -22557888000), (Sum.inl 312, 22481664000), (Sum.inl 334, 26607974400), (Sum.inl 336, -26607974400), (Sum.inl 423, -76224000), (Sum.inl 424, 85911960000), (Sum.inl 437, -22481664000), (Sum.inl 450, 6990076800), (Sum.inl 467, 315115968000), (Sum.inl 472, 26607974400), (Sum.inl 503, -101840016000), (Sum.inl 517, -61727616000), (Sum.inl 520, 178693257600), (Sum.inl 521, -120210436800)]

theorem originalBlockCheck24 : originalBlock24 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock24 keyMomentRows) := by decide +kernel

theorem originalBlockEval24 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock24 x =
      Integer.Sparse.eval keyPolynomialBlock24 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck24, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
