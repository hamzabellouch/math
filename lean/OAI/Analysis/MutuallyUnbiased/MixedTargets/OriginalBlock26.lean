import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock26 : Integer.Sparse (Fin 2886) := [(832, 130816320), (833, 15116823680), (834, -12345523200), (835, -11306956800), (836, -1488550080), (837, -106003785600), (838, 106003785600), (839, -5531680320), (840, -9503812800), (841, -20716922880), (842, -2832503040), (843, 11649499200), (844, 3594201600), (845, -28344173760), (846, -23457219840), (847, -1972067520), (848, 46731375360), (849, -88185976320), (850, -9764424000), (851, -23304249600), (852, -24632757120), (853, -8902558560), (854, -29171005440), (855, -33694815360), (856, 11704045440), (857, -8577817920), (858, 12928711680), (859, 17480376480), (860, -15921950400), (861, -626952960), (862, 2761647360), (863, 124757280960)]

def originalBlock26 : Integer.Sparse OriginalKey := [(Sum.inl 34, 654081600), (Sum.inl 39, -27658401600), (Sum.inl 69, -56534784000), (Sum.inl 99, 75584118400), (Sum.inl 186, -7442750400), (Sum.inl 275, -530018928000), (Sum.inl 277, 530018928000), (Sum.inl 510, -61727616000), (Sum.inl 2243, 87401882400), (Sum.inl 2244, -145855027200), (Sum.inl 2245, -168474076800), (Sum.inl 2247, -117286099200), (Sum.inl 2262, 58520227200), (Sum.inl 2263, -42889089600), (Sum.inl 2264, -9860337600), (Sum.inl 2265, 233656876800), (Sum.inl 2266, -440929881600), (Sum.inl 2268, -183194366400), (Sum.inl 2277, 64643558400), (Sum.inl 2278, -48822120000), (Sum.inl 2279, -116521248000), (Sum.inl 2281, -14162515200), (Sum.inl 2291, -123163785600), (Sum.inl 2293, 17971008000), (Sum.inl 2294, -141720868800), (Sum.inl 2734, -3134764800), (Sum.inl 2740, 13808236800), (Sum.inl 2742, 623786404800), (Sum.inl 4083, -44512792800), (Sum.inl 4084, 58247496000), (Sum.inl 4085, -47519064000)]

theorem originalBlockCheck26 : originalBlock26 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock26 keyMomentRows) := by decide +kernel

theorem originalBlockEval26 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock26 x =
      Integer.Sparse.eval keyPolynomialBlock26 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck26, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
