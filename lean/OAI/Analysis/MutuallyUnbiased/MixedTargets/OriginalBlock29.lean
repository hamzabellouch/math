import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock29 : Integer.Sparse (Fin 2886) := [(928, -36049392000), (929, -4079589120), (930, 184428679680), (931, -222970521600), (932, -20355807360), (933, -104945280), (934, -59045352000), (935, -29794296960), (936, 19140878400), (937, 7079086080), (938, 16494482880), (939, -64920779520), (940, 6370032960), (941, 15863424000), (942, -19381936320), (943, 11365163040), (944, -16491696480), (945, 19270920960), (946, 51401866080), (947, 18475167840), (948, 2659780800), (949, -216714240), (950, -5166429120), (951, 3284599680), (952, -4025032320), (953, -3347095680), (954, -3989436480), (955, 21910199040), (956, 75516028800), (957, 33619985280), (958, 28376352000), (959, 28803375360)]

def originalBlock29 : Integer.Sparse OriginalKey := [(Sum.inl 1270, -96909681600), (Sum.inl 1273, 35395430400), (Sum.inl 1306, -148971484800), (Sum.inl 1310, -524726400), (Sum.inl 1797, 144016876800), (Sum.inl 1813, 168099926400), (Sum.inl 1820, -16735478400), (Sum.inl 1828, -19947182400), (Sum.inl 1832, -25832145600), (Sum.inl 1980, 141881760000), (Sum.inl 2037, 109550995200), (Sum.inl 2092, 377580144000), (Sum.inl 2113, -20125161600), (Sum.inl 2136, -1083571200), (Sum.inl 2255, 16422998400), (Sum.inl 2285, 13298904000), (Sum.inl 2573, 92375839200), (Sum.inl 2575, 257009330400), (Sum.inl 2600, 56825815200), (Sum.inl 2603, 82472414400), (Sum.inl 2641, 79317120000), (Sum.inl 2643, 95704392000), (Sum.inl 2754, -82458482400), (Sum.inl 2769, -324603897600), (Sum.inl 2777, -295226760000), (Sum.inl 2789, -101779036800), (Sum.inl 2964, -180246960000), (Sum.inl 3084, -1114852608000), (Sum.inl 3096, -20397945600), (Sum.inl 3097, 922143398400), (Sum.inl 3108, 96354604800), (Sum.inl 3118, 31850164800)]

theorem originalBlockCheck29 : originalBlock29 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock29 keyMomentRows) := by decide +kernel

theorem originalBlockEval29 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock29 x =
      Integer.Sparse.eval keyPolynomialBlock29 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck29, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
