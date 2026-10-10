import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock30 : Integer.Sparse (Fin 2886) := [(960, 16533460800), (961, 16044998400), (962, -9284467680), (963, 10910926080), (964, 19835609280), (965, 11914051200), (966, -20923219680), (967, -2542207680), (968, 52549732800), (969, 951422400), (970, -22592992320), (971, -23117454720), (972, -71602124160), (973, -46537849920), (974, -85112192640), (975, -24438657600), (976, 34373554560), (977, 61001697600), (978, 57071091840), (979, 36849767040), (980, 50345853120), (981, -14412450240), (982, 35427759360), (983, -34668051360), (984, 2761647360), (985, -12025560000), (986, 2228996160), (987, 5315318400), (988, 43907532480), (989, 40694216640), (990, -34229623680), (991, -57840823680)]

def originalBlock30 : Integer.Sparse OriginalKey := [(Sum.inl 1793, 99178046400), (Sum.inl 1957, -12711038400), (Sum.inl 1965, 59570256000), (Sum.inl 1971, 82667304000), (Sum.inl 1976, 54554630400), (Sum.inl 2010, -104616098400), (Sum.inl 2026, 80224992000), (Sum.inl 2235, -46422338400), (Sum.inl 2255, 262748664000), (Sum.inl 2716, 4757112000), (Sum.inl 2803, 203471083200), (Sum.inl 2816, 26576592000), (Sum.inl 2821, -60127800000), (Sum.inl 3033, -112964961600), (Sum.inl 3062, -122193288000), (Sum.inl 3127, -72062251200), (Sum.inl 3129, -171148118400), (Sum.inl 3131, -425560963200), (Sum.inl 3134, 251729265600), (Sum.inl 3136, 184248835200), (Sum.inl 3138, 219537662400), (Sum.inl 3156, -115587273600), (Sum.inl 3161, 13808236800), (Sum.inl 3163, 285355459200), (Sum.inl 3170, 177138796800), (Sum.inl 3174, -289204118400), (Sum.inl 3180, -232689249600), (Sum.inl 3196, 171867772800), (Sum.inl 3198, 11144980800), (Sum.inl 3202, 305008488000), (Sum.inl 3221, -173340256800), (Sum.inl 3222, -358010620800)]

theorem originalBlockCheck30 : originalBlock30 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock30 keyMomentRows) := by decide +kernel

theorem originalBlockEval30 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock30 x =
      Integer.Sparse.eval keyPolynomialBlock30 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck30, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
