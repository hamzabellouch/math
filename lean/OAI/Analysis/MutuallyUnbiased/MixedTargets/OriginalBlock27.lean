import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock27 : Integer.Sparse (Fin 2886) := [(864, 38659256640), (865, -39041011200), (866, -139338829440), (867, -15298080000), (868, -53502945600), (869, -11586662400), (870, -26782492800), (871, -841374720), (872, 33502659840), (873, 51263390400), (874, 5789256000), (875, -5331376320), (876, 19464549600), (877, -59197275840), (878, 15514438560), (879, -2761647360), (880, -4111730880), (881, 59045352000), (882, 28669344960), (883, -2238993600), (884, 24027390720), (885, 841374720), (886, -81169111680), (887, -15863424000), (888, 30703624320), (889, 13384772640), (890, -43329504960), (891, -697308960), (892, 51263390400), (893, 20184249600), (894, 16303636800), (895, 17888192640)]

def originalBlock27 : Integer.Sparse OriginalKey := [(Sum.inl 2281, 100921248000), (Sum.inl 2709, 28946280000), (Sum.inl 2710, -26656881600), (Sum.inl 2720, 97322748000), (Sum.inl 2721, -295986379200), (Sum.inl 2722, -696694147200), (Sum.inl 2723, -76490400000), (Sum.inl 2724, -267514728000), (Sum.inl 2730, 77572192800), (Sum.inl 2731, -57933312000), (Sum.inl 2732, -133912464000), (Sum.inl 2734, 81518184000), (Sum.inl 2738, -4206873600), (Sum.inl 2739, 167513299200), (Sum.inl 2741, 256316952000), (Sum.inl 2743, 193296283200), (Sum.inl 2744, -195205056000), (Sum.inl 2750, 256316952000), (Sum.inl 2751, -79317120000), (Sum.inl 2754, 153518121600), (Sum.inl 2763, 66923863200), (Sum.inl 2764, -216647524800), (Sum.inl 2765, 295226760000), (Sum.inl 2769, 143346724800), (Sum.inl 2773, -3486544800), (Sum.inl 2774, -11194968000), (Sum.inl 2777, 120136953600), (Sum.inl 2781, 4206873600), (Sum.inl 2782, -405845558400), (Sum.inl 2783, -13808236800), (Sum.inl 2789, -20558654400), (Sum.inl 3046, 89440963200)]

theorem originalBlockCheck27 : originalBlock27 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock27 keyMomentRows) := by decide +kernel

theorem originalBlockEval27 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock27 x =
      Integer.Sparse.eval keyPolynomialBlock27 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck27, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
