import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock84 : Integer.Sparse (Fin 2886) := [(2688, 120925828800), (2689, 34333871040), (2690, 295124194240), (2691, 18758213000), (2692, 16155720480), (2693, -25307791360), (2694, -67165112880), (2695, -2034772080), (2696, 17682887520), (2697, 55271146720), (2698, 48308224200), (2699, -24528769920), (2700, -17029644480), (2701, 15275984160), (2702, 78108851520), (2703, -17194545400), (2704, -50478153360), (2705, 25338206080), (2706, -212802172000), (2707, -57578695560), (2708, 19207074240), (2709, -13314241320), (2710, -8039874240), (2711, -32556736560), (2712, -135136641600), (2713, -13241985360), (2714, -66152373120), (2715, -21855207840), (2716, 58899945120), (2717, 2985990720), (2718, -63013829520), (2719, -84110226760)]

def originalBlock84 : Integer.Sparse OriginalKey := [(Sum.inl 2147, -13241985360), (Sum.inl 2153, -135136641600), (Sum.inl 2175, -66152373120), (Sum.inl 2201, -21855207840), (Sum.inl 2207, -8039874240), (Sum.inl 2259, -32556736560), (Sum.inl 3291, 25338206080), (Sum.inl 3302, -50478153360), (Sum.inl 3462, -63013829520), (Sum.inl 3463, 2985990720), (Sum.inl 3464, 58899945120), (Sum.inl 3480, -84110226760), (Sum.inl 3516, 17682887520), (Sum.inl 3519, -13314241320), (Sum.inl 3523, -212802172000), (Sum.inl 3524, -17029644480), (Sum.inl 3526, -24528769920), (Sum.inl 3530, 112442722560), (Sum.inl 3535, 15275984160), (Sum.inl 3537, 55271146720), (Sum.inl 3538, -2034772080), (Sum.inl 3539, 48308224200), (Sum.inl 3540, -67165112880), (Sum.inl 3541, -25307791360), (Sum.inl 3542, 19207074240), (Sum.inl 3543, -57578695560), (Sum.inl 3549, -17194545400), (Sum.inl 3562, 16155720480), (Sum.inl 3578, 295124194240), (Sum.inl 3579, 120925828800), (Sum.inl 3580, 18758213000), (Sum.inl 4591, 101352824320), (Sum.inl 4609, -201912613440), (Sum.inl 4664, -52967941440), (Sum.inl 4682, -540546566400), (Sum.inl 4761, -264609492480), (Sum.inl 4792, -87420831360), (Sum.inl 4817, -32159496960), (Sum.inl 4853, -130226946240), (Sum.inl 5042, -252055318080), (Sum.inl 5074, 11943962880), (Sum.inl 5086, 235599780480), (Sum.inl 5090, -336440907040), (Sum.inl 5128, -53256965280), (Sum.inl 5129, 70731550080), (Sum.inl 5139, -851208688000), (Sum.inl 5145, 64622881920), (Sum.inl 5147, 449770890240), (Sum.inl 5184, -68118577920), (Sum.inl 5187, 221084586880), (Sum.inl 5188, -8139088320), (Sum.inl 5189, 76828296960), (Sum.inl 5199, 1180496776960), (Sum.inl 5201, 483703315200), (Sum.inl 5251, 193232896800), (Sum.inl 5252, -230314782240), (Sum.inl 5260, -268660451520), (Sum.inl 5265, -98115079680), (Sum.inl 5266, 61103936640), (Sum.inl 5267, -101231165440), (Sum.inl 5268, -68778181600), (Sum.inl 5282, 75032852000)]

theorem originalBlockCheck84 : originalBlock84 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock84 keyMomentRows) := by decide +kernel

theorem originalBlockEval84 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock84 x =
      Integer.Sparse.eval keyPolynomialBlock84 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck84, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
