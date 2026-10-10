import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock86 : Integer.Sparse (Fin 2886) := [(2752, -4749425680), (2753, 30723827920), (2754, 11529636880), (2755, -40891467760), (2756, -24878305840), (2757, 12932955920), (2758, -3537700800), (2759, -24240774400), (2760, 15773304000), (2761, 20010395440), (2762, -30400177280), (2763, -32053738400), (2764, -39808563600), (2765, -11048475840), (2766, -42685139784), (2767, -4183807880), (2768, -3263229280), (2769, 28301606400), (2770, 52615829600), (2771, -10038288560), (2772, 5759404800), (2773, 12229556240), (2774, -30751249440), (2775, -12420556560), (2776, 34567384320), (2777, -4411061760), (2778, -37829664000), (2779, -1563432960), (2780, 37829664000), (2781, 5614752000), (2782, -14164588800), (2783, 15559531200)]

def originalBlock86 : Integer.Sparse OriginalKey := [(Sum.inl 1516, 12229556240), (Sum.inl 1672, -30751249440), (Sum.inl 2149, -39808563600), (Sum.inl 2172, -11048475840), (Sum.inl 2661, 5614752000), (Sum.inl 2662, 37829664000), (Sum.inl 2710, -1563432960), (Sum.inl 2724, -14164588800), (Sum.inl 2751, -37829664000), (Sum.inl 2753, -4411061760), (Sum.inl 2755, 34567384320), (Sum.inl 2763, 15559531200), (Sum.inl 3255, 28301606400), (Sum.inl 3258, -42685139784), (Sum.inl 3260, -10038288560), (Sum.inl 3261, 5759404800), (Sum.inl 3262, 52615829600), (Sum.inl 3267, -3263229280), (Sum.inl 3268, -4183807880), (Sum.inl 3272, -12420556560), (Sum.inl 3288, 9395255120), (Sum.inl 3289, 30723827920), (Sum.inl 3290, 15773304000), (Sum.inl 3291, -54640951680), (Sum.inl 3294, -40891467760), (Sum.inl 3295, -24878305840), (Sum.inl 3296, -4749425680), (Sum.inl 3297, -32053738400), (Sum.inl 3298, 20010395440), (Sum.inl 3302, 11529636880), (Sum.inl 4156, 48918224960), (Sum.inl 4330, -123004997760), (Sum.inl 4527, 113206425600), (Sum.inl 4528, -40153154240), (Sum.inl 4529, -170740559136), (Sum.inl 4530, 23037619200), (Sum.inl 4531, 210463318400), (Sum.inl 4532, -44193903360), (Sum.inl 4533, -13052917120), (Sum.inl 4534, -16735231520), (Sum.inl 4535, -49682226240), (Sum.inl 4536, -159234254400), (Sum.inl 4589, 37581020480), (Sum.inl 4590, 63093216000), (Sum.inl 4591, -218563806720), (Sum.inl 4592, -99513223360), (Sum.inl 4593, -128214953600), (Sum.inl 4594, 80041581760), (Sum.inl 4599, 122895311680), (Sum.inl 4603, -163565871040), (Sum.inl 4607, -18997702720), (Sum.inl 4609, 46118547520), (Sum.inl 4890, 138269537280), (Sum.inl 5219, 22459008000), (Sum.inl 5220, 151318656000), (Sum.inl 5251, -6253731840), (Sum.inl 5260, -56658355200), (Sum.inl 5282, -151318656000), (Sum.inl 5284, -17644247040), (Sum.inl 5289, 62238124800)]

theorem originalBlockCheck86 : originalBlock86 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock86 keyMomentRows) := by decide +kernel

theorem originalBlockEval86 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock86 x =
      Integer.Sparse.eval keyPolynomialBlock86 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck86, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
