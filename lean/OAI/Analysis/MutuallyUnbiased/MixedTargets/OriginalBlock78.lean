import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock78 : Integer.Sparse (Fin 2886) := [(2496, 133109377360), (2497, 2581495960), (2498, 173815992000), (2499, 63243540000), (2500, 31159570480), (2501, 5916834080), (2502, 63279700800), (2503, -65633791200), (2504, 22988392800), (2505, 2014495680), (2506, 61881626560), (2507, -29434869600), (2508, -3120878880), (2509, -149969145600), (2510, -14079306480), (2511, -88321265280), (2512, 8725170240), (2513, -102848410080), (2514, -416271120), (2515, 97890662400), (2516, 20479536000), (2517, 23608051200), (2518, 73703074320), (2519, -15470073480), (2520, 12391456080), (2521, -28844880000), (2522, -65612324040), (2523, -28582650720), (2524, 44975981600), (2525, -158264635200), (2526, 172581972960), (2527, -151040588880)]

def originalBlock78 : Integer.Sparse OriginalKey := [(Sum.inl 2664, 23608051200), (Sum.inl 2676, 12391456080), (Sum.inl 2677, 20479536000), (Sum.inl 2678, 97890662400), (Sum.inl 2680, 8725170240), (Sum.inl 2697, -28582650720), (Sum.inl 2698, -28844880000), (Sum.inl 2730, -65612324040), (Sum.inl 2731, 73703074320), (Sum.inl 2732, -102848410080), (Sum.inl 2734, -149969145600), (Sum.inl 2773, -416271120), (Sum.inl 2774, -88321265280), (Sum.inl 2775, -15470073480), (Sum.inl 2776, -14079306480), (Sum.inl 2778, -3120878880), (Sum.inl 3039, -158264635200), (Sum.inl 3225, 44975981600), (Sum.inl 3302, 2014495680), (Sum.inl 3523, -65633791200), (Sum.inl 3524, 5916834080), (Sum.inl 3529, 22988392800), (Sum.inl 3530, 61881626560), (Sum.inl 3537, 63279700800), (Sum.inl 3538, 31159570480), (Sum.inl 3542, -29434869600), (Sum.inl 3562, 63243540000), (Sum.inl 3565, 133109377360), (Sum.inl 3580, 2581495960), (Sum.inl 3881, -151040588880), (Sum.inl 3883, 172581972960), (Sum.inl 3960, 173815992000), (Sum.inl 4609, 8057982720), (Sum.inl 4896, 179903926400), (Sum.inl 4899, -12483515520), (Sum.inl 5139, -262535164800), (Sum.inl 5145, 252974160000), (Sum.inl 5147, 247526506240), (Sum.inl 5164, 532437509440), (Sum.inl 5184, 23667336320), (Sum.inl 5185, 91953571200), (Sum.inl 5187, 253118803200), (Sum.inl 5188, 124638281920), (Sum.inl 5189, -117739478400), (Sum.inl 5222, 94432204800), (Sum.inl 5231, 49565824320), (Sum.inl 5232, 81918144000), (Sum.inl 5233, 391562649600), (Sum.inl 5235, 34900680960), (Sum.inl 5243, -114330602880), (Sum.inl 5244, -115379520000), (Sum.inl 5265, -262449296160), (Sum.inl 5266, -338246243520), (Sum.inl 5267, -411393640320), (Sum.inl 5268, -599876582400), (Sum.inl 5282, 10325983840), (Sum.inl 5299, -1665084480), (Sum.inl 5300, -353285061120), (Sum.inl 5301, -61880293920), (Sum.inl 5302, -56317225920), (Sum.inl 5411, 690327891840), (Sum.inl 5446, -604162355520), (Sum.inl 5463, 695263968000)]

theorem originalBlockCheck78 : originalBlock78 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock78 keyMomentRows) := by decide +kernel

theorem originalBlockEval78 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock78 x =
      Integer.Sparse.eval keyPolynomialBlock78 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck78, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
