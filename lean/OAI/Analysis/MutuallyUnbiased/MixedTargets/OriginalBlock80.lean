import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock80 : Integer.Sparse (Fin 2886) := [(2560, 31541459520), (2561, -44657792160), (2562, -49852232640), (2563, 10651267200), (2564, 122991876480), (2565, -70259291520), (2566, 148491963360), (2567, 31886642880), (2568, 23979208800), (2569, -26523501600), (2570, 44837716800), (2571, -79936891680), (2572, 103267498800), (2573, -220655614320), (2574, -75840805840), (2575, -114367811520), (2576, 78936544320), (2577, -65159040000), (2578, -4824040720), (2579, -33392949200), (2580, 32205942360), (2581, -19207074240), (2582, -9298233920), (2583, 35162608800), (2584, 36502799040), (2585, 98777203200), (2586, 107266045360), (2587, 72601052160), (2588, -27682830720), (2589, 20597398080), (2590, 28063444320), (2591, 19866199680)]

def originalBlock80 : Integer.Sparse OriginalKey := [(Sum.inl 2145, 19866199680), (Sum.inl 2146, -27682830720), (Sum.inl 2196, 20597398080), (Sum.inl 2197, 98777203200), (Sum.inl 2250, 28063444320), (Sum.inl 2251, 72601052160), (Sum.inl 2253, 107266045360), (Sum.inl 2255, 36502799040), (Sum.inl 2670, -114367811520), (Sum.inl 2676, 10651267200), (Sum.inl 2681, -70259291520), (Sum.inl 2682, -65159040000), (Sum.inl 2683, -79936891680), (Sum.inl 3037, 31541459520), (Sum.inl 3051, 122991876480), (Sum.inl 3052, 44837716800), (Sum.inl 3288, -4824040720), (Sum.inl 3295, -75840805840), (Sum.inl 3296, -220655614320), (Sum.inl 3516, 14680974880), (Sum.inl 3517, -33392949200), (Sum.inl 3539, 32205942360), (Sum.inl 3540, 78936544320), (Sum.inl 3541, 103267498800), (Sum.inl 3557, 31886642880), (Sum.inl 3835, 35162608800), (Sum.inl 3839, 148491963360), (Sum.inl 3842, -19207074240), (Sum.inl 3846, -49852232640), (Sum.inl 3847, -44657792160), (Sum.inl 3848, -26523501600), (Sum.inl 4589, -19296162880), (Sum.inl 4592, -303363223360), (Sum.inl 4607, -882622457280), (Sum.inl 4611, -319747566720), (Sum.inl 4680, 79464798720), (Sum.inl 4683, -110731322880), (Sum.inl 4816, 82389592320), (Sum.inl 4836, 395108812800), (Sum.inl 4852, 112253777280), (Sum.inl 4867, 290404208640), (Sum.inl 4891, 429064181440), (Sum.inl 4892, 146011196160), (Sum.inl 5129, 58723899520), (Sum.inl 5138, -133571796800), (Sum.inl 5140, -457471246080), (Sum.inl 5144, 127546571520), (Sum.inl 5151, -281037166080), (Sum.inl 5231, 42605068800), (Sum.inl 5236, -260636160000), (Sum.inl 5251, 128823769440), (Sum.inl 5260, 315746177280), (Sum.inl 5265, 126165838080), (Sum.inl 5267, 413069995200), (Sum.inl 5276, 179350867200), (Sum.inl 5299, 491967505920), (Sum.inl 5377, 140650435200), (Sum.inl 5406, -178631168640), (Sum.inl 5419, -76828296960), (Sum.inl 5425, 593967853440), (Sum.inl 5429, -199408930560), (Sum.inl 5430, -106094006400)]

theorem originalBlockCheck80 : originalBlock80 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock80 keyMomentRows) := by decide +kernel

theorem originalBlockEval80 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock80 x =
      Integer.Sparse.eval keyPolynomialBlock80 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck80, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
