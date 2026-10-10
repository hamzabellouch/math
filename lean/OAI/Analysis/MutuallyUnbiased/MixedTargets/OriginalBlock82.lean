import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock82 : Integer.Sparse (Fin 2886) := [(2624, -145887997200), (2625, -846506880), (2626, -48604387680), (2627, -29289765120), (2628, -67829291760), (2629, 88892606880), (2630, -38744668320), (2631, 8541086400), (2632, 124850719680), (2633, 68215020240), (2634, -52044372480), (2635, 33301422000), (2636, -70282894080), (2637, 15724160040), (2638, -34643013720), (2639, -13199134080), (2640, 206772988320), (2641, -38735335280), (2642, -152669552880), (2643, -33321692640), (2644, 23524214800), (2645, -16741642320), (2646, -59248431360), (2647, -43730807040), (2648, -41524809400), (2649, -54920555760), (2650, 4696238880), (2651, 154383516080), (2652, 47107195560), (2653, 19207074240), (2654, 60804089920), (2655, 86048565120)]

def originalBlock82 : Integer.Sparse OriginalKey := [(Sum.inl 1510, -48604387680), (Sum.inl 1526, 86048565120), (Sum.inl 1667, -38744668320), (Sum.inl 1668, -29289765120), (Sum.inl 1713, -67829291760), (Sum.inl 1714, -145887997200), (Sum.inl 1740, 60804089920), (Sum.inl 2154, 33301422000), (Sum.inl 2158, -52044372480), (Sum.inl 2178, -70282894080), (Sum.inl 2213, 15724160040), (Sum.inl 2217, 124850719680), (Sum.inl 2274, 68215020240), (Sum.inl 2658, -846506880), (Sum.inl 3267, 4696238880), (Sum.inl 3271, -54920555760), (Sum.inl 3406, 8541086400), (Sum.inl 3407, 88892606880), (Sum.inl 3454, 154383516080), (Sum.inl 3476, 47107195560), (Sum.inl 3480, -41524809400), (Sum.inl 3508, -33321692640), (Sum.inl 3555, -152669552880), (Sum.inl 3556, -43730807040), (Sum.inl 3755, 23524214800), (Sum.inl 3759, -59248431360), (Sum.inl 3760, 206772988320), (Sum.inl 3761, -13199134080), (Sum.inl 3762, -34643013720), (Sum.inl 3763, 19207074240), (Sum.inl 3768, -16741642320), (Sum.inl 3772, -38735335280), (Sum.inl 4152, -194417550720), (Sum.inl 4188, 344194260480), (Sum.inl 4328, -154978673280), (Sum.inl 4345, -117159060480), (Sum.inl 4439, -271317167040), (Sum.inl 4459, -583551988800), (Sum.inl 4480, 243216359680), (Sum.inl 4533, 18784955520), (Sum.inl 4556, -219682223040), (Sum.inl 4668, 133205688000), (Sum.inl 4690, -208177489920), (Sum.inl 4768, -281131576320), (Sum.inl 4795, 62896640160), (Sum.inl 4821, 499402878720), (Sum.inl 4856, 272860080960), (Sum.inl 4931, 34164345600), (Sum.inl 4942, 355570427520), (Sum.inl 4945, -3386027520), (Sum.inl 4955, -133286770560), (Sum.inl 4966, -610678211520), (Sum.inl 5040, 617534064320), (Sum.inl 5067, 188428782240), (Sum.inl 5090, -166099237600), (Sum.inl 5112, -174923228160), (Sum.inl 5338, 94096859200), (Sum.inl 5339, 827091953280), (Sum.inl 5340, 76828296960), (Sum.inl 5348, -66966569280), (Sum.inl 5353, -52796536320), (Sum.inl 5359, -236993725440), (Sum.inl 5360, -138572054880), (Sum.inl 5361, -154941341120)]

theorem originalBlockCheck82 : originalBlock82 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock82 keyMomentRows) := by decide +kernel

theorem originalBlockEval82 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock82 x =
      Integer.Sparse.eval keyPolynomialBlock82 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck82, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
