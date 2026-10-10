import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock66 : Integer.Sparse (Fin 2886) := [(2112, 131229672720), (2113, -9690454880), (2114, -26760117120), (2115, 18091419840), (2116, -57081145120), (2117, -6363334320), (2118, 16189117920), (2119, 99197019360), (2120, 40264353360), (2121, 81239126400), (2122, 20783692320), (2123, -15832544160), (2124, 20936366640), (2125, -59143728960), (2126, -29358881040), (2127, 81173468160), (2128, 74963023680), (2129, 82255072920), (2130, 2628710400), (2131, 37334957520), (2132, -31265090760), (2133, -47344442160), (2134, 10032668640), (2135, -40049530080), (2136, -59091869600), (2137, -22095397440), (2138, -16215945520), (2139, -61828894080), (2140, 186807476960), (2141, -19790860320), (2142, -224386793040), (2143, -106234789400)]

def originalBlock66 : Integer.Sparse OriginalKey := [(Sum.inl 0, 131229672720), (Sum.inl 2754, 81173468160), (Sum.inl 2769, -61828894080), (Sum.inl 2777, 20783692320), (Sum.inl 2789, -40049530080), (Sum.inl 3037, -47344442160), (Sum.inl 3038, -29358881040), (Sum.inl 3052, -16215945520), (Sum.inl 3064, 2628710400), (Sum.inl 3075, -19790860320), (Sum.inl 3085, 37334957520), (Sum.inl 3086, -59143728960), (Sum.inl 3087, -31265090760), (Sum.inl 3088, 20936366640), (Sum.inl 3089, -15832544160), (Sum.inl 3097, -224386793040), (Sum.inl 3098, -22095397440), (Sum.inl 3099, -106234789400), (Sum.inl 3103, -59091869600), (Sum.inl 3109, 74963023680), (Sum.inl 3110, 81239126400), (Sum.inl 3111, 82255072920), (Sum.inl 3112, 40264353360), (Sum.inl 3113, 99197019360), (Sum.inl 3114, 16189117920), (Sum.inl 3119, 186807476960), (Sum.inl 3125, 10032668640), (Sum.inl 3223, -66771600000), (Sum.inl 3226, -6363334320), (Sum.inl 3227, -26760117120), (Sum.inl 3228, 18091419840), (Sum.inl 4083, 524918690880), (Sum.inl 4887, -25453337280), (Sum.inl 4888, -107040468480), (Sum.inl 4889, -267086400000), (Sum.inl 4893, 72365679360), (Sum.inl 4897, 64756471680), (Sum.inl 5251, 10514841600), (Sum.inl 5256, 149339830080), (Sum.inl 5257, -125060363040), (Sum.inl 5258, -63330176640), (Sum.inl 5259, 83745466560), (Sum.inl 5260, -236574915840), (Sum.inl 5265, -189377768640), (Sum.inl 5267, -117435524160), (Sum.inl 5270, 245530431360), (Sum.inl 5271, 299852094720), (Sum.inl 5272, 396788077440), (Sum.inl 5273, 329020291680), (Sum.inl 5274, 161057413440), (Sum.inl 5275, 324956505600), (Sum.inl 5276, 18270987200), (Sum.inl 5289, -897547172160), (Sum.inl 5290, -424939157600), (Sum.inl 5291, -236367478400), (Sum.inl 5295, -335697166080), (Sum.inl 5304, 747229907840), (Sum.inl 5305, 40130674560), (Sum.inl 5311, -160198120320)]

theorem originalBlockCheck66 : originalBlock66 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock66 keyMomentRows) := by decide +kernel

theorem originalBlockEval66 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock66 x =
      Integer.Sparse.eval keyPolynomialBlock66 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck66, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
