import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock88 : Integer.Sparse (Fin 2886) := [(2816, -48344200800), (2817, 17229204000), (2818, -27995450400), (2819, 140987363520), (2820, 50555669760), (2821, 192202411200), (2822, 1255236480), (2823, -47324040000), (2824, 191985931200), (2825, -22754900160), (2826, -12673492800), (2827, -78356439360), (2828, -296620039680), (2829, 56788848000), (2830, -64948270080), (2831, 34650547200), (2832, 37859232000), (2833, -47324040000), (2834, 100765398400), (2835, -42474746880), (2836, -63619065120), (2837, -41004096000), (2838, 56475672000), (2839, -118195249920), (2840, 50555669760), (2841, 84811104000), (2842, -56475672000), (2843, -14366992320), (2844, 41004096000), (2845, 3537700800), (2846, 19033325280), (2847, -16509386400)]

def originalBlock88 : Integer.Sparse OriginalKey := [(Sum.inl 0, 140987363520), (Sum.inl 3, 192202411200), (Sum.inl 2697, 56475672000), (Sum.inl 2702, -56475672000), (Sum.inl 3064, -42474746880), (Sum.inl 3074, 50555669760), (Sum.inl 3075, 84811104000), (Sum.inl 3087, -22754900160), (Sum.inl 3099, -78356439360), (Sum.inl 3111, 50555669760), (Sum.inl 3223, 100765398400), (Sum.inl 3226, -118195249920), (Sum.inl 3228, 191985931200), (Sum.inl 3288, 3537700800), (Sum.inl 3289, 41004096000), (Sum.inl 3523, -48344200800), (Sum.inl 3526, -14366992320), (Sum.inl 3539, 94648080000), (Sum.inl 3542, -27995450400), (Sum.inl 3543, -47324040000), (Sum.inl 3839, 19033325280), (Sum.inl 3842, 17229204000), (Sum.inl 3846, -41004096000), (Sum.inl 3847, -63619065120), (Sum.inl 3848, -16509386400), (Sum.inl 3855, -47324040000), (Sum.inl 4026, -361568309760), (Sum.inl 4028, 34650547200), (Sum.inl 4034, 1255236480), (Sum.inl 4038, -12673492800), (Sum.inl 4083, 563949454080), (Sum.inl 4091, 768809644800), (Sum.inl 4589, 14150803200), (Sum.inl 4599, 164016384000), (Sum.inl 4600, -225902688000), (Sum.inl 4887, -472780999680), (Sum.inl 4889, 403061593600), (Sum.inl 4893, 767943724800), (Sum.inl 5139, -193376803200), (Sum.inl 5189, -111981801600), (Sum.inl 5243, 225902688000), (Sum.inl 5251, 208693332480), (Sum.inl 5252, -189296160000), (Sum.inl 5257, -91019600640), (Sum.inl 5265, -57467969280), (Sum.inl 5270, 339244416000), (Sum.inl 5273, 202222679040), (Sum.inl 5281, 202222679040), (Sum.inl 5290, -313425757440), (Sum.inl 5406, -254476260480), (Sum.inl 5408, -50693971200), (Sum.inl 5419, 68916816000), (Sum.inl 5425, 76133301120), (Sum.inl 5427, 5020945920), (Sum.inl 5429, -164016384000), (Sum.inl 5430, -66037545600), (Sum.inl 5431, -1446273239040), (Sum.inl 5437, -189296160000), (Sum.inl 5448, 138602188800)]

theorem originalBlockCheck88 : originalBlock88 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock88 keyMomentRows) := by decide +kernel

theorem originalBlockEval88 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock88 x =
      Integer.Sparse.eval keyPolynomialBlock88 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck88, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
