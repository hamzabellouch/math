import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock87 : Integer.Sparse (Fin 2886) := [(2784, 10373020800), (2785, 5614752000), (2786, 5186510400), (2787, 128192524800), (2788, -42336357120), (2789, -32626140000), (2790, 122293680000), (2791, 56715248160), (2792, -6462957600), (2793, -122293680000), (2794, -74677500000), (2795, -19842213120), (2796, -13875116800), (2797, -38761696800), (2798, -7336967200), (2799, 506570400), (2800, 41709844800), (2801, -49533427200), (2802, -81289584000), (2803, -56475672000), (2804, 626512320), (2805, 56475672000), (2806, 66389719680), (2807, 81289584000), (2808, 86075299200), (2809, -9717393600), (2810, -15789352800), (2811, -76405896000), (2812, -56050135200), (2813, 76405896000), (2814, 41641183200), (2815, 33408700800)]

def originalBlock87 : Integer.Sparse OriginalKey := [(Sum.inl 2669, 10373020800), (Sum.inl 2670, 5614752000), (Sum.inl 2682, 5186510400), (Sum.inl 2698, -56475672000), (Sum.inl 2706, 56475672000), (Sum.inl 3065, 41709844800), (Sum.inl 3078, 626512320), (Sum.inl 3088, -42336357120), (Sum.inl 3227, 506570400), (Sum.inl 3229, 128192524800), (Sum.inl 3517, 33408700800), (Sum.inl 3529, 41641183200), (Sum.inl 3537, 86075299200), (Sum.inl 3540, -7336967200), (Sum.inl 3569, 81289584000), (Sum.inl 3578, 76405896000), (Sum.inl 3840, -74677500000), (Sum.inl 3848, -38761696800), (Sum.inl 3873, -76405896000), (Sum.inl 3880, -122293680000), (Sum.inl 3954, 66389719680), (Sum.inl 3959, -56050135200), (Sum.inl 3972, -9717393600), (Sum.inl 3976, -81289584000), (Sum.inl 3977, -49533427200), (Sum.inl 3978, -15789352800), (Sum.inl 3990, 56715248160), (Sum.inl 3993, -19842213120), (Sum.inl 3994, -6462957600), (Sum.inl 3995, 122293680000), (Sum.inl 3996, -32626140000), (Sum.inl 3997, -13875116800), (Sum.inl 4888, 2026281600), (Sum.inl 4895, 512770099200), (Sum.inl 5138, 133634803200), (Sum.inl 5140, 22459008000), (Sum.inl 5185, 166564732800), (Sum.inl 5187, 344301196800), (Sum.inl 5197, 325158336000), (Sum.inl 5199, 305623584000), (Sum.inl 5205, 225902688000), (Sum.inl 5226, 41492083200), (Sum.inl 5236, 20746041600), (Sum.inl 5244, -225902688000), (Sum.inl 5250, 166839379200), (Sum.inl 5259, -169345428480), (Sum.inl 5260, -29347868800), (Sum.inl 5282, 2506049280), (Sum.inl 5405, -198133708800), (Sum.inl 5410, -130504560000), (Sum.inl 5421, -305623584000), (Sum.inl 5424, 226860992640), (Sum.inl 5425, -298710000000), (Sum.inl 5429, 265558878720), (Sum.inl 5430, -193916361600), (Sum.inl 5438, -79368852480), (Sum.inl 5445, -489174720000), (Sum.inl 5446, -224200540800), (Sum.inl 5471, -325158336000), (Sum.inl 5473, 489174720000), (Sum.inl 5478, -25851830400), (Sum.inl 5480, -63157411200), (Sum.inl 5484, -55500467200)]

theorem originalBlockCheck87 : originalBlock87 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock87 keyMomentRows) := by decide +kernel

theorem originalBlockEval87 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock87 x =
      Integer.Sparse.eval keyPolynomialBlock87 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck87, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
