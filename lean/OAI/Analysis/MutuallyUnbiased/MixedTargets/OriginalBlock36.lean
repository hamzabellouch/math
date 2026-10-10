import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock36 : Integer.Sparse (Fin 2886) := [(1152, -69426360000), (1153, 99565244000), (1154, 102398444800), (1155, 78169707040), (1156, -17487314800), (1157, -1075968000), (1158, -11396067600), (1159, -3560809200), (1160, -31561775200), (1161, -6982212000), (1162, 11104874400), (1163, 3560809200), (1164, 291193200), (1165, -31687339200), (1166, -160946364480), (1167, 20693438400), (1168, 126898217120), (1169, -18828969360), (1170, 37891362240), (1171, 41215104000), (1172, -121005753600), (1173, 15908878400), (1174, -104300972640), (1175, 64664352000), (1176, 19120223520), (1177, 11396067600), (1178, 3560809200), (1179, 11800540800), (1180, 21440509600), (1181, 7362845120), (1182, -47177037200), (1183, -58083479520)]

def originalBlock36 : Integer.Sparse OriginalKey := [(Sum.inl 2264, -158436696000), (Sum.inl 2722, -804731822400), (Sum.inl 3038, -186950205600), (Sum.inl 3051, 36814225600), (Sum.inl 3052, 59002704000), (Sum.inl 3064, 206075520000), (Sum.inl 3077, -347131800000), (Sum.inl 3541, 189456811200), (Sum.inl 3800, -157808876000), (Sum.inl 3801, -34911060000), (Sum.inl 3805, 55524372000), (Sum.inl 3806, 17804046000), (Sum.inl 3807, 1132317305600), (Sum.inl 3808, 511992224000), (Sum.inl 3809, 390848535200), (Sum.inl 3812, 1455966000), (Sum.inl 3813, -87436574000), (Sum.inl 3814, -5379840000), (Sum.inl 3816, -56980338000), (Sum.inl 3837, -605028768000), (Sum.inl 3838, 79544392000), (Sum.inl 3839, -521504863200), (Sum.inl 3840, 323321760000), (Sum.inl 3841, 95601117600), (Sum.inl 3843, 56980338000), (Sum.inl 3844, 17804046000), (Sum.inl 3845, -94144846800), (Sum.inl 3850, 107202548000), (Sum.inl 3854, -235885186000), (Sum.inl 4091, -17804046000)]

theorem originalBlockCheck36 : originalBlock36 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock36 keyMomentRows) := by decide +kernel

theorem originalBlockEval36 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock36 x =
      Integer.Sparse.eval keyPolynomialBlock36 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck36, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
