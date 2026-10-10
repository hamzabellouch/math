import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock37 : Integer.Sparse (Fin 2886) := [(1184, -21792797600), (1185, -32676890400), (1186, -11104874400), (1187, -3560809200), (1188, -291193200), (1189, 38109254400), (1190, 28211256000), (1191, 21440509600), (1192, -118307323200), (1193, 26131265600), (1194, 31561775200), (1195, 6982212000), (1196, -11104874400), (1197, -3560809200), (1198, -21440509600), (1199, -7362845120), (1200, 21792797600), (1201, 32676890400), (1202, 11104874400), (1203, 3560809200), (1204, -11117361600), (1205, -47177037200), (1206, -24430589280), (1207, -291193200), (1208, 47177037200), (1209, 54890312640), (1210, 291193200), (1211, -43347340800), (1212, 29740402080), (1213, -3951411840), (1214, -24973506720), (1215, -22104192000)]

def originalBlock37 : Integer.Sparse OriginalKey := [(Sum.inl 2279, -124867533600), (Sum.inl 2730, -1455966000), (Sum.inl 2731, 1455966000), (Sum.inl 2732, -122152946400), (Sum.inl 2734, 274451563200), (Sum.inl 2765, 190546272000), (Sum.inl 2773, -235885186000), (Sum.inl 2774, 235885186000), (Sum.inl 2777, -55586808000), (Sum.inl 3037, -163384452000), (Sum.inl 3039, 163384452000), (Sum.inl 3055, -36814225600), (Sum.inl 3086, 141056280000), (Sum.inl 3629, -216736704000), (Sum.inl 3632, -110520960000), (Sum.inl 3840, -1455966000), (Sum.inl 3846, -108963988000), (Sum.inl 3848, -55524372000), (Sum.inl 3849, -17804046000), (Sum.inl 3850, 107202548000), (Sum.inl 3871, 157808876000), (Sum.inl 3872, 34911060000), (Sum.inl 3874, -55524372000), (Sum.inl 3875, -17804046000), (Sum.inl 3876, -591536616000), (Sum.inl 3877, 130656328000), (Sum.inl 3881, 108963988000), (Sum.inl 3884, 55524372000), (Sum.inl 3885, 17804046000), (Sum.inl 3886, -107202548000), (Sum.inl 3905, 148702010400), (Sum.inl 3907, -19757059200)]

theorem originalBlockCheck37 : originalBlock37 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock37 keyMomentRows) := by decide +kernel

theorem originalBlockEval37 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock37 x =
      Integer.Sparse.eval keyPolynomialBlock37 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck37, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
