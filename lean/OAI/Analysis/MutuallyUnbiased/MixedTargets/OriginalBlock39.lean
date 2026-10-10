import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock39 : Integer.Sparse (Fin 2886) := [(1248, -11104874400), (1249, -3560809200), (1250, -291193200), (1251, 91030713600), (1252, -49478184000), (1253, -88127299200), (1254, 54562934400), (1255, 30092011200), (1256, 58035288000), (1257, 49478184000), (1258, 24742564800), (1259, 13716326400), (1260, 1298386560), (1261, -33543998400), (1262, -115978276160), (1263, 33383971440), (1264, 9637868160), (1265, -16078464000), (1266, 121005753600), (1267, 78487319200), (1268, 42507384960), (1269, -43220870400), (1270, -44737755360), (1271, -11396067600), (1272, -3560809200), (1273, -91030713600), (1274, 110625926400), (1275, -23566032000), (1276, 49478184000), (1277, 88127299200), (1278, 34898174400), (1279, 64718544000)]

def originalBlock39 : Integer.Sparse OriginalKey := [(Sum.inl 2244, -455153568000), (Sum.inl 2265, 455153568000), (Sum.inl 2278, 68581632000), (Sum.inl 2709, 553129632000), (Sum.inl 2731, 6491932800), (Sum.inl 2952, 323592720000), (Sum.inl 3029, -117830160000), (Sum.inl 3044, -167719992000), (Sum.inl 3068, -80392320000), (Sum.inl 3098, 123712824000), (Sum.inl 3505, 174490872000), (Sum.inl 3506, 48189340800), (Sum.inl 3573, 272814672000), (Sum.inl 3723, -223688776800), (Sum.inl 3730, 212536924800), (Sum.inl 3800, 247390920000), (Sum.inl 3808, -247390920000), (Sum.inl 3813, -579891380800), (Sum.inl 3826, -216104352000), (Sum.inl 3840, 605028768000), (Sum.inl 3848, -56980338000), (Sum.inl 3872, 247390920000), (Sum.inl 3874, -1455966000), (Sum.inl 3880, 682613036000), (Sum.inl 3884, 166919857200), (Sum.inl 3909, -17804046000), (Sum.inl 3953, 440636496000), (Sum.inl 3956, -55524372000), (Sum.inl 3957, -17804046000), (Sum.inl 3958, -440636496000), (Sum.inl 3972, 150460056000)]

theorem originalBlockCheck39 : originalBlock39 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock39 keyMomentRows) := by decide +kernel

theorem originalBlockEval39 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock39 x =
      Integer.Sparse.eval keyPolynomialBlock39 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck39, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
