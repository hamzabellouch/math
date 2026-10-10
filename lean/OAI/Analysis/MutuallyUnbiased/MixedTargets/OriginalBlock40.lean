import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock40 : Integer.Sparse (Fin 2886) := [(1280, 90276033600), (1281, -58035288000), (1282, -52661520000), (1283, 11800540800), (1284, 2445982400), (1285, -40959046880), (1286, -17018832400), (1287, -40602700320), (1288, -22297619200), (1289, -37544311200), (1290, 11104874400), (1291, 3560809200), (1292, 291193200), (1293, 30435985920), (1294, -20684376000), (1295, 2445982400), (1296, 111510828000), (1297, 27302836000), (1298, -86879699200), (1299, -68743742400), (1300, 11104874400), (1301, 3560809200), (1302, -110625926400), (1303, -30092011200), (1304, -90276033600), (1305, -2445982400), (1306, 40959046880), (1307, 22297619200), (1308, 37544311200), (1309, -11104874400), (1310, -3560809200), (1311, 21713208000)]

def originalBlock40 : Integer.Sparse OriginalKey := [(Sum.inl 1260, -187721556000), (Sum.inl 1261, -203013501600), (Sum.inl 1262, 187721556000), (Sum.inl 1291, -204795234400), (Sum.inl 1292, 59002704000), (Sum.inl 1295, 204795234400), (Sum.inl 2566, 1455966000), (Sum.inl 2587, 55524372000), (Sum.inl 2591, -55524372000), (Sum.inl 2631, -111488096000), (Sum.inl 2632, -85094162000), (Sum.inl 2633, 111488096000), (Sum.inl 2643, 108566040000), (Sum.inl 2750, 17804046000), (Sum.inl 2751, -570933678000), (Sum.inl 2773, 12229912000), (Sum.inl 2774, 139950017600), (Sum.inl 2933, -263307600000), (Sum.inl 2951, 451380168000), (Sum.inl 2955, -451380168000), (Sum.inl 3092, -103421880000), (Sum.inl 3724, -343718712000), (Sum.inl 3733, 136514180000), (Sum.inl 3819, 55524372000), (Sum.inl 3827, -724574936000), (Sum.inl 3846, 17804046000), (Sum.inl 3854, 12229912000), (Sum.inl 3881, 557554140000), (Sum.inl 3949, -150460056000)]

theorem originalBlockCheck40 : originalBlock40 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock40 keyMomentRows) := by decide +kernel

theorem originalBlockEval40 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock40 x =
      Integer.Sparse.eval keyPolynomialBlock40 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck40, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
