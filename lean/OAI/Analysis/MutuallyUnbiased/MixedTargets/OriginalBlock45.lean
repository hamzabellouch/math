import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock45 : Integer.Sparse (Fin 2886) := [(1440, -51075779520), (1441, -35840326080), (1442, -35942025600), (1443, -99611985600), (1444, 11784321600), (1445, 13048718880), (1446, 14555002080), (1447, 23928148800), (1448, 24607056000), (1449, 40578692160), (1450, 19197336000), (1451, -10898468640), (1452, -17945004000), (1453, -35897460960), (1454, -45515356800), (1455, 34898174400), (1456, -24607056000), (1457, 6950538240), (1458, 4689156000), (1459, -50312723040), (1460, -24807384000), (1461, -46836888480), (1462, 12231642240), (1463, 33493728000), (1464, 35564084160), (1465, 26364576000), (1466, 3229858560), (1467, 30595320000), (1468, 4665144000), (1469, 42812467200), (1470, 35911291200), (1471, 33493728000)]

def originalBlock45 : Integer.Sparse OriginalKey := [(Sum.inl 580, 23325720000), (Sum.inl 582, 16149292800), (Sum.inl 604, 177820420800), (Sum.inl 607, 61158211200), (Sum.inl 944, 152976600000), (Sum.inl 946, 131822880000), (Sum.inl 1058, 167468640000), (Sum.inl 1113, -234184442400), (Sum.inl 1130, -251563615200), (Sum.inl 1133, 34752691200), (Sum.inl 1791, -179201630400), (Sum.inl 1806, -255378897600), (Sum.inl 1829, 179556456000), (Sum.inl 2039, 167468640000), (Sum.inl 2138, 214062336000), (Sum.inl 2233, -227576784000), (Sum.inl 2253, -179710128000), (Sum.inl 2438, -124036920000), (Sum.inl 2494, 23445780000), (Sum.inl 2513, -123035280000), (Sum.inl 2714, -498059928000), (Sum.inl 2798, -179487304800), (Sum.inl 2810, -54492343200), (Sum.inl 2812, 202893460800), (Sum.inl 2892, 174490872000), (Sum.inl 3032, 58921608000), (Sum.inl 3365, 119640744000), (Sum.inl 3577, 123035280000), (Sum.inl 3674, -89725020000), (Sum.inl 3698, 95986680000), (Sum.inl 3788, 72775010400), (Sum.inl 3803, 65243594400)]

theorem originalBlockCheck45 : originalBlock45 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock45 keyMomentRows) := by decide +kernel

theorem originalBlockEval45 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock45 x =
      Integer.Sparse.eval keyPolynomialBlock45 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck45, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
