import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock46 : Integer.Sparse (Fin 2886) := [(1472, 84202680960), (1473, 46716867840), (1474, -6565147200), (1475, 3579796800), (1476, -43017496320), (1477, -7526880000), (1478, 23886492000), (1479, 6796495200), (1480, 19255503840), (1481, 17506285600), (1482, 47636768000), (1483, 11371866400), (1484, -7127592000), (1485, -11104874400), (1486, -3560809200), (1487, -27656481600), (1488, -30092011200), (1489, -41392777600), (1490, 4632541600), (1491, -144359200), (1492, -1332079200), (1493, 11104874400), (1494, 3560809200), (1495, -33493728000), (1496, -12576042240), (1497, -30595320000), (1498, -4667459520), (1499, 12691492800), (1500, 26364576000), (1501, 43992542400), (1502, -52712952000), (1503, -21308906400)]

def originalBlock46 : Integer.Sparse OriginalKey := [(Sum.inl 586, -23337297600), (Sum.inl 616, -62880211200), (Sum.inl 950, -152976600000), (Sum.inl 1063, -167468640000), (Sum.inl 1117, -6660396000), (Sum.inl 1141, 23162708000), (Sum.inl 1794, 17898984000), (Sum.inl 1795, 219962712000), (Sum.inl 1816, 233584339200), (Sum.inl 1830, 63457464000), (Sum.inl 1977, -32825736000), (Sum.inl 1978, 131822880000), (Sum.inl 2094, 421013404800), (Sum.inl 2353, -106544532000), (Sum.inl 2362, -263564760000), (Sum.inl 2433, 55524372000), (Sum.inl 2441, -721796000), (Sum.inl 2473, 17804046000), (Sum.inl 2499, -206963888000), (Sum.inl 2745, -138282408000), (Sum.inl 2758, -215087481600), (Sum.inl 2801, -35637960000), (Sum.inl 2819, 238183840000), (Sum.inl 2898, -150460056000), (Sum.inl 3083, -37634400000), (Sum.inl 3673, -55524372000), (Sum.inl 3676, 56859332000), (Sum.inl 3685, -17804046000), (Sum.inl 3699, 87531428000), (Sum.inl 3710, 96277519200), (Sum.inl 3780, 119432460000), (Sum.inl 3783, 33982476000)]

theorem originalBlockCheck46 : originalBlock46 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock46 keyMomentRows) := by decide +kernel

theorem originalBlockEval46 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock46 x =
      Integer.Sparse.eval keyPolynomialBlock46 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck46, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
