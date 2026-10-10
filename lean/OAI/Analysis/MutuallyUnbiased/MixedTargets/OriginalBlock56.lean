import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock56 : Integer.Sparse (Fin 2886) := [(1792, -19041576000), (1793, 18466607040), (1794, -13131941760), (1795, -49561960800), (1796, 34778529600), (1797, 17459255520), (1798, -4480224000), (1799, -30968316480), (1800, -22351752960), (1801, -15860171520), (1802, -11202278400), (1803, -13532618880), (1804, -20109456000), (1805, 915603840), (1806, 1949826240), (1807, -5904316800), (1808, 4422816000), (1809, 47828960640), (1810, 37489950720), (1811, -5904316800), (1812, 1949826240), (1813, 20109456000), (1814, -47828960640), (1815, -18744975360), (1816, 11808633600), (1817, -18744975360), (1818, -6965038080), (1819, -2891059200), (1820, 14527101600), (1821, 7235763840), (1822, 1090258560), (1823, 26360455680)]

def originalBlock56 : Integer.Sparse OriginalKey := [(Sum.inl 1094, -56011392000), (Sum.inl 2266, 5451292800), (Sum.inl 2291, -67663094400), (Sum.inl 2522, -111758764800), (Sum.inl 2724, -14455296000), (Sum.inl 2739, -100547280000), (Sum.inl 2740, -79300857600), (Sum.inl 2769, -34825190400), (Sum.inl 2782, 100547280000), (Sum.inl 2783, -154841582400), (Sum.inl 3051, 4578019200), (Sum.inl 3074, 239144803200), (Sum.inl 3097, -239144803200), (Sum.inl 3394, 173892648000), (Sum.inl 3397, 92333035200), (Sum.inl 3496, -22401120000), (Sum.inl 3534, 87296277600), (Sum.inl 3535, 22114080000), (Sum.inl 3548, -65659708800), (Sum.inl 3583, -95207880000), (Sum.inl 3623, -247809804000), (Sum.inl 3627, 131802278400), (Sum.inl 3816, 9749131200), (Sum.inl 3839, 9749131200), (Sum.inl 3908, 72635508000), (Sum.inl 3913, 36178819200), (Sum.inl 3959, 59043168000), (Sum.inl 3961, -29521584000), (Sum.inl 3972, -93724876800), (Sum.inl 3974, 187449753600), (Sum.inl 3983, -93724876800), (Sum.inl 4024, -29521584000)]

theorem originalBlockCheck56 : originalBlock56 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock56 keyMomentRows) := by decide +kernel

theorem originalBlockEval56 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock56 x =
      Integer.Sparse.eval keyPolynomialBlock56 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck56, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
