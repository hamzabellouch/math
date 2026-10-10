import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock57 : Integer.Sparse (Fin 2886) := [(1824, 24067801440), (1825, 9468954720), (1826, -9264926880), (1827, 3846663360), (1828, 77009292000), (1829, -31227593760), (1830, -9468954720), (1831, -77009292000), (1832, 13532618880), (1833, 50291959680), (1834, -17272396800), (1835, -7210152000), (1836, 41929908480), (1837, -2211408000), (1838, -2211408000), (1839, 41929908480), (1840, -7210152000), (1841, -50291959680), (1842, -47828960640), (1843, -18744975360), (1844, -41929908480), (1845, -41929908480), (1846, -18744975360), (1847, 23321831040), (1848, 6705855360), (1849, 6705855360), (1850, -14527101600), (1851, -7235763840), (1852, -1090258560), (1853, -26360455680), (1854, -24067801440), (1855, 9468954720)]

def originalBlock57 : Integer.Sparse OriginalKey := [(Sum.inl 2058, -5451292800), (Sum.inl 2262, 67663094400), (Sum.inl 2557, 33529276800), (Sum.inl 2558, 33529276800), (Sum.inl 2600, 116609155200), (Sum.inl 2720, 251459798400), (Sum.inl 2763, -251459798400), (Sum.inl 2861, -36050760000), (Sum.inl 2862, -93724876800), (Sum.inl 2878, 209649542400), (Sum.inl 2879, -11057040000), (Sum.inl 2882, -209649542400), (Sum.inl 3036, -86361984000), (Sum.inl 3084, -239144803200), (Sum.inl 3497, -11057040000), (Sum.inl 3544, -131802278400), (Sum.inl 3805, -36050760000), (Sum.inl 3809, -46324634400), (Sum.inl 3857, -36178819200), (Sum.inl 3903, -228773476800), (Sum.inl 3946, -209649542400), (Sum.inl 3956, 209649542400), (Sum.inl 3978, -93724876800), (Sum.inl 4008, 47344773600), (Sum.inl 4010, 47344773600), (Sum.inl 4025, -47344773600), (Sum.inl 4046, -385046460000), (Sum.inl 4047, -101105690400), (Sum.inl 4048, 385046460000), (Sum.inl 4049, 120339007200)]

theorem originalBlockCheck57 : originalBlock57 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock57 keyMomentRows) := by decide +kernel

theorem originalBlockEval57 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock57 x =
      Integer.Sparse.eval keyPolynomialBlock57 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck57, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
