import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock58 : Integer.Sparse (Fin 2886) := [(1856, -22831165440), (1857, -13668665760), (1858, 32313669600), (1859, 15078927840), (1860, -35549871840), (1861, 20421514080), (1862, -7975556160), (1863, -9468954720), (1864, -32313669600), (1865, 47828960640), (1866, 18744975360), (1867, 18744975360), (1868, 3829473600), (1869, 10847290560), (1870, 3671820480), (1871, 23307218400), (1872, -152009150400), (1873, -59820541920), (1874, 119695480800), (1875, -13485216000), (1876, 46573672320), (1877, -33906730080), (1878, 48973251360), (1879, 74999858400), (1880, 13485216000), (1881, -42686188800), (1882, -17356602240), (1883, 8282807520), (1884, 79225920), (1885, 16069440000), (1886, 45201499680), (1887, 24044996160)]

def originalBlock58 : Integer.Sparse OriginalKey := [(Sum.inl 2508, 80347200000), (Sum.inl 2515, 41414037600), (Sum.inl 2519, 226007498400), (Sum.inl 2739, 396129600), (Sum.inl 2743, 120224980800), (Sum.inl 2782, -86783011200), (Sum.inl 2868, 93724876800), (Sum.inl 2880, -47344773600), (Sum.inl 2881, -177749359200), (Sum.inl 2884, 244866256800), (Sum.inl 2889, 232868361600), (Sum.inl 3108, 239144803200), (Sum.inl 3703, -67426080000), (Sum.inl 3705, 67426080000), (Sum.inl 3706, 18359102400), (Sum.inl 3782, -114155827200), (Sum.inl 3843, 75394639200), (Sum.inl 3845, -39877780800), (Sum.inl 3913, 19147368000), (Sum.inl 3922, 93724876800), (Sum.inl 3945, -213430944000), (Sum.inl 3957, -161568348000), (Sum.inl 3958, 374999292000), (Sum.inl 3961, 218643662400), (Sum.inl 3963, -169533650400), (Sum.inl 3964, -299102709600), (Sum.inl 3974, 598477404000), (Sum.inl 3983, 54236452800), (Sum.inl 4010, -760045752000), (Sum.inl 4044, -68343328800), (Sum.inl 4046, 161568348000)]

theorem originalBlockCheck58 : originalBlock58 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock58 keyMomentRows) := by decide +kernel

theorem originalBlockEval58 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock58 x =
      Integer.Sparse.eval keyPolynomialBlock58 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck58, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
