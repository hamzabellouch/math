import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock47 : Integer.Sparse (Fin 2886) := [(1504, -11280429120), (1505, 38327738800), (1506, 77076726240), (1507, -291193200), (1508, -23566032000), (1509, -3183336000), (1510, -17018832400), (1511, -6949810080), (1512, 291193200), (1513, -26364576000), (1514, -5035968480), (1515, 6731640000), (1516, 2212876800), (1517, -38890668960), (1518, -9290004480), (1519, 32100528000), (1520, -29404575360), (1521, 62360648640), (1522, -13995250560), (1523, 15206696640), (1524, 4231169280), (1525, 14870793600), (1526, 28580212800), (1527, 471075840), (1528, 27338481600), (1529, -17671608000), (1530, -106770856320), (1531, -75915910080), (1532, -48648709440), (1533, -129299112000), (1534, 5397932160), (1535, 123079896000)]

def originalBlock47 : Integer.Sparse OriginalKey := [(Sum.inl 588, -25179842400), (Sum.inl 952, -131822880000), (Sum.inl 1119, -34749050400), (Sum.inl 1804, 74353968000), (Sum.inl 1811, 142901064000), (Sum.inl 1814, 68559696000), (Sum.inl 1817, -46450022400), (Sum.inl 1966, 136692408000), (Sum.inl 2023, 2355379200), (Sum.inl 2028, 21155846400), (Sum.inl 2058, -69976252800), (Sum.inl 2110, -147022876800), (Sum.inl 2115, -194453344800), (Sum.inl 2245, 76033483200), (Sum.inl 2266, 160502640000), (Sum.inl 2279, 11064384000), (Sum.inl 2294, 33658200000), (Sum.inl 2347, 1455966000), (Sum.inl 2348, -1455966000), (Sum.inl 2349, -15916680000), (Sum.inl 2350, -56402145600), (Sum.inl 2352, 385383631200), (Sum.inl 2355, -85094162000), (Sum.inl 2356, 191638694000), (Sum.inl 2361, -117830160000), (Sum.inl 3626, -88358040000), (Sum.inl 3708, 615399480000), (Sum.inl 3732, -379579550400), (Sum.inl 3789, 26989660800), (Sum.inl 3809, -646495560000), (Sum.inl 3814, -533854281600)]

theorem originalBlockCheck47 : originalBlock47 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock47 keyMomentRows) := by decide +kernel

theorem originalBlockEval47 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock47 x =
      Integer.Sparse.eval keyPolynomialBlock47 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck47, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
