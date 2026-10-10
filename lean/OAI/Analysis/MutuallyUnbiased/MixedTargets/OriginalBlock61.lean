import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock61 : Integer.Sparse (Fin 2886) := [(1952, 14650172640), (1953, 81065138400), (1954, 18915148800), (1955, 29083992000), (1956, -29083992000), (1957, 29071918080), (1958, 118767916800), (1959, -22846209600), (1960, 27796672800), (1961, -30472704000), (1962, -17303419200), (1963, -18915148800), (1964, -4055846400), (1965, -9114832320), (1966, 18800954880), (1967, 31148367840), (1968, -16069440000), (1969, 5635431360), (1970, -5635431360), (1971, -14826551040), (1972, -116690400), (1973, 16069440000), (1974, 40518361920), (1975, 17242670400), (1976, 34485340800), (1977, -7331790720), (1978, 7542887040), (1979, 6917552640), (1980, -3478201920), (1981, -151724160), (1982, -13532618880), (1983, 2211408000)]

def originalBlock61 : Integer.Sparse OriginalKey := [(Sum.inl 1044, 86213352000), (Sum.inl 1046, 172426704000), (Sum.inl 1049, 202591809600), (Sum.inl 1051, -36658953600), (Sum.inl 1240, -152363520000), (Sum.inl 1242, -74132755200), (Sum.inl 1246, -114231048000), (Sum.inl 1821, 34587763200), (Sum.inl 2104, -758620800), (Sum.inl 2131, 37714435200), (Sum.inl 2252, -85054104000), (Sum.inl 2479, -80347200000), (Sum.inl 2482, 80347200000), (Sum.inl 2483, -28177156800), (Sum.inl 2488, 94004774400), (Sum.inl 2556, -20279232000), (Sum.inl 2561, -94575744000), (Sum.inl 2722, 155741839200), (Sum.inl 2723, -86517096000), (Sum.inl 2726, -583452000), (Sum.inl 2743, 138983364000), (Sum.inl 2764, 28177156800), (Sum.inl 2765, -45574161600), (Sum.inl 2806, 11057040000), (Sum.inl 2931, 145359590400), (Sum.inl 3689, 94575744000), (Sum.inl 3692, -145419960000), (Sum.inl 3721, 73250863200), (Sum.inl 3838, 405325692000), (Sum.inl 3910, 145419960000), (Sum.inl 3958, 593839584000)]

theorem originalBlockCheck61 : originalBlock61 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock61 keyMomentRows) := by decide +kernel

theorem originalBlockEval61 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock61 x =
      Integer.Sparse.eval keyPolynomialBlock61 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck61, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
