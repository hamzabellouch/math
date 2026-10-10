import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock63 : Integer.Sparse (Fin 2886) := [(2016, 15952749600), (2017, -5862948480), (2018, 447692640), (2019, -5840294400), (2020, 12133370880), (2021, 12133370880), (2022, 10296464640), (2023, 30322132800), (2024, 1175356800), (2025, 13131941760), (2026, 49561960800), (2027, 23623006080), (2028, 4018583520), (2029, -39832000320), (2030, -34826690400), (2031, 1672306560), (2032, 9276596160), (2033, 123751327200), (2034, 5855827200), (2035, 33906730080), (2036, 4287736800), (2037, -14428365600), (2038, -18915148800), (2039, -29083992000), (2040, 12073920), (2041, -118767916800), (2042, 30085022400), (2043, -27796672800), (2044, 98133722880), (2045, -68101300800), (2046, 13485216000), (2047, -3772083840)]

def originalBlock63 : Integer.Sparse OriginalKey := [(Sum.inl 583, 60666854400), (Sum.inl 599, -29314742400), (Sum.inl 608, -18860419200), (Sum.inl 1039, 2238463200), (Sum.inl 1129, 490668614400), (Sum.inl 1134, 150425112000), (Sum.inl 1792, 60666854400), (Sum.inl 1805, 118115030400), (Sum.inl 1810, 5876784000), (Sum.inl 1827, -29201472000), (Sum.inl 2020, 20092917600), (Sum.inl 2054, 65659708800), (Sum.inl 2107, 151610664000), (Sum.inl 2244, 247809804000), (Sum.inl 2278, 51482323200), (Sum.inl 2428, 67426080000), (Sum.inl 2479, 79763748000), (Sum.inl 2480, -340506504000), (Sum.inl 2512, -138983364000), (Sum.inl 2809, 21438684000), (Sum.inl 2813, 29279136000), (Sum.inl 2893, 60369600), (Sum.inl 3670, -94575744000), (Sum.inl 3671, 8361532800), (Sum.inl 3690, -72141828000), (Sum.inl 3705, 169533650400), (Sum.inl 3781, 46382980800), (Sum.inl 3787, -174133452000), (Sum.inl 3800, 618756636000), (Sum.inl 3813, -199160001600), (Sum.inl 3909, -145419960000), (Sum.inl 3945, -593839584000)]

theorem originalBlockCheck63 : originalBlock63 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock63 keyMomentRows) := by decide +kernel

theorem originalBlockEval63 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock63 x =
      Integer.Sparse.eval keyPolynomialBlock63 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck63, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
