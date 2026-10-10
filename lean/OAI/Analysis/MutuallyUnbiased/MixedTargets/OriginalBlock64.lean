import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock64 : Integer.Sparse (Fin 2886) := [(2048, 1681554240), (2049, -5375609280), (2050, 5429932800), (2051, 4480224000), (2052, 46742035200), (2053, 30968316480), (2054, 30573719040), (2055, 15860171520), (2056, 26471434560), (2057, 17820905760), (2058, -31227593760), (2059, -34466263200), (2060, -24044996160), (2061, 16069440000), (2062, -5635431360), (2063, -22541725440), (2064, 16611600000), (2065, 116690400), (2066, -16069440000), (2067, -11211492480), (2068, 11202278400), (2069, -21890630400), (2070, -18277105920), (2071, -17242670400), (2072, -34485340800), (2073, 7331790720), (2074, -11280556800), (2075, -45503496000), (2076, -12979031520), (2077, 4480224000), (2078, 54639324000), (2079, -123751327200)]

def originalBlock64 : Integer.Sparse OriginalKey := [(Sum.inl 603, 8407771200), (Sum.inl 605, -56057462400), (Sum.inl 922, 22401120000), (Sum.inl 929, -86213352000), (Sum.inl 930, -172426704000), (Sum.inl 932, -109453152000), (Sum.inl 934, 36658953600), (Sum.inl 937, 56011392000), (Sum.inl 939, -91385529600), (Sum.inl 1041, -26878046400), (Sum.inl 1131, 83058000000), (Sum.inl 1807, 152868595200), (Sum.inl 1815, -227517480000), (Sum.inl 1967, 22401120000), (Sum.inl 2022, 79300857600), (Sum.inl 2029, -64895157600), (Sum.inl 2109, 154841582400), (Sum.inl 2116, -56402784000), (Sum.inl 2332, 233710176000), (Sum.inl 2337, 27149664000), (Sum.inl 2425, -80347200000), (Sum.inl 2428, 80347200000), (Sum.inl 2429, -112708627200), (Sum.inl 2431, 89104528800), (Sum.inl 2434, -172331316000), (Sum.inl 2482, 583452000), (Sum.inl 2553, -156137968800), (Sum.inl 2561, -120224980800), (Sum.inl 2589, -28177156800), (Sum.inl 2590, 132357172800), (Sum.inl 3709, 273196620000), (Sum.inl 3779, -618756636000)]

theorem originalBlockCheck64 : originalBlock64 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock64 keyMomentRows) := by decide +kernel

theorem originalBlockEval64 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock64 x =
      Integer.Sparse.eval keyPolynomialBlock64 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck64, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
