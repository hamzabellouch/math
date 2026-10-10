import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock65 : Integer.Sparse (Fin 2886) := [(2080, -43792033440), (2081, -28257823200), (2082, 42686188800), (2083, -48723109440), (2084, 64045454400), (2085, 4055846400), (2086, 4181394240), (2087, 4927916640), (2088, -4480224000), (2089, -46742035200), (2090, -27863929920), (2091, -18021080640), (2092, -5429932800), (2093, -63164736000), (2094, 5429932800), (2095, 34719423360), (2096, -6542266560), (2097, -9023861760), (2098, 5429932800), (2099, 14983576320), (2100, -5429932800), (2101, 28588357440), (2102, 173684799360), (2103, 198521277840), (2104, 84976313760), (2105, 22112948160), (2106, 218407535040), (2107, 36277422720), (2108, -4352643360), (2109, -6833967600), (2110, 52544808000), (2111, 332760998400)]

def originalBlock65 : Integer.Sparse OriginalKey := [(Sum.inl 1, 198521277840), (Sum.inl 2, 28588357440), (Sum.inl 614, 20906971200), (Sum.inl 619, 74917881600), (Sum.inl 933, -22401120000), (Sum.inl 1050, 24639583200), (Sum.inl 1139, -243615547200), (Sum.inl 1144, -45119308800), (Sum.inl 1818, -139319649600), (Sum.inl 2330, -27149664000), (Sum.inl 2334, 27149664000), (Sum.inl 2337, 27149664000), (Sum.inl 2338, 173597116800), (Sum.inl 2339, -32711332800), (Sum.inl 2341, -90105403200), (Sum.inl 2342, -233710176000), (Sum.inl 2344, -27149664000), (Sum.inl 2345, -315823680000), (Sum.inl 2432, 20279232000), (Sum.inl 2489, 320227272000), (Sum.inl 2755, 52544808000), (Sum.inl 2778, 22112948160), (Sum.inl 2818, -218960167200), (Sum.inl 3114, 173684799360), (Sum.inl 3224, -6833967600), (Sum.inl 3225, -4352643360), (Sum.inl 3229, 369038421120), (Sum.inl 3230, 218407535040), (Sum.inl 3231, 84976313760), (Sum.inl 3672, 213430944000), (Sum.inl 3694, -141289116000), (Sum.inl 4084, 794085111360), (Sum.inl 4085, 114353429760), (Sum.inl 4890, 210179232000), (Sum.inl 4894, 873630140160), (Sum.inl 4895, 1476153684480), (Sum.inl 4896, -17410573440), (Sum.inl 4897, 694739197440), (Sum.inl 4898, -27335870400), (Sum.inl 4899, 88451792640), (Sum.inl 4901, 339905255040)]

theorem originalBlockCheck65 : originalBlock65 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock65 keyMomentRows) := by decide +kernel

theorem originalBlockEval65 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock65 x =
      Integer.Sparse.eval keyPolynomialBlock65 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck65, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
