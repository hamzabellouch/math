import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock68 : Integer.Sparse (Fin 2886) := [(2176, -5614752000), (2177, -11068343040), (2178, -244351925760), (2179, -19789087680), (2180, 41492083200), (2181, -79879749600), (2182, -5820135840), (2183, -108445633760), (2184, 32040920640), (2185, 3331916000), (2186, -34052750400), (2187, -202090914000), (2188, 27361002240), (2189, 27803192880), (2190, 131029924320), (2191, 95785122320), (2192, 86974335360), (2193, 30987058800), (2194, -5186510400), (2195, -5864927880), (2196, -10946874240), (2197, -70512808320), (2198, -35933301360), (2199, -8729926560), (2200, 2785553280), (2201, -64386633600), (2202, 15131114400), (2203, 28779193920), (2204, 12247949280), (2205, 2152584000), (2206, 30023799840), (2207, 28430653200)]

def originalBlock68 : Integer.Sparse OriginalKey := [(Sum.inl 2161, 12247949280), (Sum.inl 2162, 28779193920), (Sum.inl 2163, 2785553280), (Sum.inl 2180, 2152584000), (Sum.inl 2220, 45154914240), (Sum.inl 2221, -64386633600), (Sum.inl 2222, -70512808320), (Sum.inl 2282, -8729926560), (Sum.inl 2283, 28430653200), (Sum.inl 2284, -35933301360), (Sum.inl 2285, -10946874240), (Sum.inl 2669, 41492083200), (Sum.inl 2670, -5614752000), (Sum.inl 2681, 30987058800), (Sum.inl 2682, -5186510400), (Sum.inl 2683, 3331916000), (Sum.inl 2700, -5864927880), (Sum.inl 2702, 27803192880), (Sum.inl 2718, -19789087680), (Sum.inl 2735, 131029924320), (Sum.inl 2736, 86974335360), (Sum.inl 2737, 32040920640), (Sum.inl 2738, 95785122320), (Sum.inl 2744, -108445633760), (Sum.inl 2760, -11068343040), (Sum.inl 2761, -34052750400), (Sum.inl 2763, -244351925760), (Sum.inl 2779, 27361002240), (Sum.inl 2780, -5820135840), (Sum.inl 2781, -202090914000), (Sum.inl 2789, -79879749600), (Sum.inl 4600, 111212771520), (Sum.inl 4611, 13327664000), (Sum.inl 4617, 128163682560), (Sum.inl 4626, -23280543360), (Sum.inl 4671, 48991797120), (Sum.inl 4687, 115116775680), (Sum.inl 4694, 11142213120), (Sum.inl 4702, 8610336000), (Sum.inl 4808, 180619656960), (Sum.inl 4819, -257546534400), (Sum.inl 4844, -282051233280), (Sum.inl 4872, -34919706240), (Sum.inl 4886, 113722612800), (Sum.inl 4892, -143733205440), (Sum.inl 4900, -43787496960), (Sum.inl 5140, -22459008000), (Sum.inl 5150, -23459711520), (Sum.inl 5151, 123948235200), (Sum.inl 5173, 524119697280), (Sum.inl 5175, -136211001600), (Sum.inl 5226, 165968332800), (Sum.inl 5236, -20746041600), (Sum.inl 5255, -79156350720), (Sum.inl 5269, 347897341440), (Sum.inl 5270, 383140489280), (Sum.inl 5276, -433782535040), (Sum.inl 5288, -44273372160), (Sum.inl 5289, -977407703040), (Sum.inl 5295, -808363656000), (Sum.inl 5303, 109444008960), (Sum.inl 5311, -319518998400)]

theorem originalBlockCheck68 : originalBlock68 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock68 keyMomentRows) := by decide +kernel

theorem originalBlockEval68 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock68 x =
      Integer.Sparse.eval keyPolynomialBlock68 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck68, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
