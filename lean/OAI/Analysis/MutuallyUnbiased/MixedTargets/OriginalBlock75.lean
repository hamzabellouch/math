import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock75 : Integer.Sparse (Fin 2886) := [(2400, -49540614480), (2401, 19060092560), (2402, -241843442320), (2403, -124444539240), (2404, 134291832480), (2405, 62008066480), (2406, 15404358800), (2407, -10586607200), (2408, 22573682640), (2409, -19248180720), (2410, -92871236160), (2411, -204446844240), (2412, 277437109200), (2413, -90645302880), (2414, -13262269160), (2415, 4553906000), (2416, -256088763600), (2417, -49077475480), (2418, -32732670720), (2419, 166076389760), (2420, -17377408080), (2421, -61944523920), (2422, -144865072880), (2423, -159417459120), (2424, -78861139280), (2425, 171064210560), (2426, 163572001920), (2427, 26302040160), (2428, 40561427520), (2429, 53989962240), (2430, 114245799840), (2431, 59984395200)]

def originalBlock75 : Integer.Sparse OriginalKey := [(Sum.inl 2751, -32732670720), (Sum.inl 2773, 53989962240), (Sum.inl 2774, -90645302880), (Sum.inl 3109, 163572001920), (Sum.inl 3110, -92871236160), (Sum.inl 3229, 171064210560), (Sum.inl 3231, -19248180720), (Sum.inl 3526, 15404358800), (Sum.inl 3535, 41633775200), (Sum.inl 3541, 62008066480), (Sum.inl 3549, -10586607200), (Sum.inl 3584, -49540614480), (Sum.inl 3846, -140805663200), (Sum.inl 3854, -49077475480), (Sum.inl 3871, 59984395200), (Sum.inl 3881, -256088763600), (Sum.inl 3959, -241843442320), (Sum.inl 3976, -144865072880), (Sum.inl 3990, 114245799840), (Sum.inl 3995, 211191723280), (Sum.inl 3996, 26302040160), (Sum.inl 4002, -159417459120), (Sum.inl 4003, -13262269160), (Sum.inl 4004, 277437109200), (Sum.inl 4005, -17377408080), (Sum.inl 4006, -204446844240), (Sum.inl 4024, 134291832480), (Sum.inl 4028, -124444539240), (Sum.inl 4895, 684256842240), (Sum.inl 4901, -76992722880), (Sum.inl 5265, 61617435200), (Sum.inl 5266, 166535100800), (Sum.inl 5267, 248032265920), (Sum.inl 5268, -42346428800), (Sum.inl 5271, 654288007680), (Sum.inl 5275, -371484944640), (Sum.inl 5282, -130930682880), (Sum.inl 5299, 215959848960), (Sum.inl 5300, -560743669440), (Sum.inl 5410, 105208160640), (Sum.inl 5413, -817787376960), (Sum.inl 5424, 456983199360), (Sum.inl 5428, -53049076640), (Sum.inl 5429, -563222652800), (Sum.inl 5430, 239937580800), (Sum.inl 5436, -196309901920), (Sum.inl 5445, 537167329920), (Sum.inl 5446, -1991728823680), (Sum.inl 5448, -497778156960), (Sum.inl 5471, -579460291520), (Sum.inl 5472, -637669836480), (Sum.inl 5473, 844766893120), (Sum.inl 5474, -69509632320), (Sum.inl 5475, 1109748436800)]

theorem originalBlockCheck75 : originalBlock75 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock75 keyMomentRows) := by decide +kernel

theorem originalBlockEval75 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock75 x =
      Integer.Sparse.eval keyPolynomialBlock75 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck75, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
