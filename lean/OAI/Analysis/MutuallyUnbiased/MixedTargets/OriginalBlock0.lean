import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock0 : Integer.Sparse (Fin 2886) := [(0, 9272200320), (1, 40990420560), (2, 14963621760), (3, 3008545920), (4, -18417761280), (5, 2070649920), (6, -14963621760), (7, 5917182000), (8, 9478498560), (9, 24964920000), (10, -7016282400), (11, -19285274880), (12, -4532866080), (13, -5679645120), (14, -206942400), (15, -11656704000), (16, -3645895920), (17, 4668639360), (18, 513062400), (19, -8117441760), (20, 26455253760), (21, -19821712320), (22, 13312972800), (23, 2022739200), (24, 11656704000), (25, 1839624000), (26, -265507200), (27, -4668639360), (28, -513062400), (29, -2207548800), (30, -2531729760), (31, -26455253760)]

def originalBlock0 : Integer.Sparse OriginalKey := [(Sum.inl 0, 124824600000), (Sum.inl 1, 204952102800), (Sum.inl 2, 46361001600), (Sum.inl 259, -28398225600), (Sum.inl 261, -57745742400), (Sum.inl 265, -96426374400), (Sum.inl 266, -92088806400), (Sum.inl 267, 57745742400), (Sum.inl 268, -74818108800), (Sum.inl 269, 29585910000), (Sum.inl 270, 15042729600), (Sum.inl 272, 74818108800), (Sum.inl 375, 66564864000), (Sum.inl 377, 2565312000), (Sum.inl 382, 10113696000), (Sum.inl 384, -40587208800), (Sum.inl 386, 132276268800), (Sum.inl 387, -99108561600), (Sum.inl 388, -58283520000), (Sum.inl 389, -18229479600), (Sum.inl 391, 10684548000), (Sum.inl 402, -2565312000), (Sum.inl 405, -11037744000), (Sum.inl 406, -132276268800), (Sum.inl 415, 58283520000), (Sum.inl 419, 9198120000), (Sum.inl 420, -1327536000), (Sum.inl 421, -23343196800), (Sum.inr 0, -1034712000)]

theorem originalBlockCheck0 : originalBlock0 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock0 keyMomentRows) := by decide +kernel

theorem originalBlockEval0 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock0 x =
      Integer.Sparse.eval keyPolynomialBlock0 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck0, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
