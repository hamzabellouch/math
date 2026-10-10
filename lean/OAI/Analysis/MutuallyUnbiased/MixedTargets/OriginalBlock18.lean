import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock18 : Integer.Sparse (Fin 2886) := [(576, 8327170560), (577, -22889021040), (578, -2520544800), (579, -4157069760), (580, 800534400), (581, -70600320), (582, -11702125440), (583, -13595421600), (584, 5946276480), (585, -519274880), (586, -5851062720), (587, 22659036000), (588, -5946276480), (589, -1455396480), (590, 1455396480), (591, 519043840), (592, -5851062720), (593, 4531807200), (594, 5946276480), (595, 16294397760), (596, 10729172160), (597, -1904308800), (598, 70600320), (599, -5946276480), (600, 14588786880), (601, 460713600), (602, -460713600), (603, -1675376640), (604, 3350753280), (605, -1675376640), (606, -971081280), (607, 772712640)]

def originalBlock18 : Integer.Sparse OriginalKey := [(Sum.inl 13, -12602724000), (Sum.inl 22, -8376883200), (Sum.inl 26, 16753766400), (Sum.inl 33, 2303568000), (Sum.inl 34, -8376883200), (Sum.inl 35, 53645860800), (Sum.inl 38, 72943934400), (Sum.inl 40, -2303568000), (Sum.inl 42, -4855406400), (Sum.inl 70, 353001600), (Sum.inl 100, -9521544000), (Sum.inl 115, -114445105200), (Sum.inl 116, 41635852800), (Sum.inl 118, 29731382400), (Sum.inl 119, -353001600), (Sum.inl 121, 29731382400), (Sum.inl 124, -29731382400), (Sum.inl 125, -7276982400), (Sum.inl 126, 7276982400), (Sum.inl 127, -58510627200), (Sum.inl 129, -29255313600), (Sum.inl 131, -20785348800), (Sum.inl 132, -29731382400), (Sum.inl 133, -29255313600), (Sum.inl 142, -67977108000), (Sum.inl 143, 4002672000), (Sum.inl 146, 22659036000), (Sum.inl 149, 113295180000), (Sum.inl 158, 2595219200), (Sum.inl 160, -2596374400), (Sum.inl 162, 81471988800), (Sum.inl 397, 3863563200)]

theorem originalBlockCheck18 : originalBlock18 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock18 keyMomentRows) := by decide +kernel

theorem originalBlockEval18 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock18 x =
      Integer.Sparse.eval keyPolynomialBlock18 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck18, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
