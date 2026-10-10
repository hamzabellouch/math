import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock4 : Integer.Sparse (Fin 2886) := [(128, -1527638400), (129, 867035520), (130, -9452638720), (131, 2943398400), (132, -6600101760), (133, -6036938560), (134, 545198400), (135, -5891803040), (136, -33069067200), (137, -49685040000), (138, -12000871440), (139, 12379132800), (140, 12066415040), (141, -8842310400), (142, -3429192960), (143, -4486000320), (144, -35552785920), (145, 197436160), (146, 3517361120), (147, -6600101760), (148, 14513679360), (149, 25793022400), (150, -17628934080), (151, -1539187200), (152, 1541328000), (153, 2565312000), (154, 735849600), (155, -1541328000), (156, 5052748800), (157, 513062400), (158, 75577280), (159, -10737091200)]

def originalBlock4 : Integer.Sparse OriginalKey := [(Sum.inl 14, -60004357200), (Sum.inl 19, -30184692800), (Sum.inl 32, -33000508800), (Sum.inl 41, 4335177600), (Sum.inl 58, -265908600000), (Sum.inl 60, 55422432000), (Sum.inl 67, 61895664000), (Sum.inl 73, 2725992000), (Sum.inl 74, 7706640000), (Sum.inl 75, -7706640000), (Sum.inl 76, -33000508800), (Sum.inl 87, 189297187200), (Sum.inl 91, 25263744000), (Sum.inl 93, -53685456000), (Sum.inl 94, 377886400), (Sum.inl 97, -11872209600), (Sum.inl 98, 3679248000), (Sum.inl 101, -7695936000), (Sum.inl 102, -46276012800), (Sum.inl 103, 12826560000), (Sum.inl 143, 14716992000), (Sum.inl 154, -7638192000), (Sum.inl 169, -22430001600), (Sum.inl 197, -165345336000), (Sum.inl 227, -44211552000), (Sum.inl 249, -248425200000), (Sum.inr 2, 2565312000)]

theorem originalBlockCheck4 : originalBlock4 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock4 keyMomentRows) := by decide +kernel

theorem originalBlockEval4 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock4 x =
      Integer.Sparse.eval keyPolynomialBlock4 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck4, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
