import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock5 : Integer.Sparse (Fin 2886) := [(160, 4627601280), (161, -1839624000), (162, 6600101760), (163, 8579179840), (164, 19375987680), (165, 6081626560), (166, -11714846400), (167, -1392067040), (168, 1121429520), (169, -2556859680), (170, -3692998080), (171, -2495842560), (172, -772712640), (173, 1352247120), (174, -2781372480), (175, -1990157760), (176, 4570859280), (177, 2300262080), (178, -2990666880), (179, 206942400), (180, -1656021360), (181, -4263292800), (182, -513062400), (183, 20407262400), (184, -4783584000), (185, -11433947040), (186, 19966740480), (187, 513062400), (188, -10614174720), (189, 4783584000), (190, -14975055360), (191, 6177366720)]

def originalBlock5 : Integer.Sparse OriginalKey := [(Sum.inl 8, -3863563200), (Sum.inl 9, 6761235600), (Sum.inl 11, -9950788800), (Sum.inl 12, -12784298400), (Sum.inl 13, -13906862400), (Sum.inl 14, 5607147600), (Sum.inl 15, -12479212800), (Sum.inl 16, 54397209600), (Sum.inl 17, -18464990400), (Sum.inl 18, -14953334400), (Sum.inl 19, -6960335200), (Sum.inl 20, 22854296400), (Sum.inl 37, 33000508800), (Sum.inl 59, -58574232000), (Sum.inl 88, 96879938400), (Sum.inl 99, 30408132800), (Sum.inl 100, -9198120000), (Sum.inl 104, 23138006400), (Sum.inl 377, -2565312000), (Sum.inl 382, 99833702400), (Sum.inl 383, -23917920000), (Sum.inl 384, -57169735200), (Sum.inl 385, -21316464000), (Sum.inl 387, 102036312000), (Sum.inl 389, -8280106800), (Sum.inl 391, 30886833600), (Sum.inl 402, 2565312000), (Sum.inl 409, -74875276800), (Sum.inl 410, 23917920000), (Sum.inl 414, -53070873600), (Sum.inr 0, 1034712000)]

theorem originalBlockCheck5 : originalBlock5 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock5 keyMomentRows) := by decide +kernel

theorem originalBlockEval5 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock5 x =
      Integer.Sparse.eval keyPolynomialBlock5 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck5, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
