import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock10 : Integer.Sparse (Fin 2886) := [(320, -6062232000), (321, -21031476480), (322, -5851062720), (323, -2973138240), (324, -4842156000), (325, -1675752000), (326, -206942400), (327, -3645895920), (328, -3021984000), (329, -16230715200), (330, 2052249600), (331, 6508739520), (332, 7805568000), (333, -10718012160), (334, 6949261440), (335, 11544219520), (336, -7681584000), (337, 45371566120), (338, 10913104800), (339, -8143950720), (340, -24128404800), (341, -32308070400), (342, -2436820320), (343, 4891350000), (344, 3062000400), (345, 7681584000), (346, 968431200), (347, 41996073600), (348, 3382263360), (349, 14205906400), (350, 24906247200), (351, 21394965600)]

def originalBlock10 : Integer.Sparse OriginalKey := [(Sum.inl 152, -29255313600), (Sum.inl 247, -8378760000), (Sum.inl 268, 57721097600), (Sum.inl 270, -1034712000), (Sum.inl 348, 106974828000), (Sum.inl 354, 16911316800), (Sum.inl 363, 34746307200), (Sum.inl 364, -53590060800), (Sum.inl 365, -1691913600), (Sum.inl 366, -81153576000), (Sum.inl 383, -38407920000), (Sum.inl 384, 10261248000), (Sum.inl 402, -24210780000), (Sum.inl 409, 32543697600), (Sum.inl 410, 23298000000), (Sum.inl 412, -18229479600), (Sum.inl 414, -14865691200), (Sum.inl 415, -30311160000), (Sum.inl 416, -105157382400), (Sum.inl 443, -12184101600), (Sum.inl 467, 226857830600), (Sum.inl 475, -161540352000), (Sum.inl 480, -120642024000), (Sum.inl 487, 124531236000), (Sum.inl 491, 71029532000), (Sum.inl 497, 24456750000), (Sum.inl 498, 54565524000), (Sum.inl 499, 15310002000), (Sum.inl 501, 209980368000), (Sum.inl 503, 4842156000)]

theorem originalBlockCheck10 : originalBlock10 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock10 keyMomentRows) := by decide +kernel

theorem originalBlockEval10 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock10 x =
      Integer.Sparse.eval keyPolynomialBlock10 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck10, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
