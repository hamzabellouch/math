import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock3 : Integer.Sparse (Fin 2886) := [(96, -11656704000), (97, -1471699200), (98, 1793145600), (99, -17455823040), (100, -3591436800), (101, 1541328000), (102, 6923236320), (103, -39682880640), (104, -19316027520), (105, 49685040000), (106, 13312972800), (107, 2022739200), (108, -3936988800), (109, -1352247120), (110, -1686608640), (111, 3936988800), (112, -113365920), (113, 1686608640), (114, 453463680), (115, 1545425280), (116, -6315936000), (117, 11656704000), (118, 2834735040), (119, -513062400), (120, -680195520), (121, 9311471520), (122, 39682880640), (123, 10344026880), (124, 6105404800), (125, -13312972800), (126, 10105497600), (127, -2022739200)]

def originalBlock3 : Integer.Sparse OriginalKey := [(Sum.inl 117, 46557357600), (Sum.inl 134, 14173675200), (Sum.inl 163, 7727126400), (Sum.inl 164, -10113696000), (Sum.inl 167, 10113696000), (Sum.inl 168, 34616181600), (Sum.inl 189, -8433043200), (Sum.inl 190, 8433043200), (Sum.inl 192, 198414403200), (Sum.inl 195, -198414403200), (Sum.inl 196, -87279115200), (Sum.inl 212, -66564864000), (Sum.inl 213, 66564864000), (Sum.inl 214, 7706640000), (Sum.inl 220, 2267318400), (Sum.inl 221, 50527488000), (Sum.inl 222, -3400977600), (Sum.inl 229, -17957184000), (Sum.inl 239, 51720134400), (Sum.inl 240, -96580137600), (Sum.inl 248, 248425200000), (Sum.inl 251, 8965728000), (Sum.inl 253, -19684944000), (Sum.inl 254, 19684944000), (Sum.inl 255, 58283520000), (Sum.inl 256, -58283520000), (Sum.inl 257, -6761235600), (Sum.inl 259, -31579680000), (Sum.inl 260, 29960194400), (Sum.inl 268, -7358496000), (Sum.inr 1, -2565312000)]

theorem originalBlockCheck3 : originalBlock3 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock3 keyMomentRows) := by decide +kernel

theorem originalBlockEval3 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock3 x =
      Integer.Sparse.eval keyPolynomialBlock3 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck3, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
