import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock1 : Integer.Sparse (Fin 2886) := [(32, 10028624640), (33, -13312972800), (34, -7014424320), (35, -1862481600), (36, 11656704000), (37, -20552948400), (38, 1541328000), (39, 2449074240), (40, 3078374400), (41, -1541328000), (42, -33813990720), (43, 6613813440), (44, 10849711680), (45, -13312972800), (46, -2022739200), (47, 3936988800), (48, 1545425280), (49, 1686608640), (50, 1545425280), (51, 522207360), (52, 762128640), (53, -3936988800), (54, 188943200), (55, -1686608640), (56, -340097760), (57, -4636275840), (58, -1044414720), (59, -1333725120), (60, 7368592000), (61, -10105497600), (62, -762128640), (63, -11656704000)]

def originalBlock1 : Integer.Sparse OriginalKey := [(Sum.inl 270, -9312408000), (Sum.inl 324, -23181379200), (Sum.inl 342, -8433043200), (Sum.inl 357, 7727126400), (Sum.inl 359, -3810643200), (Sum.inl 363, -10113696000), (Sum.inl 364, -169069953600), (Sum.inl 376, -50527488000), (Sum.inl 377, -1700488800), (Sum.inl 380, -66564864000), (Sum.inl 381, -7706640000), (Sum.inl 384, 15391872000), (Sum.inl 386, 19684944000), (Sum.inl 391, 58283520000), (Sum.inl 392, 2611036800), (Sum.inl 393, 41502110400), (Sum.inl 394, 3810643200), (Sum.inl 397, 7727126400), (Sum.inl 399, -5222073600), (Sum.inl 400, -73233489600), (Sum.inl 403, 36842960000), (Sum.inl 404, 944716000), (Sum.inl 406, -19684944000), (Sum.inl 408, 12245371200), (Sum.inl 409, 19176436800), (Sum.inl 410, 7706640000), (Sum.inl 412, -102764742000), (Sum.inl 414, 50143123200), (Sum.inl 421, -58283520000)]

theorem originalBlockCheck1 : originalBlock1 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock1 keyMomentRows) := by decide +kernel

theorem originalBlockEval1 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock1 x =
      Integer.Sparse.eval keyPolynomialBlock1 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck1, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
