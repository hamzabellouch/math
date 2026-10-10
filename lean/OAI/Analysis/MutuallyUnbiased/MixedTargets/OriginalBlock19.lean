import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock19 : Integer.Sparse (Fin 2886) := [(608, 9927207360), (609, 1524257280), (610, 9927207360), (611, 772712640), (612, -952660800), (613, -19854414720), (614, -1524257280), (615, -188943200), (616, 4161320640), (617, -15086390400), (618, 23154986880), (619, 2950909760), (620, -1020293280), (621, -4161320640), (622, -214004160), (623, 952660800), (624, 4864653120), (625, -3088286400), (626, 18756605760), (627, -23154986880), (628, -12712813440), (629, 3088286400), (630, 24091104960), (631, -11306956800), (632, 4204656000), (633, 4893592320), (634, 642406880), (635, -943747200), (636, -983184000), (637, 983184000), (638, 983184000), (639, 4511577600)]

def originalBlock19 : Integer.Sparse OriginalKey := [(Sum.inl 113, -4718736000), (Sum.inl 316, 24467961600), (Sum.inl 357, 3863563200), (Sum.inl 358, 49636036800), (Sum.inl 359, -7621286400), (Sum.inl 360, -20806603200), (Sum.inl 361, -75431952000), (Sum.inl 362, -99272073600), (Sum.inl 367, 4763304000), (Sum.inl 368, 15441432000), (Sum.inl 369, 93783028800), (Sum.inl 371, -56534784000), (Sum.inl 376, -1070020800), (Sum.inl 377, -5101466400), (Sum.inl 378, 115774934400), (Sum.inl 387, 120455524800), (Sum.inl 388, 3212034400), (Sum.inl 390, -115774934400), (Sum.inl 394, 7621286400), (Sum.inl 395, 49636036800), (Sum.inl 400, -4763304000), (Sum.inl 401, 20806603200), (Sum.inl 403, 14754548800), (Sum.inl 404, -944716000), (Sum.inl 414, -15441432000), (Sum.inl 415, 21023280000), (Sum.inl 416, -63564067200), (Sum.inl 420, 24323265600), (Sum.inl 489, 4915920000), (Sum.inl 518, 22557888000), (Sum.inl 521, 4915920000), (Sum.inr 4, -4915920000)]

theorem originalBlockCheck19 : originalBlock19 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock19 keyMomentRows) := by decide +kernel

theorem originalBlockEval19 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock19 x =
      Integer.Sparse.eval keyPolynomialBlock19 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck19, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
