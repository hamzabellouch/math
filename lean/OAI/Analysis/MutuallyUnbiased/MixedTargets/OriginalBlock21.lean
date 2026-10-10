import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock21 : Integer.Sparse (Fin 2886) := [(672, -6493545600), (673, -286883520), (674, -5194836480), (675, -5844191040), (676, -286883520), (677, -239069600), (678, 21428167680), (679, 5321594880), (680, 282042720), (681, -2632325760), (682, -25302504960), (683, 35004375360), (684, 5321594880), (685, -778348800), (686, -1363832640), (687, -1434417600), (688, 6530198400), (689, 9775883520), (690, -143441760), (691, 12577524480), (692, -143441760), (693, 430325280), (694, 525953120), (695, 11688382080), (696, 655456000), (697, -4511577600), (698, 143441760), (699, -24301392480), (700, -10643189760), (701, -13515732000), (702, 5264651520), (703, 50605009920)]

def originalBlock21 : Integer.Sparse OriginalKey := [(Sum.inl 5, 107140838400), (Sum.inl 7, 175021876800), (Sum.inl 224, 26323257600), (Sum.inl 259, 48879417600), (Sum.inl 262, -13161628800), (Sum.inl 319, 58441910400), (Sum.inl 327, 62887622400), (Sum.inl 373, -58441910400), (Sum.inl 374, -29220955200), (Sum.inl 376, -717208800), (Sum.inl 378, 2629765600), (Sum.inl 387, 253025049600), (Sum.inl 397, -3891744000), (Sum.inl 416, -126512524800), (Sum.inl 479, -20406261600), (Sum.inl 488, -1195348000), (Sum.inl 489, 3277280000), (Sum.inl 490, -67578660000), (Sum.inl 494, -8606505600), (Sum.inl 504, 26607974400), (Sum.inl 505, 1410213600), (Sum.inl 506, -121506962400), (Sum.inl 526, -53215948800), (Sum.inl 529, 26607974400), (Sum.inl 531, 32650992000), (Sum.inl 532, -6819163200), (Sum.inr 7, -1434417600)]

theorem originalBlockCheck21 : originalBlock21 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock21 keyMomentRows) := by decide +kernel

theorem originalBlockEval21 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock21 x =
      Integer.Sparse.eval keyPolynomialBlock21 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck21, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
