import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock55 : Integer.Sparse (Fin 2886) := [(1760, 60791849280), (1761, 1154695680), (1762, 30959360640), (1763, -1831777920), (1764, -577347840), (1765, -4359585600), (1766, 1831777920), (1767, -7542887040), (1768, -6917552640), (1769, 3478201920), (1770, 151724160), (1771, 23664430080), (1772, 37304058240), (1773, 151724160), (1774, 3478201920), (1775, 7542887040), (1776, -53169154560), (1777, -25170687360), (1778, -303448320), (1779, -25170687360), (1780, 6917552640), (1781, -6956403840), (1782, -1172142720), (1783, -20813333760), (1784, 13131941760), (1785, 45081736800), (1786, 15860171520), (1787, -12898039680), (1788, -8498807520), (1789, 29504724480), (1790, 13037316480), (1791, -10296464640)]

def originalBlock55 : Integer.Sparse OriginalKey := [(Sum.inl 603, 5773478400), (Sum.inl 605, -9158889600), (Sum.inl 611, 303959246400), (Sum.inl 614, -2886739200), (Sum.inl 615, 154796803200), (Sum.inl 619, 9158889600), (Sum.inl 622, -21797928000), (Sum.inl 2560, -34782019200), (Sum.inl 2603, 34587763200), (Sum.inl 2738, -37714435200), (Sum.inl 2781, 37714435200), (Sum.inl 3050, -34587763200), (Sum.inl 3073, 118322150400), (Sum.inl 3096, -265845772800), (Sum.inl 3118, 147523622400), (Sum.inl 3375, 17391009600), (Sum.inl 3376, -125853436800), (Sum.inl 3380, 65186582400), (Sum.inl 3388, 758620800), (Sum.inl 3390, -64490198400), (Sum.inl 3391, -104066668800), (Sum.inl 3392, -1517241600), (Sum.inl 3532, -42494037600), (Sum.inl 3533, 79300857600), (Sum.inl 3544, 65659708800), (Sum.inl 3571, 186520291200), (Sum.inl 3572, -125853436800), (Sum.inl 3580, 758620800), (Sum.inl 3581, -5860713600), (Sum.inl 3622, 225408684000), (Sum.inl 3625, 17391009600), (Sum.inl 3633, -51482323200)]

theorem originalBlockCheck55 : originalBlock55 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock55 keyMomentRows) := by decide +kernel

theorem originalBlockEval55 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock55 x =
      Integer.Sparse.eval keyPolynomialBlock55 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck55, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
