import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock62 : Integer.Sparse (Fin 2886) := [(1984, 2211408000), (1985, -151724160), (1986, -3478201920), (1987, -7542887040), (1988, 5840294400), (1989, -12133370880), (1990, 151724160), (1991, 151724160), (1992, -12133370880), (1993, -6917552640), (1994, 3478201920), (1995, -6049434240), (1996, 504296640), (1997, 504296640), (1998, 3478201920), (1999, 1172142720), (2000, 20813333760), (2001, -13131941760), (2002, -45081736800), (2003, -15860171520), (2004, 14527101600), (2005, 7235763840), (2006, 1090258560), (2007, 26360455680), (2008, 24067801440), (2009, 35549871840), (2010, -20421514080), (2011, 7975556160), (2012, -5286291840), (2013, -38544670080), (2014, 17240785920), (2015, 8881524000)]

def originalBlock62 : Integer.Sparse OriginalKey := [(Sum.inl 577, -17391009600), (Sum.inl 578, -60666854400), (Sum.inl 579, 17391009600), (Sum.inl 597, -758620800), (Sum.inl 601, 758620800), (Sum.inl 1111, 2521483200), (Sum.inl 1125, 11057040000), (Sum.inl 1126, 86203929600), (Sum.inl 1789, 17391009600), (Sum.inl 1802, 104066668800), (Sum.inl 1803, 758620800), (Sum.inl 1822, 29201472000), (Sum.inl 1823, -34587763200), (Sum.inl 1964, -26431459200), (Sum.inl 1966, 5451292800), (Sum.inl 2019, -79300857600), (Sum.inl 2051, -65659708800), (Sum.inl 2088, -60666854400), (Sum.inl 2105, 5860713600), (Sum.inl 2132, -37714435200), (Sum.inl 2243, -225408684000), (Sum.inl 2508, 44407620000), (Sum.inl 2524, 2521483200), (Sum.inl 2529, -30247171200), (Sum.inl 2807, 177749359200), (Sum.inl 3493, 131802278400), (Sum.inl 3496, -192723350400), (Sum.inl 3689, 39877780800), (Sum.inl 3703, -102107570400), (Sum.inl 3786, 36178819200), (Sum.inl 3805, 120339007200), (Sum.inl 3812, 72635508000)]

theorem originalBlockCheck62 : originalBlock62 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock62 keyMomentRows) := by decide +kernel

theorem originalBlockEval62 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock62 x =
      Integer.Sparse.eval keyPolynomialBlock62 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck62, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
