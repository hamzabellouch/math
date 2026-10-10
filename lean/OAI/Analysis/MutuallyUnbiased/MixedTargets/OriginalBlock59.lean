import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock59 : Integer.Sparse (Fin 2886) := [(1888, -16069440000), (1889, -18627731520), (1890, 18277105920), (1891, 8835269760), (1892, 64004486400), (1893, 18317710080), (1894, -1911841920), (1895, 18317710080), (1896, -17670539520), (1897, -64004486400), (1898, -18317710080), (1899, 1911841920), (1900, 1911841920), (1901, -18317710080), (1902, -64004486400), (1903, -18317710080), (1904, -18317710080), (1905, -5286291840), (1906, -38544670080), (1907, -29071918080), (1908, -118767916800), (1909, 13532618880), (1910, -30182503680), (1911, 16356792960), (1912, 5260325760), (1913, -36025591680), (1914, -2211408000), (1915, 8835269760), (1916, -1911841920), (1917, -2211408000), (1918, -36025591680), (1919, 5260325760)]

def originalBlock59 : Integer.Sparse OriginalKey := [(Sum.inl 1087, -93138657600), (Sum.inl 1091, 91385529600), (Sum.inl 1212, 26301628800), (Sum.inl 1233, -180127958400), (Sum.inl 1234, -11057040000), (Sum.inl 2243, 44176348800), (Sum.inl 2247, -26431459200), (Sum.inl 2263, -88352697600), (Sum.inl 2277, 67663094400), (Sum.inl 2512, -80347200000), (Sum.inl 2721, -320022432000), (Sum.inl 2730, -150912518400), (Sum.inl 2741, 320022432000), (Sum.inl 2764, -320022432000), (Sum.inl 2923, -9559209600), (Sum.inl 3043, 81783964800), (Sum.inl 3074, -91588550400), (Sum.inl 3075, 9559209600), (Sum.inl 3077, -145359590400), (Sum.inl 3078, -91588550400), (Sum.inl 3488, -11057040000), (Sum.inl 3526, 9559209600), (Sum.inl 3619, -9559209600), (Sum.inl 3623, -192723350400), (Sum.inl 3812, 26301628800), (Sum.inl 3874, -180127958400), (Sum.inl 3954, -91588550400), (Sum.inl 3957, -91588550400), (Sum.inl 3962, 91588550400), (Sum.inl 4010, -593839584000), (Sum.inl 4025, 91588550400), (Sum.inl 4083, 44176348800)]

theorem originalBlockCheck59 : originalBlock59 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock59 keyMomentRows) := by decide +kernel

theorem originalBlockEval59 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock59 x =
      Integer.Sparse.eval keyPolynomialBlock59 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck59, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
