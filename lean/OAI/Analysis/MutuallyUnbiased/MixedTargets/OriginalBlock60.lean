import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock60 : Integer.Sparse (Fin 2886) := [(1920, 30182503680), (1921, 36025591680), (1922, 64004486400), (1923, 36635420160), (1924, 36025591680), (1925, -10307358720), (1926, -5764622400), (1927, -5764622400), (1928, -14527101600), (1929, -7235763840), (1930, -1090258560), (1931, -26360455680), (1932, -24067801440), (1933, -18937909440), (1934, 32096092320), (1935, 9822002400), (1936, -109322961600), (1937, 16148665920), (1938, 10572583680), (1939, 77089340160), (1940, 29071918080), (1941, 118767916800), (1942, -17240785920), (1943, -8881524000), (1944, -15952749600), (1945, -18937909440), (1946, 21359265600), (1947, 36002526720), (1948, 23979399840), (1949, -32227714560), (1950, -32583814560), (1951, 28257823200)]

def originalBlock60 : Integer.Sparse OriginalKey := [(Sum.inl 1215, -28823112000), (Sum.inl 1235, -94689547200), (Sum.inl 1236, -86203929600), (Sum.inl 1237, 180127958400), (Sum.inl 2025, 52862918400), (Sum.inl 2028, -5451292800), (Sum.inl 2545, -28823112000), (Sum.inl 2575, -51536793600), (Sum.inl 2721, 106796328000), (Sum.inl 2722, -79763748000), (Sum.inl 2739, -44407620000), (Sum.inl 2750, 320022432000), (Sum.inl 2773, 150912518400), (Sum.inl 2924, 145359590400), (Sum.inl 2925, 183177100800), (Sum.inl 3533, -131802278400), (Sum.inl 3534, 385446700800), (Sum.inl 3693, -161138572800), (Sum.inl 3719, 160480461600), (Sum.inl 3720, 180127958400), (Sum.inl 3837, 80743329600), (Sum.inl 3843, 49110012000), (Sum.inl 3845, -162919072800), (Sum.inl 3850, -36178819200), (Sum.inl 3875, -94689547200), (Sum.inl 3876, 119896999200), (Sum.inl 3901, -546614808000), (Sum.inl 3902, 141289116000), (Sum.inl 3903, -120339007200), (Sum.inl 3906, -72635508000), (Sum.inl 3907, 180012633600), (Sum.inl 3974, 593839584000)]

theorem originalBlockCheck60 : originalBlock60 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock60 keyMomentRows) := by decide +kernel

theorem originalBlockEval60 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock60 x =
      Integer.Sparse.eval keyPolynomialBlock60 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck60, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
