import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock31 : Integer.Sparse (Fin 2886) := [(992, -6245040000), (993, -21241960320), (994, -33279843360), (995, 36651522720), (996, -3277440480), (997, 33313173120), (998, -4504694400), (999, 15924055680), (1000, -17303277120), (1001, -46633697280), (1002, -15305165760), (1003, -15924055680), (1004, -51897707520), (1005, 10095405120), (1006, -27138769920), (1007, 26705880000), (1008, 7207872000), (1009, -4330238400), (1010, 50924900160), (1011, 20355807360), (1012, 891888000), (1013, 11949730560), (1014, 2484509760), (1015, -32966534400), (1016, -46581556800), (1017, 28382808960), (1018, -53860588800), (1019, 4330238400), (1020, -5789256000), (1021, -5990311680), (1022, 106116756960), (1023, 28717637280)]

def originalBlock31 : Integer.Sparse OriginalKey := [(Sum.inl 1116, -29951558400), (Sum.inl 1121, -232907784000), (Sum.inl 1137, 12422548800), (Sum.inl 1146, 4459440000), (Sum.inl 2235, 166565865600), (Sum.inl 2430, 530583784800), (Sum.inl 2435, 141914044800), (Sum.inl 2440, -28946280000), (Sum.inl 2443, -164832672000), (Sum.inl 2471, 143588186400), (Sum.inl 2486, -269302944000), (Sum.inl 2497, 59748652800), (Sum.inl 2520, 101779036800), (Sum.inl 2707, -22523472000), (Sum.inl 2800, -106209801600), (Sum.inl 2890, 36039360000), (Sum.inl 2895, -135693849600), (Sum.inl 2899, -259488537600), (Sum.inl 3128, -21651192000), (Sum.inl 3130, -76525828800), (Sum.inl 3132, 21651192000), (Sum.inl 3133, -16387202400), (Sum.inl 3137, 133529400000), (Sum.inl 3155, 79620278400), (Sum.inl 3158, -79620278400), (Sum.inl 3162, -166399216800), (Sum.inl 3172, 254624500800), (Sum.inl 3179, -233168486400), (Sum.inl 3189, -31225200000), (Sum.inl 3197, 50477025600), (Sum.inl 3199, 183257613600), (Sum.inl 3221, -86516385600)]

theorem originalBlockCheck31 : originalBlock31 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock31 keyMomentRows) := by decide +kernel

theorem originalBlockEval31 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock31 x =
      Integer.Sparse.eval keyPolynomialBlock31 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck31, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
