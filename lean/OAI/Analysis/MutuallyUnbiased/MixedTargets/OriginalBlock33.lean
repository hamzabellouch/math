import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock33 : Integer.Sparse (Fin 2886) := [(1056, -56074103040), (1057, 39131352000), (1058, -4355479680), (1059, 31775260800), (1060, 24750694560), (1061, -61274348160), (1062, -45903946560), (1063, 22108464000), (1064, 46238529600), (1065, -23562930240), (1066, -12524753760), (1067, -12225940800), (1068, 4504694400), (1069, -10095405120), (1070, -16121574720), (1071, 10095405120), (1072, 63188161920), (1073, -50924900160), (1074, 47095621440), (1075, 27309787200), (1076, -10074168000), (1077, 25372248000), (1078, 39026473920), (1079, -12225940800), (1080, 50924900160), (1081, -28392524640), (1082, 19938131520), (1083, 15962798400), (1084, 39648541440), (1085, 26313788160), (1086, -18614069760), (1087, -22360001760)]

def originalBlock33 : Integer.Sparse OriginalKey := [(Sum.inl 587, 131568940800), (Sum.inl 617, 79813992000), (Sum.inl 936, -93070348800), (Sum.inl 951, 198242707200), (Sum.inl 1027, -111800008800), (Sum.inl 1064, 99690657600), (Sum.inl 1118, 126861240000), (Sum.inl 1142, 136548936000), (Sum.inl 1314, 158876304000), (Sum.inl 1316, -254624500800), (Sum.inl 1317, 195132369600), (Sum.inl 1318, -117814651200), (Sum.inl 1319, -80607873600), (Sum.inl 1320, 315940809600), (Sum.inl 1321, -280370515200), (Sum.inl 1322, 254624500800), (Sum.inl 1325, -229519732800), (Sum.inl 1327, -141962623200), (Sum.inl 1328, -61129704000), (Sum.inl 1330, -21777398400), (Sum.inl 1334, 231192648000), (Sum.inl 1335, 195656760000), (Sum.inl 1337, -50370840000), (Sum.inl 1338, 110542320000), (Sum.inl 1366, -50477025600), (Sum.inl 1370, 50477025600), (Sum.inl 1372, 235478107200), (Sum.inl 1375, -306371740800), (Sum.inl 1383, 123753472800), (Sum.inl 1388, -61129704000), (Sum.inl 1391, -62623768800), (Sum.inl 1435, 22523472000)]

theorem originalBlockCheck33 : originalBlock33 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock33 keyMomentRows) := by decide +kernel

theorem originalBlockEval33 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock33 x =
      Integer.Sparse.eval keyPolynomialBlock33 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck33, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
