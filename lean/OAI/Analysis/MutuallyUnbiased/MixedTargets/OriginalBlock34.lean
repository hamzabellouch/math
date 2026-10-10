import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock34 : Integer.Sparse (Fin 2886) := [(1088, -47238804480), (1089, 39376221600), (1090, 40618465440), (1091, 1679664960), (1092, -18611928000), (1093, -24355312320), (1094, -1930870080), (1095, 4742619840), (1096, 27842882880), (1097, -19243593600), (1098, -6689957760), (1099, -41668538880), (1100, -21260339520), (1101, -4572421440), (1102, 26705880000), (1103, 7207872000), (1104, -26705880000), (1105, -7207872000), (1106, 13825656000), (1107, 24529604160), (1108, 21275371200), (1109, 18611928000), (1110, 12182188800), (1111, 1930870080), (1112, -10012992000), (1113, 9714124800), (1114, 3043320000), (1115, -602036640), (1116, 7662680640), (1117, 12231642240), (1118, -8983886400), (1119, 44248805760)]

def originalBlock34 : Integer.Sparse OriginalKey := [(Sum.inl 591, 60910944000), (Sum.inl 623, -33449788800), (Sum.inl 624, -9654350400), (Sum.inl 626, 106376856000), (Sum.inl 627, -22862107200), (Sum.inl 628, 9654350400), (Sum.inl 629, 36039360000), (Sum.inl 630, -36039360000), (Sum.inl 631, -96217968000), (Sum.inl 633, 122648020800), (Sum.inl 634, -121776561600), (Sum.inl 635, -50064960000), (Sum.inl 636, -106301697600), (Sum.inl 637, 133529400000), (Sum.inl 638, 139214414400), (Sum.inl 639, -93059640000), (Sum.inl 640, -133529400000), (Sum.inl 641, 69128280000), (Sum.inl 642, -208342694400), (Sum.inl 643, 93059640000), (Sum.inl 653, 23713099200), (Sum.inl 654, 8398324800), (Sum.inl 911, 196881108000), (Sum.inl 1324, -236194022400), (Sum.inl 1333, 203092327200), (Sum.inl 2740, 48570624000), (Sum.inl 3052, 15216600000), (Sum.inl 3075, -44919432000), (Sum.inl 3534, 221244028800), (Sum.inl 3547, -3010183200), (Sum.inl 3548, 38313403200), (Sum.inl 3549, 61158211200)]

theorem originalBlockCheck34 : originalBlock34 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock34 keyMomentRows) := by decide +kernel

theorem originalBlockEval34 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock34 x =
      Integer.Sparse.eval keyPolynomialBlock34 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck34, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
