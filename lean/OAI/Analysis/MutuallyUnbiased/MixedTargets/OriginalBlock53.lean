import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock53 : Integer.Sparse (Fin 2886) := [(1696, -3865770240), (1697, -3223732800), (1698, 12618492000), (1699, -2352340800), (1700, 29232033200), (1701, 851860800), (1702, 291193200), (1703, -29232033200), (1704, -23250407520), (1705, -291193200), (1706, -34066862400), (1707, -7788551600), (1708, 12943412160), (1709, -291193200), (1710, -23566032000), (1711, -3183336000), (1712, 7788551600), (1713, 5169799200), (1714, 291193200), (1715, 3223732800), (1716, -14424601920), (1717, 36419203200), (1718, -21443481600), (1719, -20181606720), (1720, 29232033200), (1721, 20057240640), (1722, 291193200), (1723, 23566032000), (1724, 3183336000), (1725, -7788551600), (1726, -8362966080), (1727, -291193200)]

def originalBlock53 : Integer.Sparse OriginalKey := [(Sum.inl 1115, -41814830400), (Sum.inl 1148, -1455966000), (Sum.inl 1149, 1455966000), (Sum.inl 1150, 15916680000), (Sum.inl 1151, -100908033600), (Sum.inl 1153, -72123009600), (Sum.inl 1155, 100286203200), (Sum.inl 1156, -107217408000), (Sum.inl 1159, -38942758000), (Sum.inl 1160, 146160166000), (Sum.inl 1169, 117830160000), (Sum.inl 1171, 182096016000), (Sum.inl 1174, 16118664000), (Sum.inl 1212, -1455966000), (Sum.inl 1215, 1455966000), (Sum.inl 1217, -15916680000), (Sum.inl 1219, 64717060800), (Sum.inl 1221, 25848996000), (Sum.inl 1233, 1455966000), (Sum.inl 1237, -1455966000), (Sum.inl 1241, 4259304000), (Sum.inl 1243, -116252037600), (Sum.inl 1245, 63092460000), (Sum.inl 1261, -38942758000), (Sum.inl 1264, 38942758000), (Sum.inl 1270, -117830160000), (Sum.inl 1273, -170334312000), (Sum.inl 1291, 146160166000), (Sum.inl 1295, -146160166000), (Sum.inl 1306, -11761704000), (Sum.inl 1310, -16118664000), (Sum.inl 2339, -19328851200)]

theorem originalBlockCheck53 : originalBlock53 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock53 keyMomentRows) := by decide +kernel

theorem originalBlockEval53 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock53 x =
      Integer.Sparse.eval keyPolynomialBlock53 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck53, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
