import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock54 : Integer.Sparse (Fin 2886) := [(1728, -602036640), (1729, 37530025920), (1730, -4526850240), (1731, -13666114560), (1732, 1759960320), (1733, 47007820800), (1734, -41642377920), (1735, 81664291200), (1736, -610496640), (1737, 3613479840), (1738, -80007093120), (1739, -10036861440), (1740, 23704545600), (1741, -23704545600), (1742, 36226100160), (1743, -36226100160), (1744, 4881795840), (1745, 29740402080), (1746, -1657198080), (1747, 13375184640), (1748, -4881795840), (1749, -21383216640), (1750, 13666114560), (1751, -1759960320), (1752, -2727826560), (1753, 9939297600), (1754, 10688469120), (1755, 1831777920), (1756, 30805021440), (1757, -1831777920), (1758, -29397516480), (1759, -577347840)]

def originalBlock54 : Integer.Sparse OriginalKey := [(Sum.inl 584, -3010183200), (Sum.inl 599, -2886739200), (Sum.inl 600, 9158889600), (Sum.inl 608, -9158889600), (Sum.inl 610, -146987582400), (Sum.inl 613, 53442345600), (Sum.inl 615, -106916083200), (Sum.inl 618, 49696488000), (Sum.inl 620, 154025107200), (Sum.inl 934, -8799801600), (Sum.inl 1051, 68330572800), (Sum.inl 1126, -3052483200), (Sum.inl 1128, 8799801600), (Sum.inl 1129, 24408979200), (Sum.inl 1131, 66875923200), (Sum.inl 1134, -50184307200), (Sum.inl 1135, -118522728000), (Sum.inl 1138, -208211889600), (Sum.inl 1139, -24408979200), (Sum.inl 1140, 148702010400), (Sum.inl 1143, -22634251200), (Sum.inl 1144, -13639132800), (Sum.inl 1145, 18067399200), (Sum.inl 1235, 181130500800), (Sum.inl 1236, 408321456000), (Sum.inl 1239, -68330572800), (Sum.inl 1240, -181130500800), (Sum.inl 1242, -8285990400), (Sum.inl 1246, -400035465600), (Sum.inl 1293, 118522728000), (Sum.inl 1294, 235039104000), (Sum.inl 1297, 187650129600)]

theorem originalBlockCheck54 : originalBlock54 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock54 keyMomentRows) := by decide +kernel

theorem originalBlockEval54 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock54 x =
      Integer.Sparse.eval keyPolynomialBlock54 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck54, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
