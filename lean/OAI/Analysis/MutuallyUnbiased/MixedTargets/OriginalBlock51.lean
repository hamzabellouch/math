import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock51 : Integer.Sparse (Fin 2886) := [(1632, 11104874400), (1633, 3560809200), (1634, 27656481600), (1635, 30092011200), (1636, 2243173600), (1637, -9353676160), (1638, -154826892800), (1639, -140283218400), (1640, -11104874400), (1641, -3560809200), (1642, 7662680640), (1643, 30595320000), (1644, 4664372160), (1645, 22447588800), (1646, 30595320000), (1647, 44618247360), (1648, -55317924000), (1649, -61761530400), (1650, 33164664000), (1651, 25549298400), (1652, 22153260000), (1653, 36212232000), (1654, -30595320000), (1655, -4666687680), (1656, 41525403840), (1657, 7131669120), (1658, -31065164640), (1659, -20695098240), (1660, -2869326720), (1661, -16331302080), (1662, -35264439360), (1663, 11728944960)]

def originalBlock51 : Integer.Sparse OriginalKey := [(Sum.inl 581, 23321860800), (Sum.inl 589, -23333438400), (Sum.inl 606, 38313403200), (Sum.inl 945, 152976600000), (Sum.inl 953, -152976600000), (Sum.inl 1112, -701416092000), (Sum.inl 1120, 181061160000), (Sum.inl 1132, -46768380800), (Sum.inl 1796, 223091236800), (Sum.inl 1812, -81656510400), (Sum.inl 1819, -155325823200), (Sum.inl 1831, 112237944000), (Sum.inl 1970, 58644724800), (Sum.inl 1979, 152976600000), (Sum.inl 2025, -176322196800), (Sum.inl 2062, -103475491200), (Sum.inl 2112, 35658345600), (Sum.inl 2247, -14346633600), (Sum.inl 2281, 207627019200), (Sum.inl 2426, -55524372000), (Sum.inl 2437, -774134464000), (Sum.inl 2442, 110766300000), (Sum.inl 2470, -17804046000), (Sum.inl 2495, 11215868000), (Sum.inl 2746, 138282408000), (Sum.inl 2802, 127746492000), (Sum.inl 2824, -308807652000), (Sum.inl 2826, -276589620000), (Sum.inl 2827, 165823320000), (Sum.inl 2846, 55524372000), (Sum.inl 2847, 150460056000), (Sum.inl 2981, 17804046000)]

theorem originalBlockCheck51 : originalBlock51 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock51 keyMomentRows) := by decide +kernel

theorem originalBlockEval51 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock51 x =
      Integer.Sparse.eval keyPolynomialBlock51 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck51, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
