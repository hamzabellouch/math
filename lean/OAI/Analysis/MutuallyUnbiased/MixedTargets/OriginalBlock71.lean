import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock71 : Integer.Sparse (Fin 2886) := [(2272, 12093438960), (2273, -2346018240), (2274, -90318763200), (2275, -2917087344), (2276, -56027260920), (2277, -69533421440), (2278, -25204183200), (2279, -229294560), (2280, 26555973120), (2281, 3168586560), (2282, -32912653520), (2283, 18985004304), (2284, 36446353920), (2285, -19642180080), (2286, -128076984960), (2287, 9755589600), (2288, -126326566320), (2289, -21978605760), (2290, 59460313280), (2291, 61205507520), (2292, 36587845440), (2293, -2541376080), (2294, 18377043840), (2295, 34751568000), (2296, -17877500160), (2297, 14621172480), (2298, -45802977600), (2299, 15506176320), (2300, 53361129600), (2301, 60118089920), (2302, 45650111040), (2303, 14396377440)]

def originalBlock71 : Integer.Sparse OriginalKey := [(Sum.inl 1667, 9755589600), (Sum.inl 1672, 14396377440), (Sum.inl 1678, 34751568000), (Sum.inl 1679, 36587845440), (Sum.inl 1684, 16067916960), (Sum.inl 1685, 24209954880), (Sum.inl 1697, 14621172480), (Sum.inl 1699, -17877500160), (Sum.inl 1703, 53361129600), (Sum.inl 1704, 15506176320), (Sum.inl 1709, -45802977600), (Sum.inl 1711, -126326566320), (Sum.inl 1712, -128076984960), (Sum.inl 1713, -21978605760), (Sum.inl 1714, -19642180080), (Sum.inl 1715, 36446353920), (Sum.inl 1722, 45650111040), (Sum.inl 1729, 60118089920), (Sum.inl 1734, -2541376080), (Sum.inl 1735, 61205507520), (Sum.inl 1736, 18377043840), (Sum.inl 1740, 59460313280), (Sum.inl 1742, 3168586560), (Sum.inl 1743, -229294560), (Sum.inl 1744, -32912653520), (Sum.inl 1745, -25204183200), (Sum.inl 1746, -69533421440), (Sum.inl 2164, -90318763200), (Sum.inl 2181, -56027260920), (Sum.inl 2223, 12093438960), (Sum.inl 4328, 39022358400), (Sum.inl 4330, 57585509760), (Sum.inl 4331, 64271667840), (Sum.inl 4332, 139006272000), (Sum.inl 4334, 146351381760), (Sum.inl 4336, 96839819520), (Sum.inl 4363, 58484689920), (Sum.inl 4364, 213444518400), (Sum.inl 4365, 62024705280), (Sum.inl 4366, -505306265280), (Sum.inl 4368, -512307939840), (Sum.inl 4370, 182600444160), (Sum.inl 4371, 12674346240), (Sum.inl 4372, -10165504320), (Sum.inl 4373, 244822030080), (Sum.inl 4375, -917178240), (Sum.inl 4439, -87914423040), (Sum.inl 4442, -131650614080), (Sum.inl 4444, 73508175360), (Sum.inl 4459, -78568720320), (Sum.inl 4464, -100816732800), (Sum.inl 4473, -71510000640), (Sum.inl 4474, -183211910400), (Sum.inl 4475, 145785415680), (Sum.inl 4476, 240472359680), (Sum.inl 4478, -278133685760), (Sum.inl 4480, 237841253120), (Sum.inl 4670, -361275052800), (Sum.inl 4757, -224109043680), (Sum.inl 4777, 48373755840)]

theorem originalBlockCheck71 : originalBlock71 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock71 keyMomentRows) := by decide +kernel

theorem originalBlockEval71 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock71 x =
      Integer.Sparse.eval keyPolynomialBlock71 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck71, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
