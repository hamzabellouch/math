import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock52 : Integer.Sparse (Fin 2886) := [(1664, 5159059200), (1665, -13563699840), (1666, -43089621120), (1667, -34178477760), (1668, 53994753600), (1669, -5630924160), (1670, 18714173760), (1671, 73534622400), (1672, 15306086400), (1673, 6777233280), (1674, -32091895680), (1675, 24375447360), (1676, -24661774080), (1677, -8993124480), (1678, -5630924160), (1679, -47794132800), (1680, -2266787520), (1681, 2266787520), (1682, -13077792000), (1683, 12286451520), (1684, -21902857920), (1685, -37611000000), (1686, 11682981120), (1687, 13077792000), (1688, 3865770240), (1689, 18457999200), (1690, 20695098240), (1691, 36961007040), (1692, 22528468800), (1693, -11728944960), (1694, -17995943040), (1695, 10446238080)]

def originalBlock52 : Integer.Sparse OriginalKey := [(Sum.inl 611, 184805035200), (Sum.inl 620, 92289996000), (Sum.inl 930, 52231190400), (Sum.inl 939, -58644724800), (Sum.inl 1046, 112642344000), (Sum.inl 1091, 103475491200), (Sum.inl 1145, 61432257600), (Sum.inl 1964, 25795296000), (Sum.inl 2345, -89979715200), (Sum.inl 2429, 19328851200), (Sum.inl 2434, 58414905600), (Sum.inl 2485, -188055000000), (Sum.inl 2519, -109514289600), (Sum.inl 2807, 76530432000), (Sum.inl 2809, -65388960000), (Sum.inl 2813, -44965622400), (Sum.inl 2814, -11333937600), (Sum.inl 2815, 133211174400), (Sum.inl 2817, -170892388800), (Sum.inl 2818, 65388960000), (Sum.inl 2820, 33886166400), (Sum.inl 2881, 269973768000), (Sum.inl 2889, -160459478400), (Sum.inl 2893, -28154620800), (Sum.inl 2896, 93570868800), (Sum.inl 2924, 367673112000), (Sum.inl 2931, -123308870400), (Sum.inl 2954, -215448105600), (Sum.inl 3053, -238970664000), (Sum.inl 3054, -67818499200), (Sum.inl 3077, -28154620800)]

theorem originalBlockCheck52 : originalBlock52 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock52 keyMomentRows) := by decide +kernel

theorem originalBlockEval52 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock52 x =
      Integer.Sparse.eval keyPolynomialBlock52 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck52, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
