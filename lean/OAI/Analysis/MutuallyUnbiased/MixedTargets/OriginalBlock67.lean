import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock67 : Integer.Sparse (Fin 2886) := [(2144, -38713886160), (2145, 51869179200), (2146, -51294132000), (2147, -261293431200), (2148, -179224764720), (2149, -61019927040), (2150, -28722546720), (2151, -257170321440), (2152, 26557454640), (2153, -71129433600), (2154, 41502743040), (2155, -70455217920), (2156, -181490878800), (2157, 498528600), (2158, -10195068000), (2159, -144585806880), (2160, -4411204680), (2161, 35352758640), (2162, -66991429440), (2163, -145433555520), (2164, -26688552960), (2165, -30261856320), (2166, -20113308480), (2167, 18952239360), (2168, 31531533120), (2169, 22459008000), (2170, -35781227520), (2171, 109742042880), (2172, -179535872640), (2173, 7047137280), (2174, -198362880), (2175, -1269676800)]

def originalBlock67 : Integer.Sparse OriginalKey := [(Sum.inl 2661, 22459008000), (Sum.inl 2676, 35352758640), (Sum.inl 2677, 41502743040), (Sum.inl 2697, -10195068000), (Sum.inl 2708, 31531533120), (Sum.inl 2710, 18952239360), (Sum.inl 2719, -1269676800), (Sum.inl 2724, -198362880), (Sum.inl 2728, -144585806880), (Sum.inl 2729, -71129433600), (Sum.inl 2730, -4411204680), (Sum.inl 2731, 26557454640), (Sum.inl 2732, -257170321440), (Sum.inl 2747, -35781227520), (Sum.inl 2748, -90568526400), (Sum.inl 2750, 109742042880), (Sum.inl 2751, -30261856320), (Sum.inl 2753, -26688552960), (Sum.inl 2754, -145433555520), (Sum.inl 2755, -66991429440), (Sum.inl 2761, 7047137280), (Sum.inl 2769, -179535872640), (Sum.inl 2771, -28722546720), (Sum.inl 2773, -181490878800), (Sum.inl 2774, -61019927040), (Sum.inl 2775, 498528600), (Sum.inl 2776, -179224764720), (Sum.inl 2777, -261293431200), (Sum.inl 2778, -51294132000), (Sum.inl 3051, -38713886160), (Sum.inl 3074, 51869179200), (Sum.inl 4890, -267965717760), (Sum.inl 4899, -205176528000), (Sum.inl 5161, -5078707200), (Sum.inl 5175, 28188549120), (Sum.inl 5219, 89836032000), (Sum.inl 5231, 141411034560), (Sum.inl 5232, 166010972160), (Sum.inl 5243, -40780272000), (Sum.inl 5249, 126126132480), (Sum.inl 5251, 75808957440), (Sum.inl 5260, -793451520), (Sum.inl 5263, -578343227520), (Sum.inl 5264, -284517734400), (Sum.inl 5265, -17644818720), (Sum.inl 5266, 106229818560), (Sum.inl 5267, -1028681285760), (Sum.inl 5270, -581734222080), (Sum.inl 5276, -1045173724800), (Sum.inl 5278, -143124910080), (Sum.inl 5279, -362274105600), (Sum.inl 5281, 646444888320), (Sum.inl 5282, -121047425280), (Sum.inl 5284, -106754211840), (Sum.inl 5295, -718143490560), (Sum.inl 5297, -114890186880), (Sum.inl 5299, -880819059840), (Sum.inl 5300, -244079708160), (Sum.inl 5301, 1994114400), (Sum.inl 5302, -716899058880)]

theorem originalBlockCheck67 : originalBlock67 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock67 keyMomentRows) := by decide +kernel

theorem originalBlockEval67 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock67 x =
      Integer.Sparse.eval keyPolynomialBlock67 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck67, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
