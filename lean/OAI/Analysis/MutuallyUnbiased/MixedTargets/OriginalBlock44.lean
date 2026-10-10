import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock44 : Integer.Sparse (Fin 2886) := [(1408, -20121827200), (1409, -84460621920), (1410, 61165874400), (1411, 59801372160), (1412, 11396067600), (1413, 3560809200), (1414, 45515356800), (1415, 27656481600), (1416, 23566032000), (1417, 29820369600), (1418, 54562934400), (1419, 30092011200), (1420, 3183336000), (1421, 24607056000), (1422, 28451084160), (1423, 36703621600), (1424, 45680181440), (1425, 41826216400), (1426, 47400364800), (1427, 144359200), (1428, 1332079200), (1429, -11104874400), (1430, -3560809200), (1431, -291193200), (1432, 28143720000), (1433, 62555452800), (1434, 12534105600), (1435, -73767985920), (1436, -97679078400), (1437, -18806785920), (1438, 4357972800), (1439, -100576605120)]

def originalBlock44 : Integer.Sparse OriginalKey := [(Sum.inl 1216, 6660396000), (Sum.inl 1219, 237001824000), (Sum.inl 1241, 228400907200), (Sum.inl 1245, 142255420800), (Sum.inl 1809, -94033929600), (Sum.inl 1824, 21789864000), (Sum.inl 1826, 62670528000), (Sum.inl 2089, -502883025600), (Sum.inl 2108, -488395392000), (Sum.inl 2133, 312777264000), (Sum.inl 2245, 227576784000), (Sum.inl 2253, -368839929600), (Sum.inl 2284, 140718600000), (Sum.inl 2545, -1455966000), (Sum.inl 2557, -55524372000), (Sum.inl 2617, 721796000), (Sum.inl 2620, 209131082000), (Sum.inl 2710, 120478362000), (Sum.inl 2732, 183518108000), (Sum.inl 2744, 123035280000), (Sum.inl 2916, 15916680000), (Sum.inl 2928, 150460056000), (Sum.inl 2930, 272814672000), (Sum.inl 3030, 117830160000), (Sum.inl 3378, 149101848000), (Sum.inl 3715, 299006860800), (Sum.inl 3722, -422303109600), (Sum.inl 3723, 305829372000), (Sum.inl 3839, 56980338000), (Sum.inl 3872, -100609136000), (Sum.inl 3899, 17804046000)]

theorem originalBlockCheck44 : originalBlock44 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock44 keyMomentRows) := by decide +kernel

theorem originalBlockEval44 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock44 x =
      Integer.Sparse.eval keyPolynomialBlock44 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck44, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
