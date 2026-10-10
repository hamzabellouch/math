import OAI.Analysis.MutuallyUnbiased.MixedData.Source11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values9
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1456 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue988 x + ((1 : ℝ) * Sparse.eval nodeValue1922 x + ((1 : ℝ) * Sparse.eval nodeValue2118 x + ((1 : ℝ) * Sparse.eval nodeValue2195 x + ((1 : ℝ) * Sparse.eval nodeValue2214 x + ((1 : ℝ) * Sparse.eval nodeValue2216 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

def numericRow1456 : Integer.Sparse Master := [(Sum.inr 988, 1), (Sum.inr 1922, 1), (Sum.inr 2118, 1), (Sum.inr 2195, 1), (Sum.inr 2214, 1), (Sum.inr 2216, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1456 : Integer.Sparse.reindex keyMap MixedData.row1456 = numericRow1456 := by decide +kernel

theorem numericCheck1456 (x : Master → ℝ) : Integer.Sparse.eval numericRow1456 x =
    (1 : ℝ) * reducedSource1456 x := by
  norm_num [numericRow1456, reducedSource1456, Integer.Sparse.eval, Sparse.eval, nodeValue988, nodeValue1922, nodeValue2118, nodeValue2195, nodeValue2214, nodeValue2216, nodeValue4080]

noncomputable def reducedSource1457 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue987 x + ((1 : ℝ) * Sparse.eval nodeValue1921 x + ((1 : ℝ) * Sparse.eval nodeValue2117 x + ((1 : ℝ) * Sparse.eval nodeValue2213 x + ((2 : ℝ) * Sparse.eval nodeValue2215 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

def numericRow1457 : Integer.Sparse Master := [(Sum.inr 987, 1), (Sum.inr 1921, 1), (Sum.inr 2117, 1), (Sum.inr 2213, 1), (Sum.inr 2215, 2), (Sum.inr 4082, -1)]

theorem reindexCheck1457 : Integer.Sparse.reindex keyMap MixedData.row1457 = numericRow1457 := by decide +kernel

theorem numericCheck1457 (x : Master → ℝ) : Integer.Sparse.eval numericRow1457 x =
    (1 : ℝ) * reducedSource1457 x := by
  norm_num [numericRow1457, reducedSource1457, Integer.Sparse.eval, Sparse.eval, nodeValue987, nodeValue1921, nodeValue2117, nodeValue2213, nodeValue2215, nodeValue4082]

noncomputable def reducedSource1458 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1023 x + ((2 : ℝ) * Sparse.eval nodeValue2091 x + ((2 : ℝ) * Sparse.eval nodeValue2234 x + ((1 : ℝ) * Sparse.eval nodeValue2241 x + ((-1 : ℝ) * Sparse.eval nodeValue4079 x + 0))))

def numericRow1458 : Integer.Sparse Master := [(Sum.inr 1023, 1), (Sum.inr 2091, 2), (Sum.inr 2234, 2), (Sum.inr 2241, 1), (Sum.inr 4079, -1)]

theorem reindexCheck1458 : Integer.Sparse.reindex keyMap MixedData.row1458 = numericRow1458 := by decide +kernel

theorem numericCheck1458 (x : Master → ℝ) : Integer.Sparse.eval numericRow1458 x =
    (1 : ℝ) * reducedSource1458 x := by
  norm_num [numericRow1458, reducedSource1458, Integer.Sparse.eval, Sparse.eval, nodeValue1023, nodeValue2091, nodeValue2234, nodeValue2241, nodeValue4079]

noncomputable def reducedSource1459 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1018 x + ((1 : ℝ) * Sparse.eval nodeValue1023 x + ((2 : ℝ) * Sparse.eval nodeValue1034 x + ((1 : ℝ) * Sparse.eval nodeValue2241 x + ((-1 : ℝ) * Sparse.eval nodeValue4079 x + 0))))

def numericRow1459 : Integer.Sparse Master := [(Sum.inr 1018, 2), (Sum.inr 1023, 1), (Sum.inr 1034, 2), (Sum.inr 2241, 1), (Sum.inr 4079, -1)]

theorem reindexCheck1459 : Integer.Sparse.reindex keyMap MixedData.row1459 = numericRow1459 := by decide +kernel

theorem numericCheck1459 (x : Master → ℝ) : Integer.Sparse.eval numericRow1459 x =
    (1 : ℝ) * reducedSource1459 x := by
  norm_num [numericRow1459, reducedSource1459, Integer.Sparse.eval, Sparse.eval, nodeValue1018, nodeValue1023, nodeValue1034, nodeValue2241, nodeValue4079]

noncomputable def reducedSource1460 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1018 x + ((2 : ℝ) * Sparse.eval nodeValue2086 x + ((1 : ℝ) * Sparse.eval nodeValue2191 x + ((1 : ℝ) * Sparse.eval nodeValue2232 x + ((1 : ℝ) * Sparse.eval nodeValue2241 x + ((-1 : ℝ) * Sparse.eval nodeValue4079 x + 0)))))

def numericRow1460 : Integer.Sparse Master := [(Sum.inr 1018, 1), (Sum.inr 2086, 2), (Sum.inr 2191, 1), (Sum.inr 2232, 1), (Sum.inr 2241, 1), (Sum.inr 4079, -1)]

theorem reindexCheck1460 : Integer.Sparse.reindex keyMap MixedData.row1460 = numericRow1460 := by decide +kernel

theorem numericCheck1460 (x : Master → ℝ) : Integer.Sparse.eval numericRow1460 x =
    (1 : ℝ) * reducedSource1460 x := by
  norm_num [numericRow1460, reducedSource1460, Integer.Sparse.eval, Sparse.eval, nodeValue1018, nodeValue2086, nodeValue2191, nodeValue2232, nodeValue2241, nodeValue4079]

noncomputable def reducedSource1461 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1017 x + ((2 : ℝ) * Sparse.eval nodeValue2085 x + ((1 : ℝ) * Sparse.eval nodeValue2190 x + ((1 : ℝ) * Sparse.eval nodeValue2240 x + ((1 : ℝ) * Sparse.eval nodeValue2242 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

def numericRow1461 : Integer.Sparse Master := [(Sum.inr 1017, 1), (Sum.inr 2085, 2), (Sum.inr 2190, 1), (Sum.inr 2240, 1), (Sum.inr 2242, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1461 : Integer.Sparse.reindex keyMap MixedData.row1461 = numericRow1461 := by decide +kernel

theorem numericCheck1461 (x : Master → ℝ) : Integer.Sparse.eval numericRow1461 x =
    (1 : ℝ) * reducedSource1461 x := by
  norm_num [numericRow1461, reducedSource1461, Integer.Sparse.eval, Sparse.eval, nodeValue1017, nodeValue2085, nodeValue2190, nodeValue2240, nodeValue2242, nodeValue4080]

noncomputable def reducedSource1462 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1045 x + ((1 : ℝ) * Sparse.eval nodeValue2024 x + ((1 : ℝ) * Sparse.eval nodeValue2111 x + ((1 : ℝ) * Sparse.eval nodeValue2246 x + ((1 : ℝ) * Sparse.eval nodeValue2254 x + ((1 : ℝ) * Sparse.eval nodeValue2260 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

def numericRow1462 : Integer.Sparse Master := [(Sum.inr 1045, 1), (Sum.inr 2024, 1), (Sum.inr 2111, 1), (Sum.inr 2246, 1), (Sum.inr 2254, 1), (Sum.inr 2260, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1462 : Integer.Sparse.reindex keyMap MixedData.row1462 = numericRow1462 := by decide +kernel

theorem numericCheck1462 (x : Master → ℝ) : Integer.Sparse.eval numericRow1462 x =
    (1 : ℝ) * reducedSource1462 x := by
  norm_num [numericRow1462, reducedSource1462, Integer.Sparse.eval, Sparse.eval, nodeValue1045, nodeValue2024, nodeValue2111, nodeValue2246, nodeValue2254, nodeValue2260, nodeValue4080]

noncomputable def reducedSource1463 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1032 x + ((1 : ℝ) * Sparse.eval nodeValue1035 x + ((1 : ℝ) * Sparse.eval nodeValue1036 x + ((1 : ℝ) * Sparse.eval nodeValue1045 x + ((1 : ℝ) * Sparse.eval nodeValue1073 x + ((1 : ℝ) * Sparse.eval nodeValue2260 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

def numericRow1463 : Integer.Sparse Master := [(Sum.inr 1032, 1), (Sum.inr 1035, 1), (Sum.inr 1036, 1), (Sum.inr 1045, 1), (Sum.inr 1073, 1), (Sum.inr 2260, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1463 : Integer.Sparse.reindex keyMap MixedData.row1463 = numericRow1463 := by decide +kernel

theorem numericCheck1463 (x : Master → ℝ) : Integer.Sparse.eval numericRow1463 x =
    (1 : ℝ) * reducedSource1463 x := by
  norm_num [numericRow1463, reducedSource1463, Integer.Sparse.eval, Sparse.eval, nodeValue1032, nodeValue1035, nodeValue1036, nodeValue1045, nodeValue1073, nodeValue2260, nodeValue4080]

noncomputable def reducedSource1464 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1036 x + ((1 : ℝ) * Sparse.eval nodeValue2017 x + ((1 : ℝ) * Sparse.eval nodeValue2102 x + ((1 : ℝ) * Sparse.eval nodeValue2206 x + ((1 : ℝ) * Sparse.eval nodeValue2251 x + ((1 : ℝ) * Sparse.eval nodeValue2260 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

def numericRow1464 : Integer.Sparse Master := [(Sum.inr 1036, 1), (Sum.inr 2017, 1), (Sum.inr 2102, 1), (Sum.inr 2206, 1), (Sum.inr 2251, 1), (Sum.inr 2260, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1464 : Integer.Sparse.reindex keyMap MixedData.row1464 = numericRow1464 := by decide +kernel

theorem numericCheck1464 (x : Master → ℝ) : Integer.Sparse.eval numericRow1464 x =
    (1 : ℝ) * reducedSource1464 x := by
  norm_num [numericRow1464, reducedSource1464, Integer.Sparse.eval, Sparse.eval, nodeValue1036, nodeValue2017, nodeValue2102, nodeValue2206, nodeValue2251, nodeValue2260, nodeValue4080]

noncomputable def reducedSource1465 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4152 x + ((1 : ℝ) * Sparse.eval nodeValue4157 x + ((2 : ℝ) * Sparse.eval nodeValue4158 x + ((1 : ℝ) * Sparse.eval nodeValue4182 x + ((1 : ℝ) * Sparse.eval nodeValue4331 x + ((2 : ℝ) * Sparse.eval nodeValue4332 x + ((1 : ℝ) * Sparse.eval nodeValue4351 x + ((1 : ℝ) * Sparse.eval nodeValue4366 x + ((1 : ℝ) * Sparse.eval nodeValue4371 x + ((2 : ℝ) * Sparse.eval nodeValue4372 x + ((2 : ℝ) * Sparse.eval nodeValue4439 x + ((2 : ℝ) * Sparse.eval nodeValue4442 x + ((2 : ℝ) * Sparse.eval nodeValue4444 x + ((1 : ℝ) * Sparse.eval nodeValue4456 x + ((2 : ℝ) * Sparse.eval nodeValue4458 x + ((2 : ℝ) * Sparse.eval nodeValue4461 x + ((1 : ℝ) * Sparse.eval nodeValue4497 x + ((1 : ℝ) * Sparse.eval nodeValue4805 x + ((1 : ℝ) * Sparse.eval nodeValue4869 x + ((2 : ℝ) * Sparse.eval nodeValue4889 x + ((1 : ℝ) * Sparse.eval nodeValue4893 x + 0))))))))))))))))))))

def numericRow1465 : Integer.Sparse Master := [(Sum.inr 610, -1), (Sum.inr 929, -1), (Sum.inr 1039, -1), (Sum.inr 1041, -2), (Sum.inr 1044, -2), (Sum.inr 1524, -1), (Sum.inr 1680, -1), (Sum.inr 1706, -1), (Sum.inr 1724, -2), (Sum.inr 1737, -2), (Sum.inr 2023, -1), (Sum.inr 2110, -1), (Sum.inr 2214, -1), (Sum.inr 2245, -2), (Sum.inr 2275, -1), (Sum.inr 2277, -2), (Sum.inr 4152, 4), (Sum.inr 4157, 4), (Sum.inr 4158, 8), (Sum.inr 4331, 4), (Sum.inr 4332, 8), (Sum.inr 4366, 4), (Sum.inr 4371, 4), (Sum.inr 4372, 8), (Sum.inr 4439, 8), (Sum.inr 4442, 8), (Sum.inr 4444, 8)]

theorem reindexCheck1465 : Integer.Sparse.reindex keyMap MixedData.row1465 = numericRow1465 := by decide +kernel

theorem numericCheck1465 (x : Master → ℝ) : Integer.Sparse.eval numericRow1465 x =
    (4 : ℝ) * reducedSource1465 x := by
  norm_num [numericRow1465, reducedSource1465, Integer.Sparse.eval, Sparse.eval, nodeValue4152, nodeValue4157, nodeValue4158, nodeValue4182, nodeValue4331, nodeValue4332, nodeValue4351, nodeValue4366, nodeValue4371, nodeValue4372, nodeValue4439, nodeValue4442, nodeValue4444, nodeValue4456, nodeValue4458, nodeValue4461, nodeValue4497, nodeValue4805, nodeValue4869, nodeValue4889, nodeValue4893]; ring

noncomputable def reducedSource1466 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1510 x + ((2 : ℝ) * Sparse.eval nodeValue1522 x + ((1 : ℝ) * Sparse.eval nodeValue1524 x + ((1 : ℝ) * Sparse.eval nodeValue1528 x + ((2 : ℝ) * Sparse.eval nodeValue1678 x + ((1 : ℝ) * Sparse.eval nodeValue1680 x + ((1 : ℝ) * Sparse.eval nodeValue1684 x + ((1 : ℝ) * Sparse.eval nodeValue1706 x + ((1 : ℝ) * Sparse.eval nodeValue1711 x + ((2 : ℝ) * Sparse.eval nodeValue1713 x + ((2 : ℝ) * Sparse.eval nodeValue1724 x + ((1 : ℝ) * Sparse.eval nodeValue1726 x + ((2 : ℝ) * Sparse.eval nodeValue1734 x + ((2 : ℝ) * Sparse.eval nodeValue1736 x + ((2 : ℝ) * Sparse.eval nodeValue1737 x + ((1 : ℝ) * Sparse.eval nodeValue1742 x + ((2 : ℝ) * Sparse.eval nodeValue1744 x + ((1 : ℝ) * Sparse.eval nodeValue2214 x + ((1 : ℝ) * Sparse.eval nodeValue2263 x + ((1 : ℝ) * Sparse.eval nodeValue2275 x + ((2 : ℝ) * Sparse.eval nodeValue2277 x + 0))))))))))))))))))))

def numericRow1466 : Integer.Sparse Master := [(Sum.inr 1510, 1), (Sum.inr 1522, 2), (Sum.inr 1524, 1), (Sum.inr 1528, 1), (Sum.inr 1678, 2), (Sum.inr 1680, 1), (Sum.inr 1684, 1), (Sum.inr 1706, 1), (Sum.inr 1711, 1), (Sum.inr 1713, 2), (Sum.inr 1724, 2), (Sum.inr 1734, 2), (Sum.inr 1736, 2), (Sum.inr 1737, 2), (Sum.inr 1742, 1), (Sum.inr 1744, 2), (Sum.inr 2214, 1), (Sum.inr 2275, 1), (Sum.inr 2277, 2)]

theorem reindexCheck1466 : Integer.Sparse.reindex keyMap MixedData.row1466 = numericRow1466 := by decide +kernel

theorem numericCheck1466 (x : Master → ℝ) : Integer.Sparse.eval numericRow1466 x =
    (1 : ℝ) * reducedSource1466 x := by
  norm_num [numericRow1466, reducedSource1466, Integer.Sparse.eval, Sparse.eval, nodeValue1510, nodeValue1522, nodeValue1524, nodeValue1528, nodeValue1678, nodeValue1680, nodeValue1684, nodeValue1706, nodeValue1711, nodeValue1713, nodeValue1724, nodeValue1726, nodeValue1734, nodeValue1736, nodeValue1737, nodeValue1742, nodeValue1744, nodeValue2214, nodeValue2263, nodeValue2275, nodeValue2277]

noncomputable def reducedSource1467 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue610 x + ((1 : ℝ) * Sparse.eval nodeValue929 x + ((3 : ℝ) * Sparse.eval nodeValue1044 x + ((1 : ℝ) * Sparse.eval nodeValue1081 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

def numericRow1467 : Integer.Sparse Master := [(Sum.inr 610, 1), (Sum.inr 929, 1), (Sum.inr 1044, 3), (Sum.inr 4083, -1)]

theorem reindexCheck1467 : Integer.Sparse.reindex keyMap MixedData.row1467 = numericRow1467 := by decide +kernel

theorem numericCheck1467 (x : Master → ℝ) : Integer.Sparse.eval numericRow1467 x =
    (1 : ℝ) * reducedSource1467 x := by
  norm_num [numericRow1467, reducedSource1467, Integer.Sparse.eval, Sparse.eval, nodeValue610, nodeValue929, nodeValue1044, nodeValue1081, nodeValue4083]

noncomputable def reducedSource1468 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue944 x + ((1 : ℝ) * Sparse.eval nodeValue949 x + ((2 : ℝ) * Sparse.eval nodeValue950 x + ((1 : ℝ) * Sparse.eval nodeValue1044 x + ((1 : ℝ) * Sparse.eval nodeValue2110 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow1468 : Integer.Sparse Master := [(Sum.inr 944, 1), (Sum.inr 949, 1), (Sum.inr 950, 2), (Sum.inr 1044, 1), (Sum.inr 2110, 1), (Sum.inr 4083, -1)]

theorem reindexCheck1468 : Integer.Sparse.reindex keyMap MixedData.row1468 = numericRow1468 := by decide +kernel

theorem numericCheck1468 (x : Master → ℝ) : Integer.Sparse.eval numericRow1468 x =
    (1 : ℝ) * reducedSource1468 x := by
  norm_num [numericRow1468, reducedSource1468, Integer.Sparse.eval, Sparse.eval, nodeValue944, nodeValue949, nodeValue950, nodeValue1044, nodeValue2110, nodeValue4083]

noncomputable def reducedSource1469 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4104 x + ((1 : ℝ) * Sparse.eval nodeValue4105 x + ((2 : ℝ) * Sparse.eval nodeValue4106 x + ((1 : ℝ) * Sparse.eval nodeValue4126 x + ((1 : ℝ) * Sparse.eval nodeValue4290 x + ((2 : ℝ) * Sparse.eval nodeValue4291 x + ((1 : ℝ) * Sparse.eval nodeValue4307 x + ((1 : ℝ) * Sparse.eval nodeValue4351 x + ((1 : ℝ) * Sparse.eval nodeValue4352 x + ((2 : ℝ) * Sparse.eval nodeValue4354 x + ((1 : ℝ) * Sparse.eval nodeValue4451 x + ((2 : ℝ) * Sparse.eval nodeValue4452 x + ((2 : ℝ) * Sparse.eval nodeValue4461 x + ((2 : ℝ) * Sparse.eval nodeValue4463 x + ((2 : ℝ) * Sparse.eval nodeValue4466 x + ((1 : ℝ) * Sparse.eval nodeValue4489 x + ((2 : ℝ) * Sparse.eval nodeValue4503 x + ((1 : ℝ) * Sparse.eval nodeValue5076 x + ((1 : ℝ) * Sparse.eval nodeValue5172 x + ((1 : ℝ) * Sparse.eval nodeValue5290 x + ((2 : ℝ) * Sparse.eval nodeValue5294 x + 0))))))))))))))))))))

def numericRow1469 : Integer.Sparse Master := [(Sum.inl 0, 113), (Sum.inl 6, -5), (Sum.inl 2, -50), (Sum.inl 7, 80), (Sum.inl 3, -160), (Sum.inl 1, -230), (Sum.inr 541, -4320), (Sum.inr 542, -4320), (Sum.inr 543, -8640), (Sum.inr 557, -4320), (Sum.inr 674, -4320), (Sum.inr 675, -8640), (Sum.inr 677, -4320), (Sum.inr 681, -4320), (Sum.inr 868, -4320), (Sum.inr 869, -8640), (Sum.inr 885, -4320), (Sum.inr 929, -4320), (Sum.inr 930, -4320), (Sum.inr 932, -8640), (Sum.inr 1034, -4320), (Sum.inr 1035, -8640), (Sum.inr 1044, -8640), (Sum.inr 1046, -8640), (Sum.inr 1049, -8640), (Sum.inr 1073, -4320), (Sum.inr 1087, -8640), (Sum.inr 1561, -8640), (Sum.inr 1563, -4320), (Sum.inr 1566, -4320), (Sum.inr 1644, -4320), (Sum.inr 1645, -8640), (Sum.inr 1648, -4320), (Sum.inr 1680, -4320), (Sum.inr 1681, -8640), (Sum.inr 1690, -4320), (Sum.inr 1737, -8640), (Sum.inr 1738, -8640), (Sum.inr 1739, -8640), (Sum.inr 1750, -8640), (Sum.inr 2483, -4320), (Sum.inr 2764, -4320), (Sum.inr 3477, -4320), (Sum.inr 3581, -4320), (Sum.inr 3613, -4320), (Sum.inr 3632, -8640)]

theorem reindexCheck1469 : Integer.Sparse.reindex keyMap MixedData.row1469 = numericRow1469 := by decide +kernel

theorem numericCheck1469 (x : Master → ℝ) : Integer.Sparse.eval numericRow1469 x =
    (17280 : ℝ) * reducedSource1469 x := by
  norm_num [numericRow1469, reducedSource1469, Integer.Sparse.eval, Sparse.eval, nodeValue4104, nodeValue4105, nodeValue4106, nodeValue4126, nodeValue4290, nodeValue4291, nodeValue4307, nodeValue4351, nodeValue4352, nodeValue4354, nodeValue4451, nodeValue4452, nodeValue4461, nodeValue4463, nodeValue4466, nodeValue4489, nodeValue4503, nodeValue5076, nodeValue5172, nodeValue5290, nodeValue5294]; ring

noncomputable def reducedSource1470 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue786 x + ((1 : ℝ) * Sparse.eval nodeValue810 x + ((2 : ℝ) * Sparse.eval nodeValue811 x + ((1 : ℝ) * Sparse.eval nodeValue827 x + ((1 : ℝ) * Sparse.eval nodeValue980 x + ((2 : ℝ) * Sparse.eval nodeValue981 x + ((1 : ℝ) * Sparse.eval nodeValue990 x + ((2 : ℝ) * Sparse.eval nodeValue1021 x + ((1 : ℝ) * Sparse.eval nodeValue1023 x + ((2 : ℝ) * Sparse.eval nodeValue1041 x + ((2 : ℝ) * Sparse.eval nodeValue1042 x + ((1 : ℝ) * Sparse.eval nodeValue1044 x + ((2 : ℝ) * Sparse.eval nodeValue1045 x + ((2 : ℝ) * Sparse.eval nodeValue1058 x + ((1 : ℝ) * Sparse.eval nodeValue1060 x + ((1 : ℝ) * Sparse.eval nodeValue1086 x + ((2 : ℝ) * Sparse.eval nodeValue1087 x + ((1 : ℝ) * Sparse.eval nodeValue1216 x + ((2 : ℝ) * Sparse.eval nodeValue1267 x + ((1 : ℝ) * Sparse.eval nodeValue1270 x + ((1 : ℝ) * Sparse.eval nodeValue1305 x + 0))))))))))))))))))))

def numericRow1470 : Integer.Sparse Master := [(Sum.inl 0, -84), (Sum.inl 5, 200), (Sum.inl 6, -40), (Sum.inl 2, -90), (Sum.inl 7, -160), (Sum.inl 35, -160), (Sum.inl 8, -160), (Sum.inl 3, -160), (Sum.inl 1, -30), (Sum.inr 786, 4320), (Sum.inr 811, 8640), (Sum.inr 827, 4320), (Sum.inr 980, 4320), (Sum.inr 981, 8640), (Sum.inr 990, 4320), (Sum.inr 1021, 8640), (Sum.inr 1023, 4320), (Sum.inr 1041, 8640), (Sum.inr 1042, 8640), (Sum.inr 1044, 4320), (Sum.inr 1045, 8640), (Sum.inr 1058, 8640), (Sum.inr 1060, 4320), (Sum.inr 1087, 8640), (Sum.inr 1216, 4320), (Sum.inr 1270, 4320)]

theorem reindexCheck1470 : Integer.Sparse.reindex keyMap MixedData.row1470 = numericRow1470 := by decide +kernel

theorem numericCheck1470 (x : Master → ℝ) : Integer.Sparse.eval numericRow1470 x =
    (4320 : ℝ) * reducedSource1470 x := by
  norm_num [numericRow1470, reducedSource1470, Integer.Sparse.eval, Sparse.eval, nodeValue786, nodeValue810, nodeValue811, nodeValue827, nodeValue980, nodeValue981, nodeValue990, nodeValue1021, nodeValue1023, nodeValue1041, nodeValue1042, nodeValue1044, nodeValue1045, nodeValue1058, nodeValue1060, nodeValue1086, nodeValue1087, nodeValue1216, nodeValue1267, nodeValue1270, nodeValue1305]; ring

noncomputable def reducedSource1471 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4150 x + ((1 : ℝ) * Sparse.eval nodeValue4153 x + ((1 : ℝ) * Sparse.eval nodeValue4155 x + ((1 : ℝ) * Sparse.eval nodeValue4158 x + ((1 : ℝ) * Sparse.eval nodeValue4175 x + ((1 : ℝ) * Sparse.eval nodeValue4327 x + ((1 : ℝ) * Sparse.eval nodeValue4329 x + ((1 : ℝ) * Sparse.eval nodeValue4332 x + ((1 : ℝ) * Sparse.eval nodeValue4344 x + ((1 : ℝ) * Sparse.eval nodeValue4364 x + ((1 : ℝ) * Sparse.eval nodeValue4367 x + ((1 : ℝ) * Sparse.eval nodeValue4369 x + ((1 : ℝ) * Sparse.eval nodeValue4372 x + ((1 : ℝ) * Sparse.eval nodeValue4438 x + ((1 : ℝ) * Sparse.eval nodeValue4440 x + ((1 : ℝ) * Sparse.eval nodeValue4444 x + ((1 : ℝ) * Sparse.eval nodeValue4456 x + ((3 : ℝ) * Sparse.eval nodeValue4458 x + ((1 : ℝ) * Sparse.eval nodeValue4461 x + ((1 : ℝ) * Sparse.eval nodeValue4463 x + ((1 : ℝ) * Sparse.eval nodeValue4467 x + ((1 : ℝ) * Sparse.eval nodeValue4497 x + ((1 : ℝ) * Sparse.eval nodeValue4502 x + ((1 : ℝ) * Sparse.eval nodeValue4802 x + ((1 : ℝ) * Sparse.eval nodeValue4866 x + ((1 : ℝ) * Sparse.eval nodeValue4888 x + ((1 : ℝ) * Sparse.eval nodeValue4893 x + ((1 : ℝ) * Sparse.eval nodeValue4895 x + 0)))))))))))))))))))))))))))

def numericRow1471 : Integer.Sparse Master := [(Sum.inr 603, -1), (Sum.inr 922, -1), (Sum.inr 1039, -1), (Sum.inr 1041, -3), (Sum.inr 1044, -1), (Sum.inr 1046, -1), (Sum.inr 1050, -1), (Sum.inr 1517, -1), (Sum.inr 1673, -1), (Sum.inr 1706, -1), (Sum.inr 1724, -3), (Sum.inr 1737, -1), (Sum.inr 1750, -1), (Sum.inr 1751, -1), (Sum.inr 2020, -1), (Sum.inr 2107, -1), (Sum.inr 2202, -1), (Sum.inr 2244, -1), (Sum.inr 2260, -1), (Sum.inr 2262, -1), (Sum.inr 4150, 4), (Sum.inr 4153, 4), (Sum.inr 4155, 4), (Sum.inr 4158, 4), (Sum.inr 4327, 4), (Sum.inr 4332, 4), (Sum.inr 4364, 4), (Sum.inr 4367, 4), (Sum.inr 4369, 4), (Sum.inr 4372, 4), (Sum.inr 4440, 4), (Sum.inr 4444, 4)]

theorem reindexCheck1471 : Integer.Sparse.reindex keyMap MixedData.row1471 = numericRow1471 := by decide +kernel

theorem numericCheck1471 (x : Master → ℝ) : Integer.Sparse.eval numericRow1471 x =
    (4 : ℝ) * reducedSource1471 x := by
  norm_num [numericRow1471, reducedSource1471, Integer.Sparse.eval, Sparse.eval, nodeValue4150, nodeValue4153, nodeValue4155, nodeValue4158, nodeValue4175, nodeValue4327, nodeValue4329, nodeValue4332, nodeValue4344, nodeValue4364, nodeValue4367, nodeValue4369, nodeValue4372, nodeValue4438, nodeValue4440, nodeValue4444, nodeValue4456, nodeValue4458, nodeValue4461, nodeValue4463, nodeValue4467, nodeValue4497, nodeValue4502, nodeValue4802, nodeValue4866, nodeValue4888, nodeValue4893, nodeValue4895]; ring

end MUB6.Certificate.MixedSourceBridge

end OAI
