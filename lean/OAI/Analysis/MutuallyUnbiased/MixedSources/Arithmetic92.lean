import OAI.Analysis.MutuallyUnbiased.MixedData.Source11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
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

noncomputable def reducedSource1472 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue625 x + ((1 : ℝ) * Sparse.eval nodeValue626 x + ((1 : ℝ) * Sparse.eval nodeValue627 x + ((1 : ℝ) * Sparse.eval nodeValue632 x + ((1 : ℝ) * Sparse.eval nodeValue644 x + ((1 : ℝ) * Sparse.eval nodeValue1316 x + ((1 : ℝ) * Sparse.eval nodeValue1317 x + ((1 : ℝ) * Sparse.eval nodeValue1318 x + ((1 : ℝ) * Sparse.eval nodeValue1322 x + ((1 : ℝ) * Sparse.eval nodeValue1327 x + ((1 : ℝ) * Sparse.eval nodeValue1328 x + ((1 : ℝ) * Sparse.eval nodeValue1331 x + ((1 : ℝ) * Sparse.eval nodeValue1339 x + ((1 : ℝ) * Sparse.eval nodeValue1386 x + ((1 : ℝ) * Sparse.eval nodeValue1388 x + ((1 : ℝ) * Sparse.eval nodeValue1391 x + ((1 : ℝ) * Sparse.eval nodeValue1409 x + ((1 : ℝ) * Sparse.eval nodeValue1410 x + ((3 : ℝ) * Sparse.eval nodeValue1411 x + ((1 : ℝ) * Sparse.eval nodeValue1413 x + ((1 : ℝ) * Sparse.eval nodeValue1420 x + ((1 : ℝ) * Sparse.eval nodeValue1446 x + ((1 : ℝ) * Sparse.eval nodeValue1447 x + ((1 : ℝ) * Sparse.eval nodeValue3184 x + ((1 : ℝ) * Sparse.eval nodeValue3204 x + ((1 : ℝ) * Sparse.eval nodeValue3227 x + ((1 : ℝ) * Sparse.eval nodeValue3228 x + ((1 : ℝ) * Sparse.eval nodeValue3229 x + 0)))))))))))))))))))))))))))

def numericRow1472 : Integer.Sparse Master := [(Sum.inl 0, -392), (Sum.inl 5, -480), (Sum.inl 6, 80), (Sum.inl 2, -160), (Sum.inl 8, 320), (Sum.inl 52, 320), (Sum.inl 1, -360), (Sum.inr 625, 4320), (Sum.inr 626, 4320), (Sum.inr 627, 4320), (Sum.inr 632, 4320), (Sum.inr 1316, 4320), (Sum.inr 1317, 4320), (Sum.inr 1318, 4320), (Sum.inr 1322, 4320), (Sum.inr 1327, 4320), (Sum.inr 1328, 4320), (Sum.inr 1388, 4320), (Sum.inr 1391, 4320)]

theorem reindexCheck1472 : Integer.Sparse.reindex keyMap MixedData.row1472 = numericRow1472 := by decide +kernel

theorem numericCheck1472 (x : Master → ℝ) : Integer.Sparse.eval numericRow1472 x =
    (4320 : ℝ) * reducedSource1472 x := by
  norm_num [numericRow1472, reducedSource1472, Integer.Sparse.eval, Sparse.eval, nodeValue625, nodeValue626, nodeValue627, nodeValue632, nodeValue644, nodeValue1316, nodeValue1317, nodeValue1318, nodeValue1322, nodeValue1327, nodeValue1328, nodeValue1331, nodeValue1339, nodeValue1386, nodeValue1388, nodeValue1391, nodeValue1409, nodeValue1410, nodeValue1411, nodeValue1413, nodeValue1420, nodeValue1446, nodeValue1447, nodeValue3184, nodeValue3204, nodeValue3227, nodeValue3228, nodeValue3229]
  ring

noncomputable def reducedSource1473 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1504 x + ((1 : ℝ) * Sparse.eval nodeValue1514 x + ((1 : ℝ) * Sparse.eval nodeValue1515 x + ((1 : ℝ) * Sparse.eval nodeValue1517 x + ((1 : ℝ) * Sparse.eval nodeValue1522 x + ((1 : ℝ) * Sparse.eval nodeValue1670 x + ((1 : ℝ) * Sparse.eval nodeValue1671 x + ((1 : ℝ) * Sparse.eval nodeValue1673 x + ((1 : ℝ) * Sparse.eval nodeValue1678 x + ((1 : ℝ) * Sparse.eval nodeValue1703 x + ((1 : ℝ) * Sparse.eval nodeValue1705 x + ((1 : ℝ) * Sparse.eval nodeValue1706 x + ((1 : ℝ) * Sparse.eval nodeValue1720 x + ((1 : ℝ) * Sparse.eval nodeValue1721 x + ((1 : ℝ) * Sparse.eval nodeValue1723 x + ((3 : ℝ) * Sparse.eval nodeValue1724 x + ((1 : ℝ) * Sparse.eval nodeValue1726 x + ((1 : ℝ) * Sparse.eval nodeValue1734 x + ((1 : ℝ) * Sparse.eval nodeValue1736 x + ((1 : ℝ) * Sparse.eval nodeValue1737 x + ((1 : ℝ) * Sparse.eval nodeValue1750 x + ((1 : ℝ) * Sparse.eval nodeValue1751 x + ((1 : ℝ) * Sparse.eval nodeValue1753 x + ((1 : ℝ) * Sparse.eval nodeValue2202 x + ((1 : ℝ) * Sparse.eval nodeValue2260 x + ((1 : ℝ) * Sparse.eval nodeValue2262 x + ((1 : ℝ) * Sparse.eval nodeValue2263 x + ((1 : ℝ) * Sparse.eval nodeValue2291 x + 0)))))))))))))))))))))))))))

def numericRow1473 : Integer.Sparse Master := [(Sum.inr 1504, 1), (Sum.inr 1514, 1), (Sum.inr 1515, 1), (Sum.inr 1517, 1), (Sum.inr 1522, 1), (Sum.inr 1670, 1), (Sum.inr 1673, 1), (Sum.inr 1678, 1), (Sum.inr 1703, 1), (Sum.inr 1706, 1), (Sum.inr 1720, 1), (Sum.inr 1721, 1), (Sum.inr 1723, 1), (Sum.inr 1724, 3), (Sum.inr 1734, 1), (Sum.inr 1736, 1), (Sum.inr 1737, 1), (Sum.inr 1750, 1), (Sum.inr 1751, 1), (Sum.inr 2202, 1), (Sum.inr 2260, 1), (Sum.inr 2262, 1)]

theorem reindexCheck1473 : Integer.Sparse.reindex keyMap MixedData.row1473 = numericRow1473 := by decide +kernel

theorem numericCheck1473 (x : Master → ℝ) : Integer.Sparse.eval numericRow1473 x =
    (1 : ℝ) * reducedSource1473 x := by
  norm_num [numericRow1473, reducedSource1473, Integer.Sparse.eval, Sparse.eval, nodeValue1504, nodeValue1514, nodeValue1515, nodeValue1517, nodeValue1522, nodeValue1670, nodeValue1671, nodeValue1673, nodeValue1678, nodeValue1703, nodeValue1705, nodeValue1706, nodeValue1720, nodeValue1721, nodeValue1723, nodeValue1724, nodeValue1726, nodeValue1734, nodeValue1736, nodeValue1737, nodeValue1750, nodeValue1751, nodeValue1753, nodeValue2202, nodeValue2260, nodeValue2262, nodeValue2263, nodeValue2291]

noncomputable def reducedSource1474 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue578 x + ((1 : ℝ) * Sparse.eval nodeValue581 x + ((1 : ℝ) * Sparse.eval nodeValue583 x + ((1 : ℝ) * Sparse.eval nodeValue586 x + ((1 : ℝ) * Sparse.eval nodeValue603 x + ((1 : ℝ) * Sparse.eval nodeValue1041 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

def numericRow1474 : Integer.Sparse Master := [(Sum.inr 578, 1), (Sum.inr 581, 1), (Sum.inr 583, 1), (Sum.inr 586, 1), (Sum.inr 603, 1), (Sum.inr 1041, 1), (Sum.inr 4083, -1)]

theorem reindexCheck1474 : Integer.Sparse.reindex keyMap MixedData.row1474 = numericRow1474 := by decide +kernel

theorem numericCheck1474 (x : Master → ℝ) : Integer.Sparse.eval numericRow1474 x =
    (1 : ℝ) * reducedSource1474 x := by
  norm_num [numericRow1474, reducedSource1474, Integer.Sparse.eval, Sparse.eval, nodeValue578, nodeValue581, nodeValue583, nodeValue586, nodeValue603, nodeValue1041, nodeValue4083]

noncomputable def reducedSource1475 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue603 x + ((1 : ℝ) * Sparse.eval nodeValue922 x + ((2 : ℝ) * Sparse.eval nodeValue1041 x + ((1 : ℝ) * Sparse.eval nodeValue1081 x + ((1 : ℝ) * Sparse.eval nodeValue1086 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow1475 : Integer.Sparse Master := [(Sum.inr 603, 1), (Sum.inr 922, 1), (Sum.inr 1041, 2), (Sum.inr 4083, -1)]

theorem reindexCheck1475 : Integer.Sparse.reindex keyMap MixedData.row1475 = numericRow1475 := by decide +kernel

theorem numericCheck1475 (x : Master → ℝ) : Integer.Sparse.eval numericRow1475 x =
    (1 : ℝ) * reducedSource1475 x := by
  norm_num [numericRow1475, reducedSource1475, Integer.Sparse.eval, Sparse.eval, nodeValue603, nodeValue922, nodeValue1041, nodeValue1081, nodeValue1086, nodeValue4083]

noncomputable def reducedSource1476 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue942 x + ((1 : ℝ) * Sparse.eval nodeValue945 x + ((1 : ℝ) * Sparse.eval nodeValue947 x + ((1 : ℝ) * Sparse.eval nodeValue950 x + ((1 : ℝ) * Sparse.eval nodeValue1041 x + ((1 : ℝ) * Sparse.eval nodeValue2107 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

def numericRow1476 : Integer.Sparse Master := [(Sum.inr 942, 1), (Sum.inr 945, 1), (Sum.inr 947, 1), (Sum.inr 950, 1), (Sum.inr 1041, 1), (Sum.inr 2107, 1), (Sum.inr 4083, -1)]

theorem reindexCheck1476 : Integer.Sparse.reindex keyMap MixedData.row1476 = numericRow1476 := by decide +kernel

theorem numericCheck1476 (x : Master → ℝ) : Integer.Sparse.eval numericRow1476 x =
    (1 : ℝ) * reducedSource1476 x := by
  norm_num [numericRow1476, reducedSource1476, Integer.Sparse.eval, Sparse.eval, nodeValue942, nodeValue945, nodeValue947, nodeValue950, nodeValue1041, nodeValue2107, nodeValue4083]

noncomputable def reducedSource1477 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4100 x + ((1 : ℝ) * Sparse.eval nodeValue4101 x + ((1 : ℝ) * Sparse.eval nodeValue4102 x + ((1 : ℝ) * Sparse.eval nodeValue4107 x + ((1 : ℝ) * Sparse.eval nodeValue4119 x + ((1 : ℝ) * Sparse.eval nodeValue4287 x + ((1 : ℝ) * Sparse.eval nodeValue4288 x + ((1 : ℝ) * Sparse.eval nodeValue4292 x + ((1 : ℝ) * Sparse.eval nodeValue4301 x + ((1 : ℝ) * Sparse.eval nodeValue4344 x + ((1 : ℝ) * Sparse.eval nodeValue4346 x + ((1 : ℝ) * Sparse.eval nodeValue4349 x + ((1 : ℝ) * Sparse.eval nodeValue4355 x + ((1 : ℝ) * Sparse.eval nodeValue4399 x + ((1 : ℝ) * Sparse.eval nodeValue4401 x + ((1 : ℝ) * Sparse.eval nodeValue4404 x + ((1 : ℝ) * Sparse.eval nodeValue4424 x + ((1 : ℝ) * Sparse.eval nodeValue4456 x + ((1 : ℝ) * Sparse.eval nodeValue4457 x + ((2 : ℝ) * Sparse.eval nodeValue4458 x + ((1 : ℝ) * Sparse.eval nodeValue4460 x + ((1 : ℝ) * Sparse.eval nodeValue4467 x + ((1 : ℝ) * Sparse.eval nodeValue4495 x + ((1 : ℝ) * Sparse.eval nodeValue4499 x + ((1 : ℝ) * Sparse.eval nodeValue5073 x + ((1 : ℝ) * Sparse.eval nodeValue5169 x + ((1 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + 0))))))))))))))))))))))))))))

def numericRow1477 : Integer.Sparse Master := [(Sum.inl 0, 142), (Sum.inl 6, -5), (Sum.inl 2, 25), (Sum.inl 8, 80), (Sum.inl 3, 80), (Sum.inl 1, -100), (Sum.inr 537, -4320), (Sum.inr 538, -4320), (Sum.inr 539, -4320), (Sum.inr 544, -4320), (Sum.inr 554, -4320), (Sum.inr 662, -4320), (Sum.inr 663, -4320), (Sum.inr 664, -4320), (Sum.inr 668, -4320), (Sum.inr 682, -4320), (Sum.inr 865, -4320), (Sum.inr 866, -4320), (Sum.inr 870, -4320), (Sum.inr 879, -4320), (Sum.inr 922, -4320), (Sum.inr 924, -4320), (Sum.inr 927, -4320), (Sum.inr 933, -4320), (Sum.inr 980, -4320), (Sum.inr 982, -4320), (Sum.inr 985, -4320), (Sum.inr 1005, -4320), (Sum.inr 1039, -4320), (Sum.inr 1040, -4320), (Sum.inr 1041, -8640), (Sum.inr 1043, -4320), (Sum.inr 1050, -4320), (Sum.inr 1079, -4320), (Sum.inr 1083, -4320), (Sum.inr 1553, -4320), (Sum.inr 1554, -4320), (Sum.inr 1556, -4320), (Sum.inr 1567, -4320), (Sum.inr 1616, -4320), (Sum.inr 1617, -4320), (Sum.inr 1618, -4320), (Sum.inr 1623, -4320), (Sum.inr 1673, -4320), (Sum.inr 1674, -4320), (Sum.inr 1675, -4320), (Sum.inr 1691, -4320), (Sum.inr 1706, -4320), (Sum.inr 1707, -4320), (Sum.inr 1708, -4320), (Sum.inr 1724, -8640), (Sum.inr 1725, -4320), (Sum.inr 1728, -4320), (Sum.inr 1751, -4320), (Sum.inr 2480, -4320), (Sum.inr 2723, -4320), (Sum.inr 3467, -4320), (Sum.inr 3544, -4320), (Sum.inr 3607, -4320), (Sum.inr 3622, -4320), (Sum.inr 3627, -4320)]

theorem reindexCheck1477 : Integer.Sparse.reindex keyMap MixedData.row1477 = numericRow1477 := by decide +kernel

theorem numericCheck1477 (x : Master → ℝ) : Integer.Sparse.eval numericRow1477 x =
    (17280 : ℝ) * reducedSource1477 x := by
  norm_num [numericRow1477, reducedSource1477, Integer.Sparse.eval, Sparse.eval, nodeValue4100, nodeValue4101, nodeValue4102, nodeValue4107, nodeValue4119, nodeValue4287, nodeValue4288, nodeValue4292, nodeValue4301, nodeValue4344, nodeValue4346, nodeValue4349, nodeValue4355, nodeValue4399, nodeValue4401, nodeValue4404, nodeValue4424, nodeValue4456, nodeValue4457, nodeValue4458, nodeValue4460, nodeValue4467, nodeValue4495, nodeValue4499, nodeValue5073, nodeValue5169, nodeValue5259, nodeValue5292, nodeValue5293]
  ring

noncomputable def reducedSource1478 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4249 x + ((1 : ℝ) * Sparse.eval nodeValue4264 x + ((1 : ℝ) * Sparse.eval nodeValue4265 x + ((1 : ℝ) * Sparse.eval nodeValue4267 x + ((1 : ℝ) * Sparse.eval nodeValue4268 x + ((1 : ℝ) * Sparse.eval nodeValue4396 x + ((1 : ℝ) * Sparse.eval nodeValue4397 x + ((1 : ℝ) * Sparse.eval nodeValue4399 x + ((1 : ℝ) * Sparse.eval nodeValue4407 x + ((1 : ℝ) * Sparse.eval nodeValue4436 x + ((1 : ℝ) * Sparse.eval nodeValue4438 x + ((1 : ℝ) * Sparse.eval nodeValue4439 x + ((1 : ℝ) * Sparse.eval nodeValue4452 x + ((1 : ℝ) * Sparse.eval nodeValue4453 x + ((1 : ℝ) * Sparse.eval nodeValue4457 x + ((2 : ℝ) * Sparse.eval nodeValue4458 x + ((1 : ℝ) * Sparse.eval nodeValue4459 x + ((1 : ℝ) * Sparse.eval nodeValue4461 x + ((1 : ℝ) * Sparse.eval nodeValue4471 x + ((1 : ℝ) * Sparse.eval nodeValue4474 x + ((1 : ℝ) * Sparse.eval nodeValue4475 x + ((1 : ℝ) * Sparse.eval nodeValue4498 x + ((1 : ℝ) * Sparse.eval nodeValue4499 x + ((1 : ℝ) * Sparse.eval nodeValue4502 x + ((1 : ℝ) * Sparse.eval nodeValue4590 x + ((1 : ℝ) * Sparse.eval nodeValue4602 x + ((1 : ℝ) * Sparse.eval nodeValue4603 x + ((1 : ℝ) * Sparse.eval nodeValue4606 x + ((1 : ℝ) * Sparse.eval nodeValue4624 x + 0))))))))))))))))))))))))))))

def numericRow1478 : Integer.Sparse Master := [(Sum.inl 0, 19), (Sum.inl 6, 5), (Sum.inl 8, -80), (Sum.inl 1, -40), (Sum.inr 783, -2160), (Sum.inr 803, -2160), (Sum.inr 807, -4320), (Sum.inr 811, -2160), (Sum.inr 824, -2160), (Sum.inr 977, -2160), (Sum.inr 980, -2160), (Sum.inr 1035, -2160), (Sum.inr 1040, -2160), (Sum.inr 1041, -4320), (Sum.inr 1044, -2160), (Sum.inr 1083, -2160), (Sum.inr 1236, -2160), (Sum.inr 1240, -2160), (Sum.inr 1597, -2160), (Sum.inr 1616, -2160), (Sum.inr 1645, -2160), (Sum.inr 1707, -2160), (Sum.inr 1724, -4320), (Sum.inr 1728, -2160), (Sum.inr 1737, -2160), (Sum.inr 3293, -2160), (Sum.inr 3299, -2160), (Sum.inr 3309, -2160), (Sum.inr 4407, 8640), (Sum.inr 4436, 8640), (Sum.inr 4439, 8640), (Sum.inr 4453, 8640), (Sum.inr 4459, 8640), (Sum.inr 4471, 8640), (Sum.inr 4474, 8640), (Sum.inr 4475, 8640), (Sum.inr 4590, 8640), (Sum.inr 4603, 8640)]

theorem reindexCheck1478 : Integer.Sparse.reindex keyMap MixedData.row1478 = numericRow1478 := by decide +kernel

theorem numericCheck1478 (x : Master → ℝ) : Integer.Sparse.eval numericRow1478 x =
    (8640 : ℝ) * reducedSource1478 x := by
  norm_num [numericRow1478, reducedSource1478, Integer.Sparse.eval, Sparse.eval, nodeValue4249, nodeValue4264, nodeValue4265, nodeValue4267, nodeValue4268, nodeValue4396, nodeValue4397, nodeValue4399, nodeValue4407, nodeValue4436, nodeValue4438, nodeValue4439, nodeValue4452, nodeValue4453, nodeValue4457, nodeValue4458, nodeValue4459, nodeValue4461, nodeValue4471, nodeValue4474, nodeValue4475, nodeValue4498, nodeValue4499, nodeValue4502, nodeValue4590, nodeValue4602, nodeValue4603, nodeValue4606, nodeValue4624]
  ring

noncomputable def reducedSource1479 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue783 x + ((1 : ℝ) * Sparse.eval nodeValue806 x + ((1 : ℝ) * Sparse.eval nodeValue807 x + ((1 : ℝ) * Sparse.eval nodeValue810 x + ((1 : ℝ) * Sparse.eval nodeValue824 x + ((1 : ℝ) * Sparse.eval nodeValue977 x + ((1 : ℝ) * Sparse.eval nodeValue978 x + ((1 : ℝ) * Sparse.eval nodeValue980 x + ((1 : ℝ) * Sparse.eval nodeValue988 x + ((1 : ℝ) * Sparse.eval nodeValue1018 x + ((1 : ℝ) * Sparse.eval nodeValue1020 x + ((1 : ℝ) * Sparse.eval nodeValue1021 x + ((1 : ℝ) * Sparse.eval nodeValue1035 x + ((1 : ℝ) * Sparse.eval nodeValue1036 x + ((1 : ℝ) * Sparse.eval nodeValue1040 x + ((2 : ℝ) * Sparse.eval nodeValue1041 x + ((1 : ℝ) * Sparse.eval nodeValue1042 x + ((1 : ℝ) * Sparse.eval nodeValue1044 x + ((1 : ℝ) * Sparse.eval nodeValue1054 x + ((1 : ℝ) * Sparse.eval nodeValue1057 x + ((1 : ℝ) * Sparse.eval nodeValue1058 x + ((1 : ℝ) * Sparse.eval nodeValue1082 x + ((1 : ℝ) * Sparse.eval nodeValue1083 x + ((1 : ℝ) * Sparse.eval nodeValue1086 x + ((1 : ℝ) * Sparse.eval nodeValue1213 x + ((1 : ℝ) * Sparse.eval nodeValue1262 x + ((1 : ℝ) * Sparse.eval nodeValue1266 x + ((1 : ℝ) * Sparse.eval nodeValue1267 x + ((1 : ℝ) * Sparse.eval nodeValue1301 x + 0))))))))))))))))))))))))))))

def numericRow1479 : Integer.Sparse Master := [(Sum.inl 0, -168), (Sum.inl 5, 440), (Sum.inl 6, -80), (Sum.inl 2, -210), (Sum.inl 7, -480), (Sum.inl 35, -160), (Sum.inl 8, -160), (Sum.inl 3, -160), (Sum.inl 1, 150), (Sum.inr 783, 8640), (Sum.inr 807, 8640), (Sum.inr 824, 8640), (Sum.inr 977, 8640), (Sum.inr 980, 8640), (Sum.inr 988, 8640), (Sum.inr 1018, 8640), (Sum.inr 1021, 8640), (Sum.inr 1035, 8640), (Sum.inr 1036, 8640), (Sum.inr 1040, 8640), (Sum.inr 1041, 17280), (Sum.inr 1042, 8640), (Sum.inr 1044, 8640), (Sum.inr 1054, 8640), (Sum.inr 1057, 8640), (Sum.inr 1058, 8640), (Sum.inr 1083, 8640), (Sum.inr 1213, 8640), (Sum.inr 1262, 8640)]

theorem reindexCheck1479 : Integer.Sparse.reindex keyMap MixedData.row1479 = numericRow1479 := by decide +kernel

theorem numericCheck1479 (x : Master → ℝ) : Integer.Sparse.eval numericRow1479 x =
    (8640 : ℝ) * reducedSource1479 x := by
  norm_num [numericRow1479, reducedSource1479, Integer.Sparse.eval, Sparse.eval, nodeValue783, nodeValue806, nodeValue807, nodeValue810, nodeValue824, nodeValue977, nodeValue978, nodeValue980, nodeValue988, nodeValue1018, nodeValue1020, nodeValue1021, nodeValue1035, nodeValue1036, nodeValue1040, nodeValue1041, nodeValue1042, nodeValue1044, nodeValue1054, nodeValue1057, nodeValue1058, nodeValue1082, nodeValue1083, nodeValue1086, nodeValue1213, nodeValue1262, nodeValue1266, nodeValue1267, nodeValue1301]
  ring

noncomputable def reducedSource1480 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1213 x + ((1 : ℝ) * Sparse.eval nodeValue1236 x + ((1 : ℝ) * Sparse.eval nodeValue1237 x + ((1 : ℝ) * Sparse.eval nodeValue1240 x + ((1 : ℝ) * Sparse.eval nodeValue1301 x + ((1 : ℝ) * Sparse.eval nodeValue1358 x + ((1 : ℝ) * Sparse.eval nodeValue1367 x + ((1 : ℝ) * Sparse.eval nodeValue1368 x + ((1 : ℝ) * Sparse.eval nodeValue1370 x + ((1 : ℝ) * Sparse.eval nodeValue1383 x + ((1 : ℝ) * Sparse.eval nodeValue1384 x + ((1 : ℝ) * Sparse.eval nodeValue1386 x + ((1 : ℝ) * Sparse.eval nodeValue1393 x + ((1 : ℝ) * Sparse.eval nodeValue1395 x + ((1 : ℝ) * Sparse.eval nodeValue1396 x + ((1 : ℝ) * Sparse.eval nodeValue1406 x + ((1 : ℝ) * Sparse.eval nodeValue1407 x + ((1 : ℝ) * Sparse.eval nodeValue1410 x + ((2 : ℝ) * Sparse.eval nodeValue1411 x + ((1 : ℝ) * Sparse.eval nodeValue1412 x + ((1 : ℝ) * Sparse.eval nodeValue1414 x + ((1 : ℝ) * Sparse.eval nodeValue1443 x + ((1 : ℝ) * Sparse.eval nodeValue1447 x + ((1 : ℝ) * Sparse.eval nodeValue1448 x + ((1 : ℝ) * Sparse.eval nodeValue1468 x + ((1 : ℝ) * Sparse.eval nodeValue1475 x + ((1 : ℝ) * Sparse.eval nodeValue1480 x + ((1 : ℝ) * Sparse.eval nodeValue1482 x + ((1 : ℝ) * Sparse.eval nodeValue1483 x + 0))))))))))))))))))))))))))))

def numericRow1480 : Integer.Sparse Master := [(Sum.inl 0, -440), (Sum.inl 5, 480), (Sum.inl 6, -160), (Sum.inl 2, -160), (Sum.inl 8, 320), (Sum.inl 52, 320), (Sum.inl 1, 120), (Sum.inr 1213, 4320), (Sum.inr 1236, 4320), (Sum.inr 1237, 4320), (Sum.inr 1240, 4320), (Sum.inr 1358, 4320), (Sum.inr 1367, 4320), (Sum.inr 1368, 4320), (Sum.inr 1370, 4320), (Sum.inr 1383, 4320), (Sum.inr 1384, 4320), (Sum.inr 1406, 4320), (Sum.inr 1407, 4320)]

theorem reindexCheck1480 : Integer.Sparse.reindex keyMap MixedData.row1480 = numericRow1480 := by decide +kernel

theorem numericCheck1480 (x : Master → ℝ) : Integer.Sparse.eval numericRow1480 x =
    (4320 : ℝ) * reducedSource1480 x := by
  norm_num [numericRow1480, reducedSource1480, Integer.Sparse.eval, Sparse.eval, nodeValue1213, nodeValue1236, nodeValue1237, nodeValue1240, nodeValue1301, nodeValue1358, nodeValue1367, nodeValue1368, nodeValue1370, nodeValue1383, nodeValue1384, nodeValue1386, nodeValue1393, nodeValue1395, nodeValue1396, nodeValue1406, nodeValue1407, nodeValue1410, nodeValue1411, nodeValue1412, nodeValue1414, nodeValue1443, nodeValue1447, nodeValue1448, nodeValue1468, nodeValue1475, nodeValue1480, nodeValue1482, nodeValue1483]
  ring

noncomputable def reducedSource1481 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1035 x + ((1 : ℝ) * Sparse.eval nodeValue2016 x + ((1 : ℝ) * Sparse.eval nodeValue2101 x + ((1 : ℝ) * Sparse.eval nodeValue2205 x + ((1 : ℝ) * Sparse.eval nodeValue2242 x + ((1 : ℝ) * Sparse.eval nodeValue2260 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

def numericRow1481 : Integer.Sparse Master := [(Sum.inr 1035, 1), (Sum.inr 2016, 1), (Sum.inr 2101, 1), (Sum.inr 2242, 1), (Sum.inr 2260, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1481 : Integer.Sparse.reindex keyMap MixedData.row1481 = numericRow1481 := by decide +kernel

theorem numericCheck1481 (x : Master → ℝ) : Integer.Sparse.eval numericRow1481 x =
    (1 : ℝ) * reducedSource1481 x := by
  norm_num [numericRow1481, reducedSource1481, Integer.Sparse.eval, Sparse.eval, nodeValue1035, nodeValue2016, nodeValue2101, nodeValue2205, nodeValue2242, nodeValue2260, nodeValue4080]

noncomputable def reducedSource1482 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue730 x + ((1 : ℝ) * Sparse.eval nodeValue733 x + ((1 : ℝ) * Sparse.eval nodeValue734 x + ((1 : ℝ) * Sparse.eval nodeValue738 x + ((1 : ℝ) * Sparse.eval nodeValue806 x + ((1 : ℝ) * Sparse.eval nodeValue1645 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

def numericRow1482 : Integer.Sparse Master := [(Sum.inr 730, 1), (Sum.inr 733, 1), (Sum.inr 734, 1), (Sum.inr 738, 1), (Sum.inr 1645, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1482 : Integer.Sparse.reindex keyMap MixedData.row1482 = numericRow1482 := by decide +kernel

theorem numericCheck1482 (x : Master → ℝ) : Integer.Sparse.eval numericRow1482 x =
    (1 : ℝ) * reducedSource1482 x := by
  norm_num [numericRow1482, reducedSource1482, Integer.Sparse.eval, Sparse.eval, nodeValue730, nodeValue733, nodeValue734, nodeValue738, nodeValue806, nodeValue1645, nodeValue4069]

noncomputable def reducedSource1483 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4149 x + ((1 : ℝ) * Sparse.eval nodeValue4151 x + ((2 : ℝ) * Sparse.eval nodeValue4154 x + ((1 : ℝ) * Sparse.eval nodeValue4172 x + ((1 : ℝ) * Sparse.eval nodeValue4326 x + ((2 : ℝ) * Sparse.eval nodeValue4328 x + ((1 : ℝ) * Sparse.eval nodeValue4341 x + ((1 : ℝ) * Sparse.eval nodeValue4363 x + ((1 : ℝ) * Sparse.eval nodeValue4365 x + ((2 : ℝ) * Sparse.eval nodeValue4368 x + ((1 : ℝ) * Sparse.eval nodeValue4455 x + ((2 : ℝ) * Sparse.eval nodeValue4457 x + ((2 : ℝ) * Sparse.eval nodeValue4459 x + ((2 : ℝ) * Sparse.eval nodeValue4460 x + ((2 : ℝ) * Sparse.eval nodeValue4466 x + ((1 : ℝ) * Sparse.eval nodeValue4495 x + ((2 : ℝ) * Sparse.eval nodeValue4498 x + ((1 : ℝ) * Sparse.eval nodeValue4801 x + ((1 : ℝ) * Sparse.eval nodeValue4865 x + ((1 : ℝ) * Sparse.eval nodeValue4888 x + ((2 : ℝ) * Sparse.eval nodeValue4894 x + 0))))))))))))))))))))

def numericRow1483 : Integer.Sparse Master := [(Sum.inr 600, -1), (Sum.inr 919, -1), (Sum.inr 1040, -2), (Sum.inr 1043, -2), (Sum.inr 1049, -2), (Sum.inr 1079, -1), (Sum.inr 1507, -1), (Sum.inr 1664, -1), (Sum.inr 1707, -2), (Sum.inr 1708, -1), (Sum.inr 1725, -2), (Sum.inr 1738, -2), (Sum.inr 2019, -1), (Sum.inr 2106, -1), (Sum.inr 2190, -1), (Sum.inr 2242, -1), (Sum.inr 2244, -1), (Sum.inr 2262, -1), (Sum.inr 4149, 4), (Sum.inr 4151, 4), (Sum.inr 4154, 8), (Sum.inr 4328, 8), (Sum.inr 4363, 4), (Sum.inr 4365, 4), (Sum.inr 4368, 8), (Sum.inr 4459, 8)]

theorem reindexCheck1483 : Integer.Sparse.reindex keyMap MixedData.row1483 = numericRow1483 := by decide +kernel

theorem numericCheck1483 (x : Master → ℝ) : Integer.Sparse.eval numericRow1483 x =
    (4 : ℝ) * reducedSource1483 x := by
  norm_num [numericRow1483, reducedSource1483, Integer.Sparse.eval, Sparse.eval, nodeValue4149, nodeValue4151, nodeValue4154, nodeValue4172, nodeValue4326, nodeValue4328, nodeValue4341, nodeValue4363, nodeValue4365, nodeValue4368, nodeValue4455, nodeValue4457, nodeValue4459, nodeValue4460, nodeValue4466, nodeValue4495, nodeValue4498, nodeValue4801, nodeValue4865, nodeValue4888, nodeValue4894]
  ring

noncomputable def reducedSource1484 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue629 x + ((1 : ℝ) * Sparse.eval nodeValue630 x + ((2 : ℝ) * Sparse.eval nodeValue631 x + ((1 : ℝ) * Sparse.eval nodeValue646 x + ((1 : ℝ) * Sparse.eval nodeValue1319 x + ((1 : ℝ) * Sparse.eval nodeValue1320 x + ((2 : ℝ) * Sparse.eval nodeValue1321 x + ((1 : ℝ) * Sparse.eval nodeValue1329 x + ((2 : ℝ) * Sparse.eval nodeValue1330 x + ((1 : ℝ) * Sparse.eval nodeValue1341 x + ((1 : ℝ) * Sparse.eval nodeValue1405 x + ((2 : ℝ) * Sparse.eval nodeValue1406 x + ((2 : ℝ) * Sparse.eval nodeValue1414 x + ((2 : ℝ) * Sparse.eval nodeValue1416 x + ((2 : ℝ) * Sparse.eval nodeValue1419 x + ((1 : ℝ) * Sparse.eval nodeValue1441 x + ((2 : ℝ) * Sparse.eval nodeValue1448 x + ((1 : ℝ) * Sparse.eval nodeValue3185 x + ((1 : ℝ) * Sparse.eval nodeValue3205 x + ((1 : ℝ) * Sparse.eval nodeValue3227 x + ((2 : ℝ) * Sparse.eval nodeValue3230 x + 0))))))))))))))))))))

def numericRow1484 : Integer.Sparse Master := [(Sum.inl 0, -212), (Sum.inl 5, -200), (Sum.inl 6, 50), (Sum.inl 2, 280), (Sum.inl 7, 160), (Sum.inl 35, 160), (Sum.inl 1, 290), (Sum.inr 629, 2160), (Sum.inr 630, 2160), (Sum.inr 631, 4320), (Sum.inr 1319, 2160), (Sum.inr 1320, 2160), (Sum.inr 1321, 4320), (Sum.inr 1330, 4320), (Sum.inr 1406, 4320)]

theorem reindexCheck1484 : Integer.Sparse.reindex keyMap MixedData.row1484 = numericRow1484 := by decide +kernel

theorem numericCheck1484 (x : Master → ℝ) : Integer.Sparse.eval numericRow1484 x =
    (2160 : ℝ) * reducedSource1484 x := by
  norm_num [numericRow1484, reducedSource1484, Integer.Sparse.eval, Sparse.eval, nodeValue629, nodeValue630, nodeValue631, nodeValue646, nodeValue1319, nodeValue1320, nodeValue1321, nodeValue1329, nodeValue1330, nodeValue1341, nodeValue1405, nodeValue1406, nodeValue1414, nodeValue1416, nodeValue1419, nodeValue1441, nodeValue1448, nodeValue3185, nodeValue3205, nodeValue3227, nodeValue3230]
  ring

noncomputable def reducedSource1485 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1501 x + ((1 : ℝ) * Sparse.eval nodeValue1505 x + ((1 : ℝ) * Sparse.eval nodeValue1507 x + ((2 : ℝ) * Sparse.eval nodeValue1511 x + ((1 : ℝ) * Sparse.eval nodeValue1663 x + ((1 : ℝ) * Sparse.eval nodeValue1664 x + ((2 : ℝ) * Sparse.eval nodeValue1667 x + ((1 : ℝ) * Sparse.eval nodeValue1697 x + ((1 : ℝ) * Sparse.eval nodeValue1698 x + ((1 : ℝ) * Sparse.eval nodeValue1704 x + ((2 : ℝ) * Sparse.eval nodeValue1707 x + ((1 : ℝ) * Sparse.eval nodeValue1708 x + ((2 : ℝ) * Sparse.eval nodeValue1712 x + ((2 : ℝ) * Sparse.eval nodeValue1714 x + ((2 : ℝ) * Sparse.eval nodeValue1725 x + ((2 : ℝ) * Sparse.eval nodeValue1727 x + ((2 : ℝ) * Sparse.eval nodeValue1738 x + ((1 : ℝ) * Sparse.eval nodeValue2190 x + ((1 : ℝ) * Sparse.eval nodeValue2242 x + ((1 : ℝ) * Sparse.eval nodeValue2244 x + ((2 : ℝ) * Sparse.eval nodeValue2264 x + 0))))))))))))))))))))

def numericRow1485 : Integer.Sparse Master := [(Sum.inr 1501, 1), (Sum.inr 1505, 1), (Sum.inr 1507, 1), (Sum.inr 1511, 2), (Sum.inr 1664, 1), (Sum.inr 1667, 2), (Sum.inr 1697, 1), (Sum.inr 1704, 1), (Sum.inr 1707, 2), (Sum.inr 1708, 1), (Sum.inr 1712, 2), (Sum.inr 1714, 2), (Sum.inr 1725, 2), (Sum.inr 1738, 2), (Sum.inr 2190, 1), (Sum.inr 2242, 1), (Sum.inr 2244, 1)]

theorem reindexCheck1485 : Integer.Sparse.reindex keyMap MixedData.row1485 = numericRow1485 := by decide +kernel

theorem numericCheck1485 (x : Master → ℝ) : Integer.Sparse.eval numericRow1485 x =
    (1 : ℝ) * reducedSource1485 x := by
  norm_num [numericRow1485, reducedSource1485, Integer.Sparse.eval, Sparse.eval, nodeValue1501, nodeValue1505, nodeValue1507, nodeValue1511, nodeValue1663, nodeValue1664, nodeValue1667, nodeValue1697, nodeValue1698, nodeValue1704, nodeValue1707, nodeValue1708, nodeValue1712, nodeValue1714, nodeValue1725, nodeValue1727, nodeValue1738, nodeValue2190, nodeValue2242, nodeValue2244, nodeValue2264]

noncomputable def reducedSource1486 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue577 x + ((1 : ℝ) * Sparse.eval nodeValue579 x + ((2 : ℝ) * Sparse.eval nodeValue582 x + ((1 : ℝ) * Sparse.eval nodeValue600 x + ((1 : ℝ) * Sparse.eval nodeValue1040 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1486 : Integer.Sparse Master := [(Sum.inr 577, 1), (Sum.inr 579, 1), (Sum.inr 582, 2), (Sum.inr 600, 1), (Sum.inr 1040, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1486 : Integer.Sparse.reindex keyMap MixedData.row1486 = numericRow1486 := by decide +kernel

theorem numericCheck1486 (x : Master → ℝ) : Integer.Sparse.eval numericRow1486 x =
    (1 : ℝ) * reducedSource1486 x := by
  norm_num [numericRow1486, reducedSource1486, Integer.Sparse.eval, Sparse.eval, nodeValue577, nodeValue579, nodeValue582, nodeValue600, nodeValue1040, nodeValue4084]

noncomputable def reducedSource1487 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue600 x + ((1 : ℝ) * Sparse.eval nodeValue919 x + ((1 : ℝ) * Sparse.eval nodeValue1040 x + ((1 : ℝ) * Sparse.eval nodeValue1079 x + ((2 : ℝ) * Sparse.eval nodeValue1082 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1487 : Integer.Sparse Master := [(Sum.inr 600, 1), (Sum.inr 919, 1), (Sum.inr 1040, 1), (Sum.inr 1079, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1487 : Integer.Sparse.reindex keyMap MixedData.row1487 = numericRow1487 := by decide +kernel

theorem numericCheck1487 (x : Master → ℝ) : Integer.Sparse.eval numericRow1487 x =
    (1 : ℝ) * reducedSource1487 x := by
  norm_num [numericRow1487, reducedSource1487, Integer.Sparse.eval, Sparse.eval, nodeValue600, nodeValue919, nodeValue1040, nodeValue1079, nodeValue1082, nodeValue4084]

end MUB6.Certificate.MixedSourceBridge

end OAI
