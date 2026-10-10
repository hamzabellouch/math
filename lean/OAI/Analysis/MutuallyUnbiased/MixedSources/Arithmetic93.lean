import OAI.Analysis.MutuallyUnbiased.MixedData.Source11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values9
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1488 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue941 x + ((1 : ℝ) * Sparse.eval nodeValue943 x + ((2 : ℝ) * Sparse.eval nodeValue946 x + ((1 : ℝ) * Sparse.eval nodeValue1040 x + ((1 : ℝ) * Sparse.eval nodeValue2106 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1488 : Integer.Sparse Master := [(Sum.inr 941, 1), (Sum.inr 943, 1), (Sum.inr 946, 2), (Sum.inr 1040, 1), (Sum.inr 2106, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1488 : Integer.Sparse.reindex keyMap MixedData.row1488 = numericRow1488 := by decide +kernel

theorem numericCheck1488 (x : Master → ℝ) : Integer.Sparse.eval numericRow1488 x =
    (1 : ℝ) * reducedSource1488 x := by
  norm_num [numericRow1488, reducedSource1488, Integer.Sparse.eval, Sparse.eval, nodeValue941, nodeValue943, nodeValue946, nodeValue1040, nodeValue2106, nodeValue4084]

noncomputable def reducedSource1489 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue577 x + ((1 : ℝ) * Sparse.eval nodeValue941 x + ((1 : ℝ) * Sparse.eval nodeValue1038 x + ((3 : ℝ) * Sparse.eval nodeValue1040 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

def numericRow1489 : Integer.Sparse Master := [(Sum.inr 577, 1), (Sum.inr 941, 1), (Sum.inr 1040, 3), (Sum.inr 4084, -1)]

theorem reindexCheck1489 : Integer.Sparse.reindex keyMap MixedData.row1489 = numericRow1489 := by decide +kernel

theorem numericCheck1489 (x : Master → ℝ) : Integer.Sparse.eval numericRow1489 x =
    (1 : ℝ) * reducedSource1489 x := by
  norm_num [numericRow1489, reducedSource1489, Integer.Sparse.eval, Sparse.eval, nodeValue577, nodeValue941, nodeValue1038, nodeValue1040, nodeValue4084]

noncomputable def reducedSource1490 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4098 x + ((1 : ℝ) * Sparse.eval nodeValue4099 x + ((2 : ℝ) * Sparse.eval nodeValue4102 x + ((1 : ℝ) * Sparse.eval nodeValue4115 x + ((1 : ℝ) * Sparse.eval nodeValue4286 x + ((2 : ℝ) * Sparse.eval nodeValue4288 x + ((1 : ℝ) * Sparse.eval nodeValue4298 x + ((1 : ℝ) * Sparse.eval nodeValue4341 x + ((1 : ℝ) * Sparse.eval nodeValue4343 x + ((2 : ℝ) * Sparse.eval nodeValue4349 x + ((2 : ℝ) * Sparse.eval nodeValue4396 x + ((2 : ℝ) * Sparse.eval nodeValue4398 x + ((2 : ℝ) * Sparse.eval nodeValue4404 x + ((2 : ℝ) * Sparse.eval nodeValue4419 x + ((1 : ℝ) * Sparse.eval nodeValue4456 x + ((2 : ℝ) * Sparse.eval nodeValue4458 x + ((1 : ℝ) * Sparse.eval nodeValue4495 x + ((1 : ℝ) * Sparse.eval nodeValue5072 x + ((1 : ℝ) * Sparse.eval nodeValue5168 x + ((2 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5292 x + 0))))))))))))))))))))

def numericRow1490 : Integer.Sparse Master := [(Sum.inl 0, 17), (Sum.inl 6, -1), (Sum.inl 2, 10), (Sum.inl 7, 16), (Sum.inl 3, 32), (Sum.inl 1, 34), (Sum.inr 535, -864), (Sum.inr 536, -864), (Sum.inr 539, -1728), (Sum.inr 552, -864), (Sum.inr 656, -864), (Sum.inr 657, -864), (Sum.inr 660, -864), (Sum.inr 664, -1728), (Sum.inr 864, -864), (Sum.inr 866, -1728), (Sum.inr 876, -864), (Sum.inr 919, -864), (Sum.inr 921, -864), (Sum.inr 927, -1728), (Sum.inr 977, -1728), (Sum.inr 979, -1728), (Sum.inr 985, -1728), (Sum.inr 1000, -1728), (Sum.inr 1039, -864), (Sum.inr 1041, -1728), (Sum.inr 1079, -864), (Sum.inr 1550, -864), (Sum.inr 1552, -864), (Sum.inr 1554, -1728), (Sum.inr 1597, -1728), (Sum.inr 1599, -1728), (Sum.inr 1605, -1728), (Sum.inr 1618, -1728), (Sum.inr 1664, -864), (Sum.inr 1666, -864), (Sum.inr 1675, -1728), (Sum.inr 1706, -864), (Sum.inr 1708, -864), (Sum.inr 1724, -1728), (Sum.inr 2479, -864), (Sum.inr 2722, -1728), (Sum.inr 3459, -864), (Sum.inr 3533, -1728), (Sum.inr 3603, -864), (Sum.inr 3622, -864)]

theorem reindexCheck1490 : Integer.Sparse.reindex keyMap MixedData.row1490 = numericRow1490 := by decide +kernel

theorem numericCheck1490 (x : Master → ℝ) : Integer.Sparse.eval numericRow1490 x =
    (3456 : ℝ) * reducedSource1490 x := by
  norm_num [numericRow1490, reducedSource1490, Integer.Sparse.eval, Sparse.eval, nodeValue4098, nodeValue4099, nodeValue4102, nodeValue4115, nodeValue4286, nodeValue4288, nodeValue4298, nodeValue4341, nodeValue4343, nodeValue4349, nodeValue4396, nodeValue4398, nodeValue4404, nodeValue4419, nodeValue4456, nodeValue4458, nodeValue4495, nodeValue5072, nodeValue5168, nodeValue5258, nodeValue5292]; ring

noncomputable def reducedSource1491 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue535 x + ((1 : ℝ) * Sparse.eval nodeValue536 x + ((2 : ℝ) * Sparse.eval nodeValue539 x + ((1 : ℝ) * Sparse.eval nodeValue552 x + ((1 : ℝ) * Sparse.eval nodeValue864 x + ((2 : ℝ) * Sparse.eval nodeValue866 x + ((1 : ℝ) * Sparse.eval nodeValue876 x + ((1 : ℝ) * Sparse.eval nodeValue919 x + ((1 : ℝ) * Sparse.eval nodeValue921 x + ((2 : ℝ) * Sparse.eval nodeValue927 x + ((2 : ℝ) * Sparse.eval nodeValue977 x + ((2 : ℝ) * Sparse.eval nodeValue979 x + ((2 : ℝ) * Sparse.eval nodeValue985 x + ((2 : ℝ) * Sparse.eval nodeValue1000 x + ((1 : ℝ) * Sparse.eval nodeValue1039 x + ((2 : ℝ) * Sparse.eval nodeValue1041 x + ((1 : ℝ) * Sparse.eval nodeValue1079 x + ((1 : ℝ) * Sparse.eval nodeValue2479 x + ((1 : ℝ) * Sparse.eval nodeValue2594 x + ((2 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue2766 x + 0))))))))))))))))))))

def numericRow1491 : Integer.Sparse Master := [(Sum.inl 0, -17), (Sum.inl 6, 1), (Sum.inl 2, -10), (Sum.inl 7, -16), (Sum.inl 3, -32), (Sum.inl 1, -34), (Sum.inr 535, 864), (Sum.inr 536, 864), (Sum.inr 539, 1728), (Sum.inr 552, 864), (Sum.inr 864, 864), (Sum.inr 866, 1728), (Sum.inr 876, 864), (Sum.inr 919, 864), (Sum.inr 921, 864), (Sum.inr 927, 1728), (Sum.inr 977, 1728), (Sum.inr 979, 1728), (Sum.inr 985, 1728), (Sum.inr 1000, 1728), (Sum.inr 1039, 864), (Sum.inr 1041, 1728), (Sum.inr 1079, 864), (Sum.inr 2479, 864), (Sum.inr 2722, 1728)]

theorem reindexCheck1491 : Integer.Sparse.reindex keyMap MixedData.row1491 = numericRow1491 := by decide +kernel

theorem numericCheck1491 (x : Master → ℝ) : Integer.Sparse.eval numericRow1491 x =
    (864 : ℝ) * reducedSource1491 x := by
  norm_num [numericRow1491, reducedSource1491, Integer.Sparse.eval, Sparse.eval, nodeValue535, nodeValue536, nodeValue539, nodeValue552, nodeValue864, nodeValue866, nodeValue876, nodeValue919, nodeValue921, nodeValue927, nodeValue977, nodeValue979, nodeValue985, nodeValue1000, nodeValue1039, nodeValue1041, nodeValue1079, nodeValue2479, nodeValue2594, nodeValue2722, nodeValue2766]; ring

noncomputable def reducedSource1492 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4248 x + ((1 : ℝ) * Sparse.eval nodeValue4251 x + ((1 : ℝ) * Sparse.eval nodeValue4255 x + ((2 : ℝ) * Sparse.eval nodeValue4264 x + ((1 : ℝ) * Sparse.eval nodeValue4395 x + ((2 : ℝ) * Sparse.eval nodeValue4396 x + ((1 : ℝ) * Sparse.eval nodeValue4406 x + ((2 : ℝ) * Sparse.eval nodeValue4435 x + ((1 : ℝ) * Sparse.eval nodeValue4438 x + ((2 : ℝ) * Sparse.eval nodeValue4450 x + ((2 : ℝ) * Sparse.eval nodeValue4452 x + ((1 : ℝ) * Sparse.eval nodeValue4457 x + ((2 : ℝ) * Sparse.eval nodeValue4458 x + ((2 : ℝ) * Sparse.eval nodeValue4470 x + ((1 : ℝ) * Sparse.eval nodeValue4474 x + ((1 : ℝ) * Sparse.eval nodeValue4496 x + ((2 : ℝ) * Sparse.eval nodeValue4498 x + ((1 : ℝ) * Sparse.eval nodeValue4589 x + ((1 : ℝ) * Sparse.eval nodeValue4606 x + ((2 : ℝ) * Sparse.eval nodeValue4607 x + ((1 : ℝ) * Sparse.eval nodeValue4623 x + 0))))))))))))))))))))

def numericRow1492 : Integer.Sparse Master := [(Sum.inl 0, 3), (Sum.inl 6, 1), (Sum.inl 7, -16), (Sum.inl 1, 12), (Sum.inr 782, -864), (Sum.inr 785, -432), (Sum.inr 789, -432), (Sum.inr 804, -432), (Sum.inr 823, -432), (Sum.inr 977, -864), (Sum.inr 1035, -864), (Sum.inr 1040, -432), (Sum.inr 1041, -864), (Sum.inr 1080, -432), (Sum.inr 1240, -432), (Sum.inr 1597, -864), (Sum.inr 1645, -864), (Sum.inr 1707, -432), (Sum.inr 1710, -432), (Sum.inr 1724, -864), (Sum.inr 3299, -432), (Sum.inr 3308, -432), (Sum.inr 4406, 1728), (Sum.inr 4435, 3456), (Sum.inr 4450, 3456), (Sum.inr 4470, 3456), (Sum.inr 4474, 1728), (Sum.inr 4589, 1728), (Sum.inr 4607, 3456)]

theorem reindexCheck1492 : Integer.Sparse.reindex keyMap MixedData.row1492 = numericRow1492 := by decide +kernel

theorem numericCheck1492 (x : Master → ℝ) : Integer.Sparse.eval numericRow1492 x =
    (1728 : ℝ) * reducedSource1492 x := by
  norm_num [numericRow1492, reducedSource1492, Integer.Sparse.eval, Sparse.eval, nodeValue4248, nodeValue4251, nodeValue4255, nodeValue4264, nodeValue4395, nodeValue4396, nodeValue4406, nodeValue4435, nodeValue4438, nodeValue4450, nodeValue4452, nodeValue4457, nodeValue4458, nodeValue4470, nodeValue4474, nodeValue4496, nodeValue4498, nodeValue4589, nodeValue4606, nodeValue4607, nodeValue4623]; ring

noncomputable def reducedSource1493 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1216 x + ((1 : ℝ) * Sparse.eval nodeValue1240 x + ((2 : ℝ) * Sparse.eval nodeValue1241 x + ((1 : ℝ) * Sparse.eval nodeValue1305 x + ((1 : ℝ) * Sparse.eval nodeValue1360 x + ((1 : ℝ) * Sparse.eval nodeValue1370 x + ((2 : ℝ) * Sparse.eval nodeValue1371 x + ((1 : ℝ) * Sparse.eval nodeValue1386 x + ((2 : ℝ) * Sparse.eval nodeValue1387 x + ((2 : ℝ) * Sparse.eval nodeValue1396 x + ((1 : ℝ) * Sparse.eval nodeValue1398 x + ((2 : ℝ) * Sparse.eval nodeValue1411 x + ((2 : ℝ) * Sparse.eval nodeValue1412 x + ((1 : ℝ) * Sparse.eval nodeValue1414 x + ((2 : ℝ) * Sparse.eval nodeValue1415 x + ((2 : ℝ) * Sparse.eval nodeValue1448 x + ((1 : ℝ) * Sparse.eval nodeValue1451 x + ((1 : ℝ) * Sparse.eval nodeValue1470 x + ((1 : ℝ) * Sparse.eval nodeValue1477 x + ((1 : ℝ) * Sparse.eval nodeValue1478 x + ((2 : ℝ) * Sparse.eval nodeValue1483 x + 0))))))))))))))))))))

def numericRow1493 : Integer.Sparse Master := [(Sum.inl 0, -212), (Sum.inl 5, 280), (Sum.inl 6, -70), (Sum.inl 2, -320), (Sum.inl 7, 160), (Sum.inl 35, 160), (Sum.inl 1, -190), (Sum.inr 1216, 2160), (Sum.inr 1240, 2160), (Sum.inr 1241, 4320), (Sum.inr 1360, 2160), (Sum.inr 1370, 2160), (Sum.inr 1371, 4320), (Sum.inr 1387, 4320), (Sum.inr 1415, 4320)]

theorem reindexCheck1493 : Integer.Sparse.reindex keyMap MixedData.row1493 = numericRow1493 := by decide +kernel

theorem numericCheck1493 (x : Master → ℝ) : Integer.Sparse.eval numericRow1493 x =
    (2160 : ℝ) * reducedSource1493 x := by
  norm_num [numericRow1493, reducedSource1493, Integer.Sparse.eval, Sparse.eval, nodeValue1216, nodeValue1240, nodeValue1241, nodeValue1305, nodeValue1360, nodeValue1370, nodeValue1371, nodeValue1386, nodeValue1387, nodeValue1396, nodeValue1398, nodeValue1411, nodeValue1412, nodeValue1414, nodeValue1415, nodeValue1448, nodeValue1451, nodeValue1470, nodeValue1477, nodeValue1478, nodeValue1483]; ring

noncomputable def reducedSource1494 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1033 x + ((1 : ℝ) * Sparse.eval nodeValue2015 x + ((1 : ℝ) * Sparse.eval nodeValue2099 x + ((1 : ℝ) * Sparse.eval nodeValue2203 x + ((1 : ℝ) * Sparse.eval nodeValue2259 x + ((1 : ℝ) * Sparse.eval nodeValue2261 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

def numericRow1494 : Integer.Sparse Master := [(Sum.inr 1033, 1), (Sum.inr 2015, 1), (Sum.inr 2099, 1), (Sum.inr 2203, 1), (Sum.inr 2259, 1), (Sum.inr 2261, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1494 : Integer.Sparse.reindex keyMap MixedData.row1494 = numericRow1494 := by decide +kernel

theorem numericCheck1494 (x : Master → ℝ) : Integer.Sparse.eval numericRow1494 x =
    (1 : ℝ) * reducedSource1494 x := by
  norm_num [numericRow1494, reducedSource1494, Integer.Sparse.eval, Sparse.eval, nodeValue1033, nodeValue2015, nodeValue2099, nodeValue2203, nodeValue2259, nodeValue2261, nodeValue4081]

noncomputable def reducedSource1495 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue981 x + ((1 : ℝ) * Sparse.eval nodeValue1913 x + ((1 : ℝ) * Sparse.eval nodeValue2078 x + ((1 : ℝ) * Sparse.eval nodeValue2192 x + ((1 : ℝ) * Sparse.eval nodeValue2196 x + ((1 : ℝ) * Sparse.eval nodeValue2202 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

def numericRow1495 : Integer.Sparse Master := [(Sum.inr 981, 1), (Sum.inr 1913, 1), (Sum.inr 2078, 1), (Sum.inr 2192, 1), (Sum.inr 2196, 1), (Sum.inr 2202, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1495 : Integer.Sparse.reindex keyMap MixedData.row1495 = numericRow1495 := by decide +kernel

theorem numericCheck1495 (x : Master → ℝ) : Integer.Sparse.eval numericRow1495 x =
    (1 : ℝ) * reducedSource1495 x := by
  norm_num [numericRow1495, reducedSource1495, Integer.Sparse.eval, Sparse.eval, nodeValue981, nodeValue1913, nodeValue2078, nodeValue2192, nodeValue2196, nodeValue2202, nodeValue4080]

noncomputable def reducedSource1496 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue977 x + ((1 : ℝ) * Sparse.eval nodeValue978 x + ((1 : ℝ) * Sparse.eval nodeValue981 x + ((1 : ℝ) * Sparse.eval nodeValue998 x + ((1 : ℝ) * Sparse.eval nodeValue1032 x + ((1 : ℝ) * Sparse.eval nodeValue2202 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

def numericRow1496 : Integer.Sparse Master := [(Sum.inr 977, 1), (Sum.inr 981, 1), (Sum.inr 998, 1), (Sum.inr 1032, 1), (Sum.inr 2202, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1496 : Integer.Sparse.reindex keyMap MixedData.row1496 = numericRow1496 := by decide +kernel

theorem numericCheck1496 (x : Master → ℝ) : Integer.Sparse.eval numericRow1496 x =
    (1 : ℝ) * reducedSource1496 x := by
  norm_num [numericRow1496, reducedSource1496, Integer.Sparse.eval, Sparse.eval, nodeValue977, nodeValue978, nodeValue981, nodeValue998, nodeValue1032, nodeValue2202, nodeValue4080]

noncomputable def reducedSource1497 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue978 x + ((1 : ℝ) * Sparse.eval nodeValue1909 x + ((1 : ℝ) * Sparse.eval nodeValue2076 x + ((1 : ℝ) * Sparse.eval nodeValue2195 x + ((1 : ℝ) * Sparse.eval nodeValue2202 x + ((1 : ℝ) * Sparse.eval nodeValue2206 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

def numericRow1497 : Integer.Sparse Master := [(Sum.inr 1909, 1), (Sum.inr 2076, 1), (Sum.inr 2195, 1), (Sum.inr 2202, 1), (Sum.inr 2206, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1497 : Integer.Sparse.reindex keyMap MixedData.row1497 = numericRow1497 := by decide +kernel

theorem numericCheck1497 (x : Master → ℝ) : Integer.Sparse.eval numericRow1497 x =
    (1 : ℝ) * reducedSource1497 x := by
  norm_num [numericRow1497, reducedSource1497, Integer.Sparse.eval, Sparse.eval, nodeValue978, nodeValue1909, nodeValue2076, nodeValue2195, nodeValue2202, nodeValue2206, nodeValue4080]

noncomputable def reducedSource1498 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue980 x + ((1 : ℝ) * Sparse.eval nodeValue1912 x + ((1 : ℝ) * Sparse.eval nodeValue2077 x + ((2 : ℝ) * Sparse.eval nodeValue2191 x + ((1 : ℝ) * Sparse.eval nodeValue2204 x + ((-1 : ℝ) * Sparse.eval nodeValue4079 x + 0)))))

def numericRow1498 : Integer.Sparse Master := [(Sum.inr 980, 1), (Sum.inr 2077, 1), (Sum.inr 2191, 2), (Sum.inr 4079, -1)]

theorem reindexCheck1498 : Integer.Sparse.reindex keyMap MixedData.row1498 = numericRow1498 := by decide +kernel

theorem numericCheck1498 (x : Master → ℝ) : Integer.Sparse.eval numericRow1498 x =
    (1 : ℝ) * reducedSource1498 x := by
  norm_num [numericRow1498, reducedSource1498, Integer.Sparse.eval, Sparse.eval, nodeValue980, nodeValue1912, nodeValue2077, nodeValue2191, nodeValue2204, nodeValue4079]

noncomputable def reducedSource1499 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue980 x + ((1 : ℝ) * Sparse.eval nodeValue1003 x + ((1 : ℝ) * Sparse.eval nodeValue1034 x + ((1 : ℝ) * Sparse.eval nodeValue2204 x + ((-1 : ℝ) * Sparse.eval nodeValue4079 x + 0))))

def numericRow1499 : Integer.Sparse Master := [(Sum.inr 980, 3), (Sum.inr 1034, 1), (Sum.inr 4079, -1)]

theorem reindexCheck1499 : Integer.Sparse.reindex keyMap MixedData.row1499 = numericRow1499 := by decide +kernel

theorem numericCheck1499 (x : Master → ℝ) : Integer.Sparse.eval numericRow1499 x =
    (1 : ℝ) * reducedSource1499 x := by
  norm_num [numericRow1499, reducedSource1499, Integer.Sparse.eval, Sparse.eval, nodeValue980, nodeValue1003, nodeValue1034, nodeValue2204, nodeValue4079]

noncomputable def reducedSource1500 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue977 x + ((1 : ℝ) * Sparse.eval nodeValue1908 x + ((1 : ℝ) * Sparse.eval nodeValue2075 x + ((1 : ℝ) * Sparse.eval nodeValue2190 x + ((1 : ℝ) * Sparse.eval nodeValue2202 x + ((1 : ℝ) * Sparse.eval nodeValue2205 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

def numericRow1500 : Integer.Sparse Master := [(Sum.inr 977, 1), (Sum.inr 2075, 1), (Sum.inr 2190, 1), (Sum.inr 2202, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1500 : Integer.Sparse.reindex keyMap MixedData.row1500 = numericRow1500 := by decide +kernel

theorem numericCheck1500 (x : Master → ℝ) : Integer.Sparse.eval numericRow1500 x =
    (1 : ℝ) * reducedSource1500 x := by
  norm_num [numericRow1500, reducedSource1500, Integer.Sparse.eval, Sparse.eval, nodeValue977, nodeValue1908, nodeValue2075, nodeValue2190, nodeValue2202, nodeValue2205, nodeValue4080]

noncomputable def reducedSource1501 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue865 x + ((1 : ℝ) * Sparse.eval nodeValue866 x + ((1 : ℝ) * Sparse.eval nodeValue869 x + ((1 : ℝ) * Sparse.eval nodeValue878 x + ((1 : ℝ) * Sparse.eval nodeValue977 x + ((1 : ℝ) * Sparse.eval nodeValue1908 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

def numericRow1501 : Integer.Sparse Master := [(Sum.inr 865, 1), (Sum.inr 866, 1), (Sum.inr 869, 1), (Sum.inr 977, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1501 : Integer.Sparse.reindex keyMap MixedData.row1501 = numericRow1501 := by decide +kernel

theorem numericCheck1501 (x : Master → ℝ) : Integer.Sparse.eval numericRow1501 x =
    (1 : ℝ) * reducedSource1501 x := by
  norm_num [numericRow1501, reducedSource1501, Integer.Sparse.eval, Sparse.eval, nodeValue865, nodeValue866, nodeValue869, nodeValue878, nodeValue977, nodeValue1908, nodeValue4080]

noncomputable def reducedSource1502 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue699 x + ((1 : ℝ) * Sparse.eval nodeValue700 x + ((1 : ℝ) * Sparse.eval nodeValue703 x + ((1 : ℝ) * Sparse.eval nodeValue712 x + ((1 : ℝ) * Sparse.eval nodeValue806 x + ((1 : ℝ) * Sparse.eval nodeValue1597 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

def numericRow1502 : Integer.Sparse Master := [(Sum.inr 699, 1), (Sum.inr 700, 1), (Sum.inr 703, 1), (Sum.inr 1597, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1502 : Integer.Sparse.reindex keyMap MixedData.row1502 = numericRow1502 := by decide +kernel

theorem numericCheck1502 (x : Master → ℝ) : Integer.Sparse.eval numericRow1502 x =
    (1 : ℝ) * reducedSource1502 x := by
  norm_num [numericRow1502, reducedSource1502, Integer.Sparse.eval, Sparse.eval, nodeValue699, nodeValue700, nodeValue703, nodeValue712, nodeValue806, nodeValue1597, nodeValue4069]

noncomputable def reducedSource1503 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue976 x + ((1 : ℝ) * Sparse.eval nodeValue1907 x + ((1 : ℝ) * Sparse.eval nodeValue2074 x + ((1 : ℝ) * Sparse.eval nodeValue2201 x + ((2 : ℝ) * Sparse.eval nodeValue2203 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0)))))

def numericRow1503 : Integer.Sparse Master := [(Sum.inr 1907, 1), (Sum.inr 2074, 1), (Sum.inr 2201, 1), (Sum.inr 2203, 2), (Sum.inr 4081, -1)]

theorem reindexCheck1503 : Integer.Sparse.reindex keyMap MixedData.row1503 = numericRow1503 := by decide +kernel

theorem numericCheck1503 (x : Master → ℝ) : Integer.Sparse.eval numericRow1503 x =
    (1 : ℝ) * reducedSource1503 x := by
  norm_num [numericRow1503, reducedSource1503, Integer.Sparse.eval, Sparse.eval, nodeValue976, nodeValue1907, nodeValue2074, nodeValue2201, nodeValue2203, nodeValue4081]

end MUB6.Certificate.MixedSourceBridge

end OAI
