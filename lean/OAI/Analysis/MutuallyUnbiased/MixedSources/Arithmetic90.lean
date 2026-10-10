import OAI.Analysis.MutuallyUnbiased.MixedData.Source11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values9
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1440 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1148 x + ((1 : ℝ) * Sparse.eval nodeValue1149 x + ((1 : ℝ) * Sparse.eval nodeValue1151 x + ((1 : ℝ) * Sparse.eval nodeValue1156 x + ((1 : ℝ) * Sparse.eval nodeValue1236 x + ((1 : ℝ) * Sparse.eval nodeValue2553 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1440 : Integer.Sparse Master := [(Sum.inr 1148, 1), (Sum.inr 1149, 1), (Sum.inr 1151, 1), (Sum.inr 1156, 1), (Sum.inr 1236, 1), (Sum.inr 2553, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1440 : Integer.Sparse.reindex keyMap MixedData.row1440 = numericRow1440 := by decide +kernel

theorem numericCheck1440 (x : Master → ℝ) : Integer.Sparse.eval numericRow1440 x =
    (1 : ℝ) * reducedSource1440 x := by
  norm_num [numericRow1440, reducedSource1440, Integer.Sparse.eval, Sparse.eval, nodeValue1148, nodeValue1149, nodeValue1151, nodeValue1156, nodeValue1236, nodeValue2553, nodeValue4092]

noncomputable def reducedSource1441 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4139 x + ((1 : ℝ) * Sparse.eval nodeValue4140 x + ((1 : ℝ) * Sparse.eval nodeValue4141 x + ((1 : ℝ) * Sparse.eval nodeValue4145 x + ((1 : ℝ) * Sparse.eval nodeValue4172 x + ((1 : ℝ) * Sparse.eval nodeValue4513 x + ((1 : ℝ) * Sparse.eval nodeValue4514 x + ((1 : ℝ) * Sparse.eval nodeValue4515 x + ((1 : ℝ) * Sparse.eval nodeValue4518 x + ((1 : ℝ) * Sparse.eval nodeValue4521 x + ((1 : ℝ) * Sparse.eval nodeValue4522 x + ((1 : ℝ) * Sparse.eval nodeValue4524 x + ((1 : ℝ) * Sparse.eval nodeValue4541 x + ((1 : ℝ) * Sparse.eval nodeValue4581 x + ((1 : ℝ) * Sparse.eval nodeValue4583 x + ((1 : ℝ) * Sparse.eval nodeValue4586 x + ((1 : ℝ) * Sparse.eval nodeValue4601 x + ((3 : ℝ) * Sparse.eval nodeValue4602 x + ((1 : ℝ) * Sparse.eval nodeValue4605 x + ((1 : ℝ) * Sparse.eval nodeValue4606 x + ((1 : ℝ) * Sparse.eval nodeValue4612 x + ((1 : ℝ) * Sparse.eval nodeValue4622 x + ((1 : ℝ) * Sparse.eval nodeValue4623 x + ((1 : ℝ) * Sparse.eval nodeValue5149 x + ((1 : ℝ) * Sparse.eval nodeValue5204 x + ((1 : ℝ) * Sparse.eval nodeValue5284 x + ((1 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + 0)))))))))))))))))))))))))))

def numericRow1441 : Integer.Sparse Master := [(Sum.inl 0, 152), (Sum.inl 6, -5), (Sum.inl 2, 5), (Sum.inl 7, -80), (Sum.inl 8, 160), (Sum.inl 3, -80), (Sum.inl 1, -50), (Sum.inr 567, -4320), (Sum.inr 568, -4320), (Sum.inr 569, -4320), (Sum.inr 573, -4320), (Sum.inr 600, -4320), (Sum.inr 1097, -4320), (Sum.inr 1098, -4320), (Sum.inr 1099, -4320), (Sum.inr 1102, -4320), (Sum.inr 1105, -4320), (Sum.inr 1106, -4320), (Sum.inr 1108, -4320), (Sum.inr 1126, -4320), (Sum.inr 1200, -4320), (Sum.inr 1202, -4320), (Sum.inr 1205, -4320), (Sum.inr 1235, -4320), (Sum.inr 1236, -12960), (Sum.inr 1239, -4320), (Sum.inr 1240, -4320), (Sum.inr 1246, -4320), (Sum.inr 1488, -4320), (Sum.inr 1489, -4320), (Sum.inr 1490, -4320), (Sum.inr 1493, -4320), (Sum.inr 1507, -4320), (Sum.inr 1887, -4320), (Sum.inr 1894, -4320), (Sum.inr 1942, -4320), (Sum.inr 2226, -4320), (Sum.inr 2881, -4320), (Sum.inr 2924, -4320), (Sum.inr 3077, -4320), (Sum.inr 3232, -4320), (Sum.inr 3233, -4320), (Sum.inr 3236, -4320), (Sum.inr 3249, -4320), (Sum.inr 3251, -4320), (Sum.inr 3256, -4320), (Sum.inr 3281, -4320), (Sum.inr 3284, -4320), (Sum.inr 3292, -4320), (Sum.inr 3293, -12960), (Sum.inr 3299, -4320), (Sum.inr 3301, -4320), (Sum.inr 3307, -4320), (Sum.inr 3308, -4320), (Sum.inr 3605, -4320), (Sum.inr 3622, -4320), (Sum.inr 3624, -4320), (Sum.inr 3625, -4320), (Sum.inr 3632, -4320)]

theorem reindexCheck1441 : Integer.Sparse.reindex keyMap MixedData.row1441 = numericRow1441 := by decide +kernel

theorem numericCheck1441 (x : Master → ℝ) : Integer.Sparse.eval numericRow1441 x =
    (17280 : ℝ) * reducedSource1441 x := by
  norm_num [numericRow1441, reducedSource1441, Integer.Sparse.eval, Sparse.eval, nodeValue4139, nodeValue4140, nodeValue4141, nodeValue4145, nodeValue4172, nodeValue4513, nodeValue4514, nodeValue4515, nodeValue4518, nodeValue4521, nodeValue4522, nodeValue4524, nodeValue4541, nodeValue4581, nodeValue4583, nodeValue4586, nodeValue4601, nodeValue4602, nodeValue4605, nodeValue4606, nodeValue4612, nodeValue4622, nodeValue4623, nodeValue5149, nodeValue5204, nodeValue5284, nodeValue5292, nodeValue5294]
  ring

noncomputable def reducedSource1442 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue567 x + ((1 : ℝ) * Sparse.eval nodeValue568 x + ((1 : ℝ) * Sparse.eval nodeValue569 x + ((1 : ℝ) * Sparse.eval nodeValue573 x + ((1 : ℝ) * Sparse.eval nodeValue600 x + ((1 : ℝ) * Sparse.eval nodeValue1097 x + ((1 : ℝ) * Sparse.eval nodeValue1098 x + ((1 : ℝ) * Sparse.eval nodeValue1099 x + ((1 : ℝ) * Sparse.eval nodeValue1102 x + ((1 : ℝ) * Sparse.eval nodeValue1105 x + ((1 : ℝ) * Sparse.eval nodeValue1106 x + ((1 : ℝ) * Sparse.eval nodeValue1108 x + ((1 : ℝ) * Sparse.eval nodeValue1126 x + ((1 : ℝ) * Sparse.eval nodeValue1200 x + ((1 : ℝ) * Sparse.eval nodeValue1202 x + ((1 : ℝ) * Sparse.eval nodeValue1205 x + ((1 : ℝ) * Sparse.eval nodeValue1235 x + ((3 : ℝ) * Sparse.eval nodeValue1236 x + ((1 : ℝ) * Sparse.eval nodeValue1239 x + ((1 : ℝ) * Sparse.eval nodeValue1240 x + ((1 : ℝ) * Sparse.eval nodeValue1246 x + ((1 : ℝ) * Sparse.eval nodeValue1299 x + ((1 : ℝ) * Sparse.eval nodeValue1300 x + ((1 : ℝ) * Sparse.eval nodeValue2881 x + ((1 : ℝ) * Sparse.eval nodeValue2924 x + ((1 : ℝ) * Sparse.eval nodeValue3077 x + ((1 : ℝ) * Sparse.eval nodeValue3100 x + ((1 : ℝ) * Sparse.eval nodeValue3101 x + 0)))))))))))))))))))))))))))

def numericRow1442 : Integer.Sparse Master := [(Sum.inl 0, -152), (Sum.inl 6, 5), (Sum.inl 2, -5), (Sum.inl 7, 80), (Sum.inl 8, -160), (Sum.inl 3, 80), (Sum.inl 1, 50), (Sum.inr 567, 4320), (Sum.inr 568, 4320), (Sum.inr 569, 4320), (Sum.inr 573, 4320), (Sum.inr 600, 4320), (Sum.inr 1097, 4320), (Sum.inr 1098, 4320), (Sum.inr 1099, 4320), (Sum.inr 1102, 4320), (Sum.inr 1105, 4320), (Sum.inr 1106, 4320), (Sum.inr 1108, 4320), (Sum.inr 1126, 4320), (Sum.inr 1200, 4320), (Sum.inr 1202, 4320), (Sum.inr 1205, 4320), (Sum.inr 1235, 4320), (Sum.inr 1236, 12960), (Sum.inr 1239, 4320), (Sum.inr 1240, 4320), (Sum.inr 1246, 4320), (Sum.inr 2881, 4320), (Sum.inr 2924, 4320), (Sum.inr 3077, 4320)]

theorem reindexCheck1442 : Integer.Sparse.reindex keyMap MixedData.row1442 = numericRow1442 := by decide +kernel

theorem numericCheck1442 (x : Master → ℝ) : Integer.Sparse.eval numericRow1442 x =
    (4320 : ℝ) * reducedSource1442 x := by
  norm_num [numericRow1442, reducedSource1442, Integer.Sparse.eval, Sparse.eval, nodeValue567, nodeValue568, nodeValue569, nodeValue573, nodeValue600, nodeValue1097, nodeValue1098, nodeValue1099, nodeValue1102, nodeValue1105, nodeValue1106, nodeValue1108, nodeValue1126, nodeValue1200, nodeValue1202, nodeValue1205, nodeValue1235, nodeValue1236, nodeValue1239, nodeValue1240, nodeValue1246, nodeValue1299, nodeValue1300, nodeValue2881, nodeValue2924, nodeValue3077, nodeValue3100, nodeValue3101]
  ring

noncomputable def reducedSource1443 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1229 x + ((1 : ℝ) * Sparse.eval nodeValue2504 x + ((1 : ℝ) * Sparse.eval nodeValue2550 x + ((1 : ℝ) * Sparse.eval nodeValue2704 x + ((1 : ℝ) * Sparse.eval nodeValue2719 x + ((1 : ℝ) * Sparse.eval nodeValue2735 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

def numericRow1443 : Integer.Sparse Master := [(Sum.inr 1229, 1), (Sum.inr 2504, 1), (Sum.inr 2550, 1), (Sum.inr 2704, 1), (Sum.inr 2719, 1), (Sum.inr 2735, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1443 : Integer.Sparse.reindex keyMap MixedData.row1443 = numericRow1443 := by decide +kernel

theorem numericCheck1443 (x : Master → ℝ) : Integer.Sparse.eval numericRow1443 x =
    (1 : ℝ) * reducedSource1443 x := by
  norm_num [numericRow1443, reducedSource1443, Integer.Sparse.eval, Sparse.eval, nodeValue1229, nodeValue2504, nodeValue2550, nodeValue2704, nodeValue2719, nodeValue2735, nodeValue4080]

noncomputable def reducedSource1444 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1183 x + ((1 : ℝ) * Sparse.eval nodeValue1188 x + ((2 : ℝ) * Sparse.eval nodeValue1189 x + ((1 : ℝ) * Sparse.eval nodeValue1286 x + ((1 : ℝ) * Sparse.eval nodeValue2684 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0)))))

def numericRow1444 : Integer.Sparse Master := [(Sum.inr 1183, 1), (Sum.inr 1188, 1), (Sum.inr 1189, 2), (Sum.inr 1286, 1), (Sum.inr 2684, 1), (Sum.inr 4088, -1)]

theorem reindexCheck1444 : Integer.Sparse.reindex keyMap MixedData.row1444 = numericRow1444 := by decide +kernel

theorem numericCheck1444 (x : Master → ℝ) : Integer.Sparse.eval numericRow1444 x =
    (1 : ℝ) * reducedSource1444 x := by
  norm_num [numericRow1444, reducedSource1444, Integer.Sparse.eval, Sparse.eval, nodeValue1183, nodeValue1188, nodeValue1189, nodeValue1286, nodeValue2684, nodeValue4088]

noncomputable def reducedSource1445 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1185 x + ((1 : ℝ) * Sparse.eval nodeValue2400 x + ((1 : ℝ) * Sparse.eval nodeValue2535 x + ((1 : ℝ) * Sparse.eval nodeValue2677 x + ((1 : ℝ) * Sparse.eval nodeValue2682 x + ((1 : ℝ) * Sparse.eval nodeValue2686 x + ((-1 : ℝ) * Sparse.eval nodeValue4089 x + 0))))))

def numericRow1445 : Integer.Sparse Master := [(Sum.inr 1185, 1), (Sum.inr 2400, 1), (Sum.inr 2535, 1), (Sum.inr 2677, 1), (Sum.inr 2682, 1), (Sum.inr 2686, 1), (Sum.inr 4089, -1)]

theorem reindexCheck1445 : Integer.Sparse.reindex keyMap MixedData.row1445 = numericRow1445 := by decide +kernel

theorem numericCheck1445 (x : Master → ℝ) : Integer.Sparse.eval numericRow1445 x =
    (1 : ℝ) * reducedSource1445 x := by
  norm_num [numericRow1445, reducedSource1445, Integer.Sparse.eval, Sparse.eval, nodeValue1185, nodeValue2400, nodeValue2535, nodeValue2677, nodeValue2682, nodeValue2686, nodeValue4089]

noncomputable def reducedSource1446 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1188 x + ((1 : ℝ) * Sparse.eval nodeValue2403 x + ((1 : ℝ) * Sparse.eval nodeValue2536 x + ((2 : ℝ) * Sparse.eval nodeValue2672 x + ((1 : ℝ) * Sparse.eval nodeValue2684 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0)))))

def numericRow1446 : Integer.Sparse Master := [(Sum.inr 1188, 1), (Sum.inr 2536, 1), (Sum.inr 2672, 2), (Sum.inr 2684, 1), (Sum.inr 4088, -1)]

theorem reindexCheck1446 : Integer.Sparse.reindex keyMap MixedData.row1446 = numericRow1446 := by decide +kernel

theorem numericCheck1446 (x : Master → ℝ) : Integer.Sparse.eval numericRow1446 x =
    (1 : ℝ) * reducedSource1446 x := by
  norm_num [numericRow1446, reducedSource1446, Integer.Sparse.eval, Sparse.eval, nodeValue1188, nodeValue2403, nodeValue2536, nodeValue2672, nodeValue2684, nodeValue4088]

noncomputable def reducedSource1447 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1184 x + ((1 : ℝ) * Sparse.eval nodeValue2399 x + ((1 : ℝ) * Sparse.eval nodeValue2534 x + ((1 : ℝ) * Sparse.eval nodeValue2670 x + ((1 : ℝ) * Sparse.eval nodeValue2681 x + ((1 : ℝ) * Sparse.eval nodeValue2685 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

def numericRow1447 : Integer.Sparse Master := [(Sum.inr 1184, 1), (Sum.inr 2399, 1), (Sum.inr 2534, 1), (Sum.inr 2670, 1), (Sum.inr 2681, 1), (Sum.inr 2685, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1447 : Integer.Sparse.reindex keyMap MixedData.row1447 = numericRow1447 := by decide +kernel

theorem numericCheck1447 (x : Master → ℝ) : Integer.Sparse.eval numericRow1447 x =
    (1 : ℝ) * reducedSource1447 x := by
  norm_num [numericRow1447, reducedSource1447, Integer.Sparse.eval, Sparse.eval, nodeValue1184, nodeValue2399, nodeValue2534, nodeValue2670, nodeValue2681, nodeValue2685, nodeValue4082]

noncomputable def reducedSource1448 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1200 x + ((2 : ℝ) * Sparse.eval nodeValue1201 x + ((2 : ℝ) * Sparse.eval nodeValue1228 x + ((1 : ℝ) * Sparse.eval nodeValue2703 x + ((-1 : ℝ) * Sparse.eval nodeValue4090 x + 0))))

def numericRow1448 : Integer.Sparse Master := [(Sum.inr 1200, 1), (Sum.inr 1201, 2), (Sum.inr 1228, 2), (Sum.inr 2703, 1), (Sum.inr 4090, -1)]

theorem reindexCheck1448 : Integer.Sparse.reindex keyMap MixedData.row1448 = numericRow1448 := by decide +kernel

theorem numericCheck1448 (x : Master → ℝ) : Integer.Sparse.eval numericRow1448 x =
    (1 : ℝ) * reducedSource1448 x := by
  norm_num [numericRow1448, reducedSource1448, Integer.Sparse.eval, Sparse.eval, nodeValue1200, nodeValue1201, nodeValue1228, nodeValue2703, nodeValue4090]

noncomputable def reducedSource1449 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1198 x + ((2 : ℝ) * Sparse.eval nodeValue2459 x + ((1 : ℝ) * Sparse.eval nodeValue2697 x + ((1 : ℝ) * Sparse.eval nodeValue2701 x + ((1 : ℝ) * Sparse.eval nodeValue2705 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0)))))

def numericRow1449 : Integer.Sparse Master := [(Sum.inr 1198, 1), (Sum.inr 2459, 2), (Sum.inr 2697, 1), (Sum.inr 2705, 1), (Sum.inr 4088, -1)]

theorem reindexCheck1449 : Integer.Sparse.reindex keyMap MixedData.row1449 = numericRow1449 := by decide +kernel

theorem numericCheck1449 (x : Master → ℝ) : Integer.Sparse.eval numericRow1449 x =
    (1 : ℝ) * reducedSource1449 x := by
  norm_num [numericRow1449, reducedSource1449, Integer.Sparse.eval, Sparse.eval, nodeValue1198, nodeValue2459, nodeValue2697, nodeValue2701, nodeValue2705, nodeValue4088]

noncomputable def reducedSource1450 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1200 x + ((2 : ℝ) * Sparse.eval nodeValue2461 x + ((2 : ℝ) * Sparse.eval nodeValue2694 x + ((1 : ℝ) * Sparse.eval nodeValue2703 x + ((-1 : ℝ) * Sparse.eval nodeValue4090 x + 0))))

def numericRow1450 : Integer.Sparse Master := [(Sum.inr 1200, 1), (Sum.inr 2694, 2), (Sum.inr 2703, 1), (Sum.inr 4090, -1)]

theorem reindexCheck1450 : Integer.Sparse.reindex keyMap MixedData.row1450 = numericRow1450 := by decide +kernel

theorem numericCheck1450 (x : Master → ℝ) : Integer.Sparse.eval numericRow1450 x =
    (1 : ℝ) * reducedSource1450 x := by
  norm_num [numericRow1450, reducedSource1450, Integer.Sparse.eval, Sparse.eval, nodeValue1200, nodeValue2461, nodeValue2694, nodeValue2703, nodeValue4090]

noncomputable def reducedSource1451 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1197 x + ((2 : ℝ) * Sparse.eval nodeValue2458 x + ((1 : ℝ) * Sparse.eval nodeValue2693 x + ((1 : ℝ) * Sparse.eval nodeValue2700 x + ((1 : ℝ) * Sparse.eval nodeValue2704 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

def numericRow1451 : Integer.Sparse Master := [(Sum.inr 1197, 1), (Sum.inr 2458, 2), (Sum.inr 2700, 1), (Sum.inr 2704, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1451 : Integer.Sparse.reindex keyMap MixedData.row1451 = numericRow1451 := by decide +kernel

theorem numericCheck1451 (x : Master → ℝ) : Integer.Sparse.eval numericRow1451 x =
    (1 : ℝ) * reducedSource1451 x := by
  norm_num [numericRow1451, reducedSource1451, Integer.Sparse.eval, Sparse.eval, nodeValue1197, nodeValue2458, nodeValue2693, nodeValue2700, nodeValue2704, nodeValue4080]

noncomputable def reducedSource1452 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1052 x + ((2 : ℝ) * Sparse.eval nodeValue1054 x + ((1 : ℝ) * Sparse.eval nodeValue1060 x + ((1 : ℝ) * Sparse.eval nodeValue1073 x + ((1 : ℝ) * Sparse.eval nodeValue2275 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

def numericRow1452 : Integer.Sparse Master := [(Sum.inr 1052, 1), (Sum.inr 1054, 2), (Sum.inr 1060, 1), (Sum.inr 1073, 1), (Sum.inr 2275, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1452 : Integer.Sparse.reindex keyMap MixedData.row1452 = numericRow1452 := by decide +kernel

theorem numericCheck1452 (x : Master → ℝ) : Integer.Sparse.eval numericRow1452 x =
    (1 : ℝ) * reducedSource1452 x := by
  norm_num [numericRow1452, reducedSource1452, Integer.Sparse.eval, Sparse.eval, nodeValue1052, nodeValue1054, nodeValue1060, nodeValue1073, nodeValue2275, nodeValue4080]

noncomputable def reducedSource1453 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1054 x + ((1 : ℝ) * Sparse.eval nodeValue2031 x + ((1 : ℝ) * Sparse.eval nodeValue2129 x + ((1 : ℝ) * Sparse.eval nodeValue2216 x + ((1 : ℝ) * Sparse.eval nodeValue2251 x + ((1 : ℝ) * Sparse.eval nodeValue2275 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

def numericRow1453 : Integer.Sparse Master := [(Sum.inr 1054, 1), (Sum.inr 2031, 1), (Sum.inr 2129, 1), (Sum.inr 2216, 1), (Sum.inr 2251, 1), (Sum.inr 2275, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1453 : Integer.Sparse.reindex keyMap MixedData.row1453 = numericRow1453 := by decide +kernel

theorem numericCheck1453 (x : Master → ℝ) : Integer.Sparse.eval numericRow1453 x =
    (1 : ℝ) * reducedSource1453 x := by
  norm_num [numericRow1453, reducedSource1453, Integer.Sparse.eval, Sparse.eval, nodeValue1054, nodeValue2031, nodeValue2129, nodeValue2216, nodeValue2251, nodeValue2275, nodeValue4080]

noncomputable def reducedSource1454 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1053 x + ((1 : ℝ) * Sparse.eval nodeValue2030 x + ((1 : ℝ) * Sparse.eval nodeValue2128 x + ((1 : ℝ) * Sparse.eval nodeValue2215 x + ((1 : ℝ) * Sparse.eval nodeValue2274 x + ((1 : ℝ) * Sparse.eval nodeValue2276 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

def numericRow1454 : Integer.Sparse Master := [(Sum.inr 1053, 1), (Sum.inr 2030, 1), (Sum.inr 2128, 1), (Sum.inr 2215, 1), (Sum.inr 2274, 1), (Sum.inr 2276, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1454 : Integer.Sparse.reindex keyMap MixedData.row1454 = numericRow1454 := by decide +kernel

theorem numericCheck1454 (x : Master → ℝ) : Integer.Sparse.eval numericRow1454 x =
    (1 : ℝ) * reducedSource1454 x := by
  norm_num [numericRow1454, reducedSource1454, Integer.Sparse.eval, Sparse.eval, nodeValue1053, nodeValue2030, nodeValue2128, nodeValue2215, nodeValue2274, nodeValue2276, nodeValue4082]

noncomputable def reducedSource1455 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue988 x + ((1 : ℝ) * Sparse.eval nodeValue990 x + ((1 : ℝ) * Sparse.eval nodeValue998 x + ((1 : ℝ) * Sparse.eval nodeValue1052 x + ((1 : ℝ) * Sparse.eval nodeValue2214 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

def numericRow1455 : Integer.Sparse Master := [(Sum.inr 988, 2), (Sum.inr 990, 1), (Sum.inr 998, 1), (Sum.inr 1052, 1), (Sum.inr 2214, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1455 : Integer.Sparse.reindex keyMap MixedData.row1455 = numericRow1455 := by decide +kernel

theorem numericCheck1455 (x : Master → ℝ) : Integer.Sparse.eval numericRow1455 x =
    (1 : ℝ) * reducedSource1455 x := by
  norm_num [numericRow1455, reducedSource1455, Integer.Sparse.eval, Sparse.eval, nodeValue988, nodeValue990, nodeValue998, nodeValue1052, nodeValue2214, nodeValue4080]

end MUB6.Certificate.MixedSourceBridge

end OAI
