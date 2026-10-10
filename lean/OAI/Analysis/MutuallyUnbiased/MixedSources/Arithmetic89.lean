import OAI.Analysis.MutuallyUnbiased.MixedData.Source11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values9
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1424 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1512 x + ((1 : ℝ) * Sparse.eval nodeValue1513 x + ((1 : ℝ) * Sparse.eval nodeValue1520 x + ((1 : ℝ) * Sparse.eval nodeValue1526 x + ((2 : ℝ) * Sparse.eval nodeValue2657 x + ((1 : ℝ) * Sparse.eval nodeValue2683 x + ((1 : ℝ) * Sparse.eval nodeValue2737 x + ((2 : ℝ) * Sparse.eval nodeValue3259 x + ((2 : ℝ) * Sparse.eval nodeValue3266 x + ((2 : ℝ) * Sparse.eval nodeValue3271 x + ((2 : ℝ) * Sparse.eval nodeValue3293 x + ((2 : ℝ) * Sparse.eval nodeValue3296 x + ((1 : ℝ) * Sparse.eval nodeValue3300 x + ((1 : ℝ) * Sparse.eval nodeValue3301 x + ((1 : ℝ) * Sparse.eval nodeValue3302 x + ((2 : ℝ) * Sparse.eval nodeValue3303 x + ((1 : ℝ) * Sparse.eval nodeValue3306 x + ((1 : ℝ) * Sparse.eval nodeValue3547 x + ((2 : ℝ) * Sparse.eval nodeValue3564 x + ((1 : ℝ) * Sparse.eval nodeValue3582 x + ((1 : ℝ) * Sparse.eval nodeValue3583 x + 0))))))))))))))))))))

def numericRow1424 : Integer.Sparse Master := [(Sum.inr 1512, 2), (Sum.inr 1513, 1), (Sum.inr 1520, 1), (Sum.inr 1526, 1), (Sum.inr 2657, 2), (Sum.inr 2683, 1), (Sum.inr 2737, 1), (Sum.inr 3259, 2), (Sum.inr 3266, 2), (Sum.inr 3271, 2), (Sum.inr 3293, 2), (Sum.inr 3296, 2), (Sum.inr 3300, 1), (Sum.inr 3301, 1), (Sum.inr 3302, 1), (Sum.inr 3303, 2), (Sum.inr 3306, 1), (Sum.inr 3564, 2), (Sum.inr 3582, 1), (Sum.inr 3583, 1)]

theorem reindexCheck1424 : Integer.Sparse.reindex keyMap MixedData.row1424 = numericRow1424 := by decide +kernel

theorem numericCheck1424 (x : Master → ℝ) : Integer.Sparse.eval numericRow1424 x =
    (1 : ℝ) * reducedSource1424 x := by
  norm_num [numericRow1424, reducedSource1424, Integer.Sparse.eval, Sparse.eval, nodeValue1512, nodeValue1513, nodeValue1520, nodeValue1526, nodeValue2657, nodeValue2683, nodeValue2737, nodeValue3259, nodeValue3266, nodeValue3271, nodeValue3293, nodeValue3296, nodeValue3300, nodeValue3301, nodeValue3302, nodeValue3303, nodeValue3306, nodeValue3547, nodeValue3564, nodeValue3582, nodeValue3583]

noncomputable def reducedSource1425 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue638 x + ((1 : ℝ) * Sparse.eval nodeValue641 x + ((1 : ℝ) * Sparse.eval nodeValue642 x + ((1 : ℝ) * Sparse.eval nodeValue653 x + ((1 : ℝ) * Sparse.eval nodeValue1294 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow1425 : Integer.Sparse Master := [(Sum.inr 638, 2), (Sum.inr 641, 1), (Sum.inr 642, 1), (Sum.inr 653, 1), (Sum.inr 1294, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1425 : Integer.Sparse.reindex keyMap MixedData.row1425 = numericRow1425 := by decide +kernel

theorem numericCheck1425 (x : Master → ℝ) : Integer.Sparse.eval numericRow1425 x =
    (1 : ℝ) * reducedSource1425 x := by
  norm_num [numericRow1425, reducedSource1425, Integer.Sparse.eval, Sparse.eval, nodeValue638, nodeValue641, nodeValue642, nodeValue653, nodeValue1294, nodeValue4092]

noncomputable def reducedSource1426 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1287 x + ((2 : ℝ) * Sparse.eval nodeValue2584 x + ((1 : ℝ) * Sparse.eval nodeValue2685 x + ((2 : ℝ) * Sparse.eval nodeValue2761 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))

def numericRow1426 : Integer.Sparse Master := [(Sum.inr 1287, 1), (Sum.inr 2584, 2), (Sum.inr 2685, 1), (Sum.inr 2761, 2), (Sum.inr 4082, -1)]

theorem reindexCheck1426 : Integer.Sparse.reindex keyMap MixedData.row1426 = numericRow1426 := by decide +kernel

theorem numericCheck1426 (x : Master → ℝ) : Integer.Sparse.eval numericRow1426 x =
    (1 : ℝ) * reducedSource1426 x := by
  norm_num [numericRow1426, reducedSource1426, Integer.Sparse.eval, Sparse.eval, nodeValue1287, nodeValue2584, nodeValue2685, nodeValue2761, nodeValue4082]

noncomputable def reducedSource1427 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1230 x + ((1 : ℝ) * Sparse.eval nodeValue2505 x + ((1 : ℝ) * Sparse.eval nodeValue2551 x + ((1 : ℝ) * Sparse.eval nodeValue2705 x + ((1 : ℝ) * Sparse.eval nodeValue2729 x + ((1 : ℝ) * Sparse.eval nodeValue2736 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0))))))

def numericRow1427 : Integer.Sparse Master := [(Sum.inr 1230, 1), (Sum.inr 2505, 1), (Sum.inr 2551, 1), (Sum.inr 2705, 1), (Sum.inr 2729, 1), (Sum.inr 2736, 1), (Sum.inr 4088, -1)]

theorem reindexCheck1427 : Integer.Sparse.reindex keyMap MixedData.row1427 = numericRow1427 := by decide +kernel

theorem numericCheck1427 (x : Master → ℝ) : Integer.Sparse.eval numericRow1427 x =
    (1 : ℝ) * reducedSource1427 x := by
  norm_num [numericRow1427, reducedSource1427, Integer.Sparse.eval, Sparse.eval, nodeValue1230, nodeValue2505, nodeValue2551, nodeValue2705, nodeValue2729, nodeValue2736, nodeValue4088]

noncomputable def reducedSource1428 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4150 x + ((1 : ℝ) * Sparse.eval nodeValue4151 x + ((2 : ℝ) * Sparse.eval nodeValue4155 x + ((1 : ℝ) * Sparse.eval nodeValue4173 x + ((1 : ℝ) * Sparse.eval nodeValue4527 x + ((2 : ℝ) * Sparse.eval nodeValue4530 x + ((1 : ℝ) * Sparse.eval nodeValue4542 x + ((1 : ℝ) * Sparse.eval nodeValue4544 x + ((1 : ℝ) * Sparse.eval nodeValue4551 x + ((2 : ℝ) * Sparse.eval nodeValue4554 x + ((2 : ℝ) * Sparse.eval nodeValue4590 x + ((2 : ℝ) * Sparse.eval nodeValue4591 x + ((2 : ℝ) * Sparse.eval nodeValue4593 x + ((1 : ℝ) * Sparse.eval nodeValue4601 x + ((2 : ℝ) * Sparse.eval nodeValue4603 x + ((2 : ℝ) * Sparse.eval nodeValue4606 x + ((1 : ℝ) * Sparse.eval nodeValue4618 x + ((1 : ℝ) * Sparse.eval nodeValue5104 x + ((1 : ℝ) * Sparse.eval nodeValue5137 x + ((2 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5273 x + 0))))))))))))))))))))

def numericRow1428 : Integer.Sparse Master := [(Sum.inr 1129, -1), (Sum.inr 1136, -1), (Sum.inr 1139, -2), (Sum.inr 1235, -1), (Sum.inr 1240, -2), (Sum.inr 1293, -1), (Sum.inr 2556, -1), (Sum.inr 2723, -2), (Sum.inr 3263, -1), (Sum.inr 3273, -1), (Sum.inr 3274, -2), (Sum.inr 3292, -1), (Sum.inr 3299, -2), (Sum.inr 3304, -1), (Sum.inr 3521, -1), (Sum.inr 3544, -2), (Sum.inr 4150, 4), (Sum.inr 4151, 4), (Sum.inr 4155, 8), (Sum.inr 4173, 4), (Sum.inr 4527, 4), (Sum.inr 4530, 8), (Sum.inr 4542, 4), (Sum.inr 4590, 8), (Sum.inr 4591, 8), (Sum.inr 4593, 8), (Sum.inr 4603, 8)]

theorem reindexCheck1428 : Integer.Sparse.reindex keyMap MixedData.row1428 = numericRow1428 := by decide +kernel

theorem numericCheck1428 (x : Master → ℝ) : Integer.Sparse.eval numericRow1428 x =
    (4 : ℝ) * reducedSource1428 x := by
  norm_num [numericRow1428, reducedSource1428, Integer.Sparse.eval, Sparse.eval, nodeValue4150, nodeValue4151, nodeValue4155, nodeValue4173, nodeValue4527, nodeValue4530, nodeValue4542, nodeValue4544, nodeValue4551, nodeValue4554, nodeValue4590, nodeValue4591, nodeValue4593, nodeValue4601, nodeValue4603, nodeValue4606, nodeValue4618, nodeValue5104, nodeValue5137, nodeValue5259, nodeValue5273]
  ring

noncomputable def reducedSource1429 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue578 x + ((1 : ℝ) * Sparse.eval nodeValue579 x + ((2 : ℝ) * Sparse.eval nodeValue583 x + ((1 : ℝ) * Sparse.eval nodeValue601 x + ((1 : ℝ) * Sparse.eval nodeValue1111 x + ((2 : ℝ) * Sparse.eval nodeValue1114 x + ((1 : ℝ) * Sparse.eval nodeValue1127 x + ((1 : ℝ) * Sparse.eval nodeValue1162 x + ((1 : ℝ) * Sparse.eval nodeValue1163 x + ((2 : ℝ) * Sparse.eval nodeValue1167 x + ((2 : ℝ) * Sparse.eval nodeValue1213 x + ((2 : ℝ) * Sparse.eval nodeValue1215 x + ((2 : ℝ) * Sparse.eval nodeValue1220 x + ((2 : ℝ) * Sparse.eval nodeValue1237 x + ((1 : ℝ) * Sparse.eval nodeValue1265 x + ((2 : ℝ) * Sparse.eval nodeValue1266 x + ((1 : ℝ) * Sparse.eval nodeValue1298 x + ((1 : ℝ) * Sparse.eval nodeValue2936 x + ((1 : ℝ) * Sparse.eval nodeValue3000 x + ((2 : ℝ) * Sparse.eval nodeValue3088 x + ((1 : ℝ) * Sparse.eval nodeValue3111 x + 0))))))))))))))))))))

def numericRow1429 : Integer.Sparse Master := [(Sum.inl 0, -77), (Sum.inl 5, -120), (Sum.inl 6, 15), (Sum.inl 2, 120), (Sum.inl 7, 80), (Sum.inl 8, 160), (Sum.inl 1, -130), (Sum.inr 578, 1440), (Sum.inr 579, 1440), (Sum.inr 583, 2880), (Sum.inr 601, 1440), (Sum.inr 1111, 1440), (Sum.inr 1114, 2880), (Sum.inr 1127, 1440), (Sum.inr 1213, 2880), (Sum.inr 1215, 2880), (Sum.inr 1220, 2880), (Sum.inr 1237, 2880)]

theorem reindexCheck1429 : Integer.Sparse.reindex keyMap MixedData.row1429 = numericRow1429 := by decide +kernel

theorem numericCheck1429 (x : Master → ℝ) : Integer.Sparse.eval numericRow1429 x =
    (1440 : ℝ) * reducedSource1429 x := by
  norm_num [numericRow1429, reducedSource1429, Integer.Sparse.eval, Sparse.eval, nodeValue578, nodeValue579, nodeValue583, nodeValue601, nodeValue1111, nodeValue1114, nodeValue1127, nodeValue1162, nodeValue1163, nodeValue1167, nodeValue1213, nodeValue1215, nodeValue1220, nodeValue1237, nodeValue1265, nodeValue1266, nodeValue1298, nodeValue2936, nodeValue3000, nodeValue3088, nodeValue3111]
  ring

noncomputable def reducedSource1430 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1504 x + ((1 : ℝ) * Sparse.eval nodeValue1505 x + ((1 : ℝ) * Sparse.eval nodeValue1508 x + ((2 : ℝ) * Sparse.eval nodeValue1515 x + ((1 : ℝ) * Sparse.eval nodeValue3255 x + ((1 : ℝ) * Sparse.eval nodeValue3257 x + ((2 : ℝ) * Sparse.eval nodeValue3261 x + ((1 : ℝ) * Sparse.eval nodeValue3263 x + ((1 : ℝ) * Sparse.eval nodeValue3273 x + ((2 : ℝ) * Sparse.eval nodeValue3274 x + ((2 : ℝ) * Sparse.eval nodeValue3290 x + ((2 : ℝ) * Sparse.eval nodeValue3291 x + ((1 : ℝ) * Sparse.eval nodeValue3292 x + ((2 : ℝ) * Sparse.eval nodeValue3294 x + ((2 : ℝ) * Sparse.eval nodeValue3297 x + ((2 : ℝ) * Sparse.eval nodeValue3299 x + ((1 : ℝ) * Sparse.eval nodeValue3304 x + ((1 : ℝ) * Sparse.eval nodeValue3483 x + ((1 : ℝ) * Sparse.eval nodeValue3521 x + ((2 : ℝ) * Sparse.eval nodeValue3544 x + ((1 : ℝ) * Sparse.eval nodeValue3546 x + 0))))))))))))))))))))

def numericRow1430 : Integer.Sparse Master := [(Sum.inr 1504, 1), (Sum.inr 1505, 1), (Sum.inr 1508, 1), (Sum.inr 1515, 2), (Sum.inr 3255, 1), (Sum.inr 3257, 1), (Sum.inr 3261, 2), (Sum.inr 3263, 1), (Sum.inr 3273, 1), (Sum.inr 3274, 2), (Sum.inr 3290, 2), (Sum.inr 3291, 2), (Sum.inr 3292, 1), (Sum.inr 3294, 2), (Sum.inr 3297, 2), (Sum.inr 3299, 2), (Sum.inr 3304, 1), (Sum.inr 3521, 1), (Sum.inr 3544, 2)]

theorem reindexCheck1430 : Integer.Sparse.reindex keyMap MixedData.row1430 = numericRow1430 := by decide +kernel

theorem numericCheck1430 (x : Master → ℝ) : Integer.Sparse.eval numericRow1430 x =
    (1 : ℝ) * reducedSource1430 x := by
  norm_num [numericRow1430, reducedSource1430, Integer.Sparse.eval, Sparse.eval, nodeValue1504, nodeValue1505, nodeValue1508, nodeValue1515, nodeValue3255, nodeValue3257, nodeValue3261, nodeValue3263, nodeValue3273, nodeValue3274, nodeValue3290, nodeValue3291, nodeValue3292, nodeValue3294, nodeValue3297, nodeValue3299, nodeValue3304, nodeValue3483, nodeValue3521, nodeValue3544, nodeValue3546]

noncomputable def reducedSource1431 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue625 x + ((1 : ℝ) * Sparse.eval nodeValue630 x + ((2 : ℝ) * Sparse.eval nodeValue632 x + ((1 : ℝ) * Sparse.eval nodeValue640 x + ((1 : ℝ) * Sparse.eval nodeValue1240 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow1431 : Integer.Sparse Master := [(Sum.inr 625, 1), (Sum.inr 630, 1), (Sum.inr 632, 2), (Sum.inr 640, 1), (Sum.inr 1240, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1431 : Integer.Sparse.reindex keyMap MixedData.row1431 = numericRow1431 := by decide +kernel

theorem numericCheck1431 (x : Master → ℝ) : Integer.Sparse.eval numericRow1431 x =
    (1 : ℝ) * reducedSource1431 x := by
  norm_num [numericRow1431, reducedSource1431, Integer.Sparse.eval, Sparse.eval, nodeValue625, nodeValue630, nodeValue632, nodeValue640, nodeValue1240, nodeValue4091]

noncomputable def reducedSource1432 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1150 x + ((2 : ℝ) * Sparse.eval nodeValue1152 x + ((1 : ℝ) * Sparse.eval nodeValue1158 x + ((1 : ℝ) * Sparse.eval nodeValue1240 x + ((1 : ℝ) * Sparse.eval nodeValue2556 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow1432 : Integer.Sparse Master := [(Sum.inr 1150, 1), (Sum.inr 1152, 2), (Sum.inr 1158, 1), (Sum.inr 1240, 1), (Sum.inr 2556, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1432 : Integer.Sparse.reindex keyMap MixedData.row1432 = numericRow1432 := by decide +kernel

theorem numericCheck1432 (x : Master → ℝ) : Integer.Sparse.eval numericRow1432 x =
    (1 : ℝ) * reducedSource1432 x := by
  norm_num [numericRow1432, reducedSource1432, Integer.Sparse.eval, Sparse.eval, nodeValue1150, nodeValue1152, nodeValue1158, nodeValue1240, nodeValue2556, nodeValue4091]

noncomputable def reducedSource1433 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4143 x + ((1 : ℝ) * Sparse.eval nodeValue4144 x + ((2 : ℝ) * Sparse.eval nodeValue4145 x + ((1 : ℝ) * Sparse.eval nodeValue4175 x + ((1 : ℝ) * Sparse.eval nodeValue4516 x + ((1 : ℝ) * Sparse.eval nodeValue4517 x + ((2 : ℝ) * Sparse.eval nodeValue4518 x + ((1 : ℝ) * Sparse.eval nodeValue4523 x + ((2 : ℝ) * Sparse.eval nodeValue4524 x + ((1 : ℝ) * Sparse.eval nodeValue4544 x + ((1 : ℝ) * Sparse.eval nodeValue4601 x + ((2 : ℝ) * Sparse.eval nodeValue4602 x + ((2 : ℝ) * Sparse.eval nodeValue4606 x + ((2 : ℝ) * Sparse.eval nodeValue4608 x + ((2 : ℝ) * Sparse.eval nodeValue4612 x + ((1 : ℝ) * Sparse.eval nodeValue4622 x + ((2 : ℝ) * Sparse.eval nodeValue4624 x + ((1 : ℝ) * Sparse.eval nodeValue5148 x + ((1 : ℝ) * Sparse.eval nodeValue5203 x + ((1 : ℝ) * Sparse.eval nodeValue5292 x + ((2 : ℝ) * Sparse.eval nodeValue5293 x + 0))))))))))))))))))))

def numericRow1433 : Integer.Sparse Master := [(Sum.inl 0, 256), (Sum.inl 6, 5), (Sum.inl 2, -65), (Sum.inl 7, 80), (Sum.inl 8, -160), (Sum.inl 3, 80), (Sum.inl 1, -370), (Sum.inr 571, -4320), (Sum.inr 572, -4320), (Sum.inr 573, -8640), (Sum.inr 603, -4320), (Sum.inr 1100, -4320), (Sum.inr 1101, -4320), (Sum.inr 1102, -8640), (Sum.inr 1107, -4320), (Sum.inr 1108, -8640), (Sum.inr 1129, -4320), (Sum.inr 1235, -4320), (Sum.inr 1236, -8640), (Sum.inr 1240, -8640), (Sum.inr 1242, -8640), (Sum.inr 1246, -8640), (Sum.inr 1491, -4320), (Sum.inr 1492, -4320), (Sum.inr 1493, -8640), (Sum.inr 1517, -4320), (Sum.inr 2884, -4320), (Sum.inr 3234, -4320), (Sum.inr 3235, -4320), (Sum.inr 3236, -8640), (Sum.inr 3250, -4320), (Sum.inr 3251, -8640), (Sum.inr 3263, -4320), (Sum.inr 3292, -4320), (Sum.inr 3293, -8640), (Sum.inr 3299, -8640), (Sum.inr 3300, -8640), (Sum.inr 3301, -8640), (Sum.inr 3307, -4320), (Sum.inr 3309, -8640), (Sum.inr 3621, -4320), (Sum.inr 3622, -4320), (Sum.inr 3627, -8640)]

theorem reindexCheck1433 : Integer.Sparse.reindex keyMap MixedData.row1433 = numericRow1433 := by decide +kernel

theorem numericCheck1433 (x : Master → ℝ) : Integer.Sparse.eval numericRow1433 x =
    (17280 : ℝ) * reducedSource1433 x := by
  norm_num [numericRow1433, reducedSource1433, Integer.Sparse.eval, Sparse.eval, nodeValue4143, nodeValue4144, nodeValue4145, nodeValue4175, nodeValue4516, nodeValue4517, nodeValue4518, nodeValue4523, nodeValue4524, nodeValue4544, nodeValue4601, nodeValue4602, nodeValue4606, nodeValue4608, nodeValue4612, nodeValue4622, nodeValue4624, nodeValue5148, nodeValue5203, nodeValue5292, nodeValue5293]
  ring

noncomputable def reducedSource1434 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue571 x + ((1 : ℝ) * Sparse.eval nodeValue572 x + ((2 : ℝ) * Sparse.eval nodeValue573 x + ((1 : ℝ) * Sparse.eval nodeValue603 x + ((1 : ℝ) * Sparse.eval nodeValue1100 x + ((1 : ℝ) * Sparse.eval nodeValue1101 x + ((2 : ℝ) * Sparse.eval nodeValue1102 x + ((1 : ℝ) * Sparse.eval nodeValue1107 x + ((2 : ℝ) * Sparse.eval nodeValue1108 x + ((1 : ℝ) * Sparse.eval nodeValue1129 x + ((1 : ℝ) * Sparse.eval nodeValue1235 x + ((2 : ℝ) * Sparse.eval nodeValue1236 x + ((2 : ℝ) * Sparse.eval nodeValue1240 x + ((2 : ℝ) * Sparse.eval nodeValue1242 x + ((2 : ℝ) * Sparse.eval nodeValue1246 x + ((1 : ℝ) * Sparse.eval nodeValue1299 x + ((2 : ℝ) * Sparse.eval nodeValue1301 x + ((1 : ℝ) * Sparse.eval nodeValue2884 x + ((1 : ℝ) * Sparse.eval nodeValue2927 x + ((1 : ℝ) * Sparse.eval nodeValue3100 x + ((2 : ℝ) * Sparse.eval nodeValue3102 x + 0))))))))))))))))))))

def numericRow1434 : Integer.Sparse Master := [(Sum.inl 0, -256), (Sum.inl 6, -5), (Sum.inl 2, 65), (Sum.inl 7, -80), (Sum.inl 8, 160), (Sum.inl 3, -80), (Sum.inl 1, 370), (Sum.inr 571, 4320), (Sum.inr 572, 4320), (Sum.inr 573, 8640), (Sum.inr 603, 4320), (Sum.inr 1100, 4320), (Sum.inr 1101, 4320), (Sum.inr 1102, 8640), (Sum.inr 1107, 4320), (Sum.inr 1108, 8640), (Sum.inr 1129, 4320), (Sum.inr 1235, 4320), (Sum.inr 1236, 8640), (Sum.inr 1240, 8640), (Sum.inr 1242, 8640), (Sum.inr 1246, 8640), (Sum.inr 2884, 4320)]

theorem reindexCheck1434 : Integer.Sparse.reindex keyMap MixedData.row1434 = numericRow1434 := by decide +kernel

theorem numericCheck1434 (x : Master → ℝ) : Integer.Sparse.eval numericRow1434 x =
    (4320 : ℝ) * reducedSource1434 x := by
  norm_num [numericRow1434, reducedSource1434, Integer.Sparse.eval, Sparse.eval, nodeValue571, nodeValue572, nodeValue573, nodeValue603, nodeValue1100, nodeValue1101, nodeValue1102, nodeValue1107, nodeValue1108, nodeValue1129, nodeValue1235, nodeValue1236, nodeValue1240, nodeValue1242, nodeValue1246, nodeValue1299, nodeValue1301, nodeValue2884, nodeValue2927, nodeValue3100, nodeValue3102]
  ring

noncomputable def reducedSource1435 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue980 x + ((1 : ℝ) * Sparse.eval nodeValue1004 x + ((2 : ℝ) * Sparse.eval nodeValue1005 x + ((1 : ℝ) * Sparse.eval nodeValue1086 x + ((1 : ℝ) * Sparse.eval nodeValue1180 x + ((1 : ℝ) * Sparse.eval nodeValue1188 x + ((2 : ℝ) * Sparse.eval nodeValue1189 x + ((1 : ℝ) * Sparse.eval nodeValue1200 x + ((2 : ℝ) * Sparse.eval nodeValue1201 x + ((2 : ℝ) * Sparse.eval nodeValue1213 x + ((1 : ℝ) * Sparse.eval nodeValue1216 x + ((2 : ℝ) * Sparse.eval nodeValue1236 x + ((2 : ℝ) * Sparse.eval nodeValue1237 x + ((1 : ℝ) * Sparse.eval nodeValue1240 x + ((2 : ℝ) * Sparse.eval nodeValue1241 x + ((2 : ℝ) * Sparse.eval nodeValue1301 x + ((1 : ℝ) * Sparse.eval nodeValue1305 x + ((1 : ℝ) * Sparse.eval nodeValue1370 x + ((1 : ℝ) * Sparse.eval nodeValue1386 x + ((2 : ℝ) * Sparse.eval nodeValue1411 x + ((1 : ℝ) * Sparse.eval nodeValue1414 x + 0))))))))))))))))))))

def numericRow1435 : Integer.Sparse Master := [(Sum.inl 0, -212), (Sum.inl 5, 340), (Sum.inl 6, -95), (Sum.inl 2, -120), (Sum.inl 7, 80), (Sum.inl 35, -80), (Sum.inl 8, 160), (Sum.inl 52, -160), (Sum.inl 1, -105), (Sum.inr 980, 4320), (Sum.inr 1005, 8640), (Sum.inr 1180, 4320), (Sum.inr 1188, 4320), (Sum.inr 1189, 8640), (Sum.inr 1200, 4320), (Sum.inr 1201, 8640), (Sum.inr 1213, 8640), (Sum.inr 1216, 4320), (Sum.inr 1236, 8640), (Sum.inr 1237, 8640), (Sum.inr 1240, 4320), (Sum.inr 1241, 8640), (Sum.inr 1370, 4320)]

theorem reindexCheck1435 : Integer.Sparse.reindex keyMap MixedData.row1435 = numericRow1435 := by decide +kernel

theorem numericCheck1435 (x : Master → ℝ) : Integer.Sparse.eval numericRow1435 x =
    (4320 : ℝ) * reducedSource1435 x := by
  norm_num [numericRow1435, reducedSource1435, Integer.Sparse.eval, Sparse.eval, nodeValue980, nodeValue1004, nodeValue1005, nodeValue1086, nodeValue1180, nodeValue1188, nodeValue1189, nodeValue1200, nodeValue1201, nodeValue1213, nodeValue1216, nodeValue1236, nodeValue1237, nodeValue1240, nodeValue1241, nodeValue1301, nodeValue1305, nodeValue1370, nodeValue1386, nodeValue1411, nodeValue1414]
  ring

noncomputable def reducedSource1436 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4152 x + ((1 : ℝ) * Sparse.eval nodeValue4153 x + ((1 : ℝ) * Sparse.eval nodeValue4154 x + ((1 : ℝ) * Sparse.eval nodeValue4158 x + ((1 : ℝ) * Sparse.eval nodeValue4176 x + ((1 : ℝ) * Sparse.eval nodeValue4528 x + ((1 : ℝ) * Sparse.eval nodeValue4529 x + ((1 : ℝ) * Sparse.eval nodeValue4533 x + ((1 : ℝ) * Sparse.eval nodeValue4541 x + ((1 : ℝ) * Sparse.eval nodeValue4545 x + ((1 : ℝ) * Sparse.eval nodeValue4546 x + ((1 : ℝ) * Sparse.eval nodeValue4549 x + ((1 : ℝ) * Sparse.eval nodeValue4553 x + ((1 : ℝ) * Sparse.eval nodeValue4589 x + ((1 : ℝ) * Sparse.eval nodeValue4591 x + ((1 : ℝ) * Sparse.eval nodeValue4592 x + ((1 : ℝ) * Sparse.eval nodeValue4599 x + ((1 : ℝ) * Sparse.eval nodeValue4602 x + ((1 : ℝ) * Sparse.eval nodeValue4603 x + ((2 : ℝ) * Sparse.eval nodeValue4607 x + ((1 : ℝ) * Sparse.eval nodeValue4608 x + ((1 : ℝ) * Sparse.eval nodeValue4612 x + ((1 : ℝ) * Sparse.eval nodeValue4616 x + ((1 : ℝ) * Sparse.eval nodeValue4619 x + ((1 : ℝ) * Sparse.eval nodeValue5101 x + ((1 : ℝ) * Sparse.eval nodeValue5134 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + 0))))))))))))))))))))))))))))

def numericRow1436 : Integer.Sparse Master := [(Sum.inr 1126, -1), (Sum.inr 1131, -1), (Sum.inr 1134, -1), (Sum.inr 1138, -1), (Sum.inr 1236, -1), (Sum.inr 1242, -1), (Sum.inr 1246, -1), (Sum.inr 1294, -1), (Sum.inr 2553, -1), (Sum.inr 2722, -1), (Sum.inr 2739, -1), (Sum.inr 3256, -1), (Sum.inr 3264, -1), (Sum.inr 3265, -1), (Sum.inr 3270, -1), (Sum.inr 3293, -1), (Sum.inr 3300, -1), (Sum.inr 3301, -1), (Sum.inr 3305, -1), (Sum.inr 3514, -1), (Sum.inr 3533, -1), (Sum.inr 3534, -1), (Sum.inr 4152, 4), (Sum.inr 4153, 4), (Sum.inr 4154, 4), (Sum.inr 4158, 4), (Sum.inr 4176, 4), (Sum.inr 4528, 4), (Sum.inr 4529, 4), (Sum.inr 4533, 4), (Sum.inr 4545, 4), (Sum.inr 4589, 4), (Sum.inr 4591, 4), (Sum.inr 4592, 4), (Sum.inr 4599, 4), (Sum.inr 4603, 4), (Sum.inr 4607, 8), (Sum.inr 4616, 4)]

theorem reindexCheck1436 : Integer.Sparse.reindex keyMap MixedData.row1436 = numericRow1436 := by decide +kernel

theorem numericCheck1436 (x : Master → ℝ) : Integer.Sparse.eval numericRow1436 x =
    (4 : ℝ) * reducedSource1436 x := by
  norm_num [numericRow1436, reducedSource1436, Integer.Sparse.eval, Sparse.eval, nodeValue4152, nodeValue4153, nodeValue4154, nodeValue4158, nodeValue4176, nodeValue4528, nodeValue4529, nodeValue4533, nodeValue4541, nodeValue4545, nodeValue4546, nodeValue4549, nodeValue4553, nodeValue4589, nodeValue4591, nodeValue4592, nodeValue4599, nodeValue4602, nodeValue4603, nodeValue4607, nodeValue4608, nodeValue4612, nodeValue4616, nodeValue4619, nodeValue5101, nodeValue5134, nodeValue5258, nodeValue5271, nodeValue5274]
  ring

noncomputable def reducedSource1437 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue580 x + ((1 : ℝ) * Sparse.eval nodeValue581 x + ((1 : ℝ) * Sparse.eval nodeValue582 x + ((1 : ℝ) * Sparse.eval nodeValue586 x + ((1 : ℝ) * Sparse.eval nodeValue604 x + ((1 : ℝ) * Sparse.eval nodeValue1112 x + ((1 : ℝ) * Sparse.eval nodeValue1113 x + ((1 : ℝ) * Sparse.eval nodeValue1117 x + ((1 : ℝ) * Sparse.eval nodeValue1130 x + ((1 : ℝ) * Sparse.eval nodeValue1164 x + ((1 : ℝ) * Sparse.eval nodeValue1165 x + ((1 : ℝ) * Sparse.eval nodeValue1166 x + ((1 : ℝ) * Sparse.eval nodeValue1172 x + ((1 : ℝ) * Sparse.eval nodeValue1216 x + ((1 : ℝ) * Sparse.eval nodeValue1217 x + ((1 : ℝ) * Sparse.eval nodeValue1219 x + ((1 : ℝ) * Sparse.eval nodeValue1241 x + ((1 : ℝ) * Sparse.eval nodeValue1260 x + ((1 : ℝ) * Sparse.eval nodeValue1261 x + ((1 : ℝ) * Sparse.eval nodeValue1262 x + ((1 : ℝ) * Sparse.eval nodeValue1267 x + ((1 : ℝ) * Sparse.eval nodeValue1269 x + ((1 : ℝ) * Sparse.eval nodeValue1274 x + ((1 : ℝ) * Sparse.eval nodeValue1291 x + ((1 : ℝ) * Sparse.eval nodeValue1302 x + ((1 : ℝ) * Sparse.eval nodeValue2937 x + ((1 : ℝ) * Sparse.eval nodeValue3001 x + ((1 : ℝ) * Sparse.eval nodeValue3089 x + ((1 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3112 x + 0)))))))))))))))))))))))))))))

def numericRow1437 : Integer.Sparse Master := [(Sum.inl 0, -210), (Sum.inl 5, -200), (Sum.inl 6, 30), (Sum.inl 2, -30), (Sum.inl 7, 320), (Sum.inl 35, 160), (Sum.inl 8, 160), (Sum.inl 3, 160), (Sum.inl 1, 150), (Sum.inr 580, 2880), (Sum.inr 581, 2880), (Sum.inr 582, 2880), (Sum.inr 586, 2880), (Sum.inr 604, 2880), (Sum.inr 1112, 2880), (Sum.inr 1113, 2880), (Sum.inr 1117, 2880), (Sum.inr 1130, 2880), (Sum.inr 1216, 2880), (Sum.inr 1217, 2880), (Sum.inr 1219, 2880), (Sum.inr 1241, 2880), (Sum.inr 1260, 2880), (Sum.inr 1261, 2880), (Sum.inr 1262, 2880), (Sum.inr 1291, 2880)]

theorem reindexCheck1437 : Integer.Sparse.reindex keyMap MixedData.row1437 = numericRow1437 := by decide +kernel

theorem numericCheck1437 (x : Master → ℝ) : Integer.Sparse.eval numericRow1437 x =
    (2880 : ℝ) * reducedSource1437 x := by
  norm_num [numericRow1437, reducedSource1437, Integer.Sparse.eval, Sparse.eval, nodeValue580, nodeValue581, nodeValue582, nodeValue586, nodeValue604, nodeValue1112, nodeValue1113, nodeValue1117, nodeValue1130, nodeValue1164, nodeValue1165, nodeValue1166, nodeValue1172, nodeValue1216, nodeValue1217, nodeValue1219, nodeValue1241, nodeValue1260, nodeValue1261, nodeValue1262, nodeValue1267, nodeValue1269, nodeValue1274, nodeValue1291, nodeValue1302, nodeValue2937, nodeValue3001, nodeValue3089, nodeValue3109, nodeValue3112]
  ring

noncomputable def reducedSource1438 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1510 x + ((1 : ℝ) * Sparse.eval nodeValue1511 x + ((1 : ℝ) * Sparse.eval nodeValue1512 x + ((1 : ℝ) * Sparse.eval nodeValue1514 x + ((1 : ℝ) * Sparse.eval nodeValue1522 x + ((1 : ℝ) * Sparse.eval nodeValue3256 x + ((1 : ℝ) * Sparse.eval nodeValue3258 x + ((1 : ℝ) * Sparse.eval nodeValue3259 x + ((1 : ℝ) * Sparse.eval nodeValue3260 x + ((1 : ℝ) * Sparse.eval nodeValue3264 x + ((1 : ℝ) * Sparse.eval nodeValue3265 x + ((1 : ℝ) * Sparse.eval nodeValue3267 x + ((1 : ℝ) * Sparse.eval nodeValue3270 x + ((1 : ℝ) * Sparse.eval nodeValue3288 x + ((1 : ℝ) * Sparse.eval nodeValue3289 x + ((1 : ℝ) * Sparse.eval nodeValue3291 x + ((1 : ℝ) * Sparse.eval nodeValue3293 x + ((1 : ℝ) * Sparse.eval nodeValue3294 x + ((1 : ℝ) * Sparse.eval nodeValue3295 x + ((2 : ℝ) * Sparse.eval nodeValue3296 x + ((1 : ℝ) * Sparse.eval nodeValue3300 x + ((1 : ℝ) * Sparse.eval nodeValue3301 x + ((1 : ℝ) * Sparse.eval nodeValue3303 x + ((1 : ℝ) * Sparse.eval nodeValue3305 x + ((1 : ℝ) * Sparse.eval nodeValue3470 x + ((1 : ℝ) * Sparse.eval nodeValue3514 x + ((1 : ℝ) * Sparse.eval nodeValue3533 x + ((1 : ℝ) * Sparse.eval nodeValue3534 x + ((1 : ℝ) * Sparse.eval nodeValue3547 x + 0))))))))))))))))))))))))))))

def numericRow1438 : Integer.Sparse Master := [(Sum.inr 1510, 1), (Sum.inr 1511, 1), (Sum.inr 1512, 1), (Sum.inr 1514, 1), (Sum.inr 1522, 1), (Sum.inr 3256, 1), (Sum.inr 3258, 1), (Sum.inr 3259, 1), (Sum.inr 3260, 1), (Sum.inr 3264, 1), (Sum.inr 3265, 1), (Sum.inr 3267, 1), (Sum.inr 3270, 1), (Sum.inr 3288, 1), (Sum.inr 3289, 1), (Sum.inr 3291, 1), (Sum.inr 3293, 1), (Sum.inr 3294, 1), (Sum.inr 3295, 1), (Sum.inr 3296, 2), (Sum.inr 3300, 1), (Sum.inr 3301, 1), (Sum.inr 3303, 1), (Sum.inr 3305, 1), (Sum.inr 3514, 1), (Sum.inr 3533, 1), (Sum.inr 3534, 1)]

theorem reindexCheck1438 : Integer.Sparse.reindex keyMap MixedData.row1438 = numericRow1438 := by decide +kernel

theorem numericCheck1438 (x : Master → ℝ) : Integer.Sparse.eval numericRow1438 x =
    (1 : ℝ) * reducedSource1438 x := by
  norm_num [numericRow1438, reducedSource1438, Integer.Sparse.eval, Sparse.eval, nodeValue1510, nodeValue1511, nodeValue1512, nodeValue1514, nodeValue1522, nodeValue3256, nodeValue3258, nodeValue3259, nodeValue3260, nodeValue3264, nodeValue3265, nodeValue3267, nodeValue3270, nodeValue3288, nodeValue3289, nodeValue3291, nodeValue3293, nodeValue3294, nodeValue3295, nodeValue3296, nodeValue3300, nodeValue3301, nodeValue3303, nodeValue3305, nodeValue3470, nodeValue3514, nodeValue3533, nodeValue3534, nodeValue3547]

noncomputable def reducedSource1439 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue623 x + ((1 : ℝ) * Sparse.eval nodeValue626 x + ((1 : ℝ) * Sparse.eval nodeValue627 x + ((1 : ℝ) * Sparse.eval nodeValue631 x + ((1 : ℝ) * Sparse.eval nodeValue638 x + ((1 : ℝ) * Sparse.eval nodeValue1236 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1439 : Integer.Sparse Master := [(Sum.inr 623, 1), (Sum.inr 626, 1), (Sum.inr 627, 1), (Sum.inr 631, 1), (Sum.inr 638, 1), (Sum.inr 1236, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1439 : Integer.Sparse.reindex keyMap MixedData.row1439 = numericRow1439 := by decide +kernel

theorem numericCheck1439 (x : Master → ℝ) : Integer.Sparse.eval numericRow1439 x =
    (1 : ℝ) * reducedSource1439 x := by
  norm_num [numericRow1439, reducedSource1439, Integer.Sparse.eval, Sparse.eval, nodeValue623, nodeValue626, nodeValue627, nodeValue631, nodeValue638, nodeValue1236, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
