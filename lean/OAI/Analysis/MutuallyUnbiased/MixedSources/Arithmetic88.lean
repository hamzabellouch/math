import OAI.Analysis.MutuallyUnbiased.MixedData.Source11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values9
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1408 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1288 x + ((2 : ℝ) * Sparse.eval nodeValue2585 x + ((1 : ℝ) * Sparse.eval nodeValue2686 x + ((1 : ℝ) * Sparse.eval nodeValue2771 x + ((1 : ℝ) * Sparse.eval nodeValue2779 x + ((-1 : ℝ) * Sparse.eval nodeValue4089 x + 0)))))

def numericRow1408 : Integer.Sparse Master := [(Sum.inr 1288, 1), (Sum.inr 2585, 2), (Sum.inr 2686, 1), (Sum.inr 2771, 1), (Sum.inr 2779, 1), (Sum.inr 4089, -1)]

theorem reindexCheck1408 : Integer.Sparse.reindex keyMap MixedData.row1408 = numericRow1408 := by decide +kernel

theorem numericCheck1408 (x : Master → ℝ) : Integer.Sparse.eval numericRow1408 x =
    (1 : ℝ) * reducedSource1408 x := by
  norm_num [numericRow1408, reducedSource1408, Integer.Sparse.eval, Sparse.eval, nodeValue1288, nodeValue2585, nodeValue2686, nodeValue2771, nodeValue2779, nodeValue4089]

noncomputable def reducedSource1409 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4182 x + ((1 : ℝ) * Sparse.eval nodeValue4183 x + ((2 : ℝ) * Sparse.eval nodeValue4185 x + ((2 : ℝ) * Sparse.eval nodeValue4550 x + ((2 : ℝ) * Sparse.eval nodeValue4551 x + ((4 : ℝ) * Sparse.eval nodeValue4553 x + ((2 : ℝ) * Sparse.eval nodeValue4618 x + ((2 : ℝ) * Sparse.eval nodeValue4619 x + ((4 : ℝ) * Sparse.eval nodeValue4623 x + ((2 : ℝ) * Sparse.eval nodeValue4625 x + ((2 : ℝ) * Sparse.eval nodeValue4627 x + ((2 : ℝ) * Sparse.eval nodeValue5168 x + ((1 : ℝ) * Sparse.eval nodeValue5306 x + ((2 : ℝ) * Sparse.eval nodeValue5308 x + 0)))))))))))))

def numericRow1409 : Integer.Sparse Master := [(Sum.inl 0, 57), (Sum.inl 6, -5), (Sum.inl 7, 80), (Sum.inl 1, 300), (Sum.inr 610, -1440), (Sum.inr 611, -720), (Sum.inr 613, -1440), (Sum.inr 1135, -1440), (Sum.inr 1136, -1440), (Sum.inr 1138, -2880), (Sum.inr 1293, -1440), (Sum.inr 1294, -1440), (Sum.inr 1524, -1440), (Sum.inr 1525, -1440), (Sum.inr 1535, -720), (Sum.inr 3269, -1440), (Sum.inr 3270, -2880), (Sum.inr 3273, -1440), (Sum.inr 3304, -1440), (Sum.inr 3305, -1440), (Sum.inr 3308, -2880), (Sum.inr 3310, -1440), (Sum.inr 3311, -1440), (Sum.inr 3603, -1440), (Sum.inr 3623, -720)]

theorem reindexCheck1409 : Integer.Sparse.reindex keyMap MixedData.row1409 = numericRow1409 := by decide +kernel

theorem numericCheck1409 (x : Master → ℝ) : Integer.Sparse.eval numericRow1409 x =
    (2880 : ℝ) * reducedSource1409 x := by
  norm_num [numericRow1409, reducedSource1409, Integer.Sparse.eval, Sparse.eval, nodeValue4182, nodeValue4183, nodeValue4185, nodeValue4550, nodeValue4551, nodeValue4553, nodeValue4618, nodeValue4619, nodeValue4623, nodeValue4625, nodeValue4627, nodeValue5168, nodeValue5306, nodeValue5308]
  ring

noncomputable def reducedSource1410 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue610 x + ((1 : ℝ) * Sparse.eval nodeValue611 x + ((2 : ℝ) * Sparse.eval nodeValue613 x + ((2 : ℝ) * Sparse.eval nodeValue1135 x + ((2 : ℝ) * Sparse.eval nodeValue1136 x + ((4 : ℝ) * Sparse.eval nodeValue1138 x + ((2 : ℝ) * Sparse.eval nodeValue1293 x + ((2 : ℝ) * Sparse.eval nodeValue1294 x + ((4 : ℝ) * Sparse.eval nodeValue1305 x + ((2 : ℝ) * Sparse.eval nodeValue1307 x + ((2 : ℝ) * Sparse.eval nodeValue1311 x + ((2 : ℝ) * Sparse.eval nodeValue2963 x + ((1 : ℝ) * Sparse.eval nodeValue3120 x + ((2 : ℝ) * Sparse.eval nodeValue3124 x + 0)))))))))))))

def numericRow1410 : Integer.Sparse Master := [(Sum.inl 0, -57), (Sum.inl 6, 5), (Sum.inl 7, -80), (Sum.inl 1, -300), (Sum.inr 610, 1440), (Sum.inr 611, 720), (Sum.inr 613, 1440), (Sum.inr 1135, 1440), (Sum.inr 1136, 1440), (Sum.inr 1138, 2880), (Sum.inr 1293, 1440), (Sum.inr 1294, 1440)]

theorem reindexCheck1410 : Integer.Sparse.reindex keyMap MixedData.row1410 = numericRow1410 := by decide +kernel

theorem numericCheck1410 (x : Master → ℝ) : Integer.Sparse.eval numericRow1410 x =
    (720 : ℝ) * reducedSource1410 x := by
  norm_num [numericRow1410, reducedSource1410, Integer.Sparse.eval, Sparse.eval, nodeValue610, nodeValue611, nodeValue613, nodeValue1135, nodeValue1136, nodeValue1138, nodeValue1293, nodeValue1294, nodeValue1305, nodeValue1307, nodeValue1311, nodeValue2963, nodeValue3120, nodeValue3124]
  ring

noncomputable def reducedSource1411 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4172 x + ((1 : ℝ) * Sparse.eval nodeValue4174 x + ((2 : ℝ) * Sparse.eval nodeValue4180 x + ((2 : ℝ) * Sparse.eval nodeValue4541 x + ((2 : ℝ) * Sparse.eval nodeValue4543 x + ((4 : ℝ) * Sparse.eval nodeValue4549 x + ((4 : ℝ) * Sparse.eval nodeValue4602 x + ((2 : ℝ) * Sparse.eval nodeValue4605 x + ((2 : ℝ) * Sparse.eval nodeValue4612 x + ((2 : ℝ) * Sparse.eval nodeValue4622 x + ((2 : ℝ) * Sparse.eval nodeValue4624 x + ((2 : ℝ) * Sparse.eval nodeValue5172 x + ((2 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5307 x + 0)))))))))))))

def numericRow1411 : Integer.Sparse Master := [(Sum.inl 0, 15), (Sum.inl 6, -1), (Sum.inl 7, 16), (Sum.inl 1, -30), (Sum.inr 600, -432), (Sum.inr 602, -216), (Sum.inr 608, -432), (Sum.inr 1126, -432), (Sum.inr 1128, -432), (Sum.inr 1134, -864), (Sum.inr 1236, -864), (Sum.inr 1239, -432), (Sum.inr 1246, -432), (Sum.inr 1507, -432), (Sum.inr 1509, -216), (Sum.inr 1519, -432), (Sum.inr 2184, -432), (Sum.inr 2226, -432), (Sum.inr 3256, -432), (Sum.inr 3265, -864), (Sum.inr 3293, -864), (Sum.inr 3301, -432), (Sum.inr 3307, -432), (Sum.inr 3309, -432), (Sum.inr 3613, -432), (Sum.inr 3632, -432)]

theorem reindexCheck1411 : Integer.Sparse.reindex keyMap MixedData.row1411 = numericRow1411 := by decide +kernel

theorem numericCheck1411 (x : Master → ℝ) : Integer.Sparse.eval numericRow1411 x =
    (864 : ℝ) * reducedSource1411 x := by
  norm_num [numericRow1411, reducedSource1411, Integer.Sparse.eval, Sparse.eval, nodeValue4172, nodeValue4174, nodeValue4180, nodeValue4541, nodeValue4543, nodeValue4549, nodeValue4602, nodeValue4605, nodeValue4612, nodeValue4622, nodeValue4624, nodeValue5172, nodeValue5294, nodeValue5307]
  ring

noncomputable def reducedSource1412 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue600 x + ((1 : ℝ) * Sparse.eval nodeValue602 x + ((2 : ℝ) * Sparse.eval nodeValue608 x + ((2 : ℝ) * Sparse.eval nodeValue1126 x + ((2 : ℝ) * Sparse.eval nodeValue1128 x + ((4 : ℝ) * Sparse.eval nodeValue1134 x + ((4 : ℝ) * Sparse.eval nodeValue1236 x + ((2 : ℝ) * Sparse.eval nodeValue1239 x + ((2 : ℝ) * Sparse.eval nodeValue1246 x + ((2 : ℝ) * Sparse.eval nodeValue1299 x + ((2 : ℝ) * Sparse.eval nodeValue1301 x + ((2 : ℝ) * Sparse.eval nodeValue2959 x + ((2 : ℝ) * Sparse.eval nodeValue3101 x + ((1 : ℝ) * Sparse.eval nodeValue3122 x + 0)))))))))))))

def numericRow1412 : Integer.Sparse Master := [(Sum.inl 0, -15), (Sum.inl 6, 1), (Sum.inl 7, -16), (Sum.inl 1, 30), (Sum.inr 600, 432), (Sum.inr 602, 216), (Sum.inr 608, 432), (Sum.inr 1126, 432), (Sum.inr 1128, 432), (Sum.inr 1134, 864), (Sum.inr 1236, 864), (Sum.inr 1239, 432), (Sum.inr 1246, 432)]

theorem reindexCheck1412 : Integer.Sparse.reindex keyMap MixedData.row1412 = numericRow1412 := by decide +kernel

theorem numericCheck1412 (x : Master → ℝ) : Integer.Sparse.eval numericRow1412 x =
    (216 : ℝ) * reducedSource1412 x := by
  norm_num [numericRow1412, reducedSource1412, Integer.Sparse.eval, Sparse.eval, nodeValue600, nodeValue602, nodeValue608, nodeValue1126, nodeValue1128, nodeValue1134, nodeValue1236, nodeValue1239, nodeValue1246, nodeValue1299, nodeValue1301, nodeValue2959, nodeValue3101, nodeValue3122]
  ring

noncomputable def reducedSource1413 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4457 x + ((2 : ℝ) * Sparse.eval nodeValue4461 x + ((1 : ℝ) * Sparse.eval nodeValue4496 x + ((2 : ℝ) * Sparse.eval nodeValue4498 x + ((1 : ℝ) * Sparse.eval nodeValue4502 x + ((2 : ℝ) * Sparse.eval nodeValue4503 x + ((2 : ℝ) * Sparse.eval nodeValue4589 x + ((2 : ℝ) * Sparse.eval nodeValue4600 x + ((4 : ℝ) * Sparse.eval nodeValue4602 x + ((2 : ℝ) * Sparse.eval nodeValue4606 x + ((4 : ℝ) * Sparse.eval nodeValue4607 x + ((2 : ℝ) * Sparse.eval nodeValue4617 x + ((2 : ℝ) * Sparse.eval nodeValue4619 x + ((2 : ℝ) * Sparse.eval nodeValue4624 x + 0)))))))))))))

def numericRow1413 : Integer.Sparse Master := [(Sum.inl 0, 19), (Sum.inl 6, 5), (Sum.inl 8, -80), (Sum.inl 1, -40), (Sum.inr 1040, -2160), (Sum.inr 1044, -2160), (Sum.inr 1080, -1080), (Sum.inr 1087, -2160), (Sum.inr 1236, -4320), (Sum.inr 1240, -2160), (Sum.inr 1294, -2160), (Sum.inr 1707, -2160), (Sum.inr 1710, -1080), (Sum.inr 1737, -2160), (Sum.inr 1739, -2160), (Sum.inr 3293, -4320), (Sum.inr 3299, -2160), (Sum.inr 3305, -2160), (Sum.inr 3309, -2160), (Sum.inr 4589, 8640), (Sum.inr 4600, 8640), (Sum.inr 4607, 17280), (Sum.inr 4617, 8640)]

theorem reindexCheck1413 : Integer.Sparse.reindex keyMap MixedData.row1413 = numericRow1413 := by decide +kernel

theorem numericCheck1413 (x : Master → ℝ) : Integer.Sparse.eval numericRow1413 x =
    (4320 : ℝ) * reducedSource1413 x := by
  norm_num [numericRow1413, reducedSource1413, Integer.Sparse.eval, Sparse.eval, nodeValue4457, nodeValue4461, nodeValue4496, nodeValue4498, nodeValue4502, nodeValue4503, nodeValue4589, nodeValue4600, nodeValue4602, nodeValue4606, nodeValue4607, nodeValue4617, nodeValue4619, nodeValue4624]
  ring

noncomputable def reducedSource1414 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1044 x + ((1 : ℝ) * Sparse.eval nodeValue1086 x + ((2 : ℝ) * Sparse.eval nodeValue1087 x + ((2 : ℝ) * Sparse.eval nodeValue1216 x + ((2 : ℝ) * Sparse.eval nodeValue1240 x + ((4 : ℝ) * Sparse.eval nodeValue1241 x + ((4 : ℝ) * Sparse.eval nodeValue1267 x + ((2 : ℝ) * Sparse.eval nodeValue1270 x + ((2 : ℝ) * Sparse.eval nodeValue1301 x + ((2 : ℝ) * Sparse.eval nodeValue1302 x + ((2 : ℝ) * Sparse.eval nodeValue1306 x + ((2 : ℝ) * Sparse.eval nodeValue1414 x + ((2 : ℝ) * Sparse.eval nodeValue1448 x + ((1 : ℝ) * Sparse.eval nodeValue1451 x + 0)))))))))))))

def numericRow1414 : Integer.Sparse Master := [(Sum.inl 0, -57), (Sum.inl 5, 120), (Sum.inl 6, -25), (Sum.inl 2, -60), (Sum.inl 7, -80), (Sum.inl 1, 30), (Sum.inr 1044, 1440), (Sum.inr 1087, 1440), (Sum.inr 1216, 1440), (Sum.inr 1240, 1440), (Sum.inr 1241, 2880), (Sum.inr 1270, 1440), (Sum.inr 1306, 1440)]

theorem reindexCheck1414 : Integer.Sparse.reindex keyMap MixedData.row1414 = numericRow1414 := by decide +kernel

theorem numericCheck1414 (x : Master → ℝ) : Integer.Sparse.eval numericRow1414 x =
    (720 : ℝ) * reducedSource1414 x := by
  norm_num [numericRow1414, reducedSource1414, Integer.Sparse.eval, Sparse.eval, nodeValue1044, nodeValue1086, nodeValue1087, nodeValue1216, nodeValue1240, nodeValue1241, nodeValue1267, nodeValue1270, nodeValue1301, nodeValue1302, nodeValue1306, nodeValue1414, nodeValue1448, nodeValue1451]
  ring

noncomputable def reducedSource1415 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1737 x + ((2 : ℝ) * Sparse.eval nodeValue1739 x + ((1 : ℝ) * Sparse.eval nodeValue1753 x + ((1 : ℝ) * Sparse.eval nodeValue3308 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))

def numericRow1415 : Integer.Sparse Master := [(Sum.inr 1737, 2), (Sum.inr 1739, 2), (Sum.inr 3308, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1415 : Integer.Sparse.reindex keyMap MixedData.row1415 = numericRow1415 := by decide +kernel

theorem numericCheck1415 (x : Master → ℝ) : Integer.Sparse.eval numericRow1415 x =
    (1 : ℝ) * reducedSource1415 x := by
  norm_num [numericRow1415, reducedSource1415, Integer.Sparse.eval, Sparse.eval, nodeValue1737, nodeValue1739, nodeValue1753, nodeValue3308, nodeValue4069]

noncomputable def reducedSource1416 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1727 x + ((2 : ℝ) * Sparse.eval nodeValue3293 x + ((1 : ℝ) * Sparse.eval nodeValue3305 x + ((1 : ℝ) * Sparse.eval nodeValue3308 x + ((1 : ℝ) * Sparse.eval nodeValue3309 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

def numericRow1416 : Integer.Sparse Master := [(Sum.inr 3293, 2), (Sum.inr 3305, 1), (Sum.inr 3308, 1), (Sum.inr 3309, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1416 : Integer.Sparse.reindex keyMap MixedData.row1416 = numericRow1416 := by decide +kernel

theorem numericCheck1416 (x : Master → ℝ) : Integer.Sparse.eval numericRow1416 x =
    (1 : ℝ) * reducedSource1416 x := by
  norm_num [numericRow1416, reducedSource1416, Integer.Sparse.eval, Sparse.eval, nodeValue1727, nodeValue3293, nodeValue3305, nodeValue3308, nodeValue3309, nodeValue4069]

noncomputable def reducedSource1417 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4175 x + ((1 : ℝ) * Sparse.eval nodeValue4177 x + ((1 : ℝ) * Sparse.eval nodeValue4180 x + ((1 : ℝ) * Sparse.eval nodeValue4186 x + ((2 : ℝ) * Sparse.eval nodeValue4544 x + ((2 : ℝ) * Sparse.eval nodeValue4546 x + ((2 : ℝ) * Sparse.eval nodeValue4549 x + ((2 : ℝ) * Sparse.eval nodeValue4554 x + ((2 : ℝ) * Sparse.eval nodeValue4606 x + ((1 : ℝ) * Sparse.eval nodeValue4608 x + ((1 : ℝ) * Sparse.eval nodeValue4612 x + ((2 : ℝ) * Sparse.eval nodeValue4622 x + ((1 : ℝ) * Sparse.eval nodeValue4623 x + ((3 : ℝ) * Sparse.eval nodeValue4624 x + ((1 : ℝ) * Sparse.eval nodeValue4625 x + ((1 : ℝ) * Sparse.eval nodeValue4628 x + ((2 : ℝ) * Sparse.eval nodeValue5169 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5307 x + ((1 : ℝ) * Sparse.eval nodeValue5309 x + 0)))))))))))))))))))

def numericRow1417 : Integer.Sparse Master := [(Sum.inl 0, 71), (Sum.inl 6, -5), (Sum.inl 8, 80), (Sum.inl 1, -50), (Sum.inr 603, -1440), (Sum.inr 605, -720), (Sum.inr 608, -720), (Sum.inr 614, -720), (Sum.inr 1129, -1440), (Sum.inr 1131, -1440), (Sum.inr 1134, -1440), (Sum.inr 1139, -1440), (Sum.inr 1240, -1440), (Sum.inr 1242, -720), (Sum.inr 1246, -720), (Sum.inr 1517, -1440), (Sum.inr 1518, -720), (Sum.inr 1519, -720), (Sum.inr 1536, -720), (Sum.inr 3263, -1440), (Sum.inr 3264, -1440), (Sum.inr 3265, -1440), (Sum.inr 3274, -1440), (Sum.inr 3299, -1440), (Sum.inr 3300, -720), (Sum.inr 3301, -720), (Sum.inr 3307, -1440), (Sum.inr 3308, -720), (Sum.inr 3309, -2160), (Sum.inr 3310, -720), (Sum.inr 3312, -720), (Sum.inr 3607, -1440), (Sum.inr 3627, -720)]

theorem reindexCheck1417 : Integer.Sparse.reindex keyMap MixedData.row1417 = numericRow1417 := by decide +kernel

theorem numericCheck1417 (x : Master → ℝ) : Integer.Sparse.eval numericRow1417 x =
    (2880 : ℝ) * reducedSource1417 x := by
  norm_num [numericRow1417, reducedSource1417, Integer.Sparse.eval, Sparse.eval, nodeValue4175, nodeValue4177, nodeValue4180, nodeValue4186, nodeValue4544, nodeValue4546, nodeValue4549, nodeValue4554, nodeValue4606, nodeValue4608, nodeValue4612, nodeValue4622, nodeValue4623, nodeValue4624, nodeValue4625, nodeValue4628, nodeValue5169, nodeValue5293, nodeValue5307, nodeValue5309]
  ring

noncomputable def reducedSource1418 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue603 x + ((1 : ℝ) * Sparse.eval nodeValue605 x + ((1 : ℝ) * Sparse.eval nodeValue608 x + ((1 : ℝ) * Sparse.eval nodeValue614 x + ((2 : ℝ) * Sparse.eval nodeValue1129 x + ((2 : ℝ) * Sparse.eval nodeValue1131 x + ((2 : ℝ) * Sparse.eval nodeValue1134 x + ((2 : ℝ) * Sparse.eval nodeValue1139 x + ((2 : ℝ) * Sparse.eval nodeValue1240 x + ((1 : ℝ) * Sparse.eval nodeValue1242 x + ((1 : ℝ) * Sparse.eval nodeValue1246 x + ((2 : ℝ) * Sparse.eval nodeValue1299 x + ((1 : ℝ) * Sparse.eval nodeValue1300 x + ((3 : ℝ) * Sparse.eval nodeValue1301 x + ((1 : ℝ) * Sparse.eval nodeValue1304 x + ((1 : ℝ) * Sparse.eval nodeValue1312 x + ((2 : ℝ) * Sparse.eval nodeValue2960 x + ((1 : ℝ) * Sparse.eval nodeValue3102 x + ((1 : ℝ) * Sparse.eval nodeValue3122 x + ((1 : ℝ) * Sparse.eval nodeValue3123 x + 0)))))))))))))))))))

def numericRow1418 : Integer.Sparse Master := [(Sum.inl 0, -71), (Sum.inl 6, 5), (Sum.inl 8, -80), (Sum.inl 1, 50), (Sum.inr 603, 1440), (Sum.inr 605, 720), (Sum.inr 608, 720), (Sum.inr 614, 720), (Sum.inr 1129, 1440), (Sum.inr 1131, 1440), (Sum.inr 1134, 1440), (Sum.inr 1139, 1440), (Sum.inr 1240, 1440), (Sum.inr 1242, 720), (Sum.inr 1246, 720)]

theorem reindexCheck1418 : Integer.Sparse.reindex keyMap MixedData.row1418 = numericRow1418 := by decide +kernel

theorem numericCheck1418 (x : Master → ℝ) : Integer.Sparse.eval numericRow1418 x =
    (720 : ℝ) * reducedSource1418 x := by
  norm_num [numericRow1418, reducedSource1418, Integer.Sparse.eval, Sparse.eval, nodeValue603, nodeValue605, nodeValue608, nodeValue614, nodeValue1129, nodeValue1131, nodeValue1134, nodeValue1139, nodeValue1240, nodeValue1242, nodeValue1246, nodeValue1299, nodeValue1300, nodeValue1301, nodeValue1304, nodeValue1312, nodeValue2960, nodeValue3102, nodeValue3122, nodeValue3123]
  ring

noncomputable def reducedSource1419 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue4458 x + ((2 : ℝ) * Sparse.eval nodeValue4498 x + ((2 : ℝ) * Sparse.eval nodeValue4499 x + ((2 : ℝ) * Sparse.eval nodeValue4502 x + ((2 : ℝ) * Sparse.eval nodeValue4590 x + ((4 : ℝ) * Sparse.eval nodeValue4602 x + ((4 : ℝ) * Sparse.eval nodeValue4603 x + ((4 : ℝ) * Sparse.eval nodeValue4606 x + ((2 : ℝ) * Sparse.eval nodeValue4619 x + ((1 : ℝ) * Sparse.eval nodeValue4620 x + ((2 : ℝ) * Sparse.eval nodeValue4623 x + ((1 : ℝ) * Sparse.eval nodeValue4624 x + 0)))))))))))

def numericRow1419 : Integer.Sparse Master := [(Sum.inl 0, 49), (Sum.inl 6, 15), (Sum.inl 7, -160), (Sum.inl 8, -80), (Sum.inl 1, 80), (Sum.inr 1041, -8640), (Sum.inr 1083, -4320), (Sum.inr 1236, -8640), (Sum.inr 1240, -8640), (Sum.inr 1294, -4320), (Sum.inr 1724, -8640), (Sum.inr 1728, -4320), (Sum.inr 3293, -8640), (Sum.inr 3299, -8640), (Sum.inr 3305, -4320), (Sum.inr 3308, -4320), (Sum.inr 3309, -2160), (Sum.inr 4590, 17280), (Sum.inr 4603, 34560), (Sum.inr 4620, 8640)]

theorem reindexCheck1419 : Integer.Sparse.reindex keyMap MixedData.row1419 = numericRow1419 := by decide +kernel

theorem numericCheck1419 (x : Master → ℝ) : Integer.Sparse.eval numericRow1419 x =
    (8640 : ℝ) * reducedSource1419 x := by
  norm_num [numericRow1419, reducedSource1419, Integer.Sparse.eval, Sparse.eval, nodeValue4458, nodeValue4498, nodeValue4499, nodeValue4502, nodeValue4590, nodeValue4602, nodeValue4603, nodeValue4606, nodeValue4619, nodeValue4620, nodeValue4623, nodeValue4624]
  ring

noncomputable def reducedSource1420 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4165 x + ((1 : ℝ) * Sparse.eval nodeValue4166 x + ((1 : ℝ) * Sparse.eval nodeValue4167 x + ((1 : ℝ) * Sparse.eval nodeValue4185 x + ((2 : ℝ) * Sparse.eval nodeValue4537 x + ((2 : ℝ) * Sparse.eval nodeValue4538 x + ((2 : ℝ) * Sparse.eval nodeValue4539 x + ((2 : ℝ) * Sparse.eval nodeValue4553 x + ((2 : ℝ) * Sparse.eval nodeValue4570 x + ((1 : ℝ) * Sparse.eval nodeValue4572 x + ((1 : ℝ) * Sparse.eval nodeValue4575 x + ((2 : ℝ) * Sparse.eval nodeValue4618 x + ((3 : ℝ) * Sparse.eval nodeValue4619 x + ((1 : ℝ) * Sparse.eval nodeValue4621 x + ((1 : ℝ) * Sparse.eval nodeValue4623 x + ((1 : ℝ) * Sparse.eval nodeValue4627 x + ((2 : ℝ) * Sparse.eval nodeValue5170 x + ((1 : ℝ) * Sparse.eval nodeValue5302 x + ((1 : ℝ) * Sparse.eval nodeValue5306 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + 0)))))))))))))))))))

def numericRow1420 : Integer.Sparse Master := [(Sum.inl 0, 61), (Sum.inl 5, 60), (Sum.inl 6, 5), (Sum.inl 2, -10), (Sum.inl 7, 160), (Sum.inl 3, 160), (Sum.inl 1, 320), (Sum.inr 593, -4320), (Sum.inr 594, -2160), (Sum.inr 595, -2160), (Sum.inr 613, -2160), (Sum.inr 1122, -4320), (Sum.inr 1123, -4320), (Sum.inr 1124, -4320), (Sum.inr 1138, -4320), (Sum.inr 1188, -4320), (Sum.inr 1190, -2160), (Sum.inr 1193, -2160), (Sum.inr 1293, -4320), (Sum.inr 1294, -6480), (Sum.inr 1297, -2160), (Sum.inr 1498, -4320), (Sum.inr 1499, -2160), (Sum.inr 1500, -2160), (Sum.inr 1525, -2160), (Sum.inr 1937, -4320), (Sum.inr 1952, -2160), (Sum.inr 2289, -2160), (Sum.inr 2954, -4320), (Sum.inr 3054, -2160), (Sum.inr 3245, -4320), (Sum.inr 3248, -2160), (Sum.inr 3253, -4320), (Sum.inr 3254, -4320), (Sum.inr 3270, -4320), (Sum.inr 3304, -4320), (Sum.inr 3305, -6480), (Sum.inr 3308, -2160), (Sum.inr 3311, -2160), (Sum.inr 3606, -4320), (Sum.inr 3623, -2160), (Sum.inr 3626, -2160), (Sum.inr 3633, -2160)]

theorem reindexCheck1420 : Integer.Sparse.reindex keyMap MixedData.row1420 = numericRow1420 := by decide +kernel

theorem numericCheck1420 (x : Master → ℝ) : Integer.Sparse.eval numericRow1420 x =
    (8640 : ℝ) * reducedSource1420 x := by
  norm_num [numericRow1420, reducedSource1420, Integer.Sparse.eval, Sparse.eval, nodeValue4165, nodeValue4166, nodeValue4167, nodeValue4185, nodeValue4537, nodeValue4538, nodeValue4539, nodeValue4553, nodeValue4570, nodeValue4572, nodeValue4575, nodeValue4618, nodeValue4619, nodeValue4621, nodeValue4623, nodeValue4627, nodeValue5170, nodeValue5302, nodeValue5306, nodeValue5310]
  ring

noncomputable def reducedSource1421 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue593 x + ((1 : ℝ) * Sparse.eval nodeValue594 x + ((1 : ℝ) * Sparse.eval nodeValue595 x + ((1 : ℝ) * Sparse.eval nodeValue613 x + ((2 : ℝ) * Sparse.eval nodeValue1122 x + ((2 : ℝ) * Sparse.eval nodeValue1123 x + ((2 : ℝ) * Sparse.eval nodeValue1124 x + ((2 : ℝ) * Sparse.eval nodeValue1138 x + ((2 : ℝ) * Sparse.eval nodeValue1188 x + ((1 : ℝ) * Sparse.eval nodeValue1190 x + ((1 : ℝ) * Sparse.eval nodeValue1193 x + ((2 : ℝ) * Sparse.eval nodeValue1293 x + ((3 : ℝ) * Sparse.eval nodeValue1294 x + ((1 : ℝ) * Sparse.eval nodeValue1297 x + ((1 : ℝ) * Sparse.eval nodeValue1305 x + ((1 : ℝ) * Sparse.eval nodeValue1311 x + ((2 : ℝ) * Sparse.eval nodeValue2954 x + ((1 : ℝ) * Sparse.eval nodeValue3054 x + ((1 : ℝ) * Sparse.eval nodeValue3120 x + ((1 : ℝ) * Sparse.eval nodeValue3121 x + 0)))))))))))))))))))

def numericRow1421 : Integer.Sparse Master := [(Sum.inl 0, -61), (Sum.inl 5, -60), (Sum.inl 6, -5), (Sum.inl 2, 10), (Sum.inl 7, -160), (Sum.inl 3, -160), (Sum.inl 1, -320), (Sum.inr 593, 4320), (Sum.inr 594, 2160), (Sum.inr 595, 2160), (Sum.inr 613, 2160), (Sum.inr 1122, 4320), (Sum.inr 1123, 4320), (Sum.inr 1124, 4320), (Sum.inr 1138, 4320), (Sum.inr 1188, 4320), (Sum.inr 1190, 2160), (Sum.inr 1193, 2160), (Sum.inr 1293, 4320), (Sum.inr 1294, 6480), (Sum.inr 1297, 2160), (Sum.inr 2954, 4320), (Sum.inr 3054, 2160)]

theorem reindexCheck1421 : Integer.Sparse.reindex keyMap MixedData.row1421 = numericRow1421 := by decide +kernel

theorem numericCheck1421 (x : Master → ℝ) : Integer.Sparse.eval numericRow1421 x =
    (2160 : ℝ) * reducedSource1421 x := by
  norm_num [numericRow1421, reducedSource1421, Integer.Sparse.eval, Sparse.eval, nodeValue593, nodeValue594, nodeValue595, nodeValue613, nodeValue1122, nodeValue1123, nodeValue1124, nodeValue1138, nodeValue1188, nodeValue1190, nodeValue1193, nodeValue1293, nodeValue1294, nodeValue1297, nodeValue1305, nodeValue1311, nodeValue2954, nodeValue3054, nodeValue3120, nodeValue3121]
  ring

noncomputable def reducedSource1422 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4176 x + ((1 : ℝ) * Sparse.eval nodeValue4178 x + ((1 : ℝ) * Sparse.eval nodeValue4179 x + ((1 : ℝ) * Sparse.eval nodeValue4188 x + ((2 : ℝ) * Sparse.eval nodeValue4545 x + ((2 : ℝ) * Sparse.eval nodeValue4547 x + ((2 : ℝ) * Sparse.eval nodeValue4548 x + ((2 : ℝ) * Sparse.eval nodeValue4556 x + ((2 : ℝ) * Sparse.eval nodeValue4602 x + ((2 : ℝ) * Sparse.eval nodeValue4607 x + ((1 : ℝ) * Sparse.eval nodeValue4608 x + ((1 : ℝ) * Sparse.eval nodeValue4609 x + ((1 : ℝ) * Sparse.eval nodeValue4611 x + ((1 : ℝ) * Sparse.eval nodeValue4612 x + ((2 : ℝ) * Sparse.eval nodeValue4616 x + ((1 : ℝ) * Sparse.eval nodeValue4617 x + ((1 : ℝ) * Sparse.eval nodeValue4620 x + ((2 : ℝ) * Sparse.eval nodeValue5163 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5304 x + 0))))))))))))))))))))

def numericRow1422 : Integer.Sparse Master := [(Sum.inr 1236, -2), (Sum.inr 1242, -1), (Sum.inr 1246, -1), (Sum.inr 2590, -2), (Sum.inr 2765, -1), (Sum.inr 2782, -1), (Sum.inr 3293, -2), (Sum.inr 3300, -1), (Sum.inr 3301, -1), (Sum.inr 3564, -2), (Sum.inr 3582, -1), (Sum.inr 3583, -1), (Sum.inr 4176, 8), (Sum.inr 4178, 4), (Sum.inr 4179, 4), (Sum.inr 4188, 4), (Sum.inr 4545, 8), (Sum.inr 4547, 8), (Sum.inr 4548, 8), (Sum.inr 4556, 8), (Sum.inr 4607, 8), (Sum.inr 4609, 4), (Sum.inr 4611, 4), (Sum.inr 4616, 8), (Sum.inr 4617, 4), (Sum.inr 4620, 4)]

theorem reindexCheck1422 : Integer.Sparse.reindex keyMap MixedData.row1422 = numericRow1422 := by decide +kernel

theorem numericCheck1422 (x : Master → ℝ) : Integer.Sparse.eval numericRow1422 x =
    (4 : ℝ) * reducedSource1422 x := by
  norm_num [numericRow1422, reducedSource1422, Integer.Sparse.eval, Sparse.eval, nodeValue4176, nodeValue4178, nodeValue4179, nodeValue4188, nodeValue4545, nodeValue4547, nodeValue4548, nodeValue4556, nodeValue4602, nodeValue4607, nodeValue4608, nodeValue4609, nodeValue4611, nodeValue4612, nodeValue4616, nodeValue4617, nodeValue4620, nodeValue5163, nodeValue5274, nodeValue5291, nodeValue5304]
  ring

noncomputable def reducedSource1423 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue604 x + ((1 : ℝ) * Sparse.eval nodeValue606 x + ((1 : ℝ) * Sparse.eval nodeValue607 x + ((1 : ℝ) * Sparse.eval nodeValue616 x + ((2 : ℝ) * Sparse.eval nodeValue1130 x + ((2 : ℝ) * Sparse.eval nodeValue1132 x + ((2 : ℝ) * Sparse.eval nodeValue1133 x + ((2 : ℝ) * Sparse.eval nodeValue1141 x + ((2 : ℝ) * Sparse.eval nodeValue1241 x + ((1 : ℝ) * Sparse.eval nodeValue1243 x + ((1 : ℝ) * Sparse.eval nodeValue1245 x + ((2 : ℝ) * Sparse.eval nodeValue1267 x + ((1 : ℝ) * Sparse.eval nodeValue1269 x + ((1 : ℝ) * Sparse.eval nodeValue1274 x + ((2 : ℝ) * Sparse.eval nodeValue1291 x + ((1 : ℝ) * Sparse.eval nodeValue1292 x + ((1 : ℝ) * Sparse.eval nodeValue1295 x + ((2 : ℝ) * Sparse.eval nodeValue2961 x + ((1 : ℝ) * Sparse.eval nodeValue3103 x + ((1 : ℝ) * Sparse.eval nodeValue3112 x + ((1 : ℝ) * Sparse.eval nodeValue3119 x + 0))))))))))))))))))))

def numericRow1423 : Integer.Sparse Master := [(Sum.inl 0, -110), (Sum.inl 5, -40), (Sum.inl 6, 10), (Sum.inl 2, -30), (Sum.inl 7, -160), (Sum.inl 35, -160), (Sum.inl 3, -160), (Sum.inl 1, 230), (Sum.inr 604, 4320), (Sum.inr 606, 2160), (Sum.inr 607, 2160), (Sum.inr 616, 2160), (Sum.inr 1130, 4320), (Sum.inr 1132, 4320), (Sum.inr 1133, 4320), (Sum.inr 1141, 4320), (Sum.inr 1241, 4320), (Sum.inr 1243, 2160), (Sum.inr 1245, 2160), (Sum.inr 1291, 4320), (Sum.inr 1292, 2160), (Sum.inr 1295, 2160)]

theorem reindexCheck1423 : Integer.Sparse.reindex keyMap MixedData.row1423 = numericRow1423 := by decide +kernel

theorem numericCheck1423 (x : Master → ℝ) : Integer.Sparse.eval numericRow1423 x =
    (2160 : ℝ) * reducedSource1423 x := by
  norm_num [numericRow1423, reducedSource1423, Integer.Sparse.eval, Sparse.eval, nodeValue604, nodeValue606, nodeValue607, nodeValue616, nodeValue1130, nodeValue1132, nodeValue1133, nodeValue1141, nodeValue1241, nodeValue1243, nodeValue1245, nodeValue1267, nodeValue1269, nodeValue1274, nodeValue1291, nodeValue1292, nodeValue1295, nodeValue2961, nodeValue3103, nodeValue3112, nodeValue3119]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
