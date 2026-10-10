import OAI.Analysis.MutuallyUnbiased.MixedData.Source9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
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

noncomputable def reducedSource1264 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1049 x + ((1 : ℝ) * Sparse.eval nodeValue1094 x + ((1 : ℝ) * Sparse.eval nodeValue1095 x + ((6 : ℝ) * Sparse.eval nodeValue1219 x + ((3 : ℝ) * Sparse.eval nodeValue1245 x + ((3 : ℝ) * Sparse.eval nodeValue1246 x + ((3 : ℝ) * Sparse.eval nodeValue1273 x + ((3 : ℝ) * Sparse.eval nodeValue1274 x + ((1 : ℝ) * Sparse.eval nodeValue1310 x + ((1 : ℝ) * Sparse.eval nodeValue1312 x + ((3 : ℝ) * Sparse.eval nodeValue1419 x + ((1 : ℝ) * Sparse.eval nodeValue1454 x + ((1 : ℝ) * Sparse.eval nodeValue1455 x + 0))))))))))))

def numericRow1264 : Integer.Sparse Master := [(Sum.inl 0, -1), (Sum.inl 5, -5), (Sum.inl 7, 4), (Sum.inl 1, 2), (Sum.inr 1049, 54), (Sum.inr 1094, 18), (Sum.inr 1219, 108), (Sum.inr 1245, 54), (Sum.inr 1246, 54), (Sum.inr 1273, 54), (Sum.inr 1310, 18)]

theorem reindexCheck1264 : Integer.Sparse.reindex keyMap MixedData.row1264 = numericRow1264 := by decide +kernel

theorem numericCheck1264 (x : Master → ℝ) : Integer.Sparse.eval numericRow1264 x =
    (18 : ℝ) * reducedSource1264 x := by
  norm_num [numericRow1264, reducedSource1264, Integer.Sparse.eval, Sparse.eval, nodeValue1049, nodeValue1094, nodeValue1095, nodeValue1219, nodeValue1245, nodeValue1246, nodeValue1273, nodeValue1274, nodeValue1310, nodeValue1312, nodeValue1419, nodeValue1454, nodeValue1455]; ring

noncomputable def reducedSource1265 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1755 x + ((3 : ℝ) * Sparse.eval nodeValue3301 x + ((1 : ℝ) * Sparse.eval nodeValue3311 x + ((1 : ℝ) * Sparse.eval nodeValue3312 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0))))

def numericRow1265 : Integer.Sparse Master := [(Sum.inr 3301, 3), (Sum.inr 3311, 1), (Sum.inr 3312, 1), (Sum.inr 4071, -1)]

theorem reindexCheck1265 : Integer.Sparse.reindex keyMap MixedData.row1265 = numericRow1265 := by decide +kernel

theorem numericCheck1265 (x : Master → ℝ) : Integer.Sparse.eval numericRow1265 x =
    (1 : ℝ) * reducedSource1265 x := by
  norm_num [numericRow1265, reducedSource1265, Integer.Sparse.eval, Sparse.eval, nodeValue1755, nodeValue3301, nodeValue3311, nodeValue3312, nodeValue4071]

noncomputable def reducedSource1266 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4186 x + ((2 : ℝ) * Sparse.eval nodeValue4191 x + ((6 : ℝ) * Sparse.eval nodeValue4554 x + ((6 : ℝ) * Sparse.eval nodeValue4558 x + ((6 : ℝ) * Sparse.eval nodeValue4624 x + ((2 : ℝ) * Sparse.eval nodeValue4625 x + ((3 : ℝ) * Sparse.eval nodeValue5177 x + ((2 : ℝ) * Sparse.eval nodeValue5309 x + 0)))))))

def numericRow1266 : Integer.Sparse Master := [(Sum.inl 0, 6), (Sum.inl 5, -5), (Sum.inl 8, -20), (Sum.inl 1, -5), (Sum.inr 614, -180), (Sum.inr 619, -120), (Sum.inr 1139, -360), (Sum.inr 1144, -360), (Sum.inr 1536, -180), (Sum.inr 1538, -120), (Sum.inr 3274, -360), (Sum.inr 3276, -360), (Sum.inr 3309, -360), (Sum.inr 3310, -120), (Sum.inr 3616, -180)]

theorem reindexCheck1266 : Integer.Sparse.reindex keyMap MixedData.row1266 = numericRow1266 := by decide +kernel

theorem numericCheck1266 (x : Master → ℝ) : Integer.Sparse.eval numericRow1266 x =
    (240 : ℝ) * reducedSource1266 x := by
  norm_num [numericRow1266, reducedSource1266, Integer.Sparse.eval, Sparse.eval, nodeValue4186, nodeValue4191, nodeValue4554, nodeValue4558, nodeValue4624, nodeValue4625, nodeValue5177, nodeValue5309]; ring

noncomputable def reducedSource1267 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue614 x + ((2 : ℝ) * Sparse.eval nodeValue619 x + ((6 : ℝ) * Sparse.eval nodeValue1139 x + ((6 : ℝ) * Sparse.eval nodeValue1144 x + ((6 : ℝ) * Sparse.eval nodeValue1301 x + ((2 : ℝ) * Sparse.eval nodeValue1304 x + ((3 : ℝ) * Sparse.eval nodeValue2969 x + ((2 : ℝ) * Sparse.eval nodeValue3123 x + 0)))))))

def numericRow1267 : Integer.Sparse Master := [(Sum.inl 0, -6), (Sum.inl 5, 5), (Sum.inl 8, 20), (Sum.inl 1, 5), (Sum.inr 614, 180), (Sum.inr 619, 120), (Sum.inr 1139, 360), (Sum.inr 1144, 360)]

theorem reindexCheck1267 : Integer.Sparse.reindex keyMap MixedData.row1267 = numericRow1267 := by decide +kernel

theorem numericCheck1267 (x : Master → ℝ) : Integer.Sparse.eval numericRow1267 x =
    (60 : ℝ) * reducedSource1267 x := by
  norm_num [numericRow1267, reducedSource1267, Integer.Sparse.eval, Sparse.eval, nodeValue614, nodeValue619, nodeValue1139, nodeValue1144, nodeValue1301, nodeValue1304, nodeValue2969, nodeValue3123]; ring

noncomputable def reducedSource1268 (x : Master → ℝ) : ℝ :=
  (6 : ℝ) * Sparse.eval nodeValue4467 x + ((4 : ℝ) * Sparse.eval nodeValue4511 x + ((6 : ℝ) * Sparse.eval nodeValue4593 x + ((12 : ℝ) * Sparse.eval nodeValue4612 x + ((2 : ℝ) * Sparse.eval nodeValue4627 x + 0))))

def numericRow1268 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 5, 5), (Sum.inl 7, 20), (Sum.inl 1, 10), (Sum.inr 1050, -540), (Sum.inr 1246, -1080), (Sum.inr 1751, -540), (Sum.inr 3301, -1080), (Sum.inr 3311, -180), (Sum.inr 4593, 2160)]

theorem reindexCheck1268 : Integer.Sparse.reindex keyMap MixedData.row1268 = numericRow1268 := by decide +kernel

theorem numericCheck1268 (x : Master → ℝ) : Integer.Sparse.eval numericRow1268 x =
    (360 : ℝ) * reducedSource1268 x := by
  norm_num [numericRow1268, reducedSource1268, Integer.Sparse.eval, Sparse.eval, nodeValue4467, nodeValue4511, nodeValue4593, nodeValue4612, nodeValue4627]; ring

noncomputable def reducedSource1269 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1050 x + ((2 : ℝ) * Sparse.eval nodeValue1095 x + ((6 : ℝ) * Sparse.eval nodeValue1220 x + ((6 : ℝ) * Sparse.eval nodeValue1246 x + ((6 : ℝ) * Sparse.eval nodeValue1274 x + ((2 : ℝ) * Sparse.eval nodeValue1311 x + ((3 : ℝ) * Sparse.eval nodeValue1420 x + ((2 : ℝ) * Sparse.eval nodeValue1455 x + 0)))))))

def numericRow1269 : Integer.Sparse Master := [(Sum.inl 0, -9), (Sum.inl 5, -50), (Sum.inl 8, 40), (Sum.inl 1, -5), (Sum.inr 1050, 360), (Sum.inr 1220, 720), (Sum.inr 1246, 720)]

theorem reindexCheck1269 : Integer.Sparse.reindex keyMap MixedData.row1269 = numericRow1269 := by decide +kernel

theorem numericCheck1269 (x : Master → ℝ) : Integer.Sparse.eval numericRow1269 x =
    (120 : ℝ) * reducedSource1269 x := by
  norm_num [numericRow1269, reducedSource1269, Integer.Sparse.eval, Sparse.eval, nodeValue1050, nodeValue1095, nodeValue1220, nodeValue1246, nodeValue1274, nodeValue1311, nodeValue1420, nodeValue1455]; ring

noncomputable def reducedSource1270 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1751 x + ((2 : ℝ) * Sparse.eval nodeValue1755 x + ((1 : ℝ) * Sparse.eval nodeValue3312 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0)))

def numericRow1270 : Integer.Sparse Master := [(Sum.inr 1751, 3), (Sum.inr 3312, 1), (Sum.inr 4071, -1)]

theorem reindexCheck1270 : Integer.Sparse.reindex keyMap MixedData.row1270 = numericRow1270 := by decide +kernel

theorem numericCheck1270 (x : Master → ℝ) : Integer.Sparse.eval numericRow1270 x =
    (1 : ℝ) * reducedSource1270 x := by
  norm_num [numericRow1270, reducedSource1270, Integer.Sparse.eval, Sparse.eval, nodeValue1751, nodeValue1755, nodeValue3312, nodeValue4071]

noncomputable def reducedSource1271 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4158 x + ((1 : ℝ) * Sparse.eval nodeValue4160 x + ((1 : ℝ) * Sparse.eval nodeValue4161 x + ((1 : ℝ) * Sparse.eval nodeValue4188 x + ((2 : ℝ) * Sparse.eval nodeValue4533 x + ((2 : ℝ) * Sparse.eval nodeValue4534 x + ((2 : ℝ) * Sparse.eval nodeValue4535 x + ((2 : ℝ) * Sparse.eval nodeValue4549 x + ((2 : ℝ) * Sparse.eval nodeValue4556 x + ((1 : ℝ) * Sparse.eval nodeValue4558 x + ((1 : ℝ) * Sparse.eval nodeValue4559 x + ((2 : ℝ) * Sparse.eval nodeValue4602 x + ((2 : ℝ) * Sparse.eval nodeValue4603 x + ((1 : ℝ) * Sparse.eval nodeValue4608 x + ((1 : ℝ) * Sparse.eval nodeValue4609 x + ((1 : ℝ) * Sparse.eval nodeValue4619 x + ((1 : ℝ) * Sparse.eval nodeValue4620 x + ((1 : ℝ) * Sparse.eval nodeValue5111 x + ((2 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + 0))))))))))))))))))))

def numericRow1271 : Integer.Sparse Master := [(Sum.inr 1134, -2), (Sum.inr 1144, -1), (Sum.inr 1145, -1), (Sum.inr 1236, -2), (Sum.inr 1242, -1), (Sum.inr 1294, -1), (Sum.inr 2561, -2), (Sum.inr 2743, -1), (Sum.inr 3265, -2), (Sum.inr 3276, -1), (Sum.inr 3277, -1), (Sum.inr 3293, -2), (Sum.inr 3300, -1), (Sum.inr 3305, -1), (Sum.inr 3522, -2), (Sum.inr 3548, -1), (Sum.inr 4158, 8), (Sum.inr 4160, 4), (Sum.inr 4161, 4), (Sum.inr 4188, 4), (Sum.inr 4533, 8), (Sum.inr 4534, 8), (Sum.inr 4535, 8), (Sum.inr 4556, 8), (Sum.inr 4603, 8), (Sum.inr 4609, 4), (Sum.inr 4620, 4)]

theorem reindexCheck1271 : Integer.Sparse.reindex keyMap MixedData.row1271 = numericRow1271 := by decide +kernel

theorem numericCheck1271 (x : Master → ℝ) : Integer.Sparse.eval numericRow1271 x =
    (4 : ℝ) * reducedSource1271 x := by
  norm_num [numericRow1271, reducedSource1271, Integer.Sparse.eval, Sparse.eval, nodeValue4158, nodeValue4160, nodeValue4161, nodeValue4188, nodeValue4533, nodeValue4534, nodeValue4535, nodeValue4549, nodeValue4556, nodeValue4558, nodeValue4559, nodeValue4602, nodeValue4603, nodeValue4608, nodeValue4609, nodeValue4619, nodeValue4620, nodeValue5111, nodeValue5141, nodeValue5274, nodeValue5275]; ring

noncomputable def reducedSource1272 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue586 x + ((1 : ℝ) * Sparse.eval nodeValue588 x + ((1 : ℝ) * Sparse.eval nodeValue589 x + ((1 : ℝ) * Sparse.eval nodeValue616 x + ((2 : ℝ) * Sparse.eval nodeValue1117 x + ((2 : ℝ) * Sparse.eval nodeValue1119 x + ((2 : ℝ) * Sparse.eval nodeValue1120 x + ((2 : ℝ) * Sparse.eval nodeValue1141 x + ((2 : ℝ) * Sparse.eval nodeValue1172 x + ((1 : ℝ) * Sparse.eval nodeValue1175 x + ((1 : ℝ) * Sparse.eval nodeValue1176 x + ((2 : ℝ) * Sparse.eval nodeValue1262 x + ((1 : ℝ) * Sparse.eval nodeValue1264 x + ((2 : ℝ) * Sparse.eval nodeValue1267 x + ((1 : ℝ) * Sparse.eval nodeValue1269 x + ((1 : ℝ) * Sparse.eval nodeValue1295 x + ((1 : ℝ) * Sparse.eval nodeValue1302 x + ((2 : ℝ) * Sparse.eval nodeValue2943 x + ((1 : ℝ) * Sparse.eval nodeValue3006 x + ((1 : ℝ) * Sparse.eval nodeValue3110 x + ((1 : ℝ) * Sparse.eval nodeValue3112 x + 0))))))))))))))))))))

def numericRow1272 : Integer.Sparse Master := [(Sum.inl 0, -26), (Sum.inl 5, 40), (Sum.inl 2, -15), (Sum.inl 7, -40), (Sum.inl 8, -40), (Sum.inl 1, 15), (Sum.inr 586, 720), (Sum.inr 588, 360), (Sum.inr 589, 360), (Sum.inr 616, 360), (Sum.inr 1117, 720), (Sum.inr 1119, 720), (Sum.inr 1120, 720), (Sum.inr 1141, 720), (Sum.inr 1262, 720), (Sum.inr 1264, 360), (Sum.inr 1295, 360)]

theorem reindexCheck1272 : Integer.Sparse.reindex keyMap MixedData.row1272 = numericRow1272 := by decide +kernel

theorem numericCheck1272 (x : Master → ℝ) : Integer.Sparse.eval numericRow1272 x =
    (360 : ℝ) * reducedSource1272 x := by
  norm_num [numericRow1272, reducedSource1272, Integer.Sparse.eval, Sparse.eval, nodeValue586, nodeValue588, nodeValue589, nodeValue616, nodeValue1117, nodeValue1119, nodeValue1120, nodeValue1141, nodeValue1172, nodeValue1175, nodeValue1176, nodeValue1262, nodeValue1264, nodeValue1267, nodeValue1269, nodeValue1295, nodeValue1302, nodeValue2943, nodeValue3006, nodeValue3110, nodeValue3112]; ring

noncomputable def reducedSource1273 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1522 x + ((1 : ℝ) * Sparse.eval nodeValue1523 x + ((1 : ℝ) * Sparse.eval nodeValue1526 x + ((1 : ℝ) * Sparse.eval nodeValue1533 x + ((2 : ℝ) * Sparse.eval nodeValue3265 x + ((2 : ℝ) * Sparse.eval nodeValue3267 x + ((2 : ℝ) * Sparse.eval nodeValue3268 x + ((2 : ℝ) * Sparse.eval nodeValue3271 x + ((2 : ℝ) * Sparse.eval nodeValue3272 x + ((1 : ℝ) * Sparse.eval nodeValue3276 x + ((1 : ℝ) * Sparse.eval nodeValue3277 x + ((2 : ℝ) * Sparse.eval nodeValue3293 x + ((2 : ℝ) * Sparse.eval nodeValue3294 x + ((1 : ℝ) * Sparse.eval nodeValue3300 x + ((1 : ℝ) * Sparse.eval nodeValue3302 x + ((1 : ℝ) * Sparse.eval nodeValue3305 x + ((1 : ℝ) * Sparse.eval nodeValue3306 x + ((1 : ℝ) * Sparse.eval nodeValue3485 x + ((2 : ℝ) * Sparse.eval nodeValue3522 x + ((1 : ℝ) * Sparse.eval nodeValue3547 x + ((1 : ℝ) * Sparse.eval nodeValue3548 x + 0))))))))))))))))))))

def numericRow1273 : Integer.Sparse Master := [(Sum.inr 1522, 2), (Sum.inr 1523, 1), (Sum.inr 1526, 1), (Sum.inr 1533, 1), (Sum.inr 3265, 2), (Sum.inr 3267, 2), (Sum.inr 3268, 2), (Sum.inr 3271, 2), (Sum.inr 3272, 2), (Sum.inr 3276, 1), (Sum.inr 3277, 1), (Sum.inr 3293, 2), (Sum.inr 3294, 2), (Sum.inr 3300, 1), (Sum.inr 3302, 1), (Sum.inr 3305, 1), (Sum.inr 3306, 1), (Sum.inr 3522, 2), (Sum.inr 3548, 1)]

theorem reindexCheck1273 : Integer.Sparse.reindex keyMap MixedData.row1273 = numericRow1273 := by decide +kernel

theorem numericCheck1273 (x : Master → ℝ) : Integer.Sparse.eval numericRow1273 x =
    (1 : ℝ) * reducedSource1273 x := by
  norm_num [numericRow1273, reducedSource1273, Integer.Sparse.eval, Sparse.eval, nodeValue1522, nodeValue1523, nodeValue1526, nodeValue1533, nodeValue3265, nodeValue3267, nodeValue3268, nodeValue3271, nodeValue3272, nodeValue3276, nodeValue3277, nodeValue3293, nodeValue3294, nodeValue3300, nodeValue3302, nodeValue3305, nodeValue3306, nodeValue3485, nodeValue3522, nodeValue3547, nodeValue3548]

noncomputable def reducedSource1274 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue627 x + ((1 : ℝ) * Sparse.eval nodeValue635 x + ((1 : ℝ) * Sparse.eval nodeValue636 x + ((1 : ℝ) * Sparse.eval nodeValue642 x + ((1 : ℝ) * Sparse.eval nodeValue1246 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow1274 : Integer.Sparse Master := [(Sum.inr 627, 2), (Sum.inr 635, 1), (Sum.inr 636, 1), (Sum.inr 642, 1), (Sum.inr 1246, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1274 : Integer.Sparse.reindex keyMap MixedData.row1274 = numericRow1274 := by decide +kernel

theorem numericCheck1274 (x : Master → ℝ) : Integer.Sparse.eval numericRow1274 x =
    (1 : ℝ) * reducedSource1274 x := by
  norm_num [numericRow1274, reducedSource1274, Integer.Sparse.eval, Sparse.eval, nodeValue627, nodeValue635, nodeValue636, nodeValue642, nodeValue1246, nodeValue4092]

noncomputable def reducedSource1275 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue627 x + ((1 : ℝ) * Sparse.eval nodeValue1134 x + ((1 : ℝ) * Sparse.eval nodeValue1149 x + ((1 : ℝ) * Sparse.eval nodeValue1236 x + ((1 : ℝ) * Sparse.eval nodeValue1237 x + ((1 : ℝ) * Sparse.eval nodeValue1246 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1275 : Integer.Sparse Master := [(Sum.inr 627, 1), (Sum.inr 1134, 1), (Sum.inr 1149, 1), (Sum.inr 1236, 1), (Sum.inr 1237, 1), (Sum.inr 1246, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1275 : Integer.Sparse.reindex keyMap MixedData.row1275 = numericRow1275 := by decide +kernel

theorem numericCheck1275 (x : Master → ℝ) : Integer.Sparse.eval numericRow1275 x =
    (1 : ℝ) * reducedSource1275 x := by
  norm_num [numericRow1275, reducedSource1275, Integer.Sparse.eval, Sparse.eval, nodeValue627, nodeValue1134, nodeValue1149, nodeValue1236, nodeValue1237, nodeValue1246, nodeValue4092]

noncomputable def reducedSource1276 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1149 x + ((1 : ℝ) * Sparse.eval nodeValue1154 x + ((1 : ℝ) * Sparse.eval nodeValue1155 x + ((1 : ℝ) * Sparse.eval nodeValue1160 x + ((1 : ℝ) * Sparse.eval nodeValue1246 x + ((1 : ℝ) * Sparse.eval nodeValue2561 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1276 : Integer.Sparse Master := [(Sum.inr 1149, 1), (Sum.inr 1154, 1), (Sum.inr 1155, 1), (Sum.inr 1160, 1), (Sum.inr 1246, 1), (Sum.inr 2561, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1276 : Integer.Sparse.reindex keyMap MixedData.row1276 = numericRow1276 := by decide +kernel

theorem numericCheck1276 (x : Master → ℝ) : Integer.Sparse.eval numericRow1276 x =
    (1 : ℝ) * reducedSource1276 x := by
  norm_num [numericRow1276, reducedSource1276, Integer.Sparse.eval, Sparse.eval, nodeValue1149, nodeValue1154, nodeValue1155, nodeValue1160, nodeValue1246, nodeValue2561, nodeValue4092]

noncomputable def reducedSource1277 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue642 x + ((2 : ℝ) * Sparse.eval nodeValue1160 x + ((1 : ℝ) * Sparse.eval nodeValue1246 x + ((1 : ℝ) * Sparse.eval nodeValue1294 x + ((1 : ℝ) * Sparse.eval nodeValue1295 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow1277 : Integer.Sparse Master := [(Sum.inr 642, 1), (Sum.inr 1160, 2), (Sum.inr 1246, 1), (Sum.inr 1294, 1), (Sum.inr 1295, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1277 : Integer.Sparse.reindex keyMap MixedData.row1277 = numericRow1277 := by decide +kernel

theorem numericCheck1277 (x : Master → ℝ) : Integer.Sparse.eval numericRow1277 x =
    (1 : ℝ) * reducedSource1277 x := by
  norm_num [numericRow1277, reducedSource1277, Integer.Sparse.eval, Sparse.eval, nodeValue642, nodeValue1160, nodeValue1246, nodeValue1294, nodeValue1295, nodeValue4092]

noncomputable def reducedSource1278 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4145 x + ((1 : ℝ) * Sparse.eval nodeValue4147 x + ((1 : ℝ) * Sparse.eval nodeValue4148 x + ((1 : ℝ) * Sparse.eval nodeValue4180 x + ((2 : ℝ) * Sparse.eval nodeValue4518 x + ((1 : ℝ) * Sparse.eval nodeValue4519 x + ((1 : ℝ) * Sparse.eval nodeValue4520 x + ((2 : ℝ) * Sparse.eval nodeValue4524 x + ((2 : ℝ) * Sparse.eval nodeValue4525 x + ((2 : ℝ) * Sparse.eval nodeValue4526 x + ((2 : ℝ) * Sparse.eval nodeValue4549 x + ((2 : ℝ) * Sparse.eval nodeValue4602 x + ((1 : ℝ) * Sparse.eval nodeValue4605 x + ((2 : ℝ) * Sparse.eval nodeValue4606 x + ((1 : ℝ) * Sparse.eval nodeValue4608 x + ((1 : ℝ) * Sparse.eval nodeValue4623 x + ((1 : ℝ) * Sparse.eval nodeValue4624 x + ((2 : ℝ) * Sparse.eval nodeValue5152 x + ((1 : ℝ) * Sparse.eval nodeValue5207 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + 0))))))))))))))))))))

def numericRow1278 : Integer.Sparse Master := [(Sum.inl 0, 77), (Sum.inl 6, 10), (Sum.inl 2, -55), (Sum.inl 7, -80), (Sum.inl 8, -80), (Sum.inl 3, -80), (Sum.inl 1, -50), (Sum.inr 573, -4320), (Sum.inr 575, -2160), (Sum.inr 576, -2160), (Sum.inr 608, -2160), (Sum.inr 1102, -4320), (Sum.inr 1103, -2160), (Sum.inr 1104, -2160), (Sum.inr 1108, -4320), (Sum.inr 1109, -4320), (Sum.inr 1110, -4320), (Sum.inr 1134, -4320), (Sum.inr 1236, -4320), (Sum.inr 1239, -2160), (Sum.inr 1240, -4320), (Sum.inr 1242, -2160), (Sum.inr 1493, -4320), (Sum.inr 1495, -2160), (Sum.inr 1496, -2160), (Sum.inr 1519, -2160), (Sum.inr 1849, -4320), (Sum.inr 1858, -2160), (Sum.inr 2226, -2160), (Sum.inr 2889, -2160), (Sum.inr 2931, -4320), (Sum.inr 3236, -4320), (Sum.inr 3237, -2160), (Sum.inr 3251, -4320), (Sum.inr 3252, -4320), (Sum.inr 3265, -4320), (Sum.inr 3293, -4320), (Sum.inr 3299, -4320), (Sum.inr 3300, -2160), (Sum.inr 3308, -2160), (Sum.inr 3309, -2160), (Sum.inr 3612, -4320), (Sum.inr 3627, -2160), (Sum.inr 3631, -2160), (Sum.inr 3632, -2160)]

theorem reindexCheck1278 : Integer.Sparse.reindex keyMap MixedData.row1278 = numericRow1278 := by decide +kernel

theorem numericCheck1278 (x : Master → ℝ) : Integer.Sparse.eval numericRow1278 x =
    (8640 : ℝ) * reducedSource1278 x := by
  norm_num [numericRow1278, reducedSource1278, Integer.Sparse.eval, Sparse.eval, nodeValue4145, nodeValue4147, nodeValue4148, nodeValue4180, nodeValue4518, nodeValue4519, nodeValue4520, nodeValue4524, nodeValue4525, nodeValue4526, nodeValue4549, nodeValue4602, nodeValue4605, nodeValue4606, nodeValue4608, nodeValue4623, nodeValue4624, nodeValue5152, nodeValue5207, nodeValue5293, nodeValue5294]; ring

noncomputable def reducedSource1279 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue573 x + ((1 : ℝ) * Sparse.eval nodeValue575 x + ((1 : ℝ) * Sparse.eval nodeValue576 x + ((1 : ℝ) * Sparse.eval nodeValue608 x + ((2 : ℝ) * Sparse.eval nodeValue1102 x + ((1 : ℝ) * Sparse.eval nodeValue1103 x + ((1 : ℝ) * Sparse.eval nodeValue1104 x + ((2 : ℝ) * Sparse.eval nodeValue1108 x + ((2 : ℝ) * Sparse.eval nodeValue1109 x + ((2 : ℝ) * Sparse.eval nodeValue1110 x + ((2 : ℝ) * Sparse.eval nodeValue1134 x + ((2 : ℝ) * Sparse.eval nodeValue1236 x + ((1 : ℝ) * Sparse.eval nodeValue1239 x + ((2 : ℝ) * Sparse.eval nodeValue1240 x + ((1 : ℝ) * Sparse.eval nodeValue1242 x + ((1 : ℝ) * Sparse.eval nodeValue1300 x + ((1 : ℝ) * Sparse.eval nodeValue1301 x + ((1 : ℝ) * Sparse.eval nodeValue2889 x + ((2 : ℝ) * Sparse.eval nodeValue2931 x + ((1 : ℝ) * Sparse.eval nodeValue3101 x + ((1 : ℝ) * Sparse.eval nodeValue3102 x + 0))))))))))))))))))))

def numericRow1279 : Integer.Sparse Master := [(Sum.inl 0, -77), (Sum.inl 6, -10), (Sum.inl 2, 55), (Sum.inl 7, 80), (Sum.inl 8, 80), (Sum.inl 3, 80), (Sum.inl 1, 50), (Sum.inr 573, 4320), (Sum.inr 575, 2160), (Sum.inr 576, 2160), (Sum.inr 608, 2160), (Sum.inr 1102, 4320), (Sum.inr 1103, 2160), (Sum.inr 1104, 2160), (Sum.inr 1108, 4320), (Sum.inr 1109, 4320), (Sum.inr 1110, 4320), (Sum.inr 1134, 4320), (Sum.inr 1236, 4320), (Sum.inr 1239, 2160), (Sum.inr 1240, 4320), (Sum.inr 1242, 2160), (Sum.inr 2889, 2160), (Sum.inr 2931, 4320)]

theorem reindexCheck1279 : Integer.Sparse.reindex keyMap MixedData.row1279 = numericRow1279 := by decide +kernel

theorem numericCheck1279 (x : Master → ℝ) : Integer.Sparse.eval numericRow1279 x =
    (2160 : ℝ) * reducedSource1279 x := by
  norm_num [numericRow1279, reducedSource1279, Integer.Sparse.eval, Sparse.eval, nodeValue573, nodeValue575, nodeValue576, nodeValue608, nodeValue1102, nodeValue1103, nodeValue1104, nodeValue1108, nodeValue1109, nodeValue1110, nodeValue1134, nodeValue1236, nodeValue1239, nodeValue1240, nodeValue1242, nodeValue1300, nodeValue1301, nodeValue2889, nodeValue2931, nodeValue3101, nodeValue3102]; ring

end MUB6.Certificate.MixedSourceBridge

end OAI
