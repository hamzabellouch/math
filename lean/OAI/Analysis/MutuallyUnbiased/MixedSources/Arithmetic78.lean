import OAI.Analysis.MutuallyUnbiased.MixedData.Source9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
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

noncomputable def reducedSource1248 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1655 x + ((1 : ℝ) * Sparse.eval nodeValue1657 x + ((1 : ℝ) * Sparse.eval nodeValue1660 x + ((1 : ℝ) * Sparse.eval nodeValue1738 x + ((1 : ℝ) * Sparse.eval nodeValue2683 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0)))))

def numericRow1248 : Integer.Sparse Master := [(Sum.inr 1655, 2), (Sum.inr 1657, 1), (Sum.inr 1660, 1), (Sum.inr 1738, 1), (Sum.inr 2683, 1), (Sum.inr 4071, -1)]

theorem reindexCheck1248 : Integer.Sparse.reindex keyMap MixedData.row1248 = numericRow1248 := by decide +kernel

theorem numericCheck1248 (x : Master → ℝ) : Integer.Sparse.eval numericRow1248 x =
    (1 : ℝ) * reducedSource1248 x := by
  norm_num [numericRow1248, reducedSource1248, Integer.Sparse.eval, Sparse.eval, nodeValue1655, nodeValue1657, nodeValue1660, nodeValue1738, nodeValue2683, nodeValue4071]

noncomputable def reducedSource1249 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1741 x + ((3 : ℝ) * Sparse.eval nodeValue2683 x + ((1 : ℝ) * Sparse.eval nodeValue2780 x + ((1 : ℝ) * Sparse.eval nodeValue3311 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0))))

def numericRow1249 : Integer.Sparse Master := [(Sum.inr 1741, 1), (Sum.inr 2683, 3), (Sum.inr 2780, 1), (Sum.inr 3311, 1), (Sum.inr 4071, -1)]

theorem reindexCheck1249 : Integer.Sparse.reindex keyMap MixedData.row1249 = numericRow1249 := by decide +kernel

theorem numericCheck1249 (x : Master → ℝ) : Integer.Sparse.eval numericRow1249 x =
    (1 : ℝ) * reducedSource1249 x := by
  norm_num [numericRow1249, reducedSource1249, Integer.Sparse.eval, Sparse.eval, nodeValue1741, nodeValue2683, nodeValue2780, nodeValue3311, nodeValue4071]

noncomputable def reducedSource1250 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1627 x + ((2 : ℝ) * Sparse.eval nodeValue2397 x + ((1 : ℝ) * Sparse.eval nodeValue2409 x + ((1 : ℝ) * Sparse.eval nodeValue2683 x + ((1 : ℝ) * Sparse.eval nodeValue3301 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0)))))

def numericRow1250 : Integer.Sparse Master := [(Sum.inr 1627, 1), (Sum.inr 2397, 2), (Sum.inr 2409, 1), (Sum.inr 2683, 1), (Sum.inr 3301, 1), (Sum.inr 4071, -1)]

theorem reindexCheck1250 : Integer.Sparse.reindex keyMap MixedData.row1250 = numericRow1250 := by decide +kernel

theorem numericCheck1250 (x : Master → ℝ) : Integer.Sparse.eval numericRow1250 x =
    (1 : ℝ) * reducedSource1250 x := by
  norm_num [numericRow1250, reducedSource1250, Integer.Sparse.eval, Sparse.eval, nodeValue1627, nodeValue2397, nodeValue2409, nodeValue2683, nodeValue3301, nodeValue4071]

noncomputable def reducedSource1251 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1738 x + ((1 : ℝ) * Sparse.eval nodeValue2683 x + ((2 : ℝ) * Sparse.eval nodeValue3295 x + ((1 : ℝ) * Sparse.eval nodeValue3301 x + ((1 : ℝ) * Sparse.eval nodeValue3311 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0)))))

def numericRow1251 : Integer.Sparse Master := [(Sum.inr 1738, 1), (Sum.inr 2683, 1), (Sum.inr 3295, 2), (Sum.inr 3301, 1), (Sum.inr 3311, 1), (Sum.inr 4071, -1)]

theorem reindexCheck1251 : Integer.Sparse.reindex keyMap MixedData.row1251 = numericRow1251 := by decide +kernel

theorem numericCheck1251 (x : Master → ℝ) : Integer.Sparse.eval numericRow1251 x =
    (1 : ℝ) * reducedSource1251 x := by
  norm_num [numericRow1251, reducedSource1251, Integer.Sparse.eval, Sparse.eval, nodeValue1738, nodeValue2683, nodeValue3295, nodeValue3301, nodeValue3311, nodeValue4071]

noncomputable def reducedSource1252 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1113 x + ((1 : ℝ) * Sparse.eval nodeValue1119 x + ((1 : ℝ) * Sparse.eval nodeValue1121 x + ((1 : ℝ) * Sparse.eval nodeValue1138 x + ((1 : ℝ) * Sparse.eval nodeValue1219 x + ((1 : ℝ) * Sparse.eval nodeValue2488 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1252 : Integer.Sparse Master := [(Sum.inr 1113, 1), (Sum.inr 1119, 1), (Sum.inr 1121, 1), (Sum.inr 1138, 1), (Sum.inr 1219, 1), (Sum.inr 2488, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1252 : Integer.Sparse.reindex keyMap MixedData.row1252 = numericRow1252 := by decide +kernel

theorem numericCheck1252 (x : Master → ℝ) : Integer.Sparse.eval numericRow1252 x =
    (1 : ℝ) * reducedSource1252 x := by
  norm_num [numericRow1252, reducedSource1252, Integer.Sparse.eval, Sparse.eval, nodeValue1113, nodeValue1119, nodeValue1121, nodeValue1138, nodeValue1219, nodeValue2488, nodeValue4092]

noncomputable def reducedSource1253 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue631 x + ((1 : ℝ) * Sparse.eval nodeValue1138 x + ((1 : ℝ) * Sparse.eval nodeValue1151 x + ((1 : ℝ) * Sparse.eval nodeValue1219 x + ((1 : ℝ) * Sparse.eval nodeValue1236 x + ((1 : ℝ) * Sparse.eval nodeValue1241 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1253 : Integer.Sparse Master := [(Sum.inr 631, 1), (Sum.inr 1138, 1), (Sum.inr 1151, 1), (Sum.inr 1219, 1), (Sum.inr 1236, 1), (Sum.inr 1241, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1253 : Integer.Sparse.reindex keyMap MixedData.row1253 = numericRow1253 := by decide +kernel

theorem numericCheck1253 (x : Master → ℝ) : Integer.Sparse.eval numericRow1253 x =
    (1 : ℝ) * reducedSource1253 x := by
  norm_num [numericRow1253, reducedSource1253, Integer.Sparse.eval, Sparse.eval, nodeValue631, nodeValue1138, nodeValue1151, nodeValue1219, nodeValue1236, nodeValue1241, nodeValue4092]

noncomputable def reducedSource1254 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1606 x + ((1 : ℝ) * Sparse.eval nodeValue1608 x + ((1 : ℝ) * Sparse.eval nodeValue1611 x + ((1 : ℝ) * Sparse.eval nodeValue1618 x + ((1 : ℝ) * Sparse.eval nodeValue1738 x + ((1 : ℝ) * Sparse.eval nodeValue3295 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0))))))

def numericRow1254 : Integer.Sparse Master := [(Sum.inr 1606, 1), (Sum.inr 1608, 1), (Sum.inr 1611, 1), (Sum.inr 1618, 1), (Sum.inr 1738, 1), (Sum.inr 3295, 1), (Sum.inr 4071, -1)]

theorem reindexCheck1254 : Integer.Sparse.reindex keyMap MixedData.row1254 = numericRow1254 := by decide +kernel

theorem numericCheck1254 (x : Master → ℝ) : Integer.Sparse.eval numericRow1254 x =
    (1 : ℝ) * reducedSource1254 x := by
  norm_num [numericRow1254, reducedSource1254, Integer.Sparse.eval, Sparse.eval, nodeValue1606, nodeValue1608, nodeValue1611, nodeValue1618, nodeValue1738, nodeValue3295, nodeValue4071]

noncomputable def reducedSource1255 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1114 x + ((2 : ℝ) * Sparse.eval nodeValue1120 x + ((1 : ℝ) * Sparse.eval nodeValue1139 x + ((1 : ℝ) * Sparse.eval nodeValue1220 x + ((1 : ℝ) * Sparse.eval nodeValue2489 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow1255 : Integer.Sparse Master := [(Sum.inr 1114, 1), (Sum.inr 1120, 2), (Sum.inr 1139, 1), (Sum.inr 1220, 1), (Sum.inr 2489, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1255 : Integer.Sparse.reindex keyMap MixedData.row1255 = numericRow1255 := by decide +kernel

theorem numericCheck1255 (x : Master → ℝ) : Integer.Sparse.eval numericRow1255 x =
    (1 : ℝ) * reducedSource1255 x := by
  norm_num [numericRow1255, reducedSource1255, Integer.Sparse.eval, Sparse.eval, nodeValue1114, nodeValue1120, nodeValue1139, nodeValue1220, nodeValue2489, nodeValue4091]

noncomputable def reducedSource1256 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue632 x + ((1 : ℝ) * Sparse.eval nodeValue1139 x + ((1 : ℝ) * Sparse.eval nodeValue1152 x + ((1 : ℝ) * Sparse.eval nodeValue1220 x + ((2 : ℝ) * Sparse.eval nodeValue1240 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow1256 : Integer.Sparse Master := [(Sum.inr 632, 1), (Sum.inr 1139, 1), (Sum.inr 1152, 1), (Sum.inr 1220, 1), (Sum.inr 1240, 2), (Sum.inr 4091, -1)]

theorem reindexCheck1256 : Integer.Sparse.reindex keyMap MixedData.row1256 = numericRow1256 := by decide +kernel

theorem numericCheck1256 (x : Master → ℝ) : Integer.Sparse.eval numericRow1256 x =
    (1 : ℝ) * reducedSource1256 x := by
  norm_num [numericRow1256, reducedSource1256, Integer.Sparse.eval, Sparse.eval, nodeValue632, nodeValue1139, nodeValue1152, nodeValue1220, nodeValue1240, nodeValue4091]

noncomputable def reducedSource1257 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1614 x + ((2 : ℝ) * Sparse.eval nodeValue1618 x + ((1 : ℝ) * Sparse.eval nodeValue1626 x + ((1 : ℝ) * Sparse.eval nodeValue1751 x + ((1 : ℝ) * Sparse.eval nodeValue3297 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0)))))

def numericRow1257 : Integer.Sparse Master := [(Sum.inr 1618, 2), (Sum.inr 1626, 1), (Sum.inr 1751, 1), (Sum.inr 3297, 1), (Sum.inr 4071, -1)]

theorem reindexCheck1257 : Integer.Sparse.reindex keyMap MixedData.row1257 = numericRow1257 := by decide +kernel

theorem numericCheck1257 (x : Master → ℝ) : Integer.Sparse.eval numericRow1257 x =
    (1 : ℝ) * reducedSource1257 x := by
  norm_num [numericRow1257, reducedSource1257, Integer.Sparse.eval, Sparse.eval, nodeValue1614, nodeValue1618, nodeValue1626, nodeValue1751, nodeValue3297, nodeValue4071]

noncomputable def reducedSource1258 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1751 x + ((2 : ℝ) * Sparse.eval nodeValue3297 x + ((2 : ℝ) * Sparse.eval nodeValue3301 x + ((1 : ℝ) * Sparse.eval nodeValue3312 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0))))

def numericRow1258 : Integer.Sparse Master := [(Sum.inr 1751, 1), (Sum.inr 3297, 2), (Sum.inr 3301, 2), (Sum.inr 3312, 1), (Sum.inr 4071, -1)]

theorem reindexCheck1258 : Integer.Sparse.reindex keyMap MixedData.row1258 = numericRow1258 := by decide +kernel

theorem numericCheck1258 (x : Master → ℝ) : Integer.Sparse.eval numericRow1258 x =
    (1 : ℝ) * reducedSource1258 x := by
  norm_num [numericRow1258, reducedSource1258, Integer.Sparse.eval, Sparse.eval, nodeValue1751, nodeValue3297, nodeValue3301, nodeValue3312, nodeValue4071]

noncomputable def reducedSource1259 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1182 x + ((1 : ℝ) * Sparse.eval nodeValue2388 x + ((1 : ℝ) * Sparse.eval nodeValue2533 x + ((1 : ℝ) * Sparse.eval nodeValue2608 x + ((1 : ℝ) * Sparse.eval nodeValue2672 x + ((1 : ℝ) * Sparse.eval nodeValue2673 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0))))))

def numericRow1259 : Integer.Sparse Master := [(Sum.inr 1182, 1), (Sum.inr 2388, 1), (Sum.inr 2533, 1), (Sum.inr 2608, 1), (Sum.inr 2672, 1), (Sum.inr 2673, 1), (Sum.inr 4088, -1)]

theorem reindexCheck1259 : Integer.Sparse.reindex keyMap MixedData.row1259 = numericRow1259 := by decide +kernel

theorem numericCheck1259 (x : Master → ℝ) : Integer.Sparse.eval numericRow1259 x =
    (1 : ℝ) * reducedSource1259 x := by
  norm_num [numericRow1259, reducedSource1259, Integer.Sparse.eval, Sparse.eval, nodeValue1182, nodeValue2388, nodeValue2533, nodeValue2608, nodeValue2672, nodeValue2673, nodeValue4088]

noncomputable def reducedSource1260 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1196 x + ((2 : ℝ) * Sparse.eval nodeValue2452 x + ((1 : ℝ) * Sparse.eval nodeValue2609 x + ((1 : ℝ) * Sparse.eval nodeValue2694 x + ((1 : ℝ) * Sparse.eval nodeValue2695 x + ((-1 : ℝ) * Sparse.eval nodeValue4090 x + 0)))))

def numericRow1260 : Integer.Sparse Master := [(Sum.inr 1196, 1), (Sum.inr 2452, 2), (Sum.inr 2609, 1), (Sum.inr 2694, 1), (Sum.inr 4090, -1)]

theorem reindexCheck1260 : Integer.Sparse.reindex keyMap MixedData.row1260 = numericRow1260 := by decide +kernel

theorem numericCheck1260 (x : Master → ℝ) : Integer.Sparse.eval numericRow1260 x =
    (1 : ℝ) * reducedSource1260 x := by
  norm_num [numericRow1260, reducedSource1260, Integer.Sparse.eval, Sparse.eval, nodeValue1196, nodeValue2452, nodeValue2609, nodeValue2694, nodeValue2695, nodeValue4090]

noncomputable def reducedSource1261 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4185 x + ((1 : ℝ) * Sparse.eval nodeValue4190 x + ((1 : ℝ) * Sparse.eval nodeValue4192 x + ((6 : ℝ) * Sparse.eval nodeValue4553 x + ((3 : ℝ) * Sparse.eval nodeValue4557 x + ((3 : ℝ) * Sparse.eval nodeValue4559 x + ((3 : ℝ) * Sparse.eval nodeValue4619 x + ((1 : ℝ) * Sparse.eval nodeValue4621 x + ((3 : ℝ) * Sparse.eval nodeValue4623 x + ((1 : ℝ) * Sparse.eval nodeValue4625 x + ((3 : ℝ) * Sparse.eval nodeValue5176 x + ((1 : ℝ) * Sparse.eval nodeValue5308 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + 0))))))))))))

def numericRow1261 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 5, -1), (Sum.inl 7, -4), (Sum.inl 1, 4), (Sum.inr 613, -54), (Sum.inr 618, -18), (Sum.inr 620, -18), (Sum.inr 1138, -108), (Sum.inr 1143, -54), (Sum.inr 1145, -54), (Sum.inr 1294, -54), (Sum.inr 1297, -18), (Sum.inr 1525, -54), (Sum.inr 1527, -18), (Sum.inr 1539, -18), (Sum.inr 2167, -54), (Sum.inr 2289, -18), (Sum.inr 3270, -108), (Sum.inr 3277, -54), (Sum.inr 3305, -54), (Sum.inr 3308, -54), (Sum.inr 3310, -18), (Sum.inr 3614, -54), (Sum.inr 3633, -18)]

theorem reindexCheck1261 : Integer.Sparse.reindex keyMap MixedData.row1261 = numericRow1261 := by decide +kernel

theorem numericCheck1261 (x : Master → ℝ) : Integer.Sparse.eval numericRow1261 x =
    (72 : ℝ) * reducedSource1261 x := by
  norm_num [numericRow1261, reducedSource1261, Integer.Sparse.eval, Sparse.eval, nodeValue4185, nodeValue4190, nodeValue4192, nodeValue4553, nodeValue4557, nodeValue4559, nodeValue4619, nodeValue4621, nodeValue4623, nodeValue4625, nodeValue5176, nodeValue5308, nodeValue5310]
  ring

noncomputable def reducedSource1262 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue613 x + ((1 : ℝ) * Sparse.eval nodeValue618 x + ((1 : ℝ) * Sparse.eval nodeValue620 x + ((6 : ℝ) * Sparse.eval nodeValue1138 x + ((3 : ℝ) * Sparse.eval nodeValue1143 x + ((3 : ℝ) * Sparse.eval nodeValue1145 x + ((3 : ℝ) * Sparse.eval nodeValue1294 x + ((1 : ℝ) * Sparse.eval nodeValue1297 x + ((3 : ℝ) * Sparse.eval nodeValue1305 x + ((1 : ℝ) * Sparse.eval nodeValue1307 x + ((3 : ℝ) * Sparse.eval nodeValue2968 x + ((1 : ℝ) * Sparse.eval nodeValue3121 x + ((1 : ℝ) * Sparse.eval nodeValue3124 x + 0))))))))))))

def numericRow1262 : Integer.Sparse Master := [(Sum.inl 0, -1), (Sum.inl 5, 1), (Sum.inl 7, 4), (Sum.inl 1, -4), (Sum.inr 613, 54), (Sum.inr 618, 18), (Sum.inr 620, 18), (Sum.inr 1138, 108), (Sum.inr 1143, 54), (Sum.inr 1145, 54), (Sum.inr 1294, 54), (Sum.inr 1297, 18)]

theorem reindexCheck1262 : Integer.Sparse.reindex keyMap MixedData.row1262 = numericRow1262 := by decide +kernel

theorem numericCheck1262 (x : Master → ℝ) : Integer.Sparse.eval numericRow1262 x =
    (18 : ℝ) * reducedSource1262 x := by
  norm_num [numericRow1262, reducedSource1262, Integer.Sparse.eval, Sparse.eval, nodeValue613, nodeValue618, nodeValue620, nodeValue1138, nodeValue1143, nodeValue1145, nodeValue1294, nodeValue1297, nodeValue1305, nodeValue1307, nodeValue2968, nodeValue3121, nodeValue3124]
  ring

noncomputable def reducedSource1263 (x : Master → ℝ) : ℝ :=
  (6 : ℝ) * Sparse.eval nodeValue4466 x + ((2 : ℝ) * Sparse.eval nodeValue4510 x + ((2 : ℝ) * Sparse.eval nodeValue4511 x + ((6 : ℝ) * Sparse.eval nodeValue4592 x + ((6 : ℝ) * Sparse.eval nodeValue4611 x + ((6 : ℝ) * Sparse.eval nodeValue4612 x + ((1 : ℝ) * Sparse.eval nodeValue4626 x + ((1 : ℝ) * Sparse.eval nodeValue4628 x + 0)))))))

def numericRow1263 : Integer.Sparse Master := [(Sum.inl 0, 3), (Sum.inl 5, 10), (Sum.inl 8, 40), (Sum.inl 1, -5), (Sum.inr 1049, -2160), (Sum.inr 1094, -720), (Sum.inr 1246, -2160), (Sum.inr 1738, -2160), (Sum.inr 1741, -720), (Sum.inr 3301, -2160), (Sum.inr 3312, -360), (Sum.inr 4592, 8640), (Sum.inr 4611, 8640), (Sum.inr 4626, 1440)]

theorem reindexCheck1263 : Integer.Sparse.reindex keyMap MixedData.row1263 = numericRow1263 := by decide +kernel

theorem numericCheck1263 (x : Master → ℝ) : Integer.Sparse.eval numericRow1263 x =
    (1440 : ℝ) * reducedSource1263 x := by
  norm_num [numericRow1263, reducedSource1263, Integer.Sparse.eval, Sparse.eval, nodeValue4466, nodeValue4510, nodeValue4511, nodeValue4592, nodeValue4611, nodeValue4612, nodeValue4626, nodeValue4628]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
