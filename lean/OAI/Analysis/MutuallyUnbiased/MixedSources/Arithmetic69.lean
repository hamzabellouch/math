import OAI.Analysis.MutuallyUnbiased.MixedData.Source8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values9
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1104 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1530 x + ((1 : ℝ) * Sparse.eval nodeValue1531 x + ((1 : ℝ) * Sparse.eval nodeValue1540 x + ((3 : ℝ) * Sparse.eval nodeValue1722 x + ((1 : ℝ) * Sparse.eval nodeValue1752 x + ((6 : ℝ) * Sparse.eval nodeValue2200 x + ((3 : ℝ) * Sparse.eval nodeValue2226 x + ((3 : ℝ) * Sparse.eval nodeValue2258 x + ((3 : ℝ) * Sparse.eval nodeValue2261 x + ((1 : ℝ) * Sparse.eval nodeValue2292 x + ((3 : ℝ) * Sparse.eval nodeValue2737 x + ((1 : ℝ) * Sparse.eval nodeValue2780 x + ((1 : ℝ) * Sparse.eval nodeValue2783 x + 0))))))))))))

def numericRow1104 : Integer.Sparse Master := [(Sum.inr 1530, 3), (Sum.inr 1531, 1), (Sum.inr 1540, 1), (Sum.inr 1722, 3), (Sum.inr 1752, 1), (Sum.inr 2200, 6), (Sum.inr 2226, 3), (Sum.inr 2258, 3), (Sum.inr 2261, 3), (Sum.inr 2737, 3), (Sum.inr 2780, 1), (Sum.inr 2783, 1)]

theorem reindexCheck1104 : Integer.Sparse.reindex keyMap MixedData.row1104 = numericRow1104 := by decide +kernel

theorem numericCheck1104 (x : Master → ℝ) : Integer.Sparse.eval numericRow1104 x =
    (1 : ℝ) * reducedSource1104 x := by
  norm_num [numericRow1104, reducedSource1104, Integer.Sparse.eval, Sparse.eval, nodeValue1530, nodeValue1531, nodeValue1540, nodeValue1722, nodeValue1752, nodeValue2200, nodeValue2226, nodeValue2258, nodeValue2261, nodeValue2292, nodeValue2737, nodeValue2780, nodeValue2783]

noncomputable def reducedSource1105 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue639 x + ((1 : ℝ) * Sparse.eval nodeValue643 x + ((1 : ℝ) * Sparse.eval nodeValue654 x + ((1 : ℝ) * Sparse.eval nodeValue1297 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

def numericRow1105 : Integer.Sparse Master := [(Sum.inr 639, 3), (Sum.inr 643, 1), (Sum.inr 654, 1), (Sum.inr 1297, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1105 : Integer.Sparse.reindex keyMap MixedData.row1105 = numericRow1105 := by decide +kernel

theorem numericCheck1105 (x : Master → ℝ) : Integer.Sparse.eval numericRow1105 x =
    (1 : ℝ) * reducedSource1105 x := by
  norm_num [numericRow1105, reducedSource1105, Integer.Sparse.eval, Sparse.eval, nodeValue639, nodeValue643, nodeValue654, nodeValue1297, nodeValue4084]

noncomputable def reducedSource1106 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue639 x + ((2 : ℝ) * Sparse.eval nodeValue1157 x + ((1 : ℝ) * Sparse.eval nodeValue1239 x + ((1 : ℝ) * Sparse.eval nodeValue1292 x + ((1 : ℝ) * Sparse.eval nodeValue1297 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1106 : Integer.Sparse Master := [(Sum.inr 639, 1), (Sum.inr 1157, 2), (Sum.inr 1239, 1), (Sum.inr 1292, 1), (Sum.inr 1297, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1106 : Integer.Sparse.reindex keyMap MixedData.row1106 = numericRow1106 := by decide +kernel

theorem numericCheck1106 (x : Master → ℝ) : Integer.Sparse.eval numericRow1106 x =
    (1 : ℝ) * reducedSource1106 x := by
  norm_num [numericRow1106, reducedSource1106, Integer.Sparse.eval, Sparse.eval, nodeValue639, nodeValue1157, nodeValue1239, nodeValue1292, nodeValue1297, nodeValue4084]

noncomputable def reducedSource1107 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue948 x + ((2 : ℝ) * Sparse.eval nodeValue1157 x + ((1 : ℝ) * Sparse.eval nodeValue1174 x + ((1 : ℝ) * Sparse.eval nodeValue1297 x + ((1 : ℝ) * Sparse.eval nodeValue2109 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1107 : Integer.Sparse Master := [(Sum.inr 948, 1), (Sum.inr 1157, 2), (Sum.inr 1174, 1), (Sum.inr 1297, 1), (Sum.inr 2109, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1107 : Integer.Sparse.reindex keyMap MixedData.row1107 = numericRow1107 := by decide +kernel

theorem numericCheck1107 (x : Master → ℝ) : Integer.Sparse.eval numericRow1107 x =
    (1 : ℝ) * reducedSource1107 x := by
  norm_num [numericRow1107, reducedSource1107, Integer.Sparse.eval, Sparse.eval, nodeValue948, nodeValue1157, nodeValue1174, nodeValue1297, nodeValue2109, nodeValue4084]

noncomputable def reducedSource1108 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4166 x + ((1 : ℝ) * Sparse.eval nodeValue4168 x + ((1 : ℝ) * Sparse.eval nodeValue4190 x + ((3 : ℝ) * Sparse.eval nodeValue4240 x + ((1 : ℝ) * Sparse.eval nodeValue4280 x + ((6 : ℝ) * Sparse.eval nodeValue4538 x + ((3 : ℝ) * Sparse.eval nodeValue4557 x + ((3 : ℝ) * Sparse.eval nodeValue4572 x + ((3 : ℝ) * Sparse.eval nodeValue4619 x + ((1 : ℝ) * Sparse.eval nodeValue4627 x + ((3 : ℝ) * Sparse.eval nodeValue4871 x + ((1 : ℝ) * Sparse.eval nodeValue4899 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + 0))))))))))))

def numericRow1108 : Integer.Sparse Master := [(Sum.inl 0, 9), (Sum.inl 5, 20), (Sum.inl 2, -5), (Sum.inl 7, 80), (Sum.inl 3, 80), (Sum.inl 1, 50), (Sum.inr 594, -2160), (Sum.inr 596, -720), (Sum.inr 618, -720), (Sum.inr 740, -2160), (Sum.inr 832, -720), (Sum.inr 842, -2160), (Sum.inr 845, -720), (Sum.inr 862, -720), (Sum.inr 1123, -4320), (Sum.inr 1143, -2160), (Sum.inr 1190, -2160), (Sum.inr 1294, -2160), (Sum.inr 1499, -2160), (Sum.inr 1527, -720), (Sum.inr 1937, -4320), (Sum.inr 1952, -2160), (Sum.inr 2112, -2160), (Sum.inr 2167, -2160), (Sum.inr 2281, -720), (Sum.inr 2287, -2160), (Sum.inr 2294, -720), (Sum.inr 3305, -2160), (Sum.inr 3311, -720), (Sum.inr 3633, -720)]

theorem reindexCheck1108 : Integer.Sparse.reindex keyMap MixedData.row1108 = numericRow1108 := by decide +kernel

theorem numericCheck1108 (x : Master → ℝ) : Integer.Sparse.eval numericRow1108 x =
    (2880 : ℝ) * reducedSource1108 x := by
  norm_num [numericRow1108, reducedSource1108, Integer.Sparse.eval, Sparse.eval, nodeValue4166, nodeValue4168, nodeValue4190, nodeValue4240, nodeValue4280, nodeValue4538, nodeValue4557, nodeValue4572, nodeValue4619, nodeValue4627, nodeValue4871, nodeValue4899, nodeValue5310]
  ring

noncomputable def reducedSource1109 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue594 x + ((1 : ℝ) * Sparse.eval nodeValue596 x + ((1 : ℝ) * Sparse.eval nodeValue618 x + ((3 : ℝ) * Sparse.eval nodeValue740 x + ((1 : ℝ) * Sparse.eval nodeValue832 x + ((6 : ℝ) * Sparse.eval nodeValue1123 x + ((3 : ℝ) * Sparse.eval nodeValue1143 x + ((3 : ℝ) * Sparse.eval nodeValue1190 x + ((3 : ℝ) * Sparse.eval nodeValue1294 x + ((1 : ℝ) * Sparse.eval nodeValue1311 x + ((3 : ℝ) * Sparse.eval nodeValue2112 x + ((1 : ℝ) * Sparse.eval nodeValue2281 x + ((1 : ℝ) * Sparse.eval nodeValue3121 x + 0))))))))))))

def numericRow1109 : Integer.Sparse Master := [(Sum.inl 0, -9), (Sum.inl 5, -20), (Sum.inl 2, 5), (Sum.inl 7, -80), (Sum.inl 3, -80), (Sum.inl 1, -50), (Sum.inr 594, 2160), (Sum.inr 596, 720), (Sum.inr 618, 720), (Sum.inr 740, 2160), (Sum.inr 832, 720), (Sum.inr 1123, 4320), (Sum.inr 1143, 2160), (Sum.inr 1190, 2160), (Sum.inr 1294, 2160), (Sum.inr 2112, 2160), (Sum.inr 2281, 720)]

theorem reindexCheck1109 : Integer.Sparse.reindex keyMap MixedData.row1109 = numericRow1109 := by decide +kernel

theorem numericCheck1109 (x : Master → ℝ) : Integer.Sparse.eval numericRow1109 x =
    (720 : ℝ) * reducedSource1109 x := by
  norm_num [numericRow1109, reducedSource1109, Integer.Sparse.eval, Sparse.eval, nodeValue594, nodeValue596, nodeValue618, nodeValue740, nodeValue832, nodeValue1123, nodeValue1143, nodeValue1190, nodeValue1294, nodeValue1311, nodeValue2112, nodeValue2281, nodeValue3121]
  ring

noncomputable def reducedSource1110 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1037 x + ((1 : ℝ) * Sparse.eval nodeValue1077 x + ((1 : ℝ) * Sparse.eval nodeValue1085 x + ((6 : ℝ) * Sparse.eval nodeValue1211 x + ((3 : ℝ) * Sparse.eval nodeValue1231 x + ((3 : ℝ) * Sparse.eval nodeValue1239 x + ((3 : ℝ) * Sparse.eval nodeValue1258 x + ((3 : ℝ) * Sparse.eval nodeValue1264 x + ((1 : ℝ) * Sparse.eval nodeValue1289 x + ((1 : ℝ) * Sparse.eval nodeValue1304 x + ((3 : ℝ) * Sparse.eval nodeValue1408 x + ((1 : ℝ) * Sparse.eval nodeValue1438 x + ((1 : ℝ) * Sparse.eval nodeValue1445 x + 0))))))))))))

def numericRow1110 : Integer.Sparse Master := [(Sum.inl 0, -40), (Sum.inl 5, 80), (Sum.inl 6, 40), (Sum.inl 2, 40), (Sum.inl 52, -320), (Sum.inl 1, -40), (Sum.inr 1037, 8640), (Sum.inr 1077, 2880), (Sum.inr 1211, 17280), (Sum.inr 1231, 8640), (Sum.inr 1239, 8640), (Sum.inr 1258, 8640), (Sum.inr 1264, 8640), (Sum.inr 1289, 2880), (Sum.inr 1408, 8640), (Sum.inr 1438, 2880)]

theorem reindexCheck1110 : Integer.Sparse.reindex keyMap MixedData.row1110 = numericRow1110 := by decide +kernel

theorem numericCheck1110 (x : Master → ℝ) : Integer.Sparse.eval numericRow1110 x =
    (2880 : ℝ) * reducedSource1110 x := by
  norm_num [numericRow1110, reducedSource1110, Integer.Sparse.eval, Sparse.eval, nodeValue1037, nodeValue1077, nodeValue1085, nodeValue1211, nodeValue1231, nodeValue1239, nodeValue1258, nodeValue1264, nodeValue1289, nodeValue1304, nodeValue1408, nodeValue1438, nodeValue1445]
  ring

noncomputable def reducedSource1111 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1047 x + ((1 : ℝ) * Sparse.eval nodeValue1091 x + ((1 : ℝ) * Sparse.eval nodeValue1092 x + ((6 : ℝ) * Sparse.eval nodeValue1218 x + ((3 : ℝ) * Sparse.eval nodeValue1243 x + ((3 : ℝ) * Sparse.eval nodeValue1244 x + ((3 : ℝ) * Sparse.eval nodeValue1271 x + ((3 : ℝ) * Sparse.eval nodeValue1272 x + ((1 : ℝ) * Sparse.eval nodeValue1307 x + ((1 : ℝ) * Sparse.eval nodeValue1309 x + ((3 : ℝ) * Sparse.eval nodeValue1417 x + ((1 : ℝ) * Sparse.eval nodeValue1452 x + ((1 : ℝ) * Sparse.eval nodeValue1453 x + 0))))))))))))

def numericRow1111 : Integer.Sparse Master := [(Sum.inl 0, -40), (Sum.inl 6, 50), (Sum.inl 2, 40), (Sum.inl 35, 160), (Sum.inl 1, 30), (Sum.inr 1047, 2160), (Sum.inr 1091, 720), (Sum.inr 1092, 720), (Sum.inr 1218, 4320), (Sum.inr 1243, 2160), (Sum.inr 1244, 2160), (Sum.inr 1272, 2160), (Sum.inr 1309, 720)]

theorem reindexCheck1111 : Integer.Sparse.reindex keyMap MixedData.row1111 = numericRow1111 := by decide +kernel

theorem numericCheck1111 (x : Master → ℝ) : Integer.Sparse.eval numericRow1111 x =
    (720 : ℝ) * reducedSource1111 x := by
  norm_num [numericRow1111, reducedSource1111, Integer.Sparse.eval, Sparse.eval, nodeValue1047, nodeValue1091, nodeValue1092, nodeValue1218, nodeValue1243, nodeValue1244, nodeValue1271, nodeValue1272, nodeValue1307, nodeValue1309, nodeValue1417, nodeValue1452, nodeValue1453]
  ring

noncomputable def reducedSource1112 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1077 x + ((3 : ℝ) * Sparse.eval nodeValue1647 x + ((1 : ℝ) * Sparse.eval nodeValue1730 x + ((1 : ℝ) * Sparse.eval nodeValue2289 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0))))

def numericRow1112 : Integer.Sparse Master := [(Sum.inr 1077, 1), (Sum.inr 1647, 3), (Sum.inr 2289, 1), (Sum.inr 4070, -1)]

theorem reindexCheck1112 : Integer.Sparse.reindex keyMap MixedData.row1112 = numericRow1112 := by decide +kernel

theorem numericCheck1112 (x : Master → ℝ) : Integer.Sparse.eval numericRow1112 x =
    (1 : ℝ) * reducedSource1112 x := by
  norm_num [numericRow1112, reducedSource1112, Integer.Sparse.eval, Sparse.eval, nodeValue1077, nodeValue1647, nodeValue1730, nodeValue2289, nodeValue4070]

noncomputable def reducedSource1113 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1289 x + ((3 : ℝ) * Sparse.eval nodeValue1657 x + ((1 : ℝ) * Sparse.eval nodeValue1741 x + ((1 : ℝ) * Sparse.eval nodeValue2780 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0))))

def numericRow1113 : Integer.Sparse Master := [(Sum.inr 1289, 1), (Sum.inr 1657, 3), (Sum.inr 1741, 1), (Sum.inr 2780, 1), (Sum.inr 4071, -1)]

theorem reindexCheck1113 : Integer.Sparse.reindex keyMap MixedData.row1113 = numericRow1113 := by decide +kernel

theorem numericCheck1113 (x : Master → ℝ) : Integer.Sparse.eval numericRow1113 x =
    (1 : ℝ) * reducedSource1113 x := by
  norm_num [numericRow1113, reducedSource1113, Integer.Sparse.eval, Sparse.eval, nodeValue1289, nodeValue1657, nodeValue1741, nodeValue2780, nodeValue4071]

noncomputable def reducedSource1114 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4153 x + ((1 : ℝ) * Sparse.eval nodeValue4156 x + ((1 : ℝ) * Sparse.eval nodeValue4161 x + ((1 : ℝ) * Sparse.eval nodeValue4178 x + ((2 : ℝ) * Sparse.eval nodeValue4528 x + ((2 : ℝ) * Sparse.eval nodeValue4531 x + ((2 : ℝ) * Sparse.eval nodeValue4535 x + ((2 : ℝ) * Sparse.eval nodeValue4546 x + ((2 : ℝ) * Sparse.eval nodeValue4547 x + ((1 : ℝ) * Sparse.eval nodeValue4555 x + ((1 : ℝ) * Sparse.eval nodeValue4558 x + ((2 : ℝ) * Sparse.eval nodeValue4591 x + ((1 : ℝ) * Sparse.eval nodeValue4594 x + ((2 : ℝ) * Sparse.eval nodeValue4602 x + ((1 : ℝ) * Sparse.eval nodeValue4609 x + ((1 : ℝ) * Sparse.eval nodeValue4612 x + ((1 : ℝ) * Sparse.eval nodeValue4619 x + ((2 : ℝ) * Sparse.eval nodeValue5075 x + ((1 : ℝ) * Sparse.eval nodeValue5107 x + ((1 : ℝ) * Sparse.eval nodeValue5261 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + 0))))))))))))))))))))

def numericRow1114 : Integer.Sparse Master := [(Sum.inr 1131, -2), (Sum.inr 1140, -1), (Sum.inr 1144, -1), (Sum.inr 1236, -2), (Sum.inr 1246, -1), (Sum.inr 1294, -1), (Sum.inr 2482, -2), (Sum.inr 2726, -1), (Sum.inr 3264, -2), (Sum.inr 3275, -1), (Sum.inr 3276, -1), (Sum.inr 3293, -2), (Sum.inr 3301, -1), (Sum.inr 3305, -1), (Sum.inr 3468, -2), (Sum.inr 3545, -1), (Sum.inr 4153, 8), (Sum.inr 4156, 4), (Sum.inr 4161, 4), (Sum.inr 4178, 4), (Sum.inr 4528, 8), (Sum.inr 4531, 8), (Sum.inr 4535, 8), (Sum.inr 4547, 8), (Sum.inr 4591, 8), (Sum.inr 4594, 4), (Sum.inr 4609, 4)]

theorem reindexCheck1114 : Integer.Sparse.reindex keyMap MixedData.row1114 = numericRow1114 := by decide +kernel

theorem numericCheck1114 (x : Master → ℝ) : Integer.Sparse.eval numericRow1114 x =
    (4 : ℝ) * reducedSource1114 x := by
  norm_num [numericRow1114, reducedSource1114, Integer.Sparse.eval, Sparse.eval, nodeValue4153, nodeValue4156, nodeValue4161, nodeValue4178, nodeValue4528, nodeValue4531, nodeValue4535, nodeValue4546, nodeValue4547, nodeValue4555, nodeValue4558, nodeValue4591, nodeValue4594, nodeValue4602, nodeValue4609, nodeValue4612, nodeValue4619, nodeValue5075, nodeValue5107, nodeValue5261, nodeValue5274]
  ring

noncomputable def reducedSource1115 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue581 x + ((1 : ℝ) * Sparse.eval nodeValue584 x + ((1 : ℝ) * Sparse.eval nodeValue589 x + ((1 : ℝ) * Sparse.eval nodeValue606 x + ((2 : ℝ) * Sparse.eval nodeValue1112 x + ((2 : ℝ) * Sparse.eval nodeValue1115 x + ((2 : ℝ) * Sparse.eval nodeValue1120 x + ((2 : ℝ) * Sparse.eval nodeValue1132 x + ((2 : ℝ) * Sparse.eval nodeValue1165 x + ((1 : ℝ) * Sparse.eval nodeValue1168 x + ((1 : ℝ) * Sparse.eval nodeValue1176 x + ((2 : ℝ) * Sparse.eval nodeValue1217 x + ((1 : ℝ) * Sparse.eval nodeValue1221 x + ((1 : ℝ) * Sparse.eval nodeValue1243 x + ((2 : ℝ) * Sparse.eval nodeValue1267 x + ((1 : ℝ) * Sparse.eval nodeValue1274 x + ((1 : ℝ) * Sparse.eval nodeValue1302 x + ((2 : ℝ) * Sparse.eval nodeValue2939 x + ((1 : ℝ) * Sparse.eval nodeValue3002 x + ((1 : ℝ) * Sparse.eval nodeValue3090 x + ((1 : ℝ) * Sparse.eval nodeValue3112 x + 0))))))))))))))))))))

def numericRow1115 : Integer.Sparse Master := [(Sum.inl 0, -13), (Sum.inl 5, 10), (Sum.inl 6, -5), (Sum.inl 2, -15), (Sum.inl 1, 5), (Sum.inr 581, 360), (Sum.inr 584, 180), (Sum.inr 589, 180), (Sum.inr 606, 180), (Sum.inr 1112, 360), (Sum.inr 1115, 360), (Sum.inr 1120, 360), (Sum.inr 1132, 360), (Sum.inr 1217, 360), (Sum.inr 1221, 180), (Sum.inr 1243, 180)]

theorem reindexCheck1115 : Integer.Sparse.reindex keyMap MixedData.row1115 = numericRow1115 := by decide +kernel

theorem numericCheck1115 (x : Master → ℝ) : Integer.Sparse.eval numericRow1115 x =
    (180 : ℝ) * reducedSource1115 x := by
  norm_num [numericRow1115, reducedSource1115, Integer.Sparse.eval, Sparse.eval, nodeValue581, nodeValue584, nodeValue589, nodeValue606, nodeValue1112, nodeValue1115, nodeValue1120, nodeValue1132, nodeValue1165, nodeValue1168, nodeValue1176, nodeValue1217, nodeValue1221, nodeValue1243, nodeValue1267, nodeValue1274, nodeValue1302, nodeValue2939, nodeValue3002, nodeValue3090, nodeValue3112]
  ring

noncomputable def reducedSource1116 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1514 x + ((1 : ℝ) * Sparse.eval nodeValue1516 x + ((1 : ℝ) * Sparse.eval nodeValue1520 x + ((1 : ℝ) * Sparse.eval nodeValue1533 x + ((2 : ℝ) * Sparse.eval nodeValue3260 x + ((2 : ℝ) * Sparse.eval nodeValue3262 x + ((2 : ℝ) * Sparse.eval nodeValue3264 x + ((2 : ℝ) * Sparse.eval nodeValue3266 x + ((2 : ℝ) * Sparse.eval nodeValue3272 x + ((1 : ℝ) * Sparse.eval nodeValue3275 x + ((1 : ℝ) * Sparse.eval nodeValue3276 x + ((2 : ℝ) * Sparse.eval nodeValue3291 x + ((2 : ℝ) * Sparse.eval nodeValue3293 x + ((1 : ℝ) * Sparse.eval nodeValue3298 x + ((1 : ℝ) * Sparse.eval nodeValue3301 x + ((1 : ℝ) * Sparse.eval nodeValue3302 x + ((1 : ℝ) * Sparse.eval nodeValue3305 x + ((2 : ℝ) * Sparse.eval nodeValue3468 x + ((1 : ℝ) * Sparse.eval nodeValue3484 x + ((1 : ℝ) * Sparse.eval nodeValue3545 x + ((1 : ℝ) * Sparse.eval nodeValue3547 x + 0))))))))))))))))))))

def numericRow1116 : Integer.Sparse Master := [(Sum.inr 1514, 2), (Sum.inr 1516, 1), (Sum.inr 1520, 1), (Sum.inr 1533, 1), (Sum.inr 3260, 2), (Sum.inr 3262, 2), (Sum.inr 3264, 2), (Sum.inr 3266, 2), (Sum.inr 3272, 2), (Sum.inr 3275, 1), (Sum.inr 3276, 1), (Sum.inr 3291, 2), (Sum.inr 3293, 2), (Sum.inr 3298, 1), (Sum.inr 3301, 1), (Sum.inr 3302, 1), (Sum.inr 3305, 1), (Sum.inr 3468, 2), (Sum.inr 3545, 1)]

theorem reindexCheck1116 : Integer.Sparse.reindex keyMap MixedData.row1116 = numericRow1116 := by decide +kernel

theorem numericCheck1116 (x : Master → ℝ) : Integer.Sparse.eval numericRow1116 x =
    (1 : ℝ) * reducedSource1116 x := by
  norm_num [numericRow1116, reducedSource1116, Integer.Sparse.eval, Sparse.eval, nodeValue1514, nodeValue1516, nodeValue1520, nodeValue1533, nodeValue3260, nodeValue3262, nodeValue3264, nodeValue3266, nodeValue3272, nodeValue3275, nodeValue3276, nodeValue3291, nodeValue3293, nodeValue3298, nodeValue3301, nodeValue3302, nodeValue3305, nodeValue3468, nodeValue3484, nodeValue3545, nodeValue3547]

noncomputable def reducedSource1117 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue626 x + ((1 : ℝ) * Sparse.eval nodeValue633 x + ((1 : ℝ) * Sparse.eval nodeValue635 x + ((1 : ℝ) * Sparse.eval nodeValue641 x + ((1 : ℝ) * Sparse.eval nodeValue1242 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow1117 : Integer.Sparse Master := [(Sum.inr 626, 2), (Sum.inr 633, 1), (Sum.inr 635, 1), (Sum.inr 641, 1), (Sum.inr 1242, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1117 : Integer.Sparse.reindex keyMap MixedData.row1117 = numericRow1117 := by decide +kernel

theorem numericCheck1117 (x : Master → ℝ) : Integer.Sparse.eval numericRow1117 x =
    (1 : ℝ) * reducedSource1117 x := by
  norm_num [numericRow1117, reducedSource1117, Integer.Sparse.eval, Sparse.eval, nodeValue626, nodeValue633, nodeValue635, nodeValue641, nodeValue1242, nodeValue4092]

noncomputable def reducedSource1118 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1115 x + ((1 : ℝ) * Sparse.eval nodeValue1148 x + ((1 : ℝ) * Sparse.eval nodeValue1154 x + ((1 : ℝ) * Sparse.eval nodeValue1159 x + ((1 : ℝ) * Sparse.eval nodeValue1242 x + ((1 : ℝ) * Sparse.eval nodeValue2482 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1118 : Integer.Sparse Master := [(Sum.inr 1115, 1), (Sum.inr 1148, 1), (Sum.inr 1154, 1), (Sum.inr 1159, 1), (Sum.inr 1242, 1), (Sum.inr 2482, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1118 : Integer.Sparse.reindex keyMap MixedData.row1118 = numericRow1118 := by decide +kernel

theorem numericCheck1118 (x : Master → ℝ) : Integer.Sparse.eval numericRow1118 x =
    (1 : ℝ) * reducedSource1118 x := by
  norm_num [numericRow1118, reducedSource1118, Integer.Sparse.eval, Sparse.eval, nodeValue1115, nodeValue1148, nodeValue1154, nodeValue1159, nodeValue1242, nodeValue2482, nodeValue4092]

noncomputable def reducedSource1119 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1131 x + ((1 : ℝ) * Sparse.eval nodeValue1140 x + ((1 : ℝ) * Sparse.eval nodeValue1144 x + ((1 : ℝ) * Sparse.eval nodeValue1242 x + ((1 : ℝ) * Sparse.eval nodeValue2517 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow1119 : Integer.Sparse Master := [(Sum.inr 1131, 2), (Sum.inr 1140, 1), (Sum.inr 1144, 1), (Sum.inr 1242, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1119 : Integer.Sparse.reindex keyMap MixedData.row1119 = numericRow1119 := by decide +kernel

theorem numericCheck1119 (x : Master → ℝ) : Integer.Sparse.eval numericRow1119 x =
    (1 : ℝ) * reducedSource1119 x := by
  norm_num [numericRow1119, reducedSource1119, Integer.Sparse.eval, Sparse.eval, nodeValue1131, nodeValue1140, nodeValue1144, nodeValue1242, nodeValue2517, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
