import OAI.Analysis.MutuallyUnbiased.MixedData.Source8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values9
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1072 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1619 x + ((1 : ℝ) * Sparse.eval nodeValue1628 x + ((1 : ℝ) * Sparse.eval nodeValue1630 x + ((1 : ℝ) * Sparse.eval nodeValue1756 x + ((1 : ℝ) * Sparse.eval nodeValue3302 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

def numericRow1072 : Integer.Sparse Master := [(Sum.inr 1619, 2), (Sum.inr 1628, 1), (Sum.inr 1630, 1), (Sum.inr 1756, 1), (Sum.inr 3302, 1), (Sum.inr 4070, -1)]

theorem reindexCheck1072 : Integer.Sparse.reindex keyMap MixedData.row1072 = numericRow1072 := by decide +kernel

theorem numericCheck1072 (x : Master → ℝ) : Integer.Sparse.eval numericRow1072 x =
    (1 : ℝ) * reducedSource1072 x := by
  norm_num [numericRow1072, reducedSource1072, Integer.Sparse.eval, Sparse.eval, nodeValue1619, nodeValue1628, nodeValue1630, nodeValue1756, nodeValue3302, nodeValue4070]

noncomputable def reducedSource1073 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1756 x + ((1 : ℝ) * Sparse.eval nodeValue2289 x + ((3 : ℝ) * Sparse.eval nodeValue3302 x + ((1 : ℝ) * Sparse.eval nodeValue3310 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0))))

def numericRow1073 : Integer.Sparse Master := [(Sum.inr 1756, 1), (Sum.inr 2289, 1), (Sum.inr 3302, 3), (Sum.inr 3310, 1), (Sum.inr 4070, -1)]

theorem reindexCheck1073 : Integer.Sparse.reindex keyMap MixedData.row1073 = numericRow1073 := by decide +kernel

theorem numericCheck1073 (x : Master → ℝ) : Integer.Sparse.eval numericRow1073 x =
    (1 : ℝ) * reducedSource1073 x := by
  norm_num [numericRow1073, reducedSource1073, Integer.Sparse.eval, Sparse.eval, nodeValue1756, nodeValue2289, nodeValue3302, nodeValue3310, nodeValue4070]

noncomputable def reducedSource1074 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1725 x + ((2 : ℝ) * Sparse.eval nodeValue3291 x + ((1 : ℝ) * Sparse.eval nodeValue3300 x + ((1 : ℝ) * Sparse.eval nodeValue3302 x + ((1 : ℝ) * Sparse.eval nodeValue3310 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

def numericRow1074 : Integer.Sparse Master := [(Sum.inr 1725, 1), (Sum.inr 3291, 2), (Sum.inr 3300, 1), (Sum.inr 3302, 1), (Sum.inr 3310, 1), (Sum.inr 4070, -1)]

theorem reindexCheck1074 : Integer.Sparse.reindex keyMap MixedData.row1074 = numericRow1074 := by decide +kernel

theorem numericCheck1074 (x : Master → ℝ) : Integer.Sparse.eval numericRow1074 x =
    (1 : ℝ) * reducedSource1074 x := by
  norm_num [numericRow1074, reducedSource1074, Integer.Sparse.eval, Sparse.eval, nodeValue1725, nodeValue3291, nodeValue3300, nodeValue3302, nodeValue3310, nodeValue4070]

noncomputable def reducedSource1075 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1630 x + ((1 : ℝ) * Sparse.eval nodeValue3247 x + ((2 : ℝ) * Sparse.eval nodeValue3283 x + ((1 : ℝ) * Sparse.eval nodeValue3300 x + ((1 : ℝ) * Sparse.eval nodeValue3302 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

def numericRow1075 : Integer.Sparse Master := [(Sum.inr 1630, 1), (Sum.inr 3247, 1), (Sum.inr 3283, 2), (Sum.inr 3300, 1), (Sum.inr 3302, 1), (Sum.inr 4070, -1)]

theorem reindexCheck1075 : Integer.Sparse.reindex keyMap MixedData.row1075 = numericRow1075 := by decide +kernel

theorem numericCheck1075 (x : Master → ℝ) : Integer.Sparse.eval numericRow1075 x =
    (1 : ℝ) * reducedSource1075 x := by
  norm_num [numericRow1075, reducedSource1075, Integer.Sparse.eval, Sparse.eval, nodeValue1630, nodeValue3247, nodeValue3283, nodeValue3300, nodeValue3302, nodeValue4070]

noncomputable def reducedSource1076 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1258 x + ((2 : ℝ) * Sparse.eval nodeValue2119 x + ((1 : ℝ) * Sparse.eval nodeValue2130 x + ((1 : ℝ) * Sparse.eval nodeValue2218 x + ((1 : ℝ) * Sparse.eval nodeValue2761 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

def numericRow1076 : Integer.Sparse Master := [(Sum.inr 1258, 1), (Sum.inr 2119, 2), (Sum.inr 2130, 1), (Sum.inr 2218, 1), (Sum.inr 2761, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1076 : Integer.Sparse.reindex keyMap MixedData.row1076 = numericRow1076 := by decide +kernel

theorem numericCheck1076 (x : Master → ℝ) : Integer.Sparse.eval numericRow1076 x =
    (1 : ℝ) * reducedSource1076 x := by
  norm_num [numericRow1076, reducedSource1076, Integer.Sparse.eval, Sparse.eval, nodeValue1258, nodeValue2119, nodeValue2130, nodeValue2218, nodeValue2761, nodeValue4082]

noncomputable def reducedSource1077 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1111 x + ((1 : ℝ) * Sparse.eval nodeValue1115 x + ((1 : ℝ) * Sparse.eval nodeValue1119 x + ((1 : ℝ) * Sparse.eval nodeValue1131 x + ((1 : ℝ) * Sparse.eval nodeValue1215 x + ((1 : ℝ) * Sparse.eval nodeValue2482 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1077 : Integer.Sparse Master := [(Sum.inr 1111, 1), (Sum.inr 1115, 1), (Sum.inr 1119, 1), (Sum.inr 1131, 1), (Sum.inr 1215, 1), (Sum.inr 2482, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1077 : Integer.Sparse.reindex keyMap MixedData.row1077 = numericRow1077 := by decide +kernel

theorem numericCheck1077 (x : Master → ℝ) : Integer.Sparse.eval numericRow1077 x =
    (1 : ℝ) * reducedSource1077 x := by
  norm_num [numericRow1077, reducedSource1077, Integer.Sparse.eval, Sparse.eval, nodeValue1111, nodeValue1115, nodeValue1119, nodeValue1131, nodeValue1215, nodeValue2482, nodeValue4092]

noncomputable def reducedSource1078 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue626 x + ((1 : ℝ) * Sparse.eval nodeValue1131 x + ((1 : ℝ) * Sparse.eval nodeValue1148 x + ((1 : ℝ) * Sparse.eval nodeValue1215 x + ((1 : ℝ) * Sparse.eval nodeValue1236 x + ((1 : ℝ) * Sparse.eval nodeValue1242 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1078 : Integer.Sparse Master := [(Sum.inr 626, 1), (Sum.inr 1131, 1), (Sum.inr 1148, 1), (Sum.inr 1215, 1), (Sum.inr 1236, 1), (Sum.inr 1242, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1078 : Integer.Sparse.reindex keyMap MixedData.row1078 = numericRow1078 := by decide +kernel

theorem numericCheck1078 (x : Master → ℝ) : Integer.Sparse.eval numericRow1078 x =
    (1 : ℝ) * reducedSource1078 x := by
  norm_num [numericRow1078, reducedSource1078, Integer.Sparse.eval, Sparse.eval, nodeValue626, nodeValue1131, nodeValue1148, nodeValue1215, nodeValue1236, nodeValue1242, nodeValue4092]

noncomputable def reducedSource1079 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue630 x + ((1 : ℝ) * Sparse.eval nodeValue1136 x + ((1 : ℝ) * Sparse.eval nodeValue1150 x + ((2 : ℝ) * Sparse.eval nodeValue1217 x + ((1 : ℝ) * Sparse.eval nodeValue1240 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow1079 : Integer.Sparse Master := [(Sum.inr 630, 1), (Sum.inr 1136, 1), (Sum.inr 1150, 1), (Sum.inr 1217, 2), (Sum.inr 1240, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1079 : Integer.Sparse.reindex keyMap MixedData.row1079 = numericRow1079 := by decide +kernel

theorem numericCheck1079 (x : Master → ℝ) : Integer.Sparse.eval numericRow1079 x =
    (1 : ℝ) * reducedSource1079 x := by
  norm_num [numericRow1079, reducedSource1079, Integer.Sparse.eval, Sparse.eval, nodeValue630, nodeValue1136, nodeValue1150, nodeValue1217, nodeValue1240, nodeValue4091]

noncomputable def reducedSource1080 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1112 x + ((1 : ℝ) * Sparse.eval nodeValue1118 x + ((1 : ℝ) * Sparse.eval nodeValue1120 x + ((1 : ℝ) * Sparse.eval nodeValue1136 x + ((1 : ℝ) * Sparse.eval nodeValue1217 x + ((1 : ℝ) * Sparse.eval nodeValue2485 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow1080 : Integer.Sparse Master := [(Sum.inr 1112, 1), (Sum.inr 1118, 1), (Sum.inr 1120, 1), (Sum.inr 1136, 1), (Sum.inr 1217, 1), (Sum.inr 2485, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1080 : Integer.Sparse.reindex keyMap MixedData.row1080 = numericRow1080 := by decide +kernel

theorem numericCheck1080 (x : Master → ℝ) : Integer.Sparse.eval numericRow1080 x =
    (1 : ℝ) * reducedSource1080 x := by
  norm_num [numericRow1080, reducedSource1080, Integer.Sparse.eval, Sparse.eval, nodeValue1112, nodeValue1118, nodeValue1120, nodeValue1136, nodeValue1217, nodeValue2485, nodeValue4091]

noncomputable def reducedSource1081 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1613 x + ((1 : ℝ) * Sparse.eval nodeValue1617 x + ((1 : ℝ) * Sparse.eval nodeValue1619 x + ((1 : ℝ) * Sparse.eval nodeValue1624 x + ((1 : ℝ) * Sparse.eval nodeValue1750 x + ((1 : ℝ) * Sparse.eval nodeValue3291 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0))))))

def numericRow1081 : Integer.Sparse Master := [(Sum.inr 1613, 1), (Sum.inr 1617, 1), (Sum.inr 1619, 1), (Sum.inr 1624, 1), (Sum.inr 1750, 1), (Sum.inr 3291, 1), (Sum.inr 4070, -1)]

theorem reindexCheck1081 : Integer.Sparse.reindex keyMap MixedData.row1081 = numericRow1081 := by decide +kernel

theorem numericCheck1081 (x : Master → ℝ) : Integer.Sparse.eval numericRow1081 x =
    (1 : ℝ) * reducedSource1081 x := by
  norm_num [numericRow1081, reducedSource1081, Integer.Sparse.eval, Sparse.eval, nodeValue1613, nodeValue1617, nodeValue1619, nodeValue1624, nodeValue1750, nodeValue3291, nodeValue4070]

noncomputable def reducedSource1082 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1596 x + ((1 : ℝ) * Sparse.eval nodeValue1599 x + ((1 : ℝ) * Sparse.eval nodeValue1604 x + ((1 : ℝ) * Sparse.eval nodeValue1617 x + ((1 : ℝ) * Sparse.eval nodeValue1725 x + ((1 : ℝ) * Sparse.eval nodeValue3291 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0))))))

def numericRow1082 : Integer.Sparse Master := [(Sum.inr 1599, 1), (Sum.inr 1604, 1), (Sum.inr 1617, 1), (Sum.inr 1725, 1), (Sum.inr 3291, 1), (Sum.inr 4070, -1)]

theorem reindexCheck1082 : Integer.Sparse.reindex keyMap MixedData.row1082 = numericRow1082 := by decide +kernel

theorem numericCheck1082 (x : Master → ℝ) : Integer.Sparse.eval numericRow1082 x =
    (1 : ℝ) * reducedSource1082 x := by
  norm_num [numericRow1082, reducedSource1082, Integer.Sparse.eval, Sparse.eval, nodeValue1596, nodeValue1599, nodeValue1604, nodeValue1617, nodeValue1725, nodeValue3291, nodeValue4070]

noncomputable def reducedSource1083 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1750 x + ((1 : ℝ) * Sparse.eval nodeValue2226 x + ((2 : ℝ) * Sparse.eval nodeValue3291 x + ((1 : ℝ) * Sparse.eval nodeValue3300 x + ((1 : ℝ) * Sparse.eval nodeValue3310 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

def numericRow1083 : Integer.Sparse Master := [(Sum.inr 1750, 1), (Sum.inr 2226, 1), (Sum.inr 3291, 2), (Sum.inr 3300, 1), (Sum.inr 3310, 1), (Sum.inr 4070, -1)]

theorem reindexCheck1083 : Integer.Sparse.reindex keyMap MixedData.row1083 = numericRow1083 := by decide +kernel

theorem numericCheck1083 (x : Master → ℝ) : Integer.Sparse.eval numericRow1083 x =
    (1 : ℝ) * reducedSource1083 x := by
  norm_num [numericRow1083, reducedSource1083, Integer.Sparse.eval, Sparse.eval, nodeValue1750, nodeValue2226, nodeValue3291, nodeValue3300, nodeValue3310, nodeValue4070]

noncomputable def reducedSource1084 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1617 x + ((1 : ℝ) * Sparse.eval nodeValue3242 x + ((1 : ℝ) * Sparse.eval nodeValue3279 x + ((2 : ℝ) * Sparse.eval nodeValue3291 x + ((1 : ℝ) * Sparse.eval nodeValue3300 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

def numericRow1084 : Integer.Sparse Master := [(Sum.inr 1617, 1), (Sum.inr 3242, 1), (Sum.inr 3279, 1), (Sum.inr 3291, 2), (Sum.inr 3300, 1), (Sum.inr 4070, -1)]

theorem reindexCheck1084 : Integer.Sparse.reindex keyMap MixedData.row1084 = numericRow1084 := by decide +kernel

theorem numericCheck1084 (x : Master → ℝ) : Integer.Sparse.eval numericRow1084 x =
    (1 : ℝ) * reducedSource1084 x := by
  norm_num [numericRow1084, reducedSource1084, Integer.Sparse.eval, Sparse.eval, nodeValue1617, nodeValue3242, nodeValue3279, nodeValue3291, nodeValue3300, nodeValue4070]

noncomputable def reducedSource1085 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1599 x + ((1 : ℝ) * Sparse.eval nodeValue1995 x + ((1 : ℝ) * Sparse.eval nodeValue2005 x + ((1 : ℝ) * Sparse.eval nodeValue2045 x + ((1 : ℝ) * Sparse.eval nodeValue2226 x + ((1 : ℝ) * Sparse.eval nodeValue3291 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0))))))

def numericRow1085 : Integer.Sparse Master := [(Sum.inr 1599, 1), (Sum.inr 1995, 1), (Sum.inr 2005, 1), (Sum.inr 2045, 1), (Sum.inr 2226, 1), (Sum.inr 3291, 1), (Sum.inr 4070, -1)]

theorem reindexCheck1085 : Integer.Sparse.reindex keyMap MixedData.row1085 = numericRow1085 := by decide +kernel

theorem numericCheck1085 (x : Master → ℝ) : Integer.Sparse.eval numericRow1085 x =
    (1 : ℝ) * reducedSource1085 x := by
  norm_num [numericRow1085, reducedSource1085, Integer.Sparse.eval, Sparse.eval, nodeValue1599, nodeValue1995, nodeValue2005, nodeValue2045, nodeValue2226, nodeValue3291, nodeValue4070]

noncomputable def reducedSource1086 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1211 x + ((1 : ℝ) * Sparse.eval nodeValue2070 x + ((1 : ℝ) * Sparse.eval nodeValue2079 x + ((1 : ℝ) * Sparse.eval nodeValue2087 x + ((1 : ℝ) * Sparse.eval nodeValue2193 x + ((1 : ℝ) * Sparse.eval nodeValue2719 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

def numericRow1086 : Integer.Sparse Master := [(Sum.inr 1211, 1), (Sum.inr 2070, 1), (Sum.inr 2079, 1), (Sum.inr 2087, 1), (Sum.inr 2193, 1), (Sum.inr 2719, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1086 : Integer.Sparse.reindex keyMap MixedData.row1086 = numericRow1086 := by decide +kernel

theorem numericCheck1086 (x : Master → ℝ) : Integer.Sparse.eval numericRow1086 x =
    (1 : ℝ) * reducedSource1086 x := by
  norm_num [numericRow1086, reducedSource1086, Integer.Sparse.eval, Sparse.eval, nodeValue1211, nodeValue2070, nodeValue2079, nodeValue2087, nodeValue2193, nodeValue2719, nodeValue4080]

noncomputable def reducedSource1087 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1181 x + ((1 : ℝ) * Sparse.eval nodeValue2385 x + ((1 : ℝ) * Sparse.eval nodeValue2453 x + ((1 : ℝ) * Sparse.eval nodeValue2492 x + ((1 : ℝ) * Sparse.eval nodeValue2664 x + ((1 : ℝ) * Sparse.eval nodeValue2672 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0))))))

def numericRow1087 : Integer.Sparse Master := [(Sum.inr 1181, 1), (Sum.inr 2385, 1), (Sum.inr 2453, 1), (Sum.inr 2492, 1), (Sum.inr 2664, 1), (Sum.inr 2672, 1), (Sum.inr 4088, -1)]

theorem reindexCheck1087 : Integer.Sparse.reindex keyMap MixedData.row1087 = numericRow1087 := by decide +kernel

theorem numericCheck1087 (x : Master → ℝ) : Integer.Sparse.eval numericRow1087 x =
    (1 : ℝ) * reducedSource1087 x := by
  norm_num [numericRow1087, reducedSource1087, Integer.Sparse.eval, Sparse.eval, nodeValue1181, nodeValue2385, nodeValue2453, nodeValue2492, nodeValue2664, nodeValue2672, nodeValue4088]

end MUB6.Certificate.MixedSourceBridge

end OAI
