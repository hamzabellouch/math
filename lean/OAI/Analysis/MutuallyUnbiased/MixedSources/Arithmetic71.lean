import OAI.Analysis.MutuallyUnbiased.MixedData.Source8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1136 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1190 x + ((2 : ℝ) * Sparse.eval nodeValue1924 x + ((1 : ℝ) * Sparse.eval nodeValue1950 x + ((1 : ℝ) * Sparse.eval nodeValue2218 x + ((1 : ℝ) * Sparse.eval nodeValue2685 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

def numericRow1136 : Integer.Sparse Master := [(Sum.inr 1190, 1), (Sum.inr 1924, 2), (Sum.inr 2218, 1), (Sum.inr 2685, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1136 : Integer.Sparse.reindex keyMap MixedData.row1136 = numericRow1136 := by decide +kernel

theorem numericCheck1136 (x : Master → ℝ) : Integer.Sparse.eval numericRow1136 x =
    (1 : ℝ) * reducedSource1136 x := by
  norm_num [numericRow1136, reducedSource1136, Integer.Sparse.eval, Sparse.eval, nodeValue1190, nodeValue1924, nodeValue1950, nodeValue2218, nodeValue2685, nodeValue4082]

noncomputable def reducedSource1137 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue893 x + ((2 : ℝ) * Sparse.eval nodeValue1098 x + ((1 : ℝ) * Sparse.eval nodeValue1103 x + ((1 : ℝ) * Sparse.eval nodeValue1190 x + ((1 : ℝ) * Sparse.eval nodeValue1950 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

def numericRow1137 : Integer.Sparse Master := [(Sum.inr 893, 1), (Sum.inr 1098, 2), (Sum.inr 1103, 1), (Sum.inr 1190, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1137 : Integer.Sparse.reindex keyMap MixedData.row1137 = numericRow1137 := by decide +kernel

theorem numericCheck1137 (x : Master → ℝ) : Integer.Sparse.eval numericRow1137 x =
    (1 : ℝ) * reducedSource1137 x := by
  norm_num [numericRow1137, reducedSource1137, Integer.Sparse.eval, Sparse.eval, nodeValue893, nodeValue1098, nodeValue1103, nodeValue1190, nodeValue1950, nodeValue4082]

noncomputable def reducedSource1138 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1184 x + ((1 : ℝ) * Sparse.eval nodeValue1190 x + ((1 : ℝ) * Sparse.eval nodeValue1192 x + ((1 : ℝ) * Sparse.eval nodeValue1287 x + ((1 : ℝ) * Sparse.eval nodeValue2685 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

def numericRow1138 : Integer.Sparse Master := [(Sum.inr 1184, 2), (Sum.inr 1190, 1), (Sum.inr 1192, 1), (Sum.inr 1287, 1), (Sum.inr 2685, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1138 : Integer.Sparse.reindex keyMap MixedData.row1138 = numericRow1138 := by decide +kernel

theorem numericCheck1138 (x : Master → ℝ) : Integer.Sparse.eval numericRow1138 x =
    (1 : ℝ) * reducedSource1138 x := by
  norm_num [numericRow1138, reducedSource1138, Integer.Sparse.eval, Sparse.eval, nodeValue1184, nodeValue1190, nodeValue1192, nodeValue1287, nodeValue2685, nodeValue4082]

noncomputable def reducedSource1139 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1186 x + ((2 : ℝ) * Sparse.eval nodeValue1608 x + ((1 : ℝ) * Sparse.eval nodeValue1627 x + ((1 : ℝ) * Sparse.eval nodeValue1741 x + ((1 : ℝ) * Sparse.eval nodeValue2683 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0)))))

def numericRow1139 : Integer.Sparse Master := [(Sum.inr 1186, 1), (Sum.inr 1608, 2), (Sum.inr 1627, 1), (Sum.inr 1741, 1), (Sum.inr 2683, 1), (Sum.inr 4071, -1)]

theorem reindexCheck1139 : Integer.Sparse.reindex keyMap MixedData.row1139 = numericRow1139 := by decide +kernel

theorem numericCheck1139 (x : Master → ℝ) : Integer.Sparse.eval numericRow1139 x =
    (1 : ℝ) * reducedSource1139 x := by
  norm_num [numericRow1139, reducedSource1139, Integer.Sparse.eval, Sparse.eval, nodeValue1186, nodeValue1608, nodeValue1627, nodeValue1741, nodeValue2683, nodeValue4071]

noncomputable def reducedSource1140 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1203 x + ((1 : ℝ) * Sparse.eval nodeValue2377 x + ((2 : ℝ) * Sparse.eval nodeValue2385 x + ((1 : ℝ) * Sparse.eval nodeValue2664 x + ((1 : ℝ) * Sparse.eval nodeValue2705 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0)))))

def numericRow1140 : Integer.Sparse Master := [(Sum.inr 1203, 1), (Sum.inr 2385, 2), (Sum.inr 2664, 1), (Sum.inr 2705, 1), (Sum.inr 4088, -1)]

theorem reindexCheck1140 : Integer.Sparse.reindex keyMap MixedData.row1140 = numericRow1140 := by decide +kernel

theorem numericCheck1140 (x : Master → ℝ) : Integer.Sparse.eval numericRow1140 x =
    (1 : ℝ) * reducedSource1140 x := by
  norm_num [numericRow1140, reducedSource1140, Integer.Sparse.eval, Sparse.eval, nodeValue1203, nodeValue2377, nodeValue2385, nodeValue2664, nodeValue2705, nodeValue4088]

noncomputable def reducedSource1141 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1198 x + ((1 : ℝ) * Sparse.eval nodeValue1203 x + ((1 : ℝ) * Sparse.eval nodeValue1205 x + ((2 : ℝ) * Sparse.eval nodeValue1230 x + ((1 : ℝ) * Sparse.eval nodeValue2705 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0)))))

def numericRow1141 : Integer.Sparse Master := [(Sum.inr 1198, 1), (Sum.inr 1203, 1), (Sum.inr 1205, 1), (Sum.inr 1230, 2), (Sum.inr 2705, 1), (Sum.inr 4088, -1)]

theorem reindexCheck1141 : Integer.Sparse.reindex keyMap MixedData.row1141 = numericRow1141 := by decide +kernel

theorem numericCheck1141 (x : Master → ℝ) : Integer.Sparse.eval numericRow1141 x =
    (1 : ℝ) * reducedSource1141 x := by
  norm_num [numericRow1141, reducedSource1141, Integer.Sparse.eval, Sparse.eval, nodeValue1198, nodeValue1203, nodeValue1205, nodeValue1230, nodeValue2705, nodeValue4088]

noncomputable def reducedSource1142 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1202 x + ((1 : ℝ) * Sparse.eval nodeValue1897 x + ((2 : ℝ) * Sparse.eval nodeValue1914 x + ((1 : ℝ) * Sparse.eval nodeValue2193 x + ((1 : ℝ) * Sparse.eval nodeValue2704 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

def numericRow1142 : Integer.Sparse Master := [(Sum.inr 1202, 1), (Sum.inr 1897, 1), (Sum.inr 2193, 1), (Sum.inr 2704, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1142 : Integer.Sparse.reindex keyMap MixedData.row1142 = numericRow1142 := by decide +kernel

theorem numericCheck1142 (x : Master → ℝ) : Integer.Sparse.eval numericRow1142 x =
    (1 : ℝ) * reducedSource1142 x := by
  norm_num [numericRow1142, reducedSource1142, Integer.Sparse.eval, Sparse.eval, nodeValue1202, nodeValue1897, nodeValue1914, nodeValue2193, nodeValue2704, nodeValue4080]

noncomputable def reducedSource1143 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue871 x + ((1 : ℝ) * Sparse.eval nodeValue1105 x + ((1 : ℝ) * Sparse.eval nodeValue1109 x + ((1 : ℝ) * Sparse.eval nodeValue1123 x + ((1 : ℝ) * Sparse.eval nodeValue1202 x + ((1 : ℝ) * Sparse.eval nodeValue1914 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

def numericRow1143 : Integer.Sparse Master := [(Sum.inr 871, 1), (Sum.inr 1105, 1), (Sum.inr 1109, 1), (Sum.inr 1123, 1), (Sum.inr 1202, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1143 : Integer.Sparse.reindex keyMap MixedData.row1143 = numericRow1143 := by decide +kernel

theorem numericCheck1143 (x : Master → ℝ) : Integer.Sparse.eval numericRow1143 x =
    (1 : ℝ) * reducedSource1143 x := by
  norm_num [numericRow1143, reducedSource1143, Integer.Sparse.eval, Sparse.eval, nodeValue871, nodeValue1105, nodeValue1109, nodeValue1123, nodeValue1202, nodeValue1914, nodeValue4080]

noncomputable def reducedSource1144 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1197 x + ((1 : ℝ) * Sparse.eval nodeValue1202 x + ((1 : ℝ) * Sparse.eval nodeValue1204 x + ((2 : ℝ) * Sparse.eval nodeValue1229 x + ((1 : ℝ) * Sparse.eval nodeValue2704 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

def numericRow1144 : Integer.Sparse Master := [(Sum.inr 1197, 1), (Sum.inr 1202, 1), (Sum.inr 1204, 1), (Sum.inr 1229, 2), (Sum.inr 2704, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1144 : Integer.Sparse.reindex keyMap MixedData.row1144 = numericRow1144 := by decide +kernel

theorem numericCheck1144 (x : Master → ℝ) : Integer.Sparse.eval numericRow1144 x =
    (1 : ℝ) * reducedSource1144 x := by
  norm_num [numericRow1144, reducedSource1144, Integer.Sparse.eval, Sparse.eval, nodeValue1197, nodeValue1202, nodeValue1204, nodeValue1229, nodeValue2704, nodeValue4080]

noncomputable def reducedSource1145 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1199 x + ((1 : ℝ) * Sparse.eval nodeValue1592 x + ((2 : ℝ) * Sparse.eval nodeValue1602 x + ((1 : ℝ) * Sparse.eval nodeValue1710 x + ((1 : ℝ) * Sparse.eval nodeValue2702 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

def numericRow1145 : Integer.Sparse Master := [(Sum.inr 1199, 1), (Sum.inr 1602, 2), (Sum.inr 1710, 1), (Sum.inr 2702, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1145 : Integer.Sparse.reindex keyMap MixedData.row1145 = numericRow1145 := by decide +kernel

theorem numericCheck1145 (x : Master → ℝ) : Integer.Sparse.eval numericRow1145 x =
    (1 : ℝ) * reducedSource1145 x := by
  norm_num [numericRow1145, reducedSource1145, Integer.Sparse.eval, Sparse.eval, nodeValue1199, nodeValue1592, nodeValue1602, nodeValue1710, nodeValue2702, nodeValue4069]

noncomputable def reducedSource1146 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1055 x + ((2 : ℝ) * Sparse.eval nodeValue2032 x + ((1 : ℝ) * Sparse.eval nodeValue2130 x + ((1 : ℝ) * Sparse.eval nodeValue2218 x + ((1 : ℝ) * Sparse.eval nodeValue2276 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

def numericRow1146 : Integer.Sparse Master := [(Sum.inr 1055, 1), (Sum.inr 2032, 2), (Sum.inr 2130, 1), (Sum.inr 2218, 1), (Sum.inr 2276, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1146 : Integer.Sparse.reindex keyMap MixedData.row1146 = numericRow1146 := by decide +kernel

theorem numericCheck1146 (x : Master → ℝ) : Integer.Sparse.eval numericRow1146 x =
    (1 : ℝ) * reducedSource1146 x := by
  norm_num [numericRow1146, reducedSource1146, Integer.Sparse.eval, Sparse.eval, nodeValue1055, nodeValue2032, nodeValue2130, nodeValue2218, nodeValue2276, nodeValue4082]

noncomputable def reducedSource1147 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1053 x + ((1 : ℝ) * Sparse.eval nodeValue1055 x + ((1 : ℝ) * Sparse.eval nodeValue1062 x + ((1 : ℝ) * Sparse.eval nodeValue1075 x + ((1 : ℝ) * Sparse.eval nodeValue2276 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

def numericRow1147 : Integer.Sparse Master := [(Sum.inr 1053, 2), (Sum.inr 1055, 1), (Sum.inr 1062, 1), (Sum.inr 1075, 1), (Sum.inr 2276, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1147 : Integer.Sparse.reindex keyMap MixedData.row1147 = numericRow1147 := by decide +kernel

theorem numericCheck1147 (x : Master → ℝ) : Integer.Sparse.eval numericRow1147 x =
    (1 : ℝ) * reducedSource1147 x := by
  norm_num [numericRow1147, reducedSource1147, Integer.Sparse.eval, Sparse.eval, nodeValue1053, nodeValue1055, nodeValue1062, nodeValue1075, nodeValue2276, nodeValue4082]

noncomputable def reducedSource1148 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue991 x + ((1 : ℝ) * Sparse.eval nodeValue1926 x + ((1 : ℝ) * Sparse.eval nodeValue1992 x + ((1 : ℝ) * Sparse.eval nodeValue2121 x + ((1 : ℝ) * Sparse.eval nodeValue2197 x + ((1 : ℝ) * Sparse.eval nodeValue2216 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

def numericRow1148 : Integer.Sparse Master := [(Sum.inr 991, 1), (Sum.inr 1926, 1), (Sum.inr 1992, 1), (Sum.inr 2121, 1), (Sum.inr 2197, 1), (Sum.inr 2216, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1148 : Integer.Sparse.reindex keyMap MixedData.row1148 = numericRow1148 := by decide +kernel

theorem numericCheck1148 (x : Master → ℝ) : Integer.Sparse.eval numericRow1148 x =
    (1 : ℝ) * reducedSource1148 x := by
  norm_num [numericRow1148, reducedSource1148, Integer.Sparse.eval, Sparse.eval, nodeValue991, nodeValue1926, nodeValue1992, nodeValue2121, nodeValue2197, nodeValue2216, nodeValue4080]

noncomputable def reducedSource1149 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue988 x + ((1 : ℝ) * Sparse.eval nodeValue991 x + ((1 : ℝ) * Sparse.eval nodeValue993 x + ((1 : ℝ) * Sparse.eval nodeValue1005 x + ((1 : ℝ) * Sparse.eval nodeValue1054 x + ((1 : ℝ) * Sparse.eval nodeValue2216 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

def numericRow1149 : Integer.Sparse Master := [(Sum.inr 988, 1), (Sum.inr 991, 1), (Sum.inr 993, 1), (Sum.inr 1005, 1), (Sum.inr 1054, 1), (Sum.inr 2216, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1149 : Integer.Sparse.reindex keyMap MixedData.row1149 = numericRow1149 := by decide +kernel

theorem numericCheck1149 (x : Master → ℝ) : Integer.Sparse.eval numericRow1149 x =
    (1 : ℝ) * reducedSource1149 x := by
  norm_num [numericRow1149, reducedSource1149, Integer.Sparse.eval, Sparse.eval, nodeValue988, nodeValue991, nodeValue993, nodeValue1005, nodeValue1054, nodeValue2216, nodeValue4080]

noncomputable def reducedSource1150 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue989 x + ((1 : ℝ) * Sparse.eval nodeValue1924 x + ((1 : ℝ) * Sparse.eval nodeValue1991 x + ((1 : ℝ) * Sparse.eval nodeValue2119 x + ((1 : ℝ) * Sparse.eval nodeValue2215 x + ((1 : ℝ) * Sparse.eval nodeValue2218 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

def numericRow1150 : Integer.Sparse Master := [(Sum.inr 989, 1), (Sum.inr 1924, 1), (Sum.inr 1991, 1), (Sum.inr 2119, 1), (Sum.inr 2215, 1), (Sum.inr 2218, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1150 : Integer.Sparse.reindex keyMap MixedData.row1150 = numericRow1150 := by decide +kernel

theorem numericCheck1150 (x : Master → ℝ) : Integer.Sparse.eval numericRow1150 x =
    (1 : ℝ) * reducedSource1150 x := by
  norm_num [numericRow1150, reducedSource1150, Integer.Sparse.eval, Sparse.eval, nodeValue989, nodeValue1924, nodeValue1991, nodeValue2119, nodeValue2215, nodeValue2218, nodeValue4082]

noncomputable def reducedSource1151 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue987 x + ((1 : ℝ) * Sparse.eval nodeValue989 x + ((1 : ℝ) * Sparse.eval nodeValue992 x + ((1 : ℝ) * Sparse.eval nodeValue1000 x + ((1 : ℝ) * Sparse.eval nodeValue1053 x + ((1 : ℝ) * Sparse.eval nodeValue2215 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

def numericRow1151 : Integer.Sparse Master := [(Sum.inr 987, 1), (Sum.inr 989, 1), (Sum.inr 992, 1), (Sum.inr 1000, 1), (Sum.inr 1053, 1), (Sum.inr 2215, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1151 : Integer.Sparse.reindex keyMap MixedData.row1151 = numericRow1151 := by decide +kernel

theorem numericCheck1151 (x : Master → ℝ) : Integer.Sparse.eval numericRow1151 x =
    (1 : ℝ) * reducedSource1151 x := by
  norm_num [numericRow1151, reducedSource1151, Integer.Sparse.eval, Sparse.eval, nodeValue987, nodeValue989, nodeValue992, nodeValue1000, nodeValue1053, nodeValue2215, nodeValue4082]

end MUB6.Certificate.MixedSourceBridge

end OAI
