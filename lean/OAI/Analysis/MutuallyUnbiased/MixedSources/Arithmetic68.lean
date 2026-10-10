import OAI.Analysis.MutuallyUnbiased.MixedData.Source8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values9
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1088 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1178 x + ((1 : ℝ) * Sparse.eval nodeValue1181 x + ((1 : ℝ) * Sparse.eval nodeValue1182 x + ((1 : ℝ) * Sparse.eval nodeValue1188 x + ((1 : ℝ) * Sparse.eval nodeValue1257 x + ((1 : ℝ) * Sparse.eval nodeValue2672 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0))))))

def numericRow1088 : Integer.Sparse Master := [(Sum.inr 1178, 1), (Sum.inr 1181, 1), (Sum.inr 1182, 1), (Sum.inr 1188, 1), (Sum.inr 1257, 1), (Sum.inr 2672, 1), (Sum.inr 4088, -1)]

theorem reindexCheck1088 : Integer.Sparse.reindex keyMap MixedData.row1088 = numericRow1088 := by decide +kernel

theorem numericCheck1088 (x : Master → ℝ) : Integer.Sparse.eval numericRow1088 x =
    (1 : ℝ) * reducedSource1088 x := by
  norm_num [numericRow1088, reducedSource1088, Integer.Sparse.eval, Sparse.eval, nodeValue1178, nodeValue1181, nodeValue1182, nodeValue1188, nodeValue1257, nodeValue2672, nodeValue4088]

noncomputable def reducedSource1089 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1179 x + ((1 : ℝ) * Sparse.eval nodeValue1991 x + ((1 : ℝ) * Sparse.eval nodeValue2003 x + ((1 : ℝ) * Sparse.eval nodeValue2032 x + ((1 : ℝ) * Sparse.eval nodeValue2218 x + ((1 : ℝ) * Sparse.eval nodeValue2670 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

def numericRow1089 : Integer.Sparse Master := [(Sum.inr 1179, 1), (Sum.inr 1991, 1), (Sum.inr 2003, 1), (Sum.inr 2032, 1), (Sum.inr 2218, 1), (Sum.inr 2670, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1089 : Integer.Sparse.reindex keyMap MixedData.row1089 = numericRow1089 := by decide +kernel

theorem numericCheck1089 (x : Master → ℝ) : Integer.Sparse.eval numericRow1089 x =
    (1 : ℝ) * reducedSource1089 x := by
  norm_num [numericRow1089, reducedSource1089, Integer.Sparse.eval, Sparse.eval, nodeValue1179, nodeValue1991, nodeValue2003, nodeValue2032, nodeValue2218, nodeValue2670, nodeValue4082]

noncomputable def reducedSource1090 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1195 x + ((2 : ℝ) * Sparse.eval nodeValue2449 x + ((1 : ℝ) * Sparse.eval nodeValue2469 x + ((1 : ℝ) * Sparse.eval nodeValue2691 x + ((1 : ℝ) * Sparse.eval nodeValue2694 x + ((-1 : ℝ) * Sparse.eval nodeValue4090 x + 0)))))

def numericRow1090 : Integer.Sparse Master := [(Sum.inr 1195, 1), (Sum.inr 2449, 2), (Sum.inr 2469, 1), (Sum.inr 2694, 1), (Sum.inr 4090, -1)]

theorem reindexCheck1090 : Integer.Sparse.reindex keyMap MixedData.row1090 = numericRow1090 := by decide +kernel

theorem numericCheck1090 (x : Master → ℝ) : Integer.Sparse.eval numericRow1090 x =
    (1 : ℝ) * reducedSource1090 x := by
  norm_num [numericRow1090, reducedSource1090, Integer.Sparse.eval, Sparse.eval, nodeValue1195, nodeValue2449, nodeValue2469, nodeValue2691, nodeValue2694, nodeValue4090]

noncomputable def reducedSource1091 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1195 x + ((1 : ℝ) * Sparse.eval nodeValue1196 x + ((1 : ℝ) * Sparse.eval nodeValue1200 x + ((2 : ℝ) * Sparse.eval nodeValue1210 x + ((1 : ℝ) * Sparse.eval nodeValue2694 x + ((-1 : ℝ) * Sparse.eval nodeValue4090 x + 0)))))

def numericRow1091 : Integer.Sparse Master := [(Sum.inr 1195, 1), (Sum.inr 1196, 1), (Sum.inr 1200, 1), (Sum.inr 1210, 2), (Sum.inr 2694, 1), (Sum.inr 4090, -1)]

theorem reindexCheck1091 : Integer.Sparse.reindex keyMap MixedData.row1091 = numericRow1091 := by decide +kernel

theorem numericCheck1091 (x : Master → ℝ) : Integer.Sparse.eval numericRow1091 x =
    (1 : ℝ) * reducedSource1091 x := by
  norm_num [numericRow1091, reducedSource1091, Integer.Sparse.eval, Sparse.eval, nodeValue1195, nodeValue1196, nodeValue1200, nodeValue1210, nodeValue2694, nodeValue4090]

noncomputable def reducedSource1092 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1194 x + ((2 : ℝ) * Sparse.eval nodeValue1987 x + ((1 : ℝ) * Sparse.eval nodeValue2008 x + ((1 : ℝ) * Sparse.eval nodeValue2193 x + ((1 : ℝ) * Sparse.eval nodeValue2693 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

def numericRow1092 : Integer.Sparse Master := [(Sum.inr 1194, 1), (Sum.inr 1987, 2), (Sum.inr 2008, 1), (Sum.inr 2193, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1092 : Integer.Sparse.reindex keyMap MixedData.row1092 = numericRow1092 := by decide +kernel

theorem numericCheck1092 (x : Master → ℝ) : Integer.Sparse.eval numericRow1092 x =
    (1 : ℝ) * reducedSource1092 x := by
  norm_num [numericRow1092, reducedSource1092, Integer.Sparse.eval, Sparse.eval, nodeValue1194, nodeValue1987, nodeValue2008, nodeValue2193, nodeValue2693, nodeValue4080]

noncomputable def reducedSource1093 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4183 x + ((1 : ℝ) * Sparse.eval nodeValue4187 x + ((1 : ℝ) * Sparse.eval nodeValue4192 x + ((6 : ℝ) * Sparse.eval nodeValue4551 x + ((3 : ℝ) * Sparse.eval nodeValue4555 x + ((3 : ℝ) * Sparse.eval nodeValue4559 x + ((3 : ℝ) * Sparse.eval nodeValue4623 x + ((3 : ℝ) * Sparse.eval nodeValue4625 x + ((1 : ℝ) * Sparse.eval nodeValue4627 x + ((1 : ℝ) * Sparse.eval nodeValue4629 x + ((3 : ℝ) * Sparse.eval nodeValue5171 x + ((1 : ℝ) * Sparse.eval nodeValue5308 x + ((1 : ℝ) * Sparse.eval nodeValue5312 x + 0))))))))))))

def numericRow1093 : Integer.Sparse Master := [(Sum.inl 0, 19), (Sum.inl 5, 20), (Sum.inl 6, 5), (Sum.inl 1, 100), (Sum.inr 611, -720), (Sum.inr 615, -240), (Sum.inr 620, -240), (Sum.inr 1136, -1440), (Sum.inr 1140, -720), (Sum.inr 1145, -720), (Sum.inr 1535, -720), (Sum.inr 1537, -240), (Sum.inr 1539, -240), (Sum.inr 3273, -1440), (Sum.inr 3275, -720), (Sum.inr 3277, -720), (Sum.inr 3308, -720), (Sum.inr 3310, -720), (Sum.inr 3311, -240), (Sum.inr 3313, -240), (Sum.inr 3608, -720)]

theorem reindexCheck1093 : Integer.Sparse.reindex keyMap MixedData.row1093 = numericRow1093 := by decide +kernel

theorem numericCheck1093 (x : Master → ℝ) : Integer.Sparse.eval numericRow1093 x =
    (960 : ℝ) * reducedSource1093 x := by
  norm_num [numericRow1093, reducedSource1093, Integer.Sparse.eval, Sparse.eval, nodeValue4183, nodeValue4187, nodeValue4192, nodeValue4551, nodeValue4555, nodeValue4559, nodeValue4623, nodeValue4625, nodeValue4627, nodeValue4629, nodeValue5171, nodeValue5308, nodeValue5312]
  ring

noncomputable def reducedSource1094 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue611 x + ((1 : ℝ) * Sparse.eval nodeValue615 x + ((1 : ℝ) * Sparse.eval nodeValue620 x + ((6 : ℝ) * Sparse.eval nodeValue1136 x + ((3 : ℝ) * Sparse.eval nodeValue1140 x + ((3 : ℝ) * Sparse.eval nodeValue1145 x + ((3 : ℝ) * Sparse.eval nodeValue1305 x + ((3 : ℝ) * Sparse.eval nodeValue1307 x + ((1 : ℝ) * Sparse.eval nodeValue1311 x + ((1 : ℝ) * Sparse.eval nodeValue1313 x + ((3 : ℝ) * Sparse.eval nodeValue2965 x + ((1 : ℝ) * Sparse.eval nodeValue3124 x + ((1 : ℝ) * Sparse.eval nodeValue3126 x + 0))))))))))))

def numericRow1094 : Integer.Sparse Master := [(Sum.inl 0, -19), (Sum.inl 5, -20), (Sum.inl 6, -5), (Sum.inl 1, -100), (Sum.inr 611, 720), (Sum.inr 615, 240), (Sum.inr 620, 240), (Sum.inr 1136, 1440), (Sum.inr 1140, 720), (Sum.inr 1145, 720)]

theorem reindexCheck1094 : Integer.Sparse.reindex keyMap MixedData.row1094 = numericRow1094 := by decide +kernel

theorem numericCheck1094 (x : Master → ℝ) : Integer.Sparse.eval numericRow1094 x =
    (240 : ℝ) * reducedSource1094 x := by
  norm_num [numericRow1094, reducedSource1094, Integer.Sparse.eval, Sparse.eval, nodeValue611, nodeValue615, nodeValue620, nodeValue1136, nodeValue1140, nodeValue1145, nodeValue1305, nodeValue1307, nodeValue1311, nodeValue1313, nodeValue2965, nodeValue3124, nodeValue3126]
  ring

noncomputable def reducedSource1095 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4177 x + ((1 : ℝ) * Sparse.eval nodeValue4181 x + ((1 : ℝ) * Sparse.eval nodeValue4191 x + ((3 : ℝ) * Sparse.eval nodeValue4356 x + ((1 : ℝ) * Sparse.eval nodeValue4468 x + ((6 : ℝ) * Sparse.eval nodeValue4546 x + ((3 : ℝ) * Sparse.eval nodeValue4558 x + ((3 : ℝ) * Sparse.eval nodeValue4608 x + ((3 : ℝ) * Sparse.eval nodeValue4624 x + ((1 : ℝ) * Sparse.eval nodeValue4628 x + ((3 : ℝ) * Sparse.eval nodeValue5174 x + ((1 : ℝ) * Sparse.eval nodeValue5296 x + ((1 : ℝ) * Sparse.eval nodeValue5309 x + 0))))))))))))

def numericRow1095 : Integer.Sparse Master := [(Sum.inl 0, 5), (Sum.inl 5, 4), (Sum.inl 6, 1), (Sum.inl 1, -10), (Sum.inr 605, -216), (Sum.inr 609, -72), (Sum.inr 619, -72), (Sum.inr 934, -216), (Sum.inr 1051, -72), (Sum.inr 1131, -432), (Sum.inr 1144, -216), (Sum.inr 1242, -216), (Sum.inr 1518, -216), (Sum.inr 1521, -72), (Sum.inr 1538, -72), (Sum.inr 1692, -216), (Sum.inr 1752, -72), (Sum.inr 3264, -432), (Sum.inr 3276, -216), (Sum.inr 3300, -216), (Sum.inr 3309, -216), (Sum.inr 3312, -72), (Sum.inr 3615, -216), (Sum.inr 3634, -72)]

theorem reindexCheck1095 : Integer.Sparse.reindex keyMap MixedData.row1095 = numericRow1095 := by decide +kernel

theorem numericCheck1095 (x : Master → ℝ) : Integer.Sparse.eval numericRow1095 x =
    (288 : ℝ) * reducedSource1095 x := by
  norm_num [numericRow1095, reducedSource1095, Integer.Sparse.eval, Sparse.eval, nodeValue4177, nodeValue4181, nodeValue4191, nodeValue4356, nodeValue4468, nodeValue4546, nodeValue4558, nodeValue4608, nodeValue4624, nodeValue4628, nodeValue5174, nodeValue5296, nodeValue5309]
  ring

noncomputable def reducedSource1096 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue605 x + ((1 : ℝ) * Sparse.eval nodeValue609 x + ((1 : ℝ) * Sparse.eval nodeValue619 x + ((3 : ℝ) * Sparse.eval nodeValue934 x + ((1 : ℝ) * Sparse.eval nodeValue1051 x + ((6 : ℝ) * Sparse.eval nodeValue1131 x + ((3 : ℝ) * Sparse.eval nodeValue1144 x + ((3 : ℝ) * Sparse.eval nodeValue1242 x + ((3 : ℝ) * Sparse.eval nodeValue1301 x + ((1 : ℝ) * Sparse.eval nodeValue1312 x + ((3 : ℝ) * Sparse.eval nodeValue2601 x + ((1 : ℝ) * Sparse.eval nodeValue2770 x + ((1 : ℝ) * Sparse.eval nodeValue3123 x + 0))))))))))))

def numericRow1096 : Integer.Sparse Master := [(Sum.inl 0, -5), (Sum.inl 5, -4), (Sum.inl 6, -1), (Sum.inl 1, 10), (Sum.inr 605, 216), (Sum.inr 609, 72), (Sum.inr 619, 72), (Sum.inr 934, 216), (Sum.inr 1051, 72), (Sum.inr 1131, 432), (Sum.inr 1144, 216), (Sum.inr 1242, 216)]

theorem reindexCheck1096 : Integer.Sparse.reindex keyMap MixedData.row1096 = numericRow1096 := by decide +kernel

theorem numericCheck1096 (x : Master → ℝ) : Integer.Sparse.eval numericRow1096 x =
    (72 : ℝ) * reducedSource1096 x := by
  norm_num [numericRow1096, reducedSource1096, Integer.Sparse.eval, Sparse.eval, nodeValue605, nodeValue609, nodeValue619, nodeValue934, nodeValue1051, nodeValue1131, nodeValue1144, nodeValue1242, nodeValue1301, nodeValue1312, nodeValue2601, nodeValue2770, nodeValue3123]
  ring

noncomputable def reducedSource1097 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4460 x + ((3 : ℝ) * Sparse.eval nodeValue4463 x + ((1 : ℝ) * Sparse.eval nodeValue4501 x + ((2 : ℝ) * Sparse.eval nodeValue4505 x + ((1 : ℝ) * Sparse.eval nodeValue4507 x + ((6 : ℝ) * Sparse.eval nodeValue4591 x + ((3 : ℝ) * Sparse.eval nodeValue4605 x + ((6 : ℝ) * Sparse.eval nodeValue4608 x + ((3 : ℝ) * Sparse.eval nodeValue4609 x + ((1 : ℝ) * Sparse.eval nodeValue4621 x + ((1 : ℝ) * Sparse.eval nodeValue4625 x + 0))))))))))

def numericRow1097 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 5, -4), (Sum.inl 6, -1), (Sum.inl 1, 4), (Sum.inr 1043, -432), (Sum.inr 1046, -432), (Sum.inr 1091, -144), (Sum.inr 1239, -432), (Sum.inr 1242, -864), (Sum.inr 1297, -144), (Sum.inr 1725, -432), (Sum.inr 1750, -432), (Sum.inr 1756, -144), (Sum.inr 2226, -432), (Sum.inr 2289, -144), (Sum.inr 3300, -864), (Sum.inr 3310, -144), (Sum.inr 4591, 3456), (Sum.inr 4609, 1728)]

theorem reindexCheck1097 : Integer.Sparse.reindex keyMap MixedData.row1097 = numericRow1097 := by decide +kernel

theorem numericCheck1097 (x : Master → ℝ) : Integer.Sparse.eval numericRow1097 x =
    (576 : ℝ) * reducedSource1097 x := by
  norm_num [numericRow1097, reducedSource1097, Integer.Sparse.eval, Sparse.eval, nodeValue4460, nodeValue4463, nodeValue4501, nodeValue4505, nodeValue4507, nodeValue4591, nodeValue4605, nodeValue4608, nodeValue4609, nodeValue4621, nodeValue4625]
  ring

noncomputable def reducedSource1098 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1046 x + ((1 : ℝ) * Sparse.eval nodeValue1089 x + ((1 : ℝ) * Sparse.eval nodeValue1091 x + ((6 : ℝ) * Sparse.eval nodeValue1217 x + ((3 : ℝ) * Sparse.eval nodeValue1242 x + ((3 : ℝ) * Sparse.eval nodeValue1243 x + ((3 : ℝ) * Sparse.eval nodeValue1269 x + ((3 : ℝ) * Sparse.eval nodeValue1271 x + ((1 : ℝ) * Sparse.eval nodeValue1304 x + ((1 : ℝ) * Sparse.eval nodeValue1308 x + ((3 : ℝ) * Sparse.eval nodeValue1416 x + ((1 : ℝ) * Sparse.eval nodeValue1450 x + ((1 : ℝ) * Sparse.eval nodeValue1452 x + 0))))))))))))

def numericRow1098 : Integer.Sparse Master := [(Sum.inl 0, -19), (Sum.inl 5, -20), (Sum.inl 6, 25), (Sum.inl 2, 30), (Sum.inl 1, 20), (Sum.inr 1046, 720), (Sum.inr 1091, 240), (Sum.inr 1217, 1440), (Sum.inr 1242, 720), (Sum.inr 1243, 720)]

theorem reindexCheck1098 : Integer.Sparse.reindex keyMap MixedData.row1098 = numericRow1098 := by decide +kernel

theorem numericCheck1098 (x : Master → ℝ) : Integer.Sparse.eval numericRow1098 x =
    (240 : ℝ) * reducedSource1098 x := by
  norm_num [numericRow1098, reducedSource1098, Integer.Sparse.eval, Sparse.eval, nodeValue1046, nodeValue1089, nodeValue1091, nodeValue1217, nodeValue1242, nodeValue1243, nodeValue1269, nodeValue1271, nodeValue1304, nodeValue1308, nodeValue1416, nodeValue1450, nodeValue1452]
  ring

noncomputable def reducedSource1099 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1750 x + ((1 : ℝ) * Sparse.eval nodeValue1754 x + ((1 : ℝ) * Sparse.eval nodeValue1756 x + ((1 : ℝ) * Sparse.eval nodeValue3310 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0))))

def numericRow1099 : Integer.Sparse Master := [(Sum.inr 1750, 3), (Sum.inr 1756, 1), (Sum.inr 3310, 1), (Sum.inr 4070, -1)]

theorem reindexCheck1099 : Integer.Sparse.reindex keyMap MixedData.row1099 = numericRow1099 := by decide +kernel

theorem numericCheck1099 (x : Master → ℝ) : Integer.Sparse.eval numericRow1099 x =
    (1 : ℝ) * reducedSource1099 x := by
  norm_num [numericRow1099, reducedSource1099, Integer.Sparse.eval, Sparse.eval, nodeValue1750, nodeValue1754, nodeValue1756, nodeValue3310, nodeValue4070]

noncomputable def reducedSource1100 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1725 x + ((1 : ℝ) * Sparse.eval nodeValue1730 x + ((1 : ℝ) * Sparse.eval nodeValue1754 x + ((1 : ℝ) * Sparse.eval nodeValue3310 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0))))

def numericRow1100 : Integer.Sparse Master := [(Sum.inr 1725, 3), (Sum.inr 3310, 1), (Sum.inr 4070, -1)]

theorem reindexCheck1100 : Integer.Sparse.reindex keyMap MixedData.row1100 = numericRow1100 := by decide +kernel

theorem numericCheck1100 (x : Master → ℝ) : Integer.Sparse.eval numericRow1100 x =
    (1 : ℝ) * reducedSource1100 x := by
  norm_num [numericRow1100, reducedSource1100, Integer.Sparse.eval, Sparse.eval, nodeValue1725, nodeValue1730, nodeValue1754, nodeValue3310, nodeValue4070]

noncomputable def reducedSource1101 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1754 x + ((3 : ℝ) * Sparse.eval nodeValue3300 x + ((2 : ℝ) * Sparse.eval nodeValue3310 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))

def numericRow1101 : Integer.Sparse Master := [(Sum.inr 3300, 3), (Sum.inr 3310, 2), (Sum.inr 4070, -1)]

theorem reindexCheck1101 : Integer.Sparse.reindex keyMap MixedData.row1101 = numericRow1101 := by decide +kernel

theorem numericCheck1101 (x : Master → ℝ) : Integer.Sparse.eval numericRow1101 x =
    (1 : ℝ) * reducedSource1101 x := by
  norm_num [numericRow1101, reducedSource1101, Integer.Sparse.eval, Sparse.eval, nodeValue1754, nodeValue3300, nodeValue3310, nodeValue4070]

noncomputable def reducedSource1102 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4184 x + ((1 : ℝ) * Sparse.eval nodeValue4189 x + ((1 : ℝ) * Sparse.eval nodeValue4193 x + ((3 : ℝ) * Sparse.eval nodeValue4370 x + ((1 : ℝ) * Sparse.eval nodeValue4468 x + ((6 : ℝ) * Sparse.eval nodeValue4552 x + ((3 : ℝ) * Sparse.eval nodeValue4560 x + ((3 : ℝ) * Sparse.eval nodeValue4605 x + ((3 : ℝ) * Sparse.eval nodeValue4617 x + ((1 : ℝ) * Sparse.eval nodeValue4626 x + ((3 : ℝ) * Sparse.eval nodeValue4868 x + ((1 : ℝ) * Sparse.eval nodeValue4897 x + ((1 : ℝ) * Sparse.eval nodeValue5305 x + 0))))))))))))

def numericRow1102 : Integer.Sparse Master := [(Sum.inr 1051, -1), (Sum.inr 1239, -3), (Sum.inr 1752, -1), (Sum.inr 2109, -3), (Sum.inr 2226, -3), (Sum.inr 2261, -3), (Sum.inr 2783, -2), (Sum.inr 4184, 12), (Sum.inr 4189, 4), (Sum.inr 4193, 4), (Sum.inr 4370, 12), (Sum.inr 4552, 24), (Sum.inr 4560, 12), (Sum.inr 4617, 12), (Sum.inr 4626, 4)]

theorem reindexCheck1102 : Integer.Sparse.reindex keyMap MixedData.row1102 = numericRow1102 := by decide +kernel

theorem numericCheck1102 (x : Master → ℝ) : Integer.Sparse.eval numericRow1102 x =
    (4 : ℝ) * reducedSource1102 x := by
  norm_num [numericRow1102, reducedSource1102, Integer.Sparse.eval, Sparse.eval, nodeValue4184, nodeValue4189, nodeValue4193, nodeValue4370, nodeValue4468, nodeValue4552, nodeValue4560, nodeValue4605, nodeValue4617, nodeValue4626, nodeValue4868, nodeValue4897, nodeValue5305]
  ring

noncomputable def reducedSource1103 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue612 x + ((1 : ℝ) * Sparse.eval nodeValue617 x + ((1 : ℝ) * Sparse.eval nodeValue621 x + ((6 : ℝ) * Sparse.eval nodeValue1137 x + ((3 : ℝ) * Sparse.eval nodeValue1142 x + ((3 : ℝ) * Sparse.eval nodeValue1146 x + ((3 : ℝ) * Sparse.eval nodeValue1271 x + ((1 : ℝ) * Sparse.eval nodeValue1275 x + ((3 : ℝ) * Sparse.eval nodeValue1306 x + ((1 : ℝ) * Sparse.eval nodeValue1310 x + ((3 : ℝ) * Sparse.eval nodeValue2966 x + ((1 : ℝ) * Sparse.eval nodeValue3114 x + ((1 : ℝ) * Sparse.eval nodeValue3125 x + 0))))))))))))

def numericRow1103 : Integer.Sparse Master := [(Sum.inl 0, -40), (Sum.inl 6, -10), (Sum.inl 2, 40), (Sum.inl 35, 160), (Sum.inl 1, 90), (Sum.inr 612, 2160), (Sum.inr 617, 720), (Sum.inr 621, 720), (Sum.inr 1137, 4320), (Sum.inr 1142, 2160), (Sum.inr 1146, 2160), (Sum.inr 1306, 2160), (Sum.inr 1310, 720)]

theorem reindexCheck1103 : Integer.Sparse.reindex keyMap MixedData.row1103 = numericRow1103 := by decide +kernel

theorem numericCheck1103 (x : Master → ℝ) : Integer.Sparse.eval numericRow1103 x =
    (720 : ℝ) * reducedSource1103 x := by
  norm_num [numericRow1103, reducedSource1103, Integer.Sparse.eval, Sparse.eval, nodeValue612, nodeValue617, nodeValue621, nodeValue1137, nodeValue1142, nodeValue1146, nodeValue1271, nodeValue1275, nodeValue1306, nodeValue1310, nodeValue2966, nodeValue3114, nodeValue3125]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
