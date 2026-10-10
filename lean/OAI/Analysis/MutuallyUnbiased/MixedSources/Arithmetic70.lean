import OAI.Analysis.MutuallyUnbiased.MixedData.Source8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values23
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values9
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1120 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4144 x + ((1 : ℝ) * Sparse.eval nodeValue4146 x + ((1 : ℝ) * Sparse.eval nodeValue4148 x + ((1 : ℝ) * Sparse.eval nodeValue4177 x + ((2 : ℝ) * Sparse.eval nodeValue4293 x + ((1 : ℝ) * Sparse.eval nodeValue4315 x + ((1 : ℝ) * Sparse.eval nodeValue4468 x + ((2 : ℝ) * Sparse.eval nodeValue4517 x + ((1 : ℝ) * Sparse.eval nodeValue4520 x + ((2 : ℝ) * Sparse.eval nodeValue4523 x + ((2 : ℝ) * Sparse.eval nodeValue4526 x + ((2 : ℝ) * Sparse.eval nodeValue4546 x + ((2 : ℝ) * Sparse.eval nodeValue4606 x + ((2 : ℝ) * Sparse.eval nodeValue4608 x + ((1 : ℝ) * Sparse.eval nodeValue4612 x + ((1 : ℝ) * Sparse.eval nodeValue4624 x + ((1 : ℝ) * Sparse.eval nodeValue4625 x + ((2 : ℝ) * Sparse.eval nodeValue5078 x + ((1 : ℝ) * Sparse.eval nodeValue5109 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5296 x + 0))))))))))))))))))))

def numericRow1120 : Integer.Sparse Master := [(Sum.inl 0, 38), (Sum.inl 5, -30), (Sum.inl 6, -5), (Sum.inl 2, 30), (Sum.inl 8, -40), (Sum.inl 1, -5), (Sum.inr 572, -2160), (Sum.inr 574, -1080), (Sum.inr 576, -1080), (Sum.inr 605, -1080), (Sum.inr 871, -2160), (Sum.inr 893, -1080), (Sum.inr 1051, -1080), (Sum.inr 1101, -2160), (Sum.inr 1104, -1080), (Sum.inr 1107, -2160), (Sum.inr 1110, -2160), (Sum.inr 1131, -2160), (Sum.inr 1240, -2160), (Sum.inr 1242, -2160), (Sum.inr 1246, -1080), (Sum.inr 1492, -2160), (Sum.inr 1494, -1080), (Sum.inr 1496, -1080), (Sum.inr 1518, -1080), (Sum.inr 1568, -2160), (Sum.inr 1578, -1080), (Sum.inr 1752, -1080), (Sum.inr 2485, -2160), (Sum.inr 2519, -1080), (Sum.inr 3235, -2160), (Sum.inr 3237, -1080), (Sum.inr 3250, -2160), (Sum.inr 3252, -2160), (Sum.inr 3264, -2160), (Sum.inr 3299, -2160), (Sum.inr 3300, -2160), (Sum.inr 3301, -1080), (Sum.inr 3309, -1080), (Sum.inr 3310, -1080), (Sum.inr 3481, -2160), (Sum.inr 3486, -1080), (Sum.inr 3627, -1080), (Sum.inr 3634, -1080)]

theorem reindexCheck1120 : Integer.Sparse.reindex keyMap MixedData.row1120 = numericRow1120 := by decide +kernel

theorem numericCheck1120 (x : Master → ℝ) : Integer.Sparse.eval numericRow1120 x =
    (4320 : ℝ) * reducedSource1120 x := by
  norm_num [numericRow1120, reducedSource1120, Integer.Sparse.eval, Sparse.eval, nodeValue4144, nodeValue4146, nodeValue4148, nodeValue4177, nodeValue4293, nodeValue4315, nodeValue4468, nodeValue4517, nodeValue4520, nodeValue4523, nodeValue4526, nodeValue4546, nodeValue4606, nodeValue4608, nodeValue4612, nodeValue4624, nodeValue4625, nodeValue5078, nodeValue5109, nodeValue5293, nodeValue5296]
  ring

noncomputable def reducedSource1121 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue572 x + ((1 : ℝ) * Sparse.eval nodeValue574 x + ((1 : ℝ) * Sparse.eval nodeValue576 x + ((1 : ℝ) * Sparse.eval nodeValue605 x + ((2 : ℝ) * Sparse.eval nodeValue871 x + ((1 : ℝ) * Sparse.eval nodeValue893 x + ((1 : ℝ) * Sparse.eval nodeValue1051 x + ((2 : ℝ) * Sparse.eval nodeValue1101 x + ((1 : ℝ) * Sparse.eval nodeValue1104 x + ((2 : ℝ) * Sparse.eval nodeValue1107 x + ((2 : ℝ) * Sparse.eval nodeValue1110 x + ((2 : ℝ) * Sparse.eval nodeValue1131 x + ((2 : ℝ) * Sparse.eval nodeValue1240 x + ((2 : ℝ) * Sparse.eval nodeValue1242 x + ((1 : ℝ) * Sparse.eval nodeValue1246 x + ((1 : ℝ) * Sparse.eval nodeValue1301 x + ((1 : ℝ) * Sparse.eval nodeValue1304 x + ((2 : ℝ) * Sparse.eval nodeValue2485 x + ((1 : ℝ) * Sparse.eval nodeValue2519 x + ((1 : ℝ) * Sparse.eval nodeValue2770 x + ((1 : ℝ) * Sparse.eval nodeValue3102 x + 0))))))))))))))))))))

def numericRow1121 : Integer.Sparse Master := [(Sum.inl 0, -38), (Sum.inl 5, 30), (Sum.inl 6, 5), (Sum.inl 2, -30), (Sum.inl 8, 40), (Sum.inl 1, 5), (Sum.inr 572, 2160), (Sum.inr 574, 1080), (Sum.inr 576, 1080), (Sum.inr 605, 1080), (Sum.inr 871, 2160), (Sum.inr 893, 1080), (Sum.inr 1051, 1080), (Sum.inr 1101, 2160), (Sum.inr 1104, 1080), (Sum.inr 1107, 2160), (Sum.inr 1110, 2160), (Sum.inr 1131, 2160), (Sum.inr 1240, 2160), (Sum.inr 1242, 2160), (Sum.inr 1246, 1080), (Sum.inr 2485, 2160), (Sum.inr 2519, 1080)]

theorem reindexCheck1121 : Integer.Sparse.reindex keyMap MixedData.row1121 = numericRow1121 := by decide +kernel

theorem numericCheck1121 (x : Master → ℝ) : Integer.Sparse.eval numericRow1121 x =
    (1080 : ℝ) * reducedSource1121 x := by
  norm_num [numericRow1121, reducedSource1121, Integer.Sparse.eval, Sparse.eval, nodeValue572, nodeValue574, nodeValue576, nodeValue605, nodeValue871, nodeValue893, nodeValue1051, nodeValue1101, nodeValue1104, nodeValue1107, nodeValue1110, nodeValue1131, nodeValue1240, nodeValue1242, nodeValue1246, nodeValue1301, nodeValue1304, nodeValue2485, nodeValue2519, nodeValue2770, nodeValue3102]
  ring

noncomputable def reducedSource1122 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1617 x + ((1 : ℝ) * Sparse.eval nodeValue1625 x + ((1 : ℝ) * Sparse.eval nodeValue1630 x + ((1 : ℝ) * Sparse.eval nodeValue1754 x + ((1 : ℝ) * Sparse.eval nodeValue3300 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

def numericRow1122 : Integer.Sparse Master := [(Sum.inr 1617, 2), (Sum.inr 1630, 1), (Sum.inr 3300, 1), (Sum.inr 4070, -1)]

theorem reindexCheck1122 : Integer.Sparse.reindex keyMap MixedData.row1122 = numericRow1122 := by decide +kernel

theorem numericCheck1122 (x : Master → ℝ) : Integer.Sparse.eval numericRow1122 x =
    (1 : ℝ) * reducedSource1122 x := by
  norm_num [numericRow1122, reducedSource1122, Integer.Sparse.eval, Sparse.eval, nodeValue1617, nodeValue1625, nodeValue1630, nodeValue1754, nodeValue3300, nodeValue4070]

noncomputable def reducedSource1123 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4157 x + ((1 : ℝ) * Sparse.eval nodeValue4159 x + ((1 : ℝ) * Sparse.eval nodeValue4162 x + ((1 : ℝ) * Sparse.eval nodeValue4184 x + ((2 : ℝ) * Sparse.eval nodeValue4330 x + ((1 : ℝ) * Sparse.eval nodeValue4356 x + ((1 : ℝ) * Sparse.eval nodeValue4468 x + ((2 : ℝ) * Sparse.eval nodeValue4532 x + ((2 : ℝ) * Sparse.eval nodeValue4536 x + ((2 : ℝ) * Sparse.eval nodeValue4543 x + ((2 : ℝ) * Sparse.eval nodeValue4552 x + ((1 : ℝ) * Sparse.eval nodeValue4557 x + ((2 : ℝ) * Sparse.eval nodeValue4600 x + ((2 : ℝ) * Sparse.eval nodeValue4605 x + ((1 : ℝ) * Sparse.eval nodeValue4611 x + ((1 : ℝ) * Sparse.eval nodeValue4617 x + ((1 : ℝ) * Sparse.eval nodeValue4621 x + ((2 : ℝ) * Sparse.eval nodeValue4804 x + ((1 : ℝ) * Sparse.eval nodeValue4841 x + ((1 : ℝ) * Sparse.eval nodeValue4897 x + ((1 : ℝ) * Sparse.eval nodeValue5272 x + 0))))))))))))))))))))

def numericRow1123 : Integer.Sparse Master := [(Sum.inr 934, -1), (Sum.inr 1051, -1), (Sum.inr 1128, -2), (Sum.inr 1143, -1), (Sum.inr 1239, -2), (Sum.inr 1297, -1), (Sum.inr 1692, -1), (Sum.inr 1752, -1), (Sum.inr 2022, -2), (Sum.inr 2167, -1), (Sum.inr 2184, -2), (Sum.inr 2203, -2), (Sum.inr 2226, -2), (Sum.inr 2289, -1), (Sum.inr 2740, -2), (Sum.inr 4157, 8), (Sum.inr 4159, 4), (Sum.inr 4162, 4), (Sum.inr 4184, 4), (Sum.inr 4330, 8), (Sum.inr 4532, 8), (Sum.inr 4536, 8), (Sum.inr 4552, 8), (Sum.inr 4600, 8), (Sum.inr 4611, 4), (Sum.inr 4617, 4)]

theorem reindexCheck1123 : Integer.Sparse.reindex keyMap MixedData.row1123 = numericRow1123 := by decide +kernel

theorem numericCheck1123 (x : Master → ℝ) : Integer.Sparse.eval numericRow1123 x =
    (4 : ℝ) * reducedSource1123 x := by
  norm_num [numericRow1123, reducedSource1123, Integer.Sparse.eval, Sparse.eval, nodeValue4157, nodeValue4159, nodeValue4162, nodeValue4184, nodeValue4330, nodeValue4356, nodeValue4468, nodeValue4532, nodeValue4536, nodeValue4543, nodeValue4552, nodeValue4557, nodeValue4600, nodeValue4605, nodeValue4611, nodeValue4617, nodeValue4621, nodeValue4804, nodeValue4841, nodeValue4897, nodeValue5272]
  ring

noncomputable def reducedSource1124 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue585 x + ((1 : ℝ) * Sparse.eval nodeValue587 x + ((1 : ℝ) * Sparse.eval nodeValue590 x + ((1 : ℝ) * Sparse.eval nodeValue612 x + ((2 : ℝ) * Sparse.eval nodeValue1116 x + ((2 : ℝ) * Sparse.eval nodeValue1118 x + ((2 : ℝ) * Sparse.eval nodeValue1121 x + ((2 : ℝ) * Sparse.eval nodeValue1137 x + ((2 : ℝ) * Sparse.eval nodeValue1170 x + ((1 : ℝ) * Sparse.eval nodeValue1173 x + ((1 : ℝ) * Sparse.eval nodeValue1177 x + ((2 : ℝ) * Sparse.eval nodeValue1270 x + ((2 : ℝ) * Sparse.eval nodeValue1271 x + ((1 : ℝ) * Sparse.eval nodeValue1273 x + ((1 : ℝ) * Sparse.eval nodeValue1275 x + ((1 : ℝ) * Sparse.eval nodeValue1306 x + ((1 : ℝ) * Sparse.eval nodeValue1308 x + ((2 : ℝ) * Sparse.eval nodeValue2941 x + ((1 : ℝ) * Sparse.eval nodeValue3004 x + ((1 : ℝ) * Sparse.eval nodeValue3113 x + ((1 : ℝ) * Sparse.eval nodeValue3114 x + 0))))))))))))))))))))

def numericRow1124 : Integer.Sparse Master := [(Sum.inl 0, -114), (Sum.inl 5, 40), (Sum.inl 6, -40), (Sum.inl 2, 140), (Sum.inl 35, -160), (Sum.inl 1, 110), (Sum.inr 585, 2880), (Sum.inr 587, 1440), (Sum.inr 590, 1440), (Sum.inr 612, 1440), (Sum.inr 1116, 2880), (Sum.inr 1118, 2880), (Sum.inr 1121, 2880), (Sum.inr 1137, 2880), (Sum.inr 1270, 2880), (Sum.inr 1273, 1440), (Sum.inr 1306, 1440)]

theorem reindexCheck1124 : Integer.Sparse.reindex keyMap MixedData.row1124 = numericRow1124 := by decide +kernel

theorem numericCheck1124 (x : Master → ℝ) : Integer.Sparse.eval numericRow1124 x =
    (1440 : ℝ) * reducedSource1124 x := by
  norm_num [numericRow1124, reducedSource1124, Integer.Sparse.eval, Sparse.eval, nodeValue585, nodeValue587, nodeValue590, nodeValue612, nodeValue1116, nodeValue1118, nodeValue1121, nodeValue1137, nodeValue1170, nodeValue1173, nodeValue1177, nodeValue1270, nodeValue1271, nodeValue1273, nodeValue1275, nodeValue1306, nodeValue1308, nodeValue2941, nodeValue3004, nodeValue3113, nodeValue3114]
  ring

noncomputable def reducedSource1125 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1528 x + ((1 : ℝ) * Sparse.eval nodeValue1529 x + ((1 : ℝ) * Sparse.eval nodeValue1530 x + ((1 : ℝ) * Sparse.eval nodeValue1532 x + ((2 : ℝ) * Sparse.eval nodeValue1672 x + ((1 : ℝ) * Sparse.eval nodeValue1692 x + ((1 : ℝ) * Sparse.eval nodeValue1752 x + ((2 : ℝ) * Sparse.eval nodeValue2149 x + ((1 : ℝ) * Sparse.eval nodeValue2167 x + ((2 : ℝ) * Sparse.eval nodeValue2172 x + ((2 : ℝ) * Sparse.eval nodeValue2184 x + ((2 : ℝ) * Sparse.eval nodeValue2200 x + ((2 : ℝ) * Sparse.eval nodeValue2203 x + ((2 : ℝ) * Sparse.eval nodeValue2226 x + ((1 : ℝ) * Sparse.eval nodeValue2228 x + ((1 : ℝ) * Sparse.eval nodeValue2289 x + ((1 : ℝ) * Sparse.eval nodeValue2292 x + ((1 : ℝ) * Sparse.eval nodeValue2683 x + ((2 : ℝ) * Sparse.eval nodeValue2702 x + ((1 : ℝ) * Sparse.eval nodeValue2737 x + ((1 : ℝ) * Sparse.eval nodeValue2740 x + 0))))))))))))))))))))

def numericRow1125 : Integer.Sparse Master := [(Sum.inr 1528, 2), (Sum.inr 1529, 1), (Sum.inr 1530, 1), (Sum.inr 1532, 1), (Sum.inr 1672, 2), (Sum.inr 1692, 1), (Sum.inr 1752, 1), (Sum.inr 2149, 2), (Sum.inr 2167, 1), (Sum.inr 2172, 2), (Sum.inr 2184, 2), (Sum.inr 2200, 2), (Sum.inr 2203, 2), (Sum.inr 2226, 2), (Sum.inr 2289, 1), (Sum.inr 2683, 1), (Sum.inr 2702, 2), (Sum.inr 2737, 1), (Sum.inr 2740, 1)]

theorem reindexCheck1125 : Integer.Sparse.reindex keyMap MixedData.row1125 = numericRow1125 := by decide +kernel

theorem numericCheck1125 (x : Master → ℝ) : Integer.Sparse.eval numericRow1125 x =
    (1 : ℝ) * reducedSource1125 x := by
  norm_num [numericRow1125, reducedSource1125, Integer.Sparse.eval, Sparse.eval, nodeValue1528, nodeValue1529, nodeValue1530, nodeValue1532, nodeValue1672, nodeValue1692, nodeValue1752, nodeValue2149, nodeValue2167, nodeValue2172, nodeValue2184, nodeValue2200, nodeValue2203, nodeValue2226, nodeValue2228, nodeValue2289, nodeValue2292, nodeValue2683, nodeValue2702, nodeValue2737, nodeValue2740]

noncomputable def reducedSource1126 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue624 x + ((1 : ℝ) * Sparse.eval nodeValue628 x + ((1 : ℝ) * Sparse.eval nodeValue634 x + ((1 : ℝ) * Sparse.eval nodeValue639 x + ((1 : ℝ) * Sparse.eval nodeValue1239 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1126 : Integer.Sparse Master := [(Sum.inr 624, 2), (Sum.inr 628, 1), (Sum.inr 634, 1), (Sum.inr 639, 1), (Sum.inr 1239, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1126 : Integer.Sparse.reindex keyMap MixedData.row1126 = numericRow1126 := by decide +kernel

theorem numericCheck1126 (x : Master → ℝ) : Integer.Sparse.eval numericRow1126 x =
    (1 : ℝ) * reducedSource1126 x := by
  norm_num [numericRow1126, reducedSource1126, Integer.Sparse.eval, Sparse.eval, nodeValue624, nodeValue628, nodeValue634, nodeValue639, nodeValue1239, nodeValue4084]

noncomputable def reducedSource1127 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue624 x + ((1 : ℝ) * Sparse.eval nodeValue1128 x + ((1 : ℝ) * Sparse.eval nodeValue1147 x + ((1 : ℝ) * Sparse.eval nodeValue1234 x + ((2 : ℝ) * Sparse.eval nodeValue1239 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1127 : Integer.Sparse Master := [(Sum.inr 624, 1), (Sum.inr 1128, 1), (Sum.inr 1147, 1), (Sum.inr 1234, 1), (Sum.inr 1239, 2), (Sum.inr 4084, -1)]

theorem reindexCheck1127 : Integer.Sparse.reindex keyMap MixedData.row1127 = numericRow1127 := by decide +kernel

theorem numericCheck1127 (x : Master → ℝ) : Integer.Sparse.eval numericRow1127 x =
    (1 : ℝ) * reducedSource1127 x := by
  norm_num [numericRow1127, reducedSource1127, Integer.Sparse.eval, Sparse.eval, nodeValue624, nodeValue1128, nodeValue1147, nodeValue1234, nodeValue1239, nodeValue4084]

noncomputable def reducedSource1128 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue908 x + ((1 : ℝ) * Sparse.eval nodeValue1147 x + ((1 : ℝ) * Sparse.eval nodeValue1153 x + ((1 : ℝ) * Sparse.eval nodeValue1157 x + ((1 : ℝ) * Sparse.eval nodeValue1239 x + ((1 : ℝ) * Sparse.eval nodeValue2022 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow1128 : Integer.Sparse Master := [(Sum.inr 908, 1), (Sum.inr 1147, 1), (Sum.inr 1153, 1), (Sum.inr 1157, 1), (Sum.inr 1239, 1), (Sum.inr 2022, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1128 : Integer.Sparse.reindex keyMap MixedData.row1128 = numericRow1128 := by decide +kernel

theorem numericCheck1128 (x : Master → ℝ) : Integer.Sparse.eval numericRow1128 x =
    (1 : ℝ) * reducedSource1128 x := by
  norm_num [numericRow1128, reducedSource1128, Integer.Sparse.eval, Sparse.eval, nodeValue908, nodeValue1147, nodeValue1153, nodeValue1157, nodeValue1239, nodeValue2022, nodeValue4084]

noncomputable def reducedSource1129 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue934 x + ((2 : ℝ) * Sparse.eval nodeValue1128 x + ((1 : ℝ) * Sparse.eval nodeValue1143 x + ((1 : ℝ) * Sparse.eval nodeValue1239 x + ((1 : ℝ) * Sparse.eval nodeValue2060 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1129 : Integer.Sparse Master := [(Sum.inr 934, 1), (Sum.inr 1128, 2), (Sum.inr 1143, 1), (Sum.inr 1239, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1129 : Integer.Sparse.reindex keyMap MixedData.row1129 = numericRow1129 := by decide +kernel

theorem numericCheck1129 (x : Master → ℝ) : Integer.Sparse.eval numericRow1129 x =
    (1 : ℝ) * reducedSource1129 x := by
  norm_num [numericRow1129, reducedSource1129, Integer.Sparse.eval, Sparse.eval, nodeValue934, nodeValue1128, nodeValue1143, nodeValue1239, nodeValue2060, nodeValue4084]

noncomputable def reducedSource1130 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4140 x + ((1 : ℝ) * Sparse.eval nodeValue4142 x + ((1 : ℝ) * Sparse.eval nodeValue4147 x + ((1 : ℝ) * Sparse.eval nodeValue4174 x + ((2 : ℝ) * Sparse.eval nodeValue4202 x + ((1 : ℝ) * Sparse.eval nodeValue4225 x + ((1 : ℝ) * Sparse.eval nodeValue4257 x + ((2 : ℝ) * Sparse.eval nodeValue4514 x + ((1 : ℝ) * Sparse.eval nodeValue4519 x + ((2 : ℝ) * Sparse.eval nodeValue4521 x + ((2 : ℝ) * Sparse.eval nodeValue4525 x + ((2 : ℝ) * Sparse.eval nodeValue4543 x + ((2 : ℝ) * Sparse.eval nodeValue4583 x + ((2 : ℝ) * Sparse.eval nodeValue4602 x + ((1 : ℝ) * Sparse.eval nodeValue4605 x + ((1 : ℝ) * Sparse.eval nodeValue4612 x + ((1 : ℝ) * Sparse.eval nodeValue4623 x + ((2 : ℝ) * Sparse.eval nodeValue4807 x + ((1 : ℝ) * Sparse.eval nodeValue4843 x + ((1 : ℝ) * Sparse.eval nodeValue4890 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + 0))))))))))))))))))))

def numericRow1130 : Integer.Sparse Master := [(Sum.inl 0, 34), (Sum.inl 6, 5), (Sum.inl 2, -25), (Sum.inl 7, -80), (Sum.inl 3, -80), (Sum.inl 1, 20), (Sum.inr 568, -4320), (Sum.inr 570, -2160), (Sum.inr 575, -2160), (Sum.inr 602, -2160), (Sum.inr 705, -4320), (Sum.inr 726, -2160), (Sum.inr 762, -4320), (Sum.inr 765, -2160), (Sum.inr 774, -2160), (Sum.inr 791, -2160), (Sum.inr 849, -2160), (Sum.inr 1098, -4320), (Sum.inr 1103, -2160), (Sum.inr 1105, -4320), (Sum.inr 1109, -4320), (Sum.inr 1128, -4320), (Sum.inr 1202, -4320), (Sum.inr 1236, -4320), (Sum.inr 1239, -2160), (Sum.inr 1246, -2160), (Sum.inr 1489, -4320), (Sum.inr 1495, -2160), (Sum.inr 1509, -2160), (Sum.inr 1849, -4320), (Sum.inr 1858, -2160), (Sum.inr 1887, -4320), (Sum.inr 1894, -4320), (Sum.inr 1942, -4320), (Sum.inr 2025, -4320), (Sum.inr 2062, -2160), (Sum.inr 2184, -4320), (Sum.inr 2224, -4320), (Sum.inr 2226, -2160), (Sum.inr 2230, -2160), (Sum.inr 2247, -2160), (Sum.inr 2290, -2160), (Sum.inr 3293, -4320), (Sum.inr 3301, -2160), (Sum.inr 3308, -2160), (Sum.inr 3632, -2160)]

theorem reindexCheck1130 : Integer.Sparse.reindex keyMap MixedData.row1130 = numericRow1130 := by decide +kernel

theorem numericCheck1130 (x : Master → ℝ) : Integer.Sparse.eval numericRow1130 x =
    (8640 : ℝ) * reducedSource1130 x := by
  norm_num [numericRow1130, reducedSource1130, Integer.Sparse.eval, Sparse.eval, nodeValue4140, nodeValue4142, nodeValue4147, nodeValue4174, nodeValue4202, nodeValue4225, nodeValue4257, nodeValue4514, nodeValue4519, nodeValue4521, nodeValue4525, nodeValue4543, nodeValue4583, nodeValue4602, nodeValue4605, nodeValue4612, nodeValue4623, nodeValue4807, nodeValue4843, nodeValue4890, nodeValue5294]
  ring

noncomputable def reducedSource1131 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue568 x + ((1 : ℝ) * Sparse.eval nodeValue570 x + ((1 : ℝ) * Sparse.eval nodeValue575 x + ((1 : ℝ) * Sparse.eval nodeValue602 x + ((2 : ℝ) * Sparse.eval nodeValue705 x + ((1 : ℝ) * Sparse.eval nodeValue726 x + ((1 : ℝ) * Sparse.eval nodeValue791 x + ((2 : ℝ) * Sparse.eval nodeValue1098 x + ((1 : ℝ) * Sparse.eval nodeValue1103 x + ((2 : ℝ) * Sparse.eval nodeValue1105 x + ((2 : ℝ) * Sparse.eval nodeValue1109 x + ((2 : ℝ) * Sparse.eval nodeValue1128 x + ((2 : ℝ) * Sparse.eval nodeValue1202 x + ((2 : ℝ) * Sparse.eval nodeValue1236 x + ((1 : ℝ) * Sparse.eval nodeValue1239 x + ((1 : ℝ) * Sparse.eval nodeValue1246 x + ((1 : ℝ) * Sparse.eval nodeValue1300 x + ((2 : ℝ) * Sparse.eval nodeValue2025 x + ((1 : ℝ) * Sparse.eval nodeValue2062 x + ((1 : ℝ) * Sparse.eval nodeValue2247 x + ((1 : ℝ) * Sparse.eval nodeValue3101 x + 0))))))))))))))))))))

def numericRow1131 : Integer.Sparse Master := [(Sum.inl 0, -34), (Sum.inl 6, -5), (Sum.inl 2, 25), (Sum.inl 7, 80), (Sum.inl 3, 80), (Sum.inl 1, -20), (Sum.inr 568, 4320), (Sum.inr 570, 2160), (Sum.inr 575, 2160), (Sum.inr 602, 2160), (Sum.inr 705, 4320), (Sum.inr 726, 2160), (Sum.inr 791, 2160), (Sum.inr 1098, 4320), (Sum.inr 1103, 2160), (Sum.inr 1105, 4320), (Sum.inr 1109, 4320), (Sum.inr 1128, 4320), (Sum.inr 1202, 4320), (Sum.inr 1236, 4320), (Sum.inr 1239, 2160), (Sum.inr 1246, 2160), (Sum.inr 2025, 4320), (Sum.inr 2062, 2160), (Sum.inr 2247, 2160)]

theorem reindexCheck1131 : Integer.Sparse.reindex keyMap MixedData.row1131 = numericRow1131 := by decide +kernel

theorem numericCheck1131 (x : Master → ℝ) : Integer.Sparse.eval numericRow1131 x =
    (2160 : ℝ) * reducedSource1131 x := by
  norm_num [numericRow1131, reducedSource1131, Integer.Sparse.eval, Sparse.eval, nodeValue568, nodeValue570, nodeValue575, nodeValue602, nodeValue705, nodeValue726, nodeValue791, nodeValue1098, nodeValue1103, nodeValue1105, nodeValue1109, nodeValue1128, nodeValue1202, nodeValue1236, nodeValue1239, nodeValue1246, nodeValue1300, nodeValue2025, nodeValue2062, nodeValue2247, nodeValue3101]
  ring

noncomputable def reducedSource1132 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1002 x + ((2 : ℝ) * Sparse.eval nodeValue1599 x + ((1 : ℝ) * Sparse.eval nodeValue1625 x + ((1 : ℝ) * Sparse.eval nodeValue1730 x + ((1 : ℝ) * Sparse.eval nodeValue2226 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

def numericRow1132 : Integer.Sparse Master := [(Sum.inr 1002, 1), (Sum.inr 1599, 2), (Sum.inr 2226, 1), (Sum.inr 4070, -1)]

theorem reindexCheck1132 : Integer.Sparse.reindex keyMap MixedData.row1132 = numericRow1132 := by decide +kernel

theorem numericCheck1132 (x : Master → ℝ) : Integer.Sparse.eval numericRow1132 x =
    (1 : ℝ) * reducedSource1132 x := by
  norm_num [numericRow1132, reducedSource1132, Integer.Sparse.eval, Sparse.eval, nodeValue1002, nodeValue1599, nodeValue1625, nodeValue1730, nodeValue2226, nodeValue4070]

noncomputable def reducedSource1133 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1231 x + ((2 : ℝ) * Sparse.eval nodeValue1637 x + ((1 : ℝ) * Sparse.eval nodeValue1650 x + ((1 : ℝ) * Sparse.eval nodeValue1710 x + ((1 : ℝ) * Sparse.eval nodeValue2737 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

def numericRow1133 : Integer.Sparse Master := [(Sum.inr 1231, 1), (Sum.inr 1637, 2), (Sum.inr 1650, 1), (Sum.inr 1710, 1), (Sum.inr 2737, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1133 : Integer.Sparse.reindex keyMap MixedData.row1133 = numericRow1133 := by decide +kernel

theorem numericCheck1133 (x : Master → ℝ) : Integer.Sparse.eval numericRow1133 x =
    (1 : ℝ) * reducedSource1133 x := by
  norm_num [numericRow1133, reducedSource1133, Integer.Sparse.eval, Sparse.eval, nodeValue1231, nodeValue1637, nodeValue1650, nodeValue1710, nodeValue2737, nodeValue4069]

noncomputable def reducedSource1134 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1191 x + ((2 : ℝ) * Sparse.eval nodeValue2391 x + ((1 : ℝ) * Sparse.eval nodeValue2407 x + ((1 : ℝ) * Sparse.eval nodeValue2680 x + ((1 : ℝ) * Sparse.eval nodeValue2686 x + ((-1 : ℝ) * Sparse.eval nodeValue4089 x + 0)))))

def numericRow1134 : Integer.Sparse Master := [(Sum.inr 1191, 1), (Sum.inr 2391, 2), (Sum.inr 2407, 1), (Sum.inr 2680, 1), (Sum.inr 2686, 1), (Sum.inr 4089, -1)]

theorem reindexCheck1134 : Integer.Sparse.reindex keyMap MixedData.row1134 = numericRow1134 := by decide +kernel

theorem numericCheck1134 (x : Master → ℝ) : Integer.Sparse.eval numericRow1134 x =
    (1 : ℝ) * reducedSource1134 x := by
  norm_num [numericRow1134, reducedSource1134, Integer.Sparse.eval, Sparse.eval, nodeValue1191, nodeValue2391, nodeValue2407, nodeValue2680, nodeValue2686, nodeValue4089]

noncomputable def reducedSource1135 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1185 x + ((1 : ℝ) * Sparse.eval nodeValue1191 x + ((1 : ℝ) * Sparse.eval nodeValue1193 x + ((1 : ℝ) * Sparse.eval nodeValue1288 x + ((1 : ℝ) * Sparse.eval nodeValue2686 x + ((-1 : ℝ) * Sparse.eval nodeValue4089 x + 0)))))

def numericRow1135 : Integer.Sparse Master := [(Sum.inr 1185, 2), (Sum.inr 1191, 1), (Sum.inr 1193, 1), (Sum.inr 1288, 1), (Sum.inr 2686, 1), (Sum.inr 4089, -1)]

theorem reindexCheck1135 : Integer.Sparse.reindex keyMap MixedData.row1135 = numericRow1135 := by decide +kernel

theorem numericCheck1135 (x : Master → ℝ) : Integer.Sparse.eval numericRow1135 x =
    (1 : ℝ) * reducedSource1135 x := by
  norm_num [numericRow1135, reducedSource1135, Integer.Sparse.eval, Sparse.eval, nodeValue1185, nodeValue1191, nodeValue1193, nodeValue1288, nodeValue2686, nodeValue4089]

end MUB6.Certificate.MixedSourceBridge

end OAI
