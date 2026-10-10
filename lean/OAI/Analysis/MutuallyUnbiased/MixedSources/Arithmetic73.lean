import OAI.Analysis.MutuallyUnbiased.MixedData.Source9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values9
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1168 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue847 x + ((1 : ℝ) * Sparse.eval nodeValue851 x + ((1 : ℝ) * Sparse.eval nodeValue853 x + ((1 : ℝ) * Sparse.eval nodeValue857 x + ((1 : ℝ) * Sparse.eval nodeValue1750 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

def numericRow1168 : Integer.Sparse Master := [(Sum.inr 847, 2), (Sum.inr 853, 1), (Sum.inr 857, 1), (Sum.inr 1750, 1), (Sum.inr 4070, -1)]

theorem reindexCheck1168 : Integer.Sparse.reindex keyMap MixedData.row1168 = numericRow1168 := by decide +kernel

theorem numericCheck1168 (x : Master → ℝ) : Integer.Sparse.eval numericRow1168 x =
    (1 : ℝ) * reducedSource1168 x := by
  norm_num [numericRow1168, reducedSource1168, Integer.Sparse.eval, Sparse.eval, nodeValue847, nodeValue851, nodeValue853, nodeValue857, nodeValue1750, nodeValue4070]

noncomputable def reducedSource1169 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4151 x + ((1 : ℝ) * Sparse.eval nodeValue4156 x + ((1 : ℝ) * Sparse.eval nodeValue4160 x + ((1 : ℝ) * Sparse.eval nodeValue4177 x + ((2 : ℝ) * Sparse.eval nodeValue4326 x + ((2 : ℝ) * Sparse.eval nodeValue4330 x + ((2 : ℝ) * Sparse.eval nodeValue4334 x + ((2 : ℝ) * Sparse.eval nodeValue4346 x + ((2 : ℝ) * Sparse.eval nodeValue4365 x + ((1 : ℝ) * Sparse.eval nodeValue4370 x + ((1 : ℝ) * Sparse.eval nodeValue4373 x + ((2 : ℝ) * Sparse.eval nodeValue4457 x + ((2 : ℝ) * Sparse.eval nodeValue4460 x + ((1 : ℝ) * Sparse.eval nodeValue4466 x + ((1 : ℝ) * Sparse.eval nodeValue4468 x + ((1 : ℝ) * Sparse.eval nodeValue4498 x + ((1 : ℝ) * Sparse.eval nodeValue4505 x + ((2 : ℝ) * Sparse.eval nodeValue4804 x + ((1 : ℝ) * Sparse.eval nodeValue4868 x + ((1 : ℝ) * Sparse.eval nodeValue4894 x + ((1 : ℝ) * Sparse.eval nodeValue4897 x + 0))))))))))))))))))))

def numericRow1169 : Integer.Sparse Master := [(Sum.inr 605, -1), (Sum.inr 924, -2), (Sum.inr 1040, -2), (Sum.inr 1043, -2), (Sum.inr 1049, -1), (Sum.inr 1051, -1), (Sum.inr 1518, -1), (Sum.inr 1674, -2), (Sum.inr 1707, -2), (Sum.inr 1725, -2), (Sum.inr 1738, -1), (Sum.inr 1752, -1), (Sum.inr 2022, -2), (Sum.inr 2109, -1), (Sum.inr 2203, -2), (Sum.inr 2261, -1), (Sum.inr 4151, 8), (Sum.inr 4156, 4), (Sum.inr 4160, 4), (Sum.inr 4330, 8), (Sum.inr 4334, 8), (Sum.inr 4365, 8), (Sum.inr 4370, 4), (Sum.inr 4373, 4)]

theorem reindexCheck1169 : Integer.Sparse.reindex keyMap MixedData.row1169 = numericRow1169 := by decide +kernel

theorem numericCheck1169 (x : Master → ℝ) : Integer.Sparse.eval numericRow1169 x =
    (4 : ℝ) * reducedSource1169 x := by
  norm_num [numericRow1169, reducedSource1169, Integer.Sparse.eval, Sparse.eval, nodeValue4151, nodeValue4156, nodeValue4160, nodeValue4177, nodeValue4326, nodeValue4330, nodeValue4334, nodeValue4346, nodeValue4365, nodeValue4370, nodeValue4373, nodeValue4457, nodeValue4460, nodeValue4466, nodeValue4468, nodeValue4498, nodeValue4505, nodeValue4804, nodeValue4868, nodeValue4894, nodeValue4897]
  ring

noncomputable def reducedSource1170 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue630 x + ((1 : ℝ) * Sparse.eval nodeValue633 x + ((1 : ℝ) * Sparse.eval nodeValue636 x + ((1 : ℝ) * Sparse.eval nodeValue647 x + ((2 : ℝ) * Sparse.eval nodeValue1118 x + ((1 : ℝ) * Sparse.eval nodeValue1142 x + ((1 : ℝ) * Sparse.eval nodeValue1275 x + ((2 : ℝ) * Sparse.eval nodeValue1320 x + ((1 : ℝ) * Sparse.eval nodeValue1325 x + ((2 : ℝ) * Sparse.eval nodeValue1329 x + ((2 : ℝ) * Sparse.eval nodeValue1334 x + ((2 : ℝ) * Sparse.eval nodeValue1342 x + ((2 : ℝ) * Sparse.eval nodeValue1414 x + ((2 : ℝ) * Sparse.eval nodeValue1416 x + ((1 : ℝ) * Sparse.eval nodeValue1419 x + ((1 : ℝ) * Sparse.eval nodeValue1448 x + ((1 : ℝ) * Sparse.eval nodeValue1450 x + ((2 : ℝ) * Sparse.eval nodeValue2941 x + ((1 : ℝ) * Sparse.eval nodeValue2966 x + ((1 : ℝ) * Sparse.eval nodeValue3114 x + ((1 : ℝ) * Sparse.eval nodeValue3230 x + 0))))))))))))))))))))

def numericRow1170 : Integer.Sparse Master := [(Sum.inl 0, -53), (Sum.inl 5, 20), (Sum.inl 6, -25), (Sum.inl 2, 60), (Sum.inl 1, 70), (Sum.inr 630, 1080), (Sum.inr 633, 540), (Sum.inr 636, 540), (Sum.inr 1118, 1080), (Sum.inr 1142, 540), (Sum.inr 1320, 1080), (Sum.inr 1325, 540), (Sum.inr 1334, 1080)]

theorem reindexCheck1170 : Integer.Sparse.reindex keyMap MixedData.row1170 = numericRow1170 := by decide +kernel

theorem numericCheck1170 (x : Master → ℝ) : Integer.Sparse.eval numericRow1170 x =
    (540 : ℝ) * reducedSource1170 x := by
  norm_num [numericRow1170, reducedSource1170, Integer.Sparse.eval, Sparse.eval, nodeValue630, nodeValue633, nodeValue636, nodeValue647, nodeValue1118, nodeValue1142, nodeValue1275, nodeValue1320, nodeValue1325, nodeValue1329, nodeValue1334, nodeValue1342, nodeValue1414, nodeValue1416, nodeValue1419, nodeValue1448, nodeValue1450, nodeValue2941, nodeValue2966, nodeValue3114, nodeValue3230]
  ring

noncomputable def reducedSource1171 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1505 x + ((1 : ℝ) * Sparse.eval nodeValue1516 x + ((1 : ℝ) * Sparse.eval nodeValue1518 x + ((1 : ℝ) * Sparse.eval nodeValue1523 x + ((2 : ℝ) * Sparse.eval nodeValue1663 x + ((2 : ℝ) * Sparse.eval nodeValue1672 x + ((2 : ℝ) * Sparse.eval nodeValue1674 x + ((2 : ℝ) * Sparse.eval nodeValue1679 x + ((2 : ℝ) * Sparse.eval nodeValue1704 x + ((2 : ℝ) * Sparse.eval nodeValue1707 x + ((1 : ℝ) * Sparse.eval nodeValue1722 x + ((2 : ℝ) * Sparse.eval nodeValue1725 x + ((1 : ℝ) * Sparse.eval nodeValue1727 x + ((1 : ℝ) * Sparse.eval nodeValue1735 x + ((1 : ℝ) * Sparse.eval nodeValue1738 x + ((1 : ℝ) * Sparse.eval nodeValue1752 x + ((1 : ℝ) * Sparse.eval nodeValue1754 x + ((2 : ℝ) * Sparse.eval nodeValue2203 x + ((1 : ℝ) * Sparse.eval nodeValue2261 x + ((1 : ℝ) * Sparse.eval nodeValue2264 x + ((1 : ℝ) * Sparse.eval nodeValue2292 x + 0))))))))))))))))))))

def numericRow1171 : Integer.Sparse Master := [(Sum.inr 1505, 2), (Sum.inr 1516, 1), (Sum.inr 1518, 1), (Sum.inr 1523, 1), (Sum.inr 1672, 2), (Sum.inr 1674, 2), (Sum.inr 1679, 2), (Sum.inr 1704, 2), (Sum.inr 1707, 2), (Sum.inr 1722, 1), (Sum.inr 1725, 2), (Sum.inr 1735, 1), (Sum.inr 1738, 1), (Sum.inr 1752, 1), (Sum.inr 2203, 2), (Sum.inr 2261, 1)]

theorem reindexCheck1171 : Integer.Sparse.reindex keyMap MixedData.row1171 = numericRow1171 := by decide +kernel

theorem numericCheck1171 (x : Master → ℝ) : Integer.Sparse.eval numericRow1171 x =
    (1 : ℝ) * reducedSource1171 x := by
  norm_num [numericRow1171, reducedSource1171, Integer.Sparse.eval, Sparse.eval, nodeValue1505, nodeValue1516, nodeValue1518, nodeValue1523, nodeValue1663, nodeValue1672, nodeValue1674, nodeValue1679, nodeValue1704, nodeValue1707, nodeValue1722, nodeValue1725, nodeValue1727, nodeValue1735, nodeValue1738, nodeValue1752, nodeValue1754, nodeValue2203, nodeValue2261, nodeValue2264, nodeValue2292]

noncomputable def reducedSource1172 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue579 x + ((1 : ℝ) * Sparse.eval nodeValue584 x + ((1 : ℝ) * Sparse.eval nodeValue588 x + ((1 : ℝ) * Sparse.eval nodeValue605 x + ((1 : ℝ) * Sparse.eval nodeValue1043 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1172 : Integer.Sparse Master := [(Sum.inr 579, 2), (Sum.inr 584, 1), (Sum.inr 588, 1), (Sum.inr 605, 1), (Sum.inr 1043, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1172 : Integer.Sparse.reindex keyMap MixedData.row1172 = numericRow1172 := by decide +kernel

theorem numericCheck1172 (x : Master → ℝ) : Integer.Sparse.eval numericRow1172 x =
    (1 : ℝ) * reducedSource1172 x := by
  norm_num [numericRow1172, reducedSource1172, Integer.Sparse.eval, Sparse.eval, nodeValue579, nodeValue584, nodeValue588, nodeValue605, nodeValue1043, nodeValue4084]

noncomputable def reducedSource1173 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue605 x + ((2 : ℝ) * Sparse.eval nodeValue924 x + ((1 : ℝ) * Sparse.eval nodeValue1043 x + ((1 : ℝ) * Sparse.eval nodeValue1082 x + ((1 : ℝ) * Sparse.eval nodeValue1089 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1173 : Integer.Sparse Master := [(Sum.inr 605, 1), (Sum.inr 924, 2), (Sum.inr 1043, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1173 : Integer.Sparse.reindex keyMap MixedData.row1173 = numericRow1173 := by decide +kernel

theorem numericCheck1173 (x : Master → ℝ) : Integer.Sparse.eval numericRow1173 x =
    (1 : ℝ) * reducedSource1173 x := by
  norm_num [numericRow1173, reducedSource1173, Integer.Sparse.eval, Sparse.eval, nodeValue605, nodeValue924, nodeValue1043, nodeValue1082, nodeValue1089, nodeValue4084]

noncomputable def reducedSource1174 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue943 x + ((1 : ℝ) * Sparse.eval nodeValue948 x + ((1 : ℝ) * Sparse.eval nodeValue952 x + ((1 : ℝ) * Sparse.eval nodeValue1043 x + ((1 : ℝ) * Sparse.eval nodeValue2109 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1174 : Integer.Sparse Master := [(Sum.inr 943, 2), (Sum.inr 948, 1), (Sum.inr 952, 1), (Sum.inr 1043, 1), (Sum.inr 2109, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1174 : Integer.Sparse.reindex keyMap MixedData.row1174 = numericRow1174 := by decide +kernel

theorem numericCheck1174 (x : Master → ℝ) : Integer.Sparse.eval numericRow1174 x =
    (1 : ℝ) * reducedSource1174 x := by
  norm_num [numericRow1174, reducedSource1174, Integer.Sparse.eval, Sparse.eval, nodeValue943, nodeValue948, nodeValue952, nodeValue1043, nodeValue2109, nodeValue4084]

noncomputable def reducedSource1175 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue579 x + ((1 : ℝ) * Sparse.eval nodeValue904 x + ((1 : ℝ) * Sparse.eval nodeValue943 x + ((1 : ℝ) * Sparse.eval nodeValue1040 x + ((2 : ℝ) * Sparse.eval nodeValue1043 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1175 : Integer.Sparse Master := [(Sum.inr 579, 1), (Sum.inr 943, 1), (Sum.inr 1040, 1), (Sum.inr 1043, 2), (Sum.inr 4084, -1)]

theorem reindexCheck1175 : Integer.Sparse.reindex keyMap MixedData.row1175 = numericRow1175 := by decide +kernel

theorem numericCheck1175 (x : Master → ℝ) : Integer.Sparse.eval numericRow1175 x =
    (1 : ℝ) * reducedSource1175 x := by
  norm_num [numericRow1175, reducedSource1175, Integer.Sparse.eval, Sparse.eval, nodeValue579, nodeValue904, nodeValue943, nodeValue1040, nodeValue1043, nodeValue4084]

noncomputable def reducedSource1176 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue904 x + ((1 : ℝ) * Sparse.eval nodeValue908 x + ((1 : ℝ) * Sparse.eval nodeValue912 x + ((1 : ℝ) * Sparse.eval nodeValue924 x + ((1 : ℝ) * Sparse.eval nodeValue1043 x + ((1 : ℝ) * Sparse.eval nodeValue2022 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow1176 : Integer.Sparse Master := [(Sum.inr 908, 1), (Sum.inr 912, 1), (Sum.inr 924, 1), (Sum.inr 1043, 1), (Sum.inr 2022, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1176 : Integer.Sparse.reindex keyMap MixedData.row1176 = numericRow1176 := by decide +kernel

theorem numericCheck1176 (x : Master → ℝ) : Integer.Sparse.eval numericRow1176 x =
    (1 : ℝ) * reducedSource1176 x := by
  norm_num [numericRow1176, reducedSource1176, Integer.Sparse.eval, Sparse.eval, nodeValue904, nodeValue908, nodeValue912, nodeValue924, nodeValue1043, nodeValue2022, nodeValue4084]

noncomputable def reducedSource1177 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4101 x + ((1 : ℝ) * Sparse.eval nodeValue4103 x + ((1 : ℝ) * Sparse.eval nodeValue4110 x + ((1 : ℝ) * Sparse.eval nodeValue4121 x + ((2 : ℝ) * Sparse.eval nodeValue4287 x + ((2 : ℝ) * Sparse.eval nodeValue4289 x + ((2 : ℝ) * Sparse.eval nodeValue4295 x + ((2 : ℝ) * Sparse.eval nodeValue4303 x + ((2 : ℝ) * Sparse.eval nodeValue4346 x + ((1 : ℝ) * Sparse.eval nodeValue4350 x + ((1 : ℝ) * Sparse.eval nodeValue4360 x + ((2 : ℝ) * Sparse.eval nodeValue4401 x + ((1 : ℝ) * Sparse.eval nodeValue4405 x + ((1 : ℝ) * Sparse.eval nodeValue4428 x + ((2 : ℝ) * Sparse.eval nodeValue4458 x + ((1 : ℝ) * Sparse.eval nodeValue4467 x + ((1 : ℝ) * Sparse.eval nodeValue4499 x + ((2 : ℝ) * Sparse.eval nodeValue5075 x + ((1 : ℝ) * Sparse.eval nodeValue5171 x + ((1 : ℝ) * Sparse.eval nodeValue5261 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + 0))))))))))))))))))))

def numericRow1177 : Integer.Sparse Master := [(Sum.inl 0, 43), (Sum.inl 5, 20), (Sum.inl 6, 5), (Sum.inl 2, -30), (Sum.inl 1, 70), (Sum.inr 538, -4320), (Sum.inr 540, -2160), (Sum.inr 547, -2160), (Sum.inr 555, -2160), (Sum.inr 663, -4320), (Sum.inr 665, -2160), (Sum.inr 671, -2160), (Sum.inr 684, -2160), (Sum.inr 865, -4320), (Sum.inr 867, -4320), (Sum.inr 873, -4320), (Sum.inr 881, -4320), (Sum.inr 924, -4320), (Sum.inr 928, -2160), (Sum.inr 938, -2160), (Sum.inr 982, -4320), (Sum.inr 986, -2160), (Sum.inr 1009, -2160), (Sum.inr 1041, -4320), (Sum.inr 1050, -2160), (Sum.inr 1083, -2160), (Sum.inr 1553, -4320), (Sum.inr 1555, -4320), (Sum.inr 1559, -4320), (Sum.inr 1569, -4320), (Sum.inr 1617, -4320), (Sum.inr 1620, -2160), (Sum.inr 1630, -2160), (Sum.inr 1674, -4320), (Sum.inr 1677, -2160), (Sum.inr 1693, -2160), (Sum.inr 1724, -4320), (Sum.inr 1728, -2160), (Sum.inr 1751, -2160), (Sum.inr 2482, -4320), (Sum.inr 2726, -2160), (Sum.inr 3468, -4320), (Sum.inr 3545, -2160), (Sum.inr 3608, -2160), (Sum.inr 3627, -2160)]

theorem reindexCheck1177 : Integer.Sparse.reindex keyMap MixedData.row1177 = numericRow1177 := by decide +kernel

theorem numericCheck1177 (x : Master → ℝ) : Integer.Sparse.eval numericRow1177 x =
    (8640 : ℝ) * reducedSource1177 x := by
  norm_num [numericRow1177, reducedSource1177, Integer.Sparse.eval, Sparse.eval, nodeValue4101, nodeValue4103, nodeValue4110, nodeValue4121, nodeValue4287, nodeValue4289, nodeValue4295, nodeValue4303, nodeValue4346, nodeValue4350, nodeValue4360, nodeValue4401, nodeValue4405, nodeValue4428, nodeValue4458, nodeValue4467, nodeValue4499, nodeValue5075, nodeValue5171, nodeValue5261, nodeValue5293]
  ring

noncomputable def reducedSource1178 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue538 x + ((1 : ℝ) * Sparse.eval nodeValue540 x + ((1 : ℝ) * Sparse.eval nodeValue547 x + ((1 : ℝ) * Sparse.eval nodeValue555 x + ((2 : ℝ) * Sparse.eval nodeValue865 x + ((2 : ℝ) * Sparse.eval nodeValue867 x + ((2 : ℝ) * Sparse.eval nodeValue873 x + ((2 : ℝ) * Sparse.eval nodeValue881 x + ((2 : ℝ) * Sparse.eval nodeValue924 x + ((1 : ℝ) * Sparse.eval nodeValue928 x + ((1 : ℝ) * Sparse.eval nodeValue938 x + ((2 : ℝ) * Sparse.eval nodeValue982 x + ((1 : ℝ) * Sparse.eval nodeValue986 x + ((1 : ℝ) * Sparse.eval nodeValue1009 x + ((2 : ℝ) * Sparse.eval nodeValue1041 x + ((1 : ℝ) * Sparse.eval nodeValue1050 x + ((1 : ℝ) * Sparse.eval nodeValue1083 x + ((2 : ℝ) * Sparse.eval nodeValue2482 x + ((1 : ℝ) * Sparse.eval nodeValue2598 x + ((1 : ℝ) * Sparse.eval nodeValue2726 x + ((1 : ℝ) * Sparse.eval nodeValue2767 x + 0))))))))))))))))))))

def numericRow1178 : Integer.Sparse Master := [(Sum.inl 0, -43), (Sum.inl 5, -20), (Sum.inl 6, -5), (Sum.inl 2, 30), (Sum.inl 1, -70), (Sum.inr 538, 4320), (Sum.inr 540, 2160), (Sum.inr 547, 2160), (Sum.inr 555, 2160), (Sum.inr 865, 4320), (Sum.inr 867, 4320), (Sum.inr 873, 4320), (Sum.inr 881, 4320), (Sum.inr 924, 4320), (Sum.inr 928, 2160), (Sum.inr 938, 2160), (Sum.inr 982, 4320), (Sum.inr 986, 2160), (Sum.inr 1009, 2160), (Sum.inr 1041, 4320), (Sum.inr 1050, 2160), (Sum.inr 1083, 2160), (Sum.inr 2482, 4320), (Sum.inr 2726, 2160)]

theorem reindexCheck1178 : Integer.Sparse.reindex keyMap MixedData.row1178 = numericRow1178 := by decide +kernel

theorem numericCheck1178 (x : Master → ℝ) : Integer.Sparse.eval numericRow1178 x =
    (2160 : ℝ) * reducedSource1178 x := by
  norm_num [numericRow1178, reducedSource1178, Integer.Sparse.eval, Sparse.eval, nodeValue538, nodeValue540, nodeValue547, nodeValue555, nodeValue865, nodeValue867, nodeValue873, nodeValue881, nodeValue924, nodeValue928, nodeValue938, nodeValue982, nodeValue986, nodeValue1009, nodeValue1041, nodeValue1050, nodeValue1083, nodeValue2482, nodeValue2598, nodeValue2726, nodeValue2767]
  ring

noncomputable def reducedSource1179 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1217 x + ((1 : ℝ) * Sparse.eval nodeValue1242 x + ((1 : ℝ) * Sparse.eval nodeValue1243 x + ((1 : ℝ) * Sparse.eval nodeValue1307 x + ((2 : ℝ) * Sparse.eval nodeValue1361 x + ((1 : ℝ) * Sparse.eval nodeValue1372 x + ((1 : ℝ) * Sparse.eval nodeValue1373 x + ((2 : ℝ) * Sparse.eval nodeValue1379 x + ((2 : ℝ) * Sparse.eval nodeValue1388 x + ((2 : ℝ) * Sparse.eval nodeValue1389 x + ((2 : ℝ) * Sparse.eval nodeValue1397 x + ((2 : ℝ) * Sparse.eval nodeValue1399 x + ((1 : ℝ) * Sparse.eval nodeValue1413 x + ((2 : ℝ) * Sparse.eval nodeValue1416 x + ((1 : ℝ) * Sparse.eval nodeValue1417 x + ((1 : ℝ) * Sparse.eval nodeValue1450 x + ((1 : ℝ) * Sparse.eval nodeValue1452 x + ((1 : ℝ) * Sparse.eval nodeValue1471 x + ((2 : ℝ) * Sparse.eval nodeValue1478 x + ((1 : ℝ) * Sparse.eval nodeValue1484 x + ((1 : ℝ) * Sparse.eval nodeValue1485 x + 0))))))))))))))))))))

def numericRow1179 : Integer.Sparse Master := [(Sum.inl 0, -53), (Sum.inl 5, 20), (Sum.inl 6, 65), (Sum.inl 2, 60), (Sum.inl 1, -20), (Sum.inr 1217, 1080), (Sum.inr 1242, 540), (Sum.inr 1243, 540), (Sum.inr 1361, 1080), (Sum.inr 1372, 540), (Sum.inr 1373, 540), (Sum.inr 1388, 1080), (Sum.inr 1389, 1080)]

theorem reindexCheck1179 : Integer.Sparse.reindex keyMap MixedData.row1179 = numericRow1179 := by decide +kernel

theorem numericCheck1179 (x : Master → ℝ) : Integer.Sparse.eval numericRow1179 x =
    (540 : ℝ) * reducedSource1179 x := by
  norm_num [numericRow1179, reducedSource1179, Integer.Sparse.eval, Sparse.eval, nodeValue1217, nodeValue1242, nodeValue1243, nodeValue1307, nodeValue1361, nodeValue1372, nodeValue1373, nodeValue1379, nodeValue1388, nodeValue1389, nodeValue1397, nodeValue1399, nodeValue1413, nodeValue1416, nodeValue1417, nodeValue1450, nodeValue1452, nodeValue1471, nodeValue1478, nodeValue1484, nodeValue1485]
  ring

noncomputable def reducedSource1180 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1037 x + ((2 : ℝ) * Sparse.eval nodeValue2018 x + ((1 : ℝ) * Sparse.eval nodeValue2103 x + ((1 : ℝ) * Sparse.eval nodeValue2208 x + ((1 : ℝ) * Sparse.eval nodeValue2261 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0)))))

def numericRow1180 : Integer.Sparse Master := [(Sum.inr 1037, 1), (Sum.inr 2018, 2), (Sum.inr 2103, 1), (Sum.inr 2261, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1180 : Integer.Sparse.reindex keyMap MixedData.row1180 = numericRow1180 := by decide +kernel

theorem numericCheck1180 (x : Master → ℝ) : Integer.Sparse.eval numericRow1180 x =
    (1 : ℝ) * reducedSource1180 x := by
  norm_num [numericRow1180, reducedSource1180, Integer.Sparse.eval, Sparse.eval, nodeValue1037, nodeValue2018, nodeValue2103, nodeValue2208, nodeValue2261, nodeValue4081]

noncomputable def reducedSource1181 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue594 x + ((2 : ℝ) * Sparse.eval nodeValue916 x + ((1 : ℝ) * Sparse.eval nodeValue1007 x + ((1 : ℝ) * Sparse.eval nodeValue1037 x + ((1 : ℝ) * Sparse.eval nodeValue1074 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0)))))

def numericRow1181 : Integer.Sparse Master := [(Sum.inr 594, 1), (Sum.inr 916, 2), (Sum.inr 1037, 1), (Sum.inr 1074, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1181 : Integer.Sparse.reindex keyMap MixedData.row1181 = numericRow1181 := by decide +kernel

theorem numericCheck1181 (x : Master → ℝ) : Integer.Sparse.eval numericRow1181 x =
    (1 : ℝ) * reducedSource1181 x := by
  norm_num [numericRow1181, reducedSource1181, Integer.Sparse.eval, Sparse.eval, nodeValue594, nodeValue916, nodeValue1007, nodeValue1037, nodeValue1074, nodeValue4081]

noncomputable def reducedSource1182 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1033 x + ((1 : ℝ) * Sparse.eval nodeValue1037 x + ((1 : ℝ) * Sparse.eval nodeValue1048 x + ((1 : ℝ) * Sparse.eval nodeValue1074 x + ((1 : ℝ) * Sparse.eval nodeValue2261 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0)))))

def numericRow1182 : Integer.Sparse Master := [(Sum.inr 1033, 2), (Sum.inr 1037, 1), (Sum.inr 1048, 1), (Sum.inr 1074, 1), (Sum.inr 2261, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1182 : Integer.Sparse.reindex keyMap MixedData.row1182 = numericRow1182 := by decide +kernel

theorem numericCheck1182 (x : Master → ℝ) : Integer.Sparse.eval numericRow1182 x =
    (1 : ℝ) * reducedSource1182 x := by
  norm_num [numericRow1182, reducedSource1182, Integer.Sparse.eval, Sparse.eval, nodeValue1033, nodeValue1037, nodeValue1048, nodeValue1074, nodeValue2261, nodeValue4081]

noncomputable def reducedSource1183 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue731 x + ((1 : ℝ) * Sparse.eval nodeValue735 x + ((1 : ℝ) * Sparse.eval nodeValue741 x + ((1 : ℝ) * Sparse.eval nodeValue809 x + ((1 : ℝ) * Sparse.eval nodeValue1647 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

def numericRow1183 : Integer.Sparse Master := [(Sum.inr 731, 2), (Sum.inr 735, 1), (Sum.inr 741, 1), (Sum.inr 1647, 1), (Sum.inr 4070, -1)]

theorem reindexCheck1183 : Integer.Sparse.reindex keyMap MixedData.row1183 = numericRow1183 := by decide +kernel

theorem numericCheck1183 (x : Master → ℝ) : Integer.Sparse.eval numericRow1183 x =
    (1 : ℝ) * reducedSource1183 x := by
  norm_num [numericRow1183, reducedSource1183, Integer.Sparse.eval, Sparse.eval, nodeValue731, nodeValue735, nodeValue741, nodeValue809, nodeValue1647, nodeValue4070]

end MUB6.Certificate.MixedSourceBridge

end OAI
