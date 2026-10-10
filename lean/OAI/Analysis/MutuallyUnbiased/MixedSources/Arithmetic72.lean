import OAI.Analysis.MutuallyUnbiased.MixedData.Source9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values9
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1152 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1019 x + ((1 : ℝ) * Sparse.eval nodeValue2008 x + ((2 : ℝ) * Sparse.eval nodeValue2087 x + ((1 : ℝ) * Sparse.eval nodeValue2193 x + ((1 : ℝ) * Sparse.eval nodeValue2242 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

def numericRow1152 : Integer.Sparse Master := [(Sum.inr 1019, 1), (Sum.inr 2008, 1), (Sum.inr 2087, 2), (Sum.inr 2193, 1), (Sum.inr 2242, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1152 : Integer.Sparse.reindex keyMap MixedData.row1152 = numericRow1152 := by decide +kernel

theorem numericCheck1152 (x : Master → ℝ) : Integer.Sparse.eval numericRow1152 x =
    (1 : ℝ) * reducedSource1152 x := by
  norm_num [numericRow1152, reducedSource1152, Integer.Sparse.eval, Sparse.eval, nodeValue1019, nodeValue2008, nodeValue2087, nodeValue2193, nodeValue2242, nodeValue4080]

noncomputable def reducedSource1153 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1017 x + ((1 : ℝ) * Sparse.eval nodeValue1019 x + ((1 : ℝ) * Sparse.eval nodeValue1025 x + ((2 : ℝ) * Sparse.eval nodeValue1035 x + ((1 : ℝ) * Sparse.eval nodeValue2242 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

def numericRow1153 : Integer.Sparse Master := [(Sum.inr 1017, 1), (Sum.inr 1019, 1), (Sum.inr 1025, 1), (Sum.inr 1035, 2), (Sum.inr 2242, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1153 : Integer.Sparse.reindex keyMap MixedData.row1153 = numericRow1153 := by decide +kernel

theorem numericCheck1153 (x : Master → ℝ) : Integer.Sparse.eval numericRow1153 x =
    (1 : ℝ) * reducedSource1153 x := by
  norm_num [numericRow1153, reducedSource1153, Integer.Sparse.eval, Sparse.eval, nodeValue1017, nodeValue1019, nodeValue1025, nodeValue1035, nodeValue2242, nodeValue4080]

noncomputable def reducedSource1154 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue972 x + ((1 : ℝ) * Sparse.eval nodeValue1898 x + ((2 : ℝ) * Sparse.eval nodeValue2071 x + ((1 : ℝ) * Sparse.eval nodeValue2187 x + ((1 : ℝ) * Sparse.eval nodeValue2191 x + ((-1 : ℝ) * Sparse.eval nodeValue4079 x + 0)))))

def numericRow1154 : Integer.Sparse Master := [(Sum.inr 972, 1), (Sum.inr 1898, 1), (Sum.inr 2071, 2), (Sum.inr 2187, 1), (Sum.inr 2191, 1), (Sum.inr 4079, -1)]

theorem reindexCheck1154 : Integer.Sparse.reindex keyMap MixedData.row1154 = numericRow1154 := by decide +kernel

theorem numericCheck1154 (x : Master → ℝ) : Integer.Sparse.eval numericRow1154 x =
    (1 : ℝ) * reducedSource1154 x := by
  norm_num [numericRow1154, reducedSource1154, Integer.Sparse.eval, Sparse.eval, nodeValue972, nodeValue1898, nodeValue2071, nodeValue2187, nodeValue2191, nodeValue4079]

noncomputable def reducedSource1155 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue972 x + ((1 : ℝ) * Sparse.eval nodeValue974 x + ((2 : ℝ) * Sparse.eval nodeValue980 x + ((1 : ℝ) * Sparse.eval nodeValue1018 x + ((1 : ℝ) * Sparse.eval nodeValue2191 x + ((-1 : ℝ) * Sparse.eval nodeValue4079 x + 0)))))

def numericRow1155 : Integer.Sparse Master := [(Sum.inr 972, 1), (Sum.inr 980, 2), (Sum.inr 1018, 1), (Sum.inr 2191, 1), (Sum.inr 4079, -1)]

theorem reindexCheck1155 : Integer.Sparse.reindex keyMap MixedData.row1155 = numericRow1155 := by decide +kernel

theorem numericCheck1155 (x : Master → ℝ) : Integer.Sparse.eval numericRow1155 x =
    (1 : ℝ) * reducedSource1155 x := by
  norm_num [numericRow1155, reducedSource1155, Integer.Sparse.eval, Sparse.eval, nodeValue972, nodeValue974, nodeValue980, nodeValue1018, nodeValue2191, nodeValue4079]

noncomputable def reducedSource1156 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue971 x + ((1 : ℝ) * Sparse.eval nodeValue1897 x + ((2 : ℝ) * Sparse.eval nodeValue2070 x + ((1 : ℝ) * Sparse.eval nodeValue2190 x + ((1 : ℝ) * Sparse.eval nodeValue2193 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

def numericRow1156 : Integer.Sparse Master := [(Sum.inr 1897, 1), (Sum.inr 2070, 2), (Sum.inr 2190, 1), (Sum.inr 2193, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1156 : Integer.Sparse.reindex keyMap MixedData.row1156 = numericRow1156 := by decide +kernel

theorem numericCheck1156 (x : Master → ℝ) : Integer.Sparse.eval numericRow1156 x =
    (1 : ℝ) * reducedSource1156 x := by
  norm_num [numericRow1156, reducedSource1156, Integer.Sparse.eval, Sparse.eval, nodeValue971, nodeValue1897, nodeValue2070, nodeValue2190, nodeValue2193, nodeValue4080]

noncomputable def reducedSource1157 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue971 x + ((1 : ℝ) * Sparse.eval nodeValue973 x + ((2 : ℝ) * Sparse.eval nodeValue977 x + ((1 : ℝ) * Sparse.eval nodeValue1017 x + ((1 : ℝ) * Sparse.eval nodeValue2190 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

def numericRow1157 : Integer.Sparse Master := [(Sum.inr 973, 1), (Sum.inr 977, 2), (Sum.inr 1017, 1), (Sum.inr 2190, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1157 : Integer.Sparse.reindex keyMap MixedData.row1157 = numericRow1157 := by decide +kernel

theorem numericCheck1157 (x : Master → ℝ) : Integer.Sparse.eval numericRow1157 x =
    (1 : ℝ) * reducedSource1157 x := by
  norm_num [numericRow1157, reducedSource1157, Integer.Sparse.eval, Sparse.eval, nodeValue971, nodeValue973, nodeValue977, nodeValue1017, nodeValue2190, nodeValue4080]

noncomputable def reducedSource1158 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4153 x + ((1 : ℝ) * Sparse.eval nodeValue4159 x + ((1 : ℝ) * Sparse.eval nodeValue4161 x + ((1 : ℝ) * Sparse.eval nodeValue4183 x + ((2 : ℝ) * Sparse.eval nodeValue4327 x + ((2 : ℝ) * Sparse.eval nodeValue4333 x + ((2 : ℝ) * Sparse.eval nodeValue4335 x + ((2 : ℝ) * Sparse.eval nodeValue4352 x + ((1 : ℝ) * Sparse.eval nodeValue4358 x + ((2 : ℝ) * Sparse.eval nodeValue4367 x + ((1 : ℝ) * Sparse.eval nodeValue4374 x + ((2 : ℝ) * Sparse.eval nodeValue4440 x + ((1 : ℝ) * Sparse.eval nodeValue4445 x + ((2 : ℝ) * Sparse.eval nodeValue4458 x + ((1 : ℝ) * Sparse.eval nodeValue4463 x + ((1 : ℝ) * Sparse.eval nodeValue4467 x + ((1 : ℝ) * Sparse.eval nodeValue4502 x + ((2 : ℝ) * Sparse.eval nodeValue4807 x + ((1 : ℝ) * Sparse.eval nodeValue4871 x + ((1 : ℝ) * Sparse.eval nodeValue4890 x + ((1 : ℝ) * Sparse.eval nodeValue4895 x + 0))))))))))))))))))))

def numericRow1158 : Integer.Sparse Master := [(Sum.inr 611, -1), (Sum.inr 930, -2), (Sum.inr 1041, -2), (Sum.inr 1046, -1), (Sum.inr 1050, -1), (Sum.inr 1535, -1), (Sum.inr 1690, -2), (Sum.inr 1724, -2), (Sum.inr 1750, -1), (Sum.inr 1751, -1), (Sum.inr 2025, -2), (Sum.inr 2112, -1), (Sum.inr 2224, -2), (Sum.inr 2247, -1), (Sum.inr 2287, -1), (Sum.inr 2290, -1), (Sum.inr 4153, 8), (Sum.inr 4159, 4), (Sum.inr 4161, 4), (Sum.inr 4327, 8), (Sum.inr 4333, 8), (Sum.inr 4335, 8), (Sum.inr 4358, 4), (Sum.inr 4367, 8), (Sum.inr 4374, 4), (Sum.inr 4440, 8), (Sum.inr 4445, 4)]

theorem reindexCheck1158 : Integer.Sparse.reindex keyMap MixedData.row1158 = numericRow1158 := by decide +kernel

theorem numericCheck1158 (x : Master → ℝ) : Integer.Sparse.eval numericRow1158 x =
    (4 : ℝ) * reducedSource1158 x := by
  norm_num [numericRow1158, reducedSource1158, Integer.Sparse.eval, Sparse.eval, nodeValue4153, nodeValue4159, nodeValue4161, nodeValue4183, nodeValue4327, nodeValue4333, nodeValue4335, nodeValue4352, nodeValue4358, nodeValue4367, nodeValue4374, nodeValue4440, nodeValue4445, nodeValue4458, nodeValue4463, nodeValue4467, nodeValue4502, nodeValue4807, nodeValue4871, nodeValue4890, nodeValue4895]
  ring

noncomputable def reducedSource1159 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue626 x + ((1 : ℝ) * Sparse.eval nodeValue628 x + ((1 : ℝ) * Sparse.eval nodeValue635 x + ((1 : ℝ) * Sparse.eval nodeValue645 x + ((2 : ℝ) * Sparse.eval nodeValue911 x + ((1 : ℝ) * Sparse.eval nodeValue936 x + ((1 : ℝ) * Sparse.eval nodeValue1027 x + ((2 : ℝ) * Sparse.eval nodeValue1317 x + ((1 : ℝ) * Sparse.eval nodeValue1324 x + ((2 : ℝ) * Sparse.eval nodeValue1327 x + ((2 : ℝ) * Sparse.eval nodeValue1333 x + ((2 : ℝ) * Sparse.eval nodeValue1340 x + ((2 : ℝ) * Sparse.eval nodeValue1388 x + ((2 : ℝ) * Sparse.eval nodeValue1411 x + ((1 : ℝ) * Sparse.eval nodeValue1413 x + ((1 : ℝ) * Sparse.eval nodeValue1420 x + ((1 : ℝ) * Sparse.eval nodeValue1447 x + ((2 : ℝ) * Sparse.eval nodeValue2574 x + ((1 : ℝ) * Sparse.eval nodeValue2602 x + ((1 : ℝ) * Sparse.eval nodeValue2755 x + ((1 : ℝ) * Sparse.eval nodeValue3229 x + 0))))))))))))))))))))

def numericRow1159 : Integer.Sparse Master := [(Sum.inl 0, -208), (Sum.inl 5, 80), (Sum.inl 6, -80), (Sum.inl 2, -320), (Sum.inl 52, -320), (Sum.inl 1, -400), (Sum.inr 626, 5760), (Sum.inr 628, 2880), (Sum.inr 635, 2880), (Sum.inr 911, 5760), (Sum.inr 936, 2880), (Sum.inr 1027, 2880), (Sum.inr 1317, 5760), (Sum.inr 1324, 2880), (Sum.inr 1327, 5760), (Sum.inr 1333, 5760), (Sum.inr 1388, 5760)]

theorem reindexCheck1159 : Integer.Sparse.reindex keyMap MixedData.row1159 = numericRow1159 := by decide +kernel

theorem numericCheck1159 (x : Master → ℝ) : Integer.Sparse.eval numericRow1159 x =
    (2880 : ℝ) * reducedSource1159 x := by
  norm_num [numericRow1159, reducedSource1159, Integer.Sparse.eval, Sparse.eval, nodeValue626, nodeValue628, nodeValue635, nodeValue645, nodeValue911, nodeValue936, nodeValue1027, nodeValue1317, nodeValue1324, nodeValue1327, nodeValue1333, nodeValue1340, nodeValue1388, nodeValue1411, nodeValue1413, nodeValue1420, nodeValue1447, nodeValue2574, nodeValue2602, nodeValue2755, nodeValue3229]
  ring

noncomputable def reducedSource1160 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1514 x + ((1 : ℝ) * Sparse.eval nodeValue1532 x + ((1 : ℝ) * Sparse.eval nodeValue1533 x + ((1 : ℝ) * Sparse.eval nodeValue1535 x + ((2 : ℝ) * Sparse.eval nodeValue1670 x + ((2 : ℝ) * Sparse.eval nodeValue1688 x + ((2 : ℝ) * Sparse.eval nodeValue1689 x + ((2 : ℝ) * Sparse.eval nodeValue1690 x + ((1 : ℝ) * Sparse.eval nodeValue1695 x + ((2 : ℝ) * Sparse.eval nodeValue1720 x + ((2 : ℝ) * Sparse.eval nodeValue1723 x + ((2 : ℝ) * Sparse.eval nodeValue1724 x + ((1 : ℝ) * Sparse.eval nodeValue1748 x + ((1 : ℝ) * Sparse.eval nodeValue1749 x + ((1 : ℝ) * Sparse.eval nodeValue1750 x + ((1 : ℝ) * Sparse.eval nodeValue1751 x + ((1 : ℝ) * Sparse.eval nodeValue1753 x + ((2 : ℝ) * Sparse.eval nodeValue2224 x + ((1 : ℝ) * Sparse.eval nodeValue2287 x + ((1 : ℝ) * Sparse.eval nodeValue2290 x + ((1 : ℝ) * Sparse.eval nodeValue2291 x + 0))))))))))))))))))))

def numericRow1160 : Integer.Sparse Master := [(Sum.inr 1514, 2), (Sum.inr 1532, 1), (Sum.inr 1533, 1), (Sum.inr 1535, 1), (Sum.inr 1670, 2), (Sum.inr 1688, 2), (Sum.inr 1689, 2), (Sum.inr 1690, 2), (Sum.inr 1695, 1), (Sum.inr 1720, 2), (Sum.inr 1723, 2), (Sum.inr 1724, 2), (Sum.inr 1748, 1), (Sum.inr 1749, 1), (Sum.inr 1750, 1), (Sum.inr 1751, 1), (Sum.inr 2224, 2), (Sum.inr 2287, 1), (Sum.inr 2290, 1)]

theorem reindexCheck1160 : Integer.Sparse.reindex keyMap MixedData.row1160 = numericRow1160 := by decide +kernel

theorem numericCheck1160 (x : Master → ℝ) : Integer.Sparse.eval numericRow1160 x =
    (1 : ℝ) * reducedSource1160 x := by
  norm_num [numericRow1160, reducedSource1160, Integer.Sparse.eval, Sparse.eval, nodeValue1514, nodeValue1532, nodeValue1533, nodeValue1535, nodeValue1670, nodeValue1688, nodeValue1689, nodeValue1690, nodeValue1695, nodeValue1720, nodeValue1723, nodeValue1724, nodeValue1748, nodeValue1749, nodeValue1750, nodeValue1751, nodeValue1753, nodeValue2224, nodeValue2287, nodeValue2290, nodeValue2291]

noncomputable def reducedSource1161 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue581 x + ((1 : ℝ) * Sparse.eval nodeValue587 x + ((1 : ℝ) * Sparse.eval nodeValue589 x + ((1 : ℝ) * Sparse.eval nodeValue611 x + ((1 : ℝ) * Sparse.eval nodeValue1046 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow1161 : Integer.Sparse Master := [(Sum.inr 581, 2), (Sum.inr 587, 1), (Sum.inr 589, 1), (Sum.inr 611, 1), (Sum.inr 1046, 1), (Sum.inr 4083, -1)]

theorem reindexCheck1161 : Integer.Sparse.reindex keyMap MixedData.row1161 = numericRow1161 := by decide +kernel

theorem numericCheck1161 (x : Master → ℝ) : Integer.Sparse.eval numericRow1161 x =
    (1 : ℝ) * reducedSource1161 x := by
  norm_num [numericRow1161, reducedSource1161, Integer.Sparse.eval, Sparse.eval, nodeValue581, nodeValue587, nodeValue589, nodeValue611, nodeValue1046, nodeValue4083]

noncomputable def reducedSource1162 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue611 x + ((2 : ℝ) * Sparse.eval nodeValue930 x + ((2 : ℝ) * Sparse.eval nodeValue1046 x + ((1 : ℝ) * Sparse.eval nodeValue1086 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

def numericRow1162 : Integer.Sparse Master := [(Sum.inr 611, 1), (Sum.inr 930, 2), (Sum.inr 1046, 2), (Sum.inr 4083, -1)]

theorem reindexCheck1162 : Integer.Sparse.reindex keyMap MixedData.row1162 = numericRow1162 := by decide +kernel

theorem numericCheck1162 (x : Master → ℝ) : Integer.Sparse.eval numericRow1162 x =
    (1 : ℝ) * reducedSource1162 x := by
  norm_num [numericRow1162, reducedSource1162, Integer.Sparse.eval, Sparse.eval, nodeValue611, nodeValue930, nodeValue1046, nodeValue1086, nodeValue4083]

noncomputable def reducedSource1163 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue945 x + ((1 : ℝ) * Sparse.eval nodeValue951 x + ((1 : ℝ) * Sparse.eval nodeValue953 x + ((1 : ℝ) * Sparse.eval nodeValue1046 x + ((1 : ℝ) * Sparse.eval nodeValue2112 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow1163 : Integer.Sparse Master := [(Sum.inr 945, 2), (Sum.inr 951, 1), (Sum.inr 953, 1), (Sum.inr 1046, 1), (Sum.inr 2112, 1), (Sum.inr 4083, -1)]

theorem reindexCheck1163 : Integer.Sparse.reindex keyMap MixedData.row1163 = numericRow1163 := by decide +kernel

theorem numericCheck1163 (x : Master → ℝ) : Integer.Sparse.eval numericRow1163 x =
    (1 : ℝ) * reducedSource1163 x := by
  norm_num [numericRow1163, reducedSource1163, Integer.Sparse.eval, Sparse.eval, nodeValue945, nodeValue951, nodeValue953, nodeValue1046, nodeValue2112, nodeValue4083]

noncomputable def reducedSource1164 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue905 x + ((1 : ℝ) * Sparse.eval nodeValue911 x + ((1 : ℝ) * Sparse.eval nodeValue913 x + ((1 : ℝ) * Sparse.eval nodeValue930 x + ((1 : ℝ) * Sparse.eval nodeValue1046 x + ((1 : ℝ) * Sparse.eval nodeValue2025 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

def numericRow1164 : Integer.Sparse Master := [(Sum.inr 905, 1), (Sum.inr 911, 1), (Sum.inr 913, 1), (Sum.inr 930, 1), (Sum.inr 1046, 1), (Sum.inr 2025, 1), (Sum.inr 4083, -1)]

theorem reindexCheck1164 : Integer.Sparse.reindex keyMap MixedData.row1164 = numericRow1164 := by decide +kernel

theorem numericCheck1164 (x : Master → ℝ) : Integer.Sparse.eval numericRow1164 x =
    (1 : ℝ) * reducedSource1164 x := by
  norm_num [numericRow1164, reducedSource1164, Integer.Sparse.eval, Sparse.eval, nodeValue905, nodeValue911, nodeValue913, nodeValue930, nodeValue1046, nodeValue2025, nodeValue4083]

noncomputable def reducedSource1165 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4105 x + ((1 : ℝ) * Sparse.eval nodeValue4108 x + ((1 : ℝ) * Sparse.eval nodeValue4111 x + ((1 : ℝ) * Sparse.eval nodeValue4128 x + ((2 : ℝ) * Sparse.eval nodeValue4290 x + ((2 : ℝ) * Sparse.eval nodeValue4293 x + ((2 : ℝ) * Sparse.eval nodeValue4296 x + ((2 : ℝ) * Sparse.eval nodeValue4309 x + ((2 : ℝ) * Sparse.eval nodeValue4352 x + ((1 : ℝ) * Sparse.eval nodeValue4356 x + ((1 : ℝ) * Sparse.eval nodeValue4361 x + ((2 : ℝ) * Sparse.eval nodeValue4461 x + ((2 : ℝ) * Sparse.eval nodeValue4463 x + ((1 : ℝ) * Sparse.eval nodeValue4466 x + ((1 : ℝ) * Sparse.eval nodeValue4468 x + ((1 : ℝ) * Sparse.eval nodeValue4503 x + ((1 : ℝ) * Sparse.eval nodeValue4507 x + ((2 : ℝ) * Sparse.eval nodeValue5078 x + ((1 : ℝ) * Sparse.eval nodeValue5174 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5296 x + 0))))))))))))))))))))

def numericRow1165 : Integer.Sparse Master := [(Sum.inl 0, 56), (Sum.inl 5, 20), (Sum.inl 6, 5), (Sum.inl 2, 35), (Sum.inl 3, -80), (Sum.inl 1, -90), (Sum.inr 542, -4320), (Sum.inr 545, -2160), (Sum.inr 548, -2160), (Sum.inr 559, -2160), (Sum.inr 681, -4320), (Sum.inr 683, -2160), (Sum.inr 685, -2160), (Sum.inr 690, -2160), (Sum.inr 868, -4320), (Sum.inr 871, -4320), (Sum.inr 874, -4320), (Sum.inr 887, -4320), (Sum.inr 930, -4320), (Sum.inr 934, -2160), (Sum.inr 939, -2160), (Sum.inr 1044, -4320), (Sum.inr 1046, -4320), (Sum.inr 1049, -2160), (Sum.inr 1051, -2160), (Sum.inr 1087, -2160), (Sum.inr 1091, -2160), (Sum.inr 1566, -4320), (Sum.inr 1568, -4320), (Sum.inr 1570, -4320), (Sum.inr 1573, -4320), (Sum.inr 1690, -4320), (Sum.inr 1692, -2160), (Sum.inr 1694, -2160), (Sum.inr 1737, -4320), (Sum.inr 1738, -2160), (Sum.inr 1739, -2160), (Sum.inr 1750, -4320), (Sum.inr 1752, -2160), (Sum.inr 1756, -2160), (Sum.inr 2485, -4320), (Sum.inr 3481, -4320), (Sum.inr 3615, -2160), (Sum.inr 3632, -2160), (Sum.inr 3634, -2160)]

theorem reindexCheck1165 : Integer.Sparse.reindex keyMap MixedData.row1165 = numericRow1165 := by decide +kernel

theorem numericCheck1165 (x : Master → ℝ) : Integer.Sparse.eval numericRow1165 x =
    (8640 : ℝ) * reducedSource1165 x := by
  norm_num [numericRow1165, reducedSource1165, Integer.Sparse.eval, Sparse.eval, nodeValue4105, nodeValue4108, nodeValue4111, nodeValue4128, nodeValue4290, nodeValue4293, nodeValue4296, nodeValue4309, nodeValue4352, nodeValue4356, nodeValue4361, nodeValue4461, nodeValue4463, nodeValue4466, nodeValue4468, nodeValue4503, nodeValue4507, nodeValue5078, nodeValue5174, nodeValue5294, nodeValue5296]
  ring

noncomputable def reducedSource1166 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4253 x + ((1 : ℝ) * Sparse.eval nodeValue4269 x + ((1 : ℝ) * Sparse.eval nodeValue4270 x + ((1 : ℝ) * Sparse.eval nodeValue4276 x + ((2 : ℝ) * Sparse.eval nodeValue4391 x + ((2 : ℝ) * Sparse.eval nodeValue4401 x + ((2 : ℝ) * Sparse.eval nodeValue4402 x + ((2 : ℝ) * Sparse.eval nodeValue4410 x + ((2 : ℝ) * Sparse.eval nodeValue4440 x + ((2 : ℝ) * Sparse.eval nodeValue4442 x + ((1 : ℝ) * Sparse.eval nodeValue4460 x + ((2 : ℝ) * Sparse.eval nodeValue4463 x + ((1 : ℝ) * Sparse.eval nodeValue4464 x + ((1 : ℝ) * Sparse.eval nodeValue4476 x + ((1 : ℝ) * Sparse.eval nodeValue4478 x + ((1 : ℝ) * Sparse.eval nodeValue4505 x + ((1 : ℝ) * Sparse.eval nodeValue4507 x + ((2 : ℝ) * Sparse.eval nodeValue4591 x + ((1 : ℝ) * Sparse.eval nodeValue4605 x + ((1 : ℝ) * Sparse.eval nodeValue4608 x + ((1 : ℝ) * Sparse.eval nodeValue4625 x + 0))))))))))))))))))))

def numericRow1166 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 5, -4), (Sum.inl 6, -1), (Sum.inl 1, 4), (Sum.inr 787, -288), (Sum.inr 813, -144), (Sum.inr 828, -144), (Sum.inr 847, -288), (Sum.inr 853, -144), (Sum.inr 857, -144), (Sum.inr 982, -288), (Sum.inr 1043, -144), (Sum.inr 1046, -288), (Sum.inr 1091, -144), (Sum.inr 1239, -144), (Sum.inr 1242, -144), (Sum.inr 1617, -288), (Sum.inr 1725, -144), (Sum.inr 1750, -288), (Sum.inr 1756, -144), (Sum.inr 2226, -144), (Sum.inr 3300, -144), (Sum.inr 3310, -144), (Sum.inr 4391, 1152), (Sum.inr 4402, 1152), (Sum.inr 4410, 1152), (Sum.inr 4440, 1152), (Sum.inr 4442, 1152), (Sum.inr 4464, 576), (Sum.inr 4476, 576), (Sum.inr 4478, 576), (Sum.inr 4591, 1152)]

theorem reindexCheck1166 : Integer.Sparse.reindex keyMap MixedData.row1166 = numericRow1166 := by decide +kernel

theorem numericCheck1166 (x : Master → ℝ) : Integer.Sparse.eval numericRow1166 x =
    (576 : ℝ) * reducedSource1166 x := by
  norm_num [numericRow1166, reducedSource1166, Integer.Sparse.eval, Sparse.eval, nodeValue4253, nodeValue4269, nodeValue4270, nodeValue4276, nodeValue4391, nodeValue4401, nodeValue4402, nodeValue4410, nodeValue4440, nodeValue4442, nodeValue4460, nodeValue4463, nodeValue4464, nodeValue4476, nodeValue4478, nodeValue4505, nodeValue4507, nodeValue4591, nodeValue4605, nodeValue4608, nodeValue4625]
  ring

noncomputable def reducedSource1167 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue787 x + ((1 : ℝ) * Sparse.eval nodeValue812 x + ((1 : ℝ) * Sparse.eval nodeValue813 x + ((1 : ℝ) * Sparse.eval nodeValue828 x + ((2 : ℝ) * Sparse.eval nodeValue972 x + ((2 : ℝ) * Sparse.eval nodeValue982 x + ((2 : ℝ) * Sparse.eval nodeValue983 x + ((2 : ℝ) * Sparse.eval nodeValue991 x + ((2 : ℝ) * Sparse.eval nodeValue1022 x + ((2 : ℝ) * Sparse.eval nodeValue1024 x + ((1 : ℝ) * Sparse.eval nodeValue1043 x + ((2 : ℝ) * Sparse.eval nodeValue1046 x + ((1 : ℝ) * Sparse.eval nodeValue1047 x + ((1 : ℝ) * Sparse.eval nodeValue1059 x + ((1 : ℝ) * Sparse.eval nodeValue1061 x + ((1 : ℝ) * Sparse.eval nodeValue1089 x + ((1 : ℝ) * Sparse.eval nodeValue1091 x + ((2 : ℝ) * Sparse.eval nodeValue1217 x + ((1 : ℝ) * Sparse.eval nodeValue1269 x + ((1 : ℝ) * Sparse.eval nodeValue1271 x + ((1 : ℝ) * Sparse.eval nodeValue1307 x + 0))))))))))))))))))))

def numericRow1167 : Integer.Sparse Master := [(Sum.inl 0, -88), (Sum.inl 6, 110), (Sum.inl 2, 100), (Sum.inl 35, 160), (Sum.inl 1, 30), (Sum.inr 787, 8640), (Sum.inr 813, 4320), (Sum.inr 828, 4320), (Sum.inr 972, 8640), (Sum.inr 982, 8640), (Sum.inr 983, 8640), (Sum.inr 991, 8640), (Sum.inr 1022, 8640), (Sum.inr 1024, 8640), (Sum.inr 1043, 4320), (Sum.inr 1046, 8640), (Sum.inr 1047, 4320), (Sum.inr 1059, 4320), (Sum.inr 1061, 4320), (Sum.inr 1091, 4320), (Sum.inr 1217, 8640)]

theorem reindexCheck1167 : Integer.Sparse.reindex keyMap MixedData.row1167 = numericRow1167 := by decide +kernel

theorem numericCheck1167 (x : Master → ℝ) : Integer.Sparse.eval numericRow1167 x =
    (4320 : ℝ) * reducedSource1167 x := by
  norm_num [numericRow1167, reducedSource1167, Integer.Sparse.eval, Sparse.eval, nodeValue787, nodeValue812, nodeValue813, nodeValue828, nodeValue972, nodeValue982, nodeValue983, nodeValue991, nodeValue1022, nodeValue1024, nodeValue1043, nodeValue1046, nodeValue1047, nodeValue1059, nodeValue1061, nodeValue1089, nodeValue1091, nodeValue1217, nodeValue1269, nodeValue1271, nodeValue1307]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
