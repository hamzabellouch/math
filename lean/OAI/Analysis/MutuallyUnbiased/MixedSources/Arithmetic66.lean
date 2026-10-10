import OAI.Analysis.MutuallyUnbiased.MixedData.Source8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values9
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1056 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue815 x + ((2 : ℝ) * Sparse.eval nodeValue1604 x + ((1 : ℝ) * Sparse.eval nodeValue1652 x + ((1 : ℝ) * Sparse.eval nodeValue1725 x + ((1 : ℝ) * Sparse.eval nodeValue1729 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

def numericRow1056 : Integer.Sparse Master := [(Sum.inr 815, 1), (Sum.inr 1604, 2), (Sum.inr 1652, 1), (Sum.inr 1725, 1), (Sum.inr 1729, 1), (Sum.inr 4070, -1)]

theorem reindexCheck1056 : Integer.Sparse.reindex keyMap MixedData.row1056 = numericRow1056 := by decide +kernel

theorem numericCheck1056 (x : Master → ℝ) : Integer.Sparse.eval numericRow1056 x =
    (1 : ℝ) * reducedSource1056 x := by
  norm_num [numericRow1056, reducedSource1056, Integer.Sparse.eval, Sparse.eval, nodeValue815, nodeValue1604, nodeValue1652, nodeValue1725, nodeValue1729, nodeValue4070]

noncomputable def reducedSource1057 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue936 x + ((2 : ℝ) * Sparse.eval nodeValue1315 x + ((1 : ℝ) * Sparse.eval nodeValue1323 x + ((1 : ℝ) * Sparse.eval nodeValue1369 x + ((1 : ℝ) * Sparse.eval nodeValue2062 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1057 : Integer.Sparse Master := [(Sum.inr 936, 1), (Sum.inr 1315, 2), (Sum.inr 1323, 1), (Sum.inr 1369, 1), (Sum.inr 2062, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1057 : Integer.Sparse.reindex keyMap MixedData.row1057 = numericRow1057 := by decide +kernel

theorem numericCheck1057 (x : Master → ℝ) : Integer.Sparse.eval numericRow1057 x =
    (1 : ℝ) * reducedSource1057 x := by
  norm_num [numericRow1057, reducedSource1057, Integer.Sparse.eval, Sparse.eval, nodeValue936, nodeValue1315, nodeValue1323, nodeValue1369, nodeValue2062, nodeValue4084]

noncomputable def reducedSource1058 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1011 x + ((1 : ℝ) * Sparse.eval nodeValue1746 x + ((1 : ℝ) * Sparse.eval nodeValue1952 x + ((2 : ℝ) * Sparse.eval nodeValue2005 x + ((1 : ℝ) * Sparse.eval nodeValue2226 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

def numericRow1058 : Integer.Sparse Master := [(Sum.inr 1011, 1), (Sum.inr 1746, 1), (Sum.inr 1952, 1), (Sum.inr 2005, 2), (Sum.inr 2226, 1), (Sum.inr 4070, -1)]

theorem reindexCheck1058 : Integer.Sparse.reindex keyMap MixedData.row1058 = numericRow1058 := by decide +kernel

theorem numericCheck1058 (x : Master → ℝ) : Integer.Sparse.eval numericRow1058 x =
    (1 : ℝ) * reducedSource1058 x := by
  norm_num [numericRow1058, reducedSource1058, Integer.Sparse.eval, Sparse.eval, nodeValue1011, nodeValue1746, nodeValue1952, nodeValue2005, nodeValue2226, nodeValue4070]

noncomputable def reducedSource1059 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue581 x + ((1 : ℝ) * Sparse.eval nodeValue905 x + ((1 : ℝ) * Sparse.eval nodeValue945 x + ((1 : ℝ) * Sparse.eval nodeValue1022 x + ((1 : ℝ) * Sparse.eval nodeValue1041 x + ((1 : ℝ) * Sparse.eval nodeValue1046 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

def numericRow1059 : Integer.Sparse Master := [(Sum.inr 581, 1), (Sum.inr 905, 1), (Sum.inr 945, 1), (Sum.inr 1022, 1), (Sum.inr 1041, 1), (Sum.inr 1046, 1), (Sum.inr 4083, -1)]

theorem reindexCheck1059 : Integer.Sparse.reindex keyMap MixedData.row1059 = numericRow1059 := by decide +kernel

theorem numericCheck1059 (x : Master → ℝ) : Integer.Sparse.eval numericRow1059 x =
    (1 : ℝ) * reducedSource1059 x := by
  norm_num [numericRow1059, reducedSource1059, Integer.Sparse.eval, Sparse.eval, nodeValue581, nodeValue905, nodeValue945, nodeValue1022, nodeValue1041, nodeValue1046, nodeValue4083]

noncomputable def reducedSource1060 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1118 x + ((1 : ℝ) * Sparse.eval nodeValue1327 x + ((1 : ℝ) * Sparse.eval nodeValue1333 x + ((1 : ℝ) * Sparse.eval nodeValue1337 x + ((1 : ℝ) * Sparse.eval nodeValue1388 x + ((1 : ℝ) * Sparse.eval nodeValue2485 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow1060 : Integer.Sparse Master := [(Sum.inr 1118, 1), (Sum.inr 1327, 1), (Sum.inr 1333, 1), (Sum.inr 1337, 1), (Sum.inr 1388, 1), (Sum.inr 2485, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1060 : Integer.Sparse.reindex keyMap MixedData.row1060 = numericRow1060 := by decide +kernel

theorem numericCheck1060 (x : Master → ℝ) : Integer.Sparse.eval numericRow1060 x =
    (1 : ℝ) * reducedSource1060 x := by
  norm_num [numericRow1060, reducedSource1060, Integer.Sparse.eval, Sparse.eval, nodeValue1118, nodeValue1327, nodeValue1333, nodeValue1337, nodeValue1388, nodeValue2485, nodeValue4091]

noncomputable def reducedSource1061 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1723 x + ((1 : ℝ) * Sparse.eval nodeValue1942 x + ((1 : ℝ) * Sparse.eval nodeValue3279 x + ((1 : ℝ) * Sparse.eval nodeValue3283 x + ((2 : ℝ) * Sparse.eval nodeValue3300 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

def numericRow1061 : Integer.Sparse Master := [(Sum.inr 1723, 1), (Sum.inr 1942, 1), (Sum.inr 3279, 1), (Sum.inr 3283, 1), (Sum.inr 3300, 2), (Sum.inr 4070, -1)]

theorem reindexCheck1061 : Integer.Sparse.reindex keyMap MixedData.row1061 = numericRow1061 := by decide +kernel

theorem numericCheck1061 (x : Master → ℝ) : Integer.Sparse.eval numericRow1061 x =
    (1 : ℝ) * reducedSource1061 x := by
  norm_num [numericRow1061, reducedSource1061, Integer.Sparse.eval, Sparse.eval, nodeValue1723, nodeValue1942, nodeValue3279, nodeValue3283, nodeValue3300, nodeValue4070]

noncomputable def reducedSource1062 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue847 x + ((1 : ℝ) * Sparse.eval nodeValue1613 x + ((1 : ℝ) * Sparse.eval nodeValue1723 x + ((1 : ℝ) * Sparse.eval nodeValue1744 x + ((2 : ℝ) * Sparse.eval nodeValue1750 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

def numericRow1062 : Integer.Sparse Master := [(Sum.inr 847, 1), (Sum.inr 1613, 1), (Sum.inr 1723, 1), (Sum.inr 1744, 1), (Sum.inr 1750, 2), (Sum.inr 4070, -1)]

theorem reindexCheck1062 : Integer.Sparse.reindex keyMap MixedData.row1062 = numericRow1062 := by decide +kernel

theorem numericCheck1062 (x : Master → ℝ) : Integer.Sparse.eval numericRow1062 x =
    (1 : ℝ) * reducedSource1062 x := by
  norm_num [numericRow1062, reducedSource1062, Integer.Sparse.eval, Sparse.eval, nodeValue847, nodeValue1613, nodeValue1723, nodeValue1744, nodeValue1750, nodeValue4070]

noncomputable def reducedSource1063 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue804 x + ((1 : ℝ) * Sparse.eval nodeValue1596 x + ((1 : ℝ) * Sparse.eval nodeValue1643 x + ((1 : ℝ) * Sparse.eval nodeValue1723 x + ((2 : ℝ) * Sparse.eval nodeValue1725 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

def numericRow1063 : Integer.Sparse Master := [(Sum.inr 804, 1), (Sum.inr 1643, 1), (Sum.inr 1723, 1), (Sum.inr 1725, 2), (Sum.inr 4070, -1)]

theorem reindexCheck1063 : Integer.Sparse.reindex keyMap MixedData.row1063 = numericRow1063 := by decide +kernel

theorem numericCheck1063 (x : Master → ℝ) : Integer.Sparse.eval numericRow1063 x =
    (1 : ℝ) * reducedSource1063 x := by
  norm_num [numericRow1063, reducedSource1063, Integer.Sparse.eval, Sparse.eval, nodeValue804, nodeValue1596, nodeValue1643, nodeValue1723, nodeValue1725, nodeValue4070]

noncomputable def reducedSource1064 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue585 x + ((1 : ℝ) * Sparse.eval nodeValue909 x + ((1 : ℝ) * Sparse.eval nodeValue949 x + ((2 : ℝ) * Sparse.eval nodeValue1024 x + ((1 : ℝ) * Sparse.eval nodeValue1044 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow1064 : Integer.Sparse Master := [(Sum.inr 585, 1), (Sum.inr 909, 1), (Sum.inr 949, 1), (Sum.inr 1024, 2), (Sum.inr 1044, 1), (Sum.inr 4083, -1)]

theorem reindexCheck1064 : Integer.Sparse.reindex keyMap MixedData.row1064 = numericRow1064 := by decide +kernel

theorem numericCheck1064 (x : Master → ℝ) : Integer.Sparse.eval numericRow1064 x =
    (1 : ℝ) * reducedSource1064 x := by
  norm_num [numericRow1064, reducedSource1064, Integer.Sparse.eval, Sparse.eval, nodeValue585, nodeValue909, nodeValue949, nodeValue1024, nodeValue1044, nodeValue4083]

noncomputable def reducedSource1065 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue911 x + ((1 : ℝ) * Sparse.eval nodeValue1326 x + ((1 : ℝ) * Sparse.eval nodeValue1332 x + ((1 : ℝ) * Sparse.eval nodeValue1336 x + ((1 : ℝ) * Sparse.eval nodeValue1385 x + ((1 : ℝ) * Sparse.eval nodeValue2025 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

def numericRow1065 : Integer.Sparse Master := [(Sum.inr 911, 1), (Sum.inr 1326, 1), (Sum.inr 1332, 1), (Sum.inr 1336, 1), (Sum.inr 1385, 1), (Sum.inr 2025, 1), (Sum.inr 4083, -1)]

theorem reindexCheck1065 : Integer.Sparse.reindex keyMap MixedData.row1065 = numericRow1065 := by decide +kernel

theorem numericCheck1065 (x : Master → ℝ) : Integer.Sparse.eval numericRow1065 x =
    (1 : ℝ) * reducedSource1065 x := by
  norm_num [numericRow1065, reducedSource1065, Integer.Sparse.eval, Sparse.eval, nodeValue911, nodeValue1326, nodeValue1332, nodeValue1336, nodeValue1385, nodeValue2025, nodeValue4083]

noncomputable def reducedSource1066 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue997 x + ((1 : ℝ) * Sparse.eval nodeValue1744 x + ((1 : ℝ) * Sparse.eval nodeValue1942 x + ((1 : ℝ) * Sparse.eval nodeValue1995 x + ((2 : ℝ) * Sparse.eval nodeValue2226 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

def numericRow1066 : Integer.Sparse Master := [(Sum.inr 997, 1), (Sum.inr 1744, 1), (Sum.inr 1942, 1), (Sum.inr 1995, 1), (Sum.inr 2226, 2), (Sum.inr 4070, -1)]

theorem reindexCheck1066 : Integer.Sparse.reindex keyMap MixedData.row1066 = numericRow1066 := by decide +kernel

theorem numericCheck1066 (x : Master → ℝ) : Integer.Sparse.eval numericRow1066 x =
    (1 : ℝ) * reducedSource1066 x := by
  norm_num [numericRow1066, reducedSource1066, Integer.Sparse.eval, Sparse.eval, nodeValue997, nodeValue1744, nodeValue1942, nodeValue1995, nodeValue2226, nodeValue4070]

noncomputable def reducedSource1067 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1355 x + ((1 : ℝ) * Sparse.eval nodeValue1902 x + ((1 : ℝ) * Sparse.eval nodeValue1915 x + ((1 : ℝ) * Sparse.eval nodeValue1926 x + ((1 : ℝ) * Sparse.eval nodeValue2197 x + ((1 : ℝ) * Sparse.eval nodeValue3024 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

def numericRow1067 : Integer.Sparse Master := [(Sum.inr 1355, 1), (Sum.inr 1902, 1), (Sum.inr 1915, 1), (Sum.inr 1926, 1), (Sum.inr 2197, 1), (Sum.inr 3024, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1067 : Integer.Sparse.reindex keyMap MixedData.row1067 = numericRow1067 := by decide +kernel

theorem numericCheck1067 (x : Master → ℝ) : Integer.Sparse.eval numericRow1067 x =
    (1 : ℝ) * reducedSource1067 x := by
  norm_num [numericRow1067, reducedSource1067, Integer.Sparse.eval, Sparse.eval, nodeValue1355, nodeValue1902, nodeValue1915, nodeValue1926, nodeValue2197, nodeValue3024, nodeValue4080]

noncomputable def reducedSource1068 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1132 x + ((1 : ℝ) * Sparse.eval nodeValue1142 x + ((1 : ℝ) * Sparse.eval nodeValue1145 x + ((1 : ℝ) * Sparse.eval nodeValue1243 x + ((1 : ℝ) * Sparse.eval nodeValue2519 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow1068 : Integer.Sparse Master := [(Sum.inr 1132, 2), (Sum.inr 1142, 1), (Sum.inr 1145, 1), (Sum.inr 1243, 1), (Sum.inr 2519, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1068 : Integer.Sparse.reindex keyMap MixedData.row1068 = numericRow1068 := by decide +kernel

theorem numericCheck1068 (x : Master → ℝ) : Integer.Sparse.eval numericRow1068 x =
    (1 : ℝ) * reducedSource1068 x := by
  norm_num [numericRow1068, reducedSource1068, Integer.Sparse.eval, Sparse.eval, nodeValue1132, nodeValue1142, nodeValue1145, nodeValue1243, nodeValue2519, nodeValue4092]

noncomputable def reducedSource1069 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue636 x + ((1 : ℝ) * Sparse.eval nodeValue1145 x + ((2 : ℝ) * Sparse.eval nodeValue1155 x + ((1 : ℝ) * Sparse.eval nodeValue1243 x + ((1 : ℝ) * Sparse.eval nodeValue1246 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow1069 : Integer.Sparse Master := [(Sum.inr 636, 1), (Sum.inr 1145, 1), (Sum.inr 1155, 2), (Sum.inr 1243, 1), (Sum.inr 1246, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1069 : Integer.Sparse.reindex keyMap MixedData.row1069 = numericRow1069 := by decide +kernel

theorem numericCheck1069 (x : Master → ℝ) : Integer.Sparse.eval numericRow1069 x =
    (1 : ℝ) * reducedSource1069 x := by
  norm_num [numericRow1069, reducedSource1069, Integer.Sparse.eval, Sparse.eval, nodeValue636, nodeValue1145, nodeValue1155, nodeValue1243, nodeValue1246, nodeValue4092]

noncomputable def reducedSource1070 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue641 x + ((2 : ℝ) * Sparse.eval nodeValue1159 x + ((1 : ℝ) * Sparse.eval nodeValue1242 x + ((1 : ℝ) * Sparse.eval nodeValue1264 x + ((1 : ℝ) * Sparse.eval nodeValue1294 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow1070 : Integer.Sparse Master := [(Sum.inr 641, 1), (Sum.inr 1159, 2), (Sum.inr 1242, 1), (Sum.inr 1264, 1), (Sum.inr 1294, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1070 : Integer.Sparse.reindex keyMap MixedData.row1070 = numericRow1070 := by decide +kernel

theorem numericCheck1070 (x : Master → ℝ) : Integer.Sparse.eval numericRow1070 x =
    (1 : ℝ) * reducedSource1070 x := by
  norm_num [numericRow1070, reducedSource1070, Integer.Sparse.eval, Sparse.eval, nodeValue641, nodeValue1159, nodeValue1242, nodeValue1264, nodeValue1294, nodeValue4092]

noncomputable def reducedSource1071 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1643 x + ((1 : ℝ) * Sparse.eval nodeValue1647 x + ((1 : ℝ) * Sparse.eval nodeValue1652 x + ((1 : ℝ) * Sparse.eval nodeValue1725 x + ((1 : ℝ) * Sparse.eval nodeValue3302 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

def numericRow1071 : Integer.Sparse Master := [(Sum.inr 1643, 2), (Sum.inr 1647, 1), (Sum.inr 1652, 1), (Sum.inr 1725, 1), (Sum.inr 3302, 1), (Sum.inr 4070, -1)]

theorem reindexCheck1071 : Integer.Sparse.reindex keyMap MixedData.row1071 = numericRow1071 := by decide +kernel

theorem numericCheck1071 (x : Master → ℝ) : Integer.Sparse.eval numericRow1071 x =
    (1 : ℝ) * reducedSource1071 x := by
  norm_num [numericRow1071, reducedSource1071, Integer.Sparse.eval, Sparse.eval, nodeValue1643, nodeValue1647, nodeValue1652, nodeValue1725, nodeValue3302, nodeValue4070]

end MUB6.Certificate.MixedSourceBridge

end OAI
