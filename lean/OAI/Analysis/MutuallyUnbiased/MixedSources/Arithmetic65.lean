import OAI.Analysis.MutuallyUnbiased.MixedData.Source8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values9
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1040 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue621 x + ((3 : ℝ) * Sparse.eval nodeValue940 x + ((1 : ℝ) * Sparse.eval nodeValue1092 x + ((1 : ℝ) * Sparse.eval nodeValue1094 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

def numericRow1040 : Integer.Sparse Master := [(Sum.inr 621, 1), (Sum.inr 940, 3), (Sum.inr 1092, 1), (Sum.inr 1094, 1), (Sum.inr 4085, -1)]

theorem reindexCheck1040 : Integer.Sparse.reindex keyMap MixedData.row1040 = numericRow1040 := by decide +kernel

theorem numericCheck1040 (x : Master → ℝ) : Integer.Sparse.eval numericRow1040 x =
    (1 : ℝ) * reducedSource1040 x := by
  norm_num [numericRow1040, reducedSource1040, Integer.Sparse.eval, Sparse.eval, nodeValue621, nodeValue940, nodeValue1092, nodeValue1094, nodeValue4085]

noncomputable def reducedSource1041 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1093 x + ((1 : ℝ) * Sparse.eval nodeValue1747 x + ((3 : ℝ) * Sparse.eval nodeValue2064 x + ((1 : ℝ) * Sparse.eval nodeValue2289 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0))))

def numericRow1041 : Integer.Sparse Master := [(Sum.inr 1093, 1), (Sum.inr 1747, 1), (Sum.inr 2064, 3), (Sum.inr 2289, 1), (Sum.inr 4070, -1)]

theorem reindexCheck1041 : Integer.Sparse.reindex keyMap MixedData.row1041 = numericRow1041 := by decide +kernel

theorem numericCheck1041 (x : Master → ℝ) : Integer.Sparse.eval numericRow1041 x =
    (1 : ℝ) * reducedSource1041 x := by
  norm_num [numericRow1041, reducedSource1041, Integer.Sparse.eval, Sparse.eval, nodeValue1093, nodeValue1747, nodeValue2064, nodeValue2289, nodeValue4070]

noncomputable def reducedSource1042 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1745 x + ((1 : ℝ) * Sparse.eval nodeValue1747 x + ((1 : ℝ) * Sparse.eval nodeValue1756 x + ((1 : ℝ) * Sparse.eval nodeValue2289 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0))))

def numericRow1042 : Integer.Sparse Master := [(Sum.inr 1745, 3), (Sum.inr 1747, 1), (Sum.inr 1756, 1), (Sum.inr 2289, 1), (Sum.inr 4070, -1)]

theorem reindexCheck1042 : Integer.Sparse.reindex keyMap MixedData.row1042 = numericRow1042 := by decide +kernel

theorem numericCheck1042 (x : Master → ℝ) : Integer.Sparse.eval numericRow1042 x =
    (1 : ℝ) * reducedSource1042 x := by
  norm_num [numericRow1042, reducedSource1042, Integer.Sparse.eval, Sparse.eval, nodeValue1745, nodeValue1747, nodeValue1756, nodeValue2289, nodeValue4070]

noncomputable def reducedSource1043 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue860 x + ((3 : ℝ) * Sparse.eval nodeValue1628 x + ((1 : ℝ) * Sparse.eval nodeValue1747 x + ((1 : ℝ) * Sparse.eval nodeValue1756 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0))))

def numericRow1043 : Integer.Sparse Master := [(Sum.inr 860, 1), (Sum.inr 1628, 3), (Sum.inr 1747, 1), (Sum.inr 1756, 1), (Sum.inr 4070, -1)]

theorem reindexCheck1043 : Integer.Sparse.reindex keyMap MixedData.row1043 = numericRow1043 := by decide +kernel

theorem numericCheck1043 (x : Master → ℝ) : Integer.Sparse.eval numericRow1043 x =
    (1 : ℝ) * reducedSource1043 x := by
  norm_num [numericRow1043, reducedSource1043, Integer.Sparse.eval, Sparse.eval, nodeValue860, nodeValue1628, nodeValue1747, nodeValue1756, nodeValue4070]

noncomputable def reducedSource1044 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue612 x + ((2 : ℝ) * Sparse.eval nodeValue931 x + ((1 : ℝ) * Sparse.eval nodeValue1047 x + ((1 : ℝ) * Sparse.eval nodeValue1061 x + ((1 : ℝ) * Sparse.eval nodeValue1087 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1044 : Integer.Sparse Master := [(Sum.inr 612, 1), (Sum.inr 931, 2), (Sum.inr 1047, 1), (Sum.inr 1061, 1), (Sum.inr 1087, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1044 : Integer.Sparse.reindex keyMap MixedData.row1044 = numericRow1044 := by decide +kernel

theorem numericCheck1044 (x : Master → ℝ) : Integer.Sparse.eval numericRow1044 x =
    (1 : ℝ) * reducedSource1044 x := by
  norm_num [numericRow1044, reducedSource1044, Integer.Sparse.eval, Sparse.eval, nodeValue612, nodeValue931, nodeValue1047, nodeValue1061, nodeValue1087, nodeValue4084]

noncomputable def reducedSource1045 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue590 x + ((2 : ℝ) * Sparse.eval nodeValue914 x + ((1 : ℝ) * Sparse.eval nodeValue954 x + ((1 : ℝ) * Sparse.eval nodeValue1047 x + ((1 : ℝ) * Sparse.eval nodeValue1049 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1045 : Integer.Sparse Master := [(Sum.inr 590, 1), (Sum.inr 914, 2), (Sum.inr 954, 1), (Sum.inr 1047, 1), (Sum.inr 1049, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1045 : Integer.Sparse.reindex keyMap MixedData.row1045 = numericRow1045 := by decide +kernel

theorem numericCheck1045 (x : Master → ℝ) : Integer.Sparse.eval numericRow1045 x =
    (1 : ℝ) * reducedSource1045 x := by
  norm_num [numericRow1045, reducedSource1045, Integer.Sparse.eval, Sparse.eval, nodeValue590, nodeValue914, nodeValue954, nodeValue1047, nodeValue1049, nodeValue4084]

noncomputable def reducedSource1046 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue951 x + ((2 : ℝ) * Sparse.eval nodeValue1336 x + ((1 : ℝ) * Sparse.eval nodeValue1348 x + ((1 : ℝ) * Sparse.eval nodeValue1408 x + ((1 : ℝ) * Sparse.eval nodeValue2112 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow1046 : Integer.Sparse Master := [(Sum.inr 951, 1), (Sum.inr 1336, 2), (Sum.inr 1348, 1), (Sum.inr 1408, 1), (Sum.inr 2112, 1), (Sum.inr 4083, -1)]

theorem reindexCheck1046 : Integer.Sparse.reindex keyMap MixedData.row1046 = numericRow1046 := by decide +kernel

theorem numericCheck1046 (x : Master → ℝ) : Integer.Sparse.eval numericRow1046 x =
    (1 : ℝ) * reducedSource1046 x := by
  norm_num [numericRow1046, reducedSource1046, Integer.Sparse.eval, Sparse.eval, nodeValue951, nodeValue1336, nodeValue1348, nodeValue1408, nodeValue2112, nodeValue4083]

noncomputable def reducedSource1047 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1072 x + ((1 : ℝ) * Sparse.eval nodeValue1745 x + ((2 : ℝ) * Sparse.eval nodeValue2045 x + ((1 : ℝ) * Sparse.eval nodeValue2226 x + ((1 : ℝ) * Sparse.eval nodeValue2289 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

def numericRow1047 : Integer.Sparse Master := [(Sum.inr 1072, 1), (Sum.inr 1745, 1), (Sum.inr 2045, 2), (Sum.inr 2226, 1), (Sum.inr 2289, 1), (Sum.inr 4070, -1)]

theorem reindexCheck1047 : Integer.Sparse.reindex keyMap MixedData.row1047 = numericRow1047 := by decide +kernel

theorem numericCheck1047 (x : Master → ℝ) : Integer.Sparse.eval numericRow1047 x =
    (1 : ℝ) * reducedSource1047 x := by
  norm_num [numericRow1047, reducedSource1047, Integer.Sparse.eval, Sparse.eval, nodeValue1072, nodeValue1745, nodeValue2045, nodeValue2226, nodeValue2289, nodeValue4070]

noncomputable def reducedSource1048 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1744 x + ((1 : ℝ) * Sparse.eval nodeValue1745 x + ((1 : ℝ) * Sparse.eval nodeValue1746 x + ((1 : ℝ) * Sparse.eval nodeValue1750 x + ((1 : ℝ) * Sparse.eval nodeValue2226 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

def numericRow1048 : Integer.Sparse Master := [(Sum.inr 1744, 2), (Sum.inr 1745, 1), (Sum.inr 1746, 1), (Sum.inr 1750, 1), (Sum.inr 2226, 1), (Sum.inr 4070, -1)]

theorem reindexCheck1048 : Integer.Sparse.reindex keyMap MixedData.row1048 = numericRow1048 := by decide +kernel

theorem numericCheck1048 (x : Master → ℝ) : Integer.Sparse.eval numericRow1048 x =
    (1 : ℝ) * reducedSource1048 x := by
  norm_num [numericRow1048, reducedSource1048, Integer.Sparse.eval, Sparse.eval, nodeValue1744, nodeValue1745, nodeValue1746, nodeValue1750, nodeValue2226, nodeValue4070]

noncomputable def reducedSource1049 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue853 x + ((2 : ℝ) * Sparse.eval nodeValue1619 x + ((1 : ℝ) * Sparse.eval nodeValue1745 x + ((1 : ℝ) * Sparse.eval nodeValue1750 x + ((1 : ℝ) * Sparse.eval nodeValue1756 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

def numericRow1049 : Integer.Sparse Master := [(Sum.inr 853, 1), (Sum.inr 1619, 2), (Sum.inr 1745, 1), (Sum.inr 1750, 1), (Sum.inr 1756, 1), (Sum.inr 4070, -1)]

theorem reindexCheck1049 : Integer.Sparse.reindex keyMap MixedData.row1049 = numericRow1049 := by decide +kernel

theorem numericCheck1049 (x : Master → ℝ) : Integer.Sparse.eval numericRow1049 x =
    (1 : ℝ) * reducedSource1049 x := by
  norm_num [numericRow1049, reducedSource1049, Integer.Sparse.eval, Sparse.eval, nodeValue853, nodeValue1619, nodeValue1745, nodeValue1750, nodeValue1756, nodeValue4070]

noncomputable def reducedSource1050 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue606 x + ((2 : ℝ) * Sparse.eval nodeValue925 x + ((1 : ℝ) * Sparse.eval nodeValue1059 x + ((1 : ℝ) * Sparse.eval nodeValue1083 x + ((1 : ℝ) * Sparse.eval nodeValue1091 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1050 : Integer.Sparse Master := [(Sum.inr 606, 1), (Sum.inr 925, 2), (Sum.inr 1059, 1), (Sum.inr 1083, 1), (Sum.inr 1091, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1050 : Integer.Sparse.reindex keyMap MixedData.row1050 = numericRow1050 := by decide +kernel

theorem numericCheck1050 (x : Master → ℝ) : Integer.Sparse.eval numericRow1050 x =
    (1 : ℝ) * reducedSource1050 x := by
  norm_num [numericRow1050, reducedSource1050, Integer.Sparse.eval, Sparse.eval, nodeValue606, nodeValue925, nodeValue1059, nodeValue1083, nodeValue1091, nodeValue4084]

noncomputable def reducedSource1051 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1142 x + ((2 : ℝ) * Sparse.eval nodeValue1317 x + ((1 : ℝ) * Sparse.eval nodeValue1324 x + ((1 : ℝ) * Sparse.eval nodeValue1372 x + ((1 : ℝ) * Sparse.eval nodeValue2519 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow1051 : Integer.Sparse Master := [(Sum.inr 1142, 1), (Sum.inr 1317, 2), (Sum.inr 1324, 1), (Sum.inr 1372, 1), (Sum.inr 2519, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1051 : Integer.Sparse.reindex keyMap MixedData.row1051 = numericRow1051 := by decide +kernel

theorem numericCheck1051 (x : Master → ℝ) : Integer.Sparse.eval numericRow1051 x =
    (1 : ℝ) * reducedSource1051 x := by
  norm_num [numericRow1051, reducedSource1051, Integer.Sparse.eval, Sparse.eval, nodeValue1142, nodeValue1317, nodeValue1324, nodeValue1372, nodeValue2519, nodeValue4092]

noncomputable def reducedSource1052 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1729 x + ((1 : ℝ) * Sparse.eval nodeValue1952 x + ((2 : ℝ) * Sparse.eval nodeValue3242 x + ((1 : ℝ) * Sparse.eval nodeValue3247 x + ((1 : ℝ) * Sparse.eval nodeValue3300 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

def numericRow1052 : Integer.Sparse Master := [(Sum.inr 1729, 1), (Sum.inr 1952, 1), (Sum.inr 3242, 2), (Sum.inr 3247, 1), (Sum.inr 3300, 1), (Sum.inr 4070, -1)]

theorem reindexCheck1052 : Integer.Sparse.reindex keyMap MixedData.row1052 = numericRow1052 := by decide +kernel

theorem numericCheck1052 (x : Master → ℝ) : Integer.Sparse.eval numericRow1052 x =
    (1 : ℝ) * reducedSource1052 x := by
  norm_num [numericRow1052, reducedSource1052, Integer.Sparse.eval, Sparse.eval, nodeValue1729, nodeValue1952, nodeValue3242, nodeValue3247, nodeValue3300, nodeValue4070]

noncomputable def reducedSource1053 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue808 x + ((1 : ℝ) * Sparse.eval nodeValue814 x + ((1 : ℝ) * Sparse.eval nodeValue815 x + ((1 : ℝ) * Sparse.eval nodeValue857 x + ((1 : ℝ) * Sparse.eval nodeValue1729 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

def numericRow1053 : Integer.Sparse Master := [(Sum.inr 808, 2), (Sum.inr 814, 1), (Sum.inr 815, 1), (Sum.inr 857, 1), (Sum.inr 1729, 1), (Sum.inr 4070, -1)]

theorem reindexCheck1053 : Integer.Sparse.reindex keyMap MixedData.row1053 = numericRow1053 := by decide +kernel

theorem numericCheck1053 (x : Master → ℝ) : Integer.Sparse.eval numericRow1053 x =
    (1 : ℝ) * reducedSource1053 x := by
  norm_num [numericRow1053, reducedSource1053, Integer.Sparse.eval, Sparse.eval, nodeValue808, nodeValue814, nodeValue815, nodeValue857, nodeValue1729, nodeValue4070]

noncomputable def reducedSource1054 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1723 x + ((1 : ℝ) * Sparse.eval nodeValue1725 x + ((1 : ℝ) * Sparse.eval nodeValue1729 x + ((1 : ℝ) * Sparse.eval nodeValue1750 x + ((1 : ℝ) * Sparse.eval nodeValue3300 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

def numericRow1054 : Integer.Sparse Master := [(Sum.inr 1723, 2), (Sum.inr 1725, 1), (Sum.inr 1729, 1), (Sum.inr 1750, 1), (Sum.inr 3300, 1), (Sum.inr 4070, -1)]

theorem reindexCheck1054 : Integer.Sparse.reindex keyMap MixedData.row1054 = numericRow1054 := by decide +kernel

theorem numericCheck1054 (x : Master → ℝ) : Integer.Sparse.eval numericRow1054 x =
    (1 : ℝ) * reducedSource1054 x := by
  norm_num [numericRow1054, reducedSource1054, Integer.Sparse.eval, Sparse.eval, nodeValue1723, nodeValue1725, nodeValue1729, nodeValue1750, nodeValue3300, nodeValue4070]

noncomputable def reducedSource1055 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue857 x + ((2 : ℝ) * Sparse.eval nodeValue1624 x + ((1 : ℝ) * Sparse.eval nodeValue1729 x + ((1 : ℝ) * Sparse.eval nodeValue1746 x + ((1 : ℝ) * Sparse.eval nodeValue1750 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

def numericRow1055 : Integer.Sparse Master := [(Sum.inr 857, 1), (Sum.inr 1624, 2), (Sum.inr 1729, 1), (Sum.inr 1746, 1), (Sum.inr 1750, 1), (Sum.inr 4070, -1)]

theorem reindexCheck1055 : Integer.Sparse.reindex keyMap MixedData.row1055 = numericRow1055 := by decide +kernel

theorem numericCheck1055 (x : Master → ℝ) : Integer.Sparse.eval numericRow1055 x =
    (1 : ℝ) * reducedSource1055 x := by
  norm_num [numericRow1055, reducedSource1055, Integer.Sparse.eval, Sparse.eval, nodeValue857, nodeValue1624, nodeValue1729, nodeValue1746, nodeValue1750, nodeValue4070]

end MUB6.Certificate.MixedSourceBridge

end OAI
