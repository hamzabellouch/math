import OAI.Analysis.MutuallyUnbiased.MixedData.Source8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values9
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1024 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue564 x + ((3 : ℝ) * Sparse.eval nodeValue726 x + ((1 : ℝ) * Sparse.eval nodeValue832 x + ((1 : ℝ) * Sparse.eval nodeValue859 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0))))

def numericRow1024 : Integer.Sparse Master := [(Sum.inr 564, 1), (Sum.inr 726, 3), (Sum.inr 832, 1), (Sum.inr 4071, -1)]

theorem reindexCheck1024 : Integer.Sparse.reindex keyMap MixedData.row1024 = numericRow1024 := by decide +kernel

theorem numericCheck1024 (x : Master → ℝ) : Integer.Sparse.eval numericRow1024 x =
    (1 : ℝ) * reducedSource1024 x := by
  norm_num [numericRow1024, reducedSource1024, Integer.Sparse.eval, Sparse.eval, nodeValue564, nodeValue726, nodeValue832, nodeValue859, nodeValue4071]

noncomputable def reducedSource1025 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue832 x + ((3 : ℝ) * Sparse.eval nodeValue1186 x + ((1 : ℝ) * Sparse.eval nodeValue1289 x + ((1 : ℝ) * Sparse.eval nodeValue1741 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0))))

def numericRow1025 : Integer.Sparse Master := [(Sum.inr 832, 1), (Sum.inr 1186, 3), (Sum.inr 1289, 1), (Sum.inr 1741, 1), (Sum.inr 4071, -1)]

theorem reindexCheck1025 : Integer.Sparse.reindex keyMap MixedData.row1025 = numericRow1025 := by decide +kernel

theorem numericCheck1025 (x : Master → ℝ) : Integer.Sparse.eval numericRow1025 x =
    (1 : ℝ) * reducedSource1025 x := by
  norm_num [numericRow1025, reducedSource1025, Integer.Sparse.eval, Sparse.eval, nodeValue832, nodeValue1186, nodeValue1289, nodeValue1741, nodeValue4071]

noncomputable def reducedSource1026 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue785 x + ((1 : ℝ) * Sparse.eval nodeValue791 x + ((2 : ℝ) * Sparse.eval nodeValue812 x + ((1 : ℝ) * Sparse.eval nodeValue1710 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))

def numericRow1026 : Integer.Sparse Master := [(Sum.inr 785, 2), (Sum.inr 791, 1), (Sum.inr 1710, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1026 : Integer.Sparse.reindex keyMap MixedData.row1026 = numericRow1026 := by decide +kernel

theorem numericCheck1026 (x : Master → ℝ) : Integer.Sparse.eval numericRow1026 x =
    (1 : ℝ) * reducedSource1026 x := by
  norm_num [numericRow1026, reducedSource1026, Integer.Sparse.eval, Sparse.eval, nodeValue785, nodeValue791, nodeValue812, nodeValue1710, nodeValue4069]

noncomputable def reducedSource1027 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue545 x + ((2 : ℝ) * Sparse.eval nodeValue705 x + ((1 : ℝ) * Sparse.eval nodeValue740 x + ((1 : ℝ) * Sparse.eval nodeValue791 x + ((1 : ℝ) * Sparse.eval nodeValue812 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

def numericRow1027 : Integer.Sparse Master := [(Sum.inr 545, 1), (Sum.inr 705, 2), (Sum.inr 740, 1), (Sum.inr 791, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1027 : Integer.Sparse.reindex keyMap MixedData.row1027 = numericRow1027 := by decide +kernel

theorem numericCheck1027 (x : Master → ℝ) : Integer.Sparse.eval numericRow1027 x =
    (1 : ℝ) * reducedSource1027 x := by
  norm_num [numericRow1027, reducedSource1027, Integer.Sparse.eval, Sparse.eval, nodeValue545, nodeValue705, nodeValue740, nodeValue791, nodeValue812, nodeValue4069]

noncomputable def reducedSource1028 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue791 x + ((2 : ℝ) * Sparse.eval nodeValue1199 x + ((2 : ℝ) * Sparse.eval nodeValue1231 x + ((1 : ℝ) * Sparse.eval nodeValue1710 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))

def numericRow1028 : Integer.Sparse Master := [(Sum.inr 791, 1), (Sum.inr 1199, 2), (Sum.inr 1231, 2), (Sum.inr 1710, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1028 : Integer.Sparse.reindex keyMap MixedData.row1028 = numericRow1028 := by decide +kernel

theorem numericCheck1028 (x : Master → ℝ) : Integer.Sparse.eval numericRow1028 x =
    (1 : ℝ) * reducedSource1028 x := by
  norm_num [numericRow1028, reducedSource1028, Integer.Sparse.eval, Sparse.eval, nodeValue791, nodeValue1199, nodeValue1231, nodeValue1710, nodeValue4069]

noncomputable def reducedSource1029 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue979 x + ((1 : ℝ) * Sparse.eval nodeValue986 x + ((1 : ℝ) * Sparse.eval nodeValue1007 x + ((1 : ℝ) * Sparse.eval nodeValue1037 x + ((1 : ℝ) * Sparse.eval nodeValue2208 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0)))))

def numericRow1029 : Integer.Sparse Master := [(Sum.inr 979, 2), (Sum.inr 986, 1), (Sum.inr 1037, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1029 : Integer.Sparse.reindex keyMap MixedData.row1029 = numericRow1029 := by decide +kernel

theorem numericCheck1029 (x : Master → ℝ) : Integer.Sparse.eval numericRow1029 x =
    (1 : ℝ) * reducedSource1029 x := by
  norm_num [numericRow1029, reducedSource1029, Integer.Sparse.eval, Sparse.eval, nodeValue979, nodeValue986, nodeValue1007, nodeValue1037, nodeValue2208, nodeValue4081]

noncomputable def reducedSource1030 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4085 x + ((8 : ℝ) * Sparse.eval nodeValue4181 x + ((1 : ℝ) * Sparse.eval nodeValue4194 x + ((12 : ℝ) * Sparse.eval nodeValue4350 x + ((8 : ℝ) * Sparse.eval nodeValue4501 x + 0))))

def numericRow1030 : Integer.Sparse Master := [(Sum.inr 609, -8), (Sum.inr 622, -1), (Sum.inr 928, -12), (Sum.inr 1521, -8), (Sum.inr 1541, -1), (Sum.inr 1677, -12), (Sum.inr 4085, 4)]

theorem reindexCheck1030 : Integer.Sparse.reindex keyMap MixedData.row1030 = numericRow1030 := by decide +kernel

theorem numericCheck1030 (x : Master → ℝ) : Integer.Sparse.eval numericRow1030 x =
    (4 : ℝ) * reducedSource1030 x := by
  norm_num [numericRow1030, reducedSource1030, Integer.Sparse.eval, Sparse.eval, nodeValue4085, nodeValue4181, nodeValue4194, nodeValue4350, nodeValue4501]
  ring

noncomputable def reducedSource1031 (x : Master → ℝ) : ℝ :=
  (8 : ℝ) * Sparse.eval nodeValue1521 x + ((1 : ℝ) * Sparse.eval nodeValue1541 x + ((12 : ℝ) * Sparse.eval nodeValue1677 x + ((8 : ℝ) * Sparse.eval nodeValue1730 x + ((1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

def numericRow1031 : Integer.Sparse Master := [(Sum.inr 1521, 8), (Sum.inr 1541, 1), (Sum.inr 1677, 12), (Sum.inr 4085, 1)]

theorem reindexCheck1031 : Integer.Sparse.reindex keyMap MixedData.row1031 = numericRow1031 := by decide +kernel

theorem numericCheck1031 (x : Master → ℝ) : Integer.Sparse.eval numericRow1031 x =
    (1 : ℝ) * reducedSource1031 x := by
  norm_num [numericRow1031, reducedSource1031, Integer.Sparse.eval, Sparse.eval, nodeValue1521, nodeValue1541, nodeValue1677, nodeValue1730, nodeValue4085]

noncomputable def reducedSource1032 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue609 x + ((1 : ℝ) * Sparse.eval nodeValue622 x + ((1 : ℝ) * Sparse.eval nodeValue1096 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0)))

def numericRow1032 : Integer.Sparse Master := [(Sum.inr 609, 4), (Sum.inr 622, 1), (Sum.inr 4085, -1)]

theorem reindexCheck1032 : Integer.Sparse.reindex keyMap MixedData.row1032 = numericRow1032 := by decide +kernel

theorem numericCheck1032 (x : Master → ℝ) : Integer.Sparse.eval numericRow1032 x =
    (1 : ℝ) * reducedSource1032 x := by
  norm_num [numericRow1032, reducedSource1032, Integer.Sparse.eval, Sparse.eval, nodeValue609, nodeValue622, nodeValue1096, nodeValue4085]

noncomputable def reducedSource1033 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4072 x + ((8 : ℝ) * Sparse.eval nodeValue4274 x + ((12 : ℝ) * Sparse.eval nodeValue4405 x + ((8 : ℝ) * Sparse.eval nodeValue4468 x + ((1 : ℝ) * Sparse.eval nodeValue4629 x + 0))))

def numericRow1033 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 5, 20), (Sum.inl 6, 5), (Sum.inl 1, 10), (Sum.inr 986, -2160), (Sum.inr 1051, -1440), (Sum.inr 1620, -2160), (Sum.inr 1752, -1440), (Sum.inr 3313, -180), (Sum.inr 4072, 720)]

theorem reindexCheck1033 : Integer.Sparse.reindex keyMap MixedData.row1033 = numericRow1033 := by decide +kernel

theorem numericCheck1033 (x : Master → ℝ) : Integer.Sparse.eval numericRow1033 x =
    (720 : ℝ) * reducedSource1033 x := by
  norm_num [numericRow1033, reducedSource1033, Integer.Sparse.eval, Sparse.eval, nodeValue4072, nodeValue4274, nodeValue4405, nodeValue4468, nodeValue4629]
  ring

noncomputable def reducedSource1034 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4070 x + ((3 : ℝ) * Sparse.eval nodeValue4103 x + ((1 : ℝ) * Sparse.eval nodeValue4112 x + ((1 : ℝ) * Sparse.eval nodeValue4131 x + ((3 : ℝ) * Sparse.eval nodeValue4142 x + ((1 : ℝ) * Sparse.eval nodeValue4168 x + ((6 : ℝ) * Sparse.eval nodeValue4198 x + ((3 : ℝ) * Sparse.eval nodeValue4222 x + ((3 : ℝ) * Sparse.eval nodeValue4235 x + ((3 : ℝ) * Sparse.eval nodeValue4266 x + ((3 : ℝ) * Sparse.eval nodeValue4421 x + ((1 : ℝ) * Sparse.eval nodeValue4493 x + ((1 : ℝ) * Sparse.eval nodeValue4501 x + 0))))))))))))

def numericRow1034 : Integer.Sparse Master := [(Sum.inr 540, -3), (Sum.inr 549, -1), (Sum.inr 570, -3), (Sum.inr 596, -1), (Sum.inr 665, -3), (Sum.inr 686, -1), (Sum.inr 701, -6), (Sum.inr 735, -3), (Sum.inr 750, -6), (Sum.inr 765, -3), (Sum.inr 801, -3), (Sum.inr 845, -1), (Sum.inr 1002, -6), (Sum.inr 1077, -2), (Sum.inr 4070, 4)]

theorem reindexCheck1034 : Integer.Sparse.reindex keyMap MixedData.row1034 = numericRow1034 := by decide +kernel

theorem numericCheck1034 (x : Master → ℝ) : Integer.Sparse.eval numericRow1034 x =
    (4 : ℝ) * reducedSource1034 x := by
  norm_num [numericRow1034, reducedSource1034, Integer.Sparse.eval, Sparse.eval, nodeValue4070, nodeValue4103, nodeValue4112, nodeValue4131, nodeValue4142, nodeValue4168, nodeValue4198, nodeValue4222, nodeValue4235, nodeValue4266, nodeValue4421, nodeValue4493, nodeValue4501]
  ring

noncomputable def reducedSource1035 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue665 x + ((1 : ℝ) * Sparse.eval nodeValue686 x + ((1 : ℝ) * Sparse.eval nodeValue691 x + ((6 : ℝ) * Sparse.eval nodeValue750 x + ((3 : ℝ) * Sparse.eval nodeValue765 x + ((3 : ℝ) * Sparse.eval nodeValue770 x + ((3 : ℝ) * Sparse.eval nodeValue801 x + ((3 : ℝ) * Sparse.eval nodeValue809 x + ((1 : ℝ) * Sparse.eval nodeValue845 x + ((3 : ℝ) * Sparse.eval nodeValue1002 x + ((1 : ℝ) * Sparse.eval nodeValue1077 x + ((1 : ℝ) * Sparse.eval nodeValue1085 x + ((1 : ℝ) * Sparse.eval nodeValue4070 x + 0))))))))))))

def numericRow1035 : Integer.Sparse Master := [(Sum.inr 665, 3), (Sum.inr 686, 1), (Sum.inr 750, 6), (Sum.inr 765, 3), (Sum.inr 801, 3), (Sum.inr 845, 1), (Sum.inr 1002, 3), (Sum.inr 1077, 1), (Sum.inr 4070, 1)]

theorem reindexCheck1035 : Integer.Sparse.reindex keyMap MixedData.row1035 = numericRow1035 := by decide +kernel

theorem numericCheck1035 (x : Master → ℝ) : Integer.Sparse.eval numericRow1035 x =
    (1 : ℝ) * reducedSource1035 x := by
  norm_num [numericRow1035, reducedSource1035, Integer.Sparse.eval, Sparse.eval, nodeValue665, nodeValue686, nodeValue691, nodeValue750, nodeValue765, nodeValue770, nodeValue801, nodeValue809, nodeValue845, nodeValue1002, nodeValue1077, nodeValue1085, nodeValue4070]

noncomputable def reducedSource1036 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue549 x + ((3 : ℝ) * Sparse.eval nodeValue570 x + ((1 : ℝ) * Sparse.eval nodeValue596 x + ((1 : ℝ) * Sparse.eval nodeValue817 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0))))

def numericRow1036 : Integer.Sparse Master := [(Sum.inr 549, 1), (Sum.inr 570, 3), (Sum.inr 596, 1), (Sum.inr 4070, -1)]

theorem reindexCheck1036 : Integer.Sparse.reindex keyMap MixedData.row1036 = numericRow1036 := by decide +kernel

theorem numericCheck1036 (x : Master → ℝ) : Integer.Sparse.eval numericRow1036 x =
    (1 : ℝ) * reducedSource1036 x := by
  norm_num [numericRow1036, reducedSource1036, Integer.Sparse.eval, Sparse.eval, nodeValue549, nodeValue570, nodeValue596, nodeValue817, nodeValue4070]

noncomputable def reducedSource1037 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue540 x + ((2 : ℝ) * Sparse.eval nodeValue701 x + ((1 : ℝ) * Sparse.eval nodeValue735 x + ((1 : ℝ) * Sparse.eval nodeValue809 x + ((1 : ℝ) * Sparse.eval nodeValue817 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

def numericRow1037 : Integer.Sparse Master := [(Sum.inr 540, 1), (Sum.inr 701, 2), (Sum.inr 735, 1), (Sum.inr 4070, -1)]

theorem reindexCheck1037 : Integer.Sparse.reindex keyMap MixedData.row1037 = numericRow1037 := by decide +kernel

theorem numericCheck1037 (x : Master → ℝ) : Integer.Sparse.eval numericRow1037 x =
    (1 : ℝ) * reducedSource1037 x := by
  norm_num [numericRow1037, reducedSource1037, Integer.Sparse.eval, Sparse.eval, nodeValue540, nodeValue701, nodeValue735, nodeValue809, nodeValue817, nodeValue4070]

noncomputable def reducedSource1038 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue596 x + ((3 : ℝ) * Sparse.eval nodeValue735 x + ((1 : ℝ) * Sparse.eval nodeValue817 x + ((1 : ℝ) * Sparse.eval nodeValue1077 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0))))

def numericRow1038 : Integer.Sparse Master := [(Sum.inr 596, 1), (Sum.inr 735, 3), (Sum.inr 1077, 1), (Sum.inr 4070, -1)]

theorem reindexCheck1038 : Integer.Sparse.reindex keyMap MixedData.row1038 = numericRow1038 := by decide +kernel

theorem numericCheck1038 (x : Master → ℝ) : Integer.Sparse.eval numericRow1038 x =
    (1 : ℝ) * reducedSource1038 x := by
  norm_num [numericRow1038, reducedSource1038, Integer.Sparse.eval, Sparse.eval, nodeValue596, nodeValue735, nodeValue817, nodeValue1077, nodeValue4070]

noncomputable def reducedSource1039 (x : Master → ℝ) : ℝ :=
  (8 : ℝ) * Sparse.eval nodeValue4060 x + ((1 : ℝ) * Sparse.eval nodeValue4062 x + ((12 : ℝ) * Sparse.eval nodeValue4066 x + ((8 : ℝ) * Sparse.eval nodeValue4070 x + ((1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

def numericRow1039 : Integer.Sparse Master := [(Sum.inr 4060, 8), (Sum.inr 4062, 1), (Sum.inr 4066, 12), (Sum.inr 4070, 8), (Sum.inr 4085, 1)]

theorem reindexCheck1039 : Integer.Sparse.reindex keyMap MixedData.row1039 = numericRow1039 := by decide +kernel

theorem numericCheck1039 (x : Master → ℝ) : Integer.Sparse.eval numericRow1039 x =
    (1 : ℝ) * reducedSource1039 x := by
  norm_num [numericRow1039, reducedSource1039, Integer.Sparse.eval, Sparse.eval, nodeValue4060, nodeValue4062, nodeValue4066, nodeValue4070, nodeValue4085]

end MUB6.Certificate.MixedSourceBridge

end OAI
