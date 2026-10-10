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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values9
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1184 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue978 x + ((1 : ℝ) * Sparse.eval nodeValue983 x + ((1 : ℝ) * Sparse.eval nodeValue985 x + ((1 : ℝ) * Sparse.eval nodeValue1005 x + ((1 : ℝ) * Sparse.eval nodeValue1036 x + ((1 : ℝ) * Sparse.eval nodeValue2206 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

def numericRow1184 : Integer.Sparse Master := [(Sum.inr 983, 1), (Sum.inr 985, 1), (Sum.inr 1005, 1), (Sum.inr 1036, 1), (Sum.inr 2206, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1184 : Integer.Sparse.reindex keyMap MixedData.row1184 = numericRow1184 := by decide +kernel

theorem numericCheck1184 (x : Master → ℝ) : Integer.Sparse.eval numericRow1184 x =
    (1 : ℝ) * reducedSource1184 x := by
  norm_num [numericRow1184, reducedSource1184, Integer.Sparse.eval, Sparse.eval, nodeValue978, nodeValue983, nodeValue985, nodeValue1005, nodeValue1036, nodeValue2206, nodeValue4080]

noncomputable def reducedSource1185 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue982 x + ((1 : ℝ) * Sparse.eval nodeValue1914 x + ((1 : ℝ) * Sparse.eval nodeValue1987 x + ((1 : ℝ) * Sparse.eval nodeValue2079 x + ((1 : ℝ) * Sparse.eval nodeValue2193 x + ((1 : ℝ) * Sparse.eval nodeValue2205 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

def numericRow1185 : Integer.Sparse Master := [(Sum.inr 982, 1), (Sum.inr 1987, 1), (Sum.inr 2079, 1), (Sum.inr 2193, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1185 : Integer.Sparse.reindex keyMap MixedData.row1185 = numericRow1185 := by decide +kernel

theorem numericCheck1185 (x : Master → ℝ) : Integer.Sparse.eval numericRow1185 x =
    (1 : ℝ) * reducedSource1185 x := by
  norm_num [numericRow1185, reducedSource1185, Integer.Sparse.eval, Sparse.eval, nodeValue982, nodeValue1914, nodeValue1987, nodeValue2079, nodeValue2193, nodeValue2205, nodeValue4080]

noncomputable def reducedSource1186 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue977 x + ((1 : ℝ) * Sparse.eval nodeValue982 x + ((1 : ℝ) * Sparse.eval nodeValue985 x + ((1 : ℝ) * Sparse.eval nodeValue1004 x + ((1 : ℝ) * Sparse.eval nodeValue1035 x + ((1 : ℝ) * Sparse.eval nodeValue2205 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

def numericRow1186 : Integer.Sparse Master := [(Sum.inr 977, 1), (Sum.inr 982, 1), (Sum.inr 985, 1), (Sum.inr 1035, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1186 : Integer.Sparse.reindex keyMap MixedData.row1186 = numericRow1186 := by decide +kernel

theorem numericCheck1186 (x : Master → ℝ) : Integer.Sparse.eval numericRow1186 x =
    (1 : ℝ) * reducedSource1186 x := by
  norm_num [numericRow1186, reducedSource1186, Integer.Sparse.eval, Sparse.eval, nodeValue977, nodeValue982, nodeValue985, nodeValue1004, nodeValue1035, nodeValue2205, nodeValue4080]

noncomputable def reducedSource1187 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue979 x + ((1 : ℝ) * Sparse.eval nodeValue1911 x + ((1 : ℝ) * Sparse.eval nodeValue1986 x + ((1 : ℝ) * Sparse.eval nodeValue2018 x + ((1 : ℝ) * Sparse.eval nodeValue2203 x + ((1 : ℝ) * Sparse.eval nodeValue2208 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

def numericRow1187 : Integer.Sparse Master := [(Sum.inr 979, 1), (Sum.inr 1986, 1), (Sum.inr 2018, 1), (Sum.inr 2203, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1187 : Integer.Sparse.reindex keyMap MixedData.row1187 = numericRow1187 := by decide +kernel

theorem numericCheck1187 (x : Master → ℝ) : Integer.Sparse.eval numericRow1187 x =
    (1 : ℝ) * reducedSource1187 x := by
  norm_num [numericRow1187, reducedSource1187, Integer.Sparse.eval, Sparse.eval, nodeValue979, nodeValue1911, nodeValue1986, nodeValue2018, nodeValue2203, nodeValue2208, nodeValue4081]

noncomputable def reducedSource1188 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue864 x + ((1 : ℝ) * Sparse.eval nodeValue867 x + ((1 : ℝ) * Sparse.eval nodeValue872 x + ((1 : ℝ) * Sparse.eval nodeValue880 x + ((1 : ℝ) * Sparse.eval nodeValue979 x + ((1 : ℝ) * Sparse.eval nodeValue1911 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

def numericRow1188 : Integer.Sparse Master := [(Sum.inr 864, 1), (Sum.inr 867, 1), (Sum.inr 872, 1), (Sum.inr 979, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1188 : Integer.Sparse.reindex keyMap MixedData.row1188 = numericRow1188 := by decide +kernel

theorem numericCheck1188 (x : Master → ℝ) : Integer.Sparse.eval numericRow1188 x =
    (1 : ℝ) * reducedSource1188 x := by
  norm_num [numericRow1188, reducedSource1188, Integer.Sparse.eval, Sparse.eval, nodeValue864, nodeValue867, nodeValue872, nodeValue880, nodeValue979, nodeValue1911, nodeValue4081]

noncomputable def reducedSource1189 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue976 x + ((1 : ℝ) * Sparse.eval nodeValue979 x + ((1 : ℝ) * Sparse.eval nodeValue984 x + ((1 : ℝ) * Sparse.eval nodeValue999 x + ((1 : ℝ) * Sparse.eval nodeValue1033 x + ((1 : ℝ) * Sparse.eval nodeValue2203 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

def numericRow1189 : Integer.Sparse Master := [(Sum.inr 979, 1), (Sum.inr 984, 1), (Sum.inr 999, 1), (Sum.inr 1033, 1), (Sum.inr 2203, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1189 : Integer.Sparse.reindex keyMap MixedData.row1189 = numericRow1189 := by decide +kernel

theorem numericCheck1189 (x : Master → ℝ) : Integer.Sparse.eval numericRow1189 x =
    (1 : ℝ) * reducedSource1189 x := by
  norm_num [numericRow1189, reducedSource1189, Integer.Sparse.eval, Sparse.eval, nodeValue976, nodeValue979, nodeValue984, nodeValue999, nodeValue1033, nodeValue2203, nodeValue4081]

noncomputable def reducedSource1190 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue698 x + ((1 : ℝ) * Sparse.eval nodeValue701 x + ((1 : ℝ) * Sparse.eval nodeValue706 x + ((1 : ℝ) * Sparse.eval nodeValue714 x + ((1 : ℝ) * Sparse.eval nodeValue809 x + ((1 : ℝ) * Sparse.eval nodeValue1599 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0))))))

def numericRow1190 : Integer.Sparse Master := [(Sum.inr 698, 1), (Sum.inr 701, 1), (Sum.inr 706, 1), (Sum.inr 1599, 1), (Sum.inr 4070, -1)]

theorem reindexCheck1190 : Integer.Sparse.reindex keyMap MixedData.row1190 = numericRow1190 := by decide +kernel

theorem numericCheck1190 (x : Master → ℝ) : Integer.Sparse.eval numericRow1190 x =
    (1 : ℝ) * reducedSource1190 x := by
  norm_num [numericRow1190, reducedSource1190, Integer.Sparse.eval, Sparse.eval, nodeValue698, nodeValue701, nodeValue706, nodeValue714, nodeValue809, nodeValue1599, nodeValue4070]

noncomputable def reducedSource1191 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4178 x + ((1 : ℝ) * Sparse.eval nodeValue4189 x + ((1 : ℝ) * Sparse.eval nodeValue4192 x + ((6 : ℝ) * Sparse.eval nodeValue4347 x + ((3 : ℝ) * Sparse.eval nodeValue4358 x + ((3 : ℝ) * Sparse.eval nodeValue4361 x + ((3 : ℝ) * Sparse.eval nodeValue4476 x + ((1 : ℝ) * Sparse.eval nodeValue4481 x + ((3 : ℝ) * Sparse.eval nodeValue4499 x + ((1 : ℝ) * Sparse.eval nodeValue4511 x + ((3 : ℝ) * Sparse.eval nodeValue4843 x + ((1 : ℝ) * Sparse.eval nodeValue4899 x + ((1 : ℝ) * Sparse.eval nodeValue4901 x + 0))))))))))))

def numericRow1191 : Integer.Sparse Master := [(Sum.inr 620, -1), (Sum.inr 939, -3), (Sum.inr 1083, -3), (Sum.inr 1539, -1), (Sum.inr 1694, -3), (Sum.inr 1728, -3), (Sum.inr 2062, -3), (Sum.inr 2230, -3), (Sum.inr 2281, -1), (Sum.inr 2294, -1), (Sum.inr 4178, 12), (Sum.inr 4189, 4), (Sum.inr 4347, 24), (Sum.inr 4358, 12), (Sum.inr 4476, 12), (Sum.inr 4481, 4)]

theorem reindexCheck1191 : Integer.Sparse.reindex keyMap MixedData.row1191 = numericRow1191 := by decide +kernel

theorem numericCheck1191 (x : Master → ℝ) : Integer.Sparse.eval numericRow1191 x =
    (4 : ℝ) * reducedSource1191 x := by
  norm_num [numericRow1191, reducedSource1191, Integer.Sparse.eval, Sparse.eval, nodeValue4178, nodeValue4189, nodeValue4192, nodeValue4347, nodeValue4358, nodeValue4361, nodeValue4476, nodeValue4481, nodeValue4499, nodeValue4511, nodeValue4843, nodeValue4899, nodeValue4901]; ring

noncomputable def reducedSource1192 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1520 x + ((1 : ℝ) * Sparse.eval nodeValue1539 x + ((1 : ℝ) * Sparse.eval nodeValue1540 x + ((6 : ℝ) * Sparse.eval nodeValue1676 x + ((3 : ℝ) * Sparse.eval nodeValue1694 x + ((3 : ℝ) * Sparse.eval nodeValue1695 x + ((3 : ℝ) * Sparse.eval nodeValue1728 x + ((3 : ℝ) * Sparse.eval nodeValue1729 x + ((1 : ℝ) * Sparse.eval nodeValue1755 x + ((1 : ℝ) * Sparse.eval nodeValue1757 x + ((3 : ℝ) * Sparse.eval nodeValue2230 x + ((1 : ℝ) * Sparse.eval nodeValue2293 x + ((1 : ℝ) * Sparse.eval nodeValue2294 x + 0))))))))))))

def numericRow1192 : Integer.Sparse Master := [(Sum.inr 1520, 3), (Sum.inr 1539, 1), (Sum.inr 1540, 1), (Sum.inr 1676, 6), (Sum.inr 1694, 3), (Sum.inr 1695, 3), (Sum.inr 1728, 3), (Sum.inr 1729, 3), (Sum.inr 1757, 1), (Sum.inr 2230, 3), (Sum.inr 2294, 1)]

theorem reindexCheck1192 : Integer.Sparse.reindex keyMap MixedData.row1192 = numericRow1192 := by decide +kernel

theorem numericCheck1192 (x : Master → ℝ) : Integer.Sparse.eval numericRow1192 x =
    (1 : ℝ) * reducedSource1192 x := by
  norm_num [numericRow1192, reducedSource1192, Integer.Sparse.eval, Sparse.eval, nodeValue1520, nodeValue1539, nodeValue1540, nodeValue1676, nodeValue1694, nodeValue1695, nodeValue1728, nodeValue1729, nodeValue1755, nodeValue1757, nodeValue2230, nodeValue2293, nodeValue2294]

noncomputable def reducedSource1193 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue925 x + ((1 : ℝ) * Sparse.eval nodeValue936 x + ((1 : ℝ) * Sparse.eval nodeValue939 x + ((1 : ℝ) * Sparse.eval nodeValue1091 x + ((1 : ℝ) * Sparse.eval nodeValue2062 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1193 : Integer.Sparse Master := [(Sum.inr 925, 2), (Sum.inr 936, 1), (Sum.inr 939, 1), (Sum.inr 1091, 1), (Sum.inr 2062, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1193 : Integer.Sparse.reindex keyMap MixedData.row1193 = numericRow1193 := by decide +kernel

theorem numericCheck1193 (x : Master → ℝ) : Integer.Sparse.eval numericRow1193 x =
    (1 : ℝ) * reducedSource1193 x := by
  norm_num [numericRow1193, reducedSource1193, Integer.Sparse.eval, Sparse.eval, nodeValue925, nodeValue936, nodeValue939, nodeValue1091, nodeValue2062, nodeValue4084]

noncomputable def reducedSource1194 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4128 x + ((1 : ℝ) * Sparse.eval nodeValue4134 x + ((1 : ℝ) * Sparse.eval nodeValue4138 x + ((6 : ℝ) * Sparse.eval nodeValue4309 x + ((3 : ℝ) * Sparse.eval nodeValue4315 x + ((3 : ℝ) * Sparse.eval nodeValue4319 x + ((3 : ℝ) * Sparse.eval nodeValue4463 x + ((1 : ℝ) * Sparse.eval nodeValue4468 x + ((3 : ℝ) * Sparse.eval nodeValue4503 x + ((1 : ℝ) * Sparse.eval nodeValue4510 x + ((3 : ℝ) * Sparse.eval nodeValue5109 x + ((1 : ℝ) * Sparse.eval nodeValue5296 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + 0))))))))))))

def numericRow1194 : Integer.Sparse Master := [(Sum.inl 0, 11), (Sum.inl 2, 25), (Sum.inl 3, 80), (Sum.inl 1, 10), (Sum.inr 559, -2160), (Sum.inr 564, -720), (Sum.inr 566, -720), (Sum.inr 690, -2160), (Sum.inr 694, -720), (Sum.inr 695, -720), (Sum.inr 887, -4320), (Sum.inr 893, -2160), (Sum.inr 897, -2160), (Sum.inr 1046, -2160), (Sum.inr 1051, -720), (Sum.inr 1087, -2160), (Sum.inr 1094, -720), (Sum.inr 1573, -4320), (Sum.inr 1577, -2160), (Sum.inr 1578, -2160), (Sum.inr 1739, -2160), (Sum.inr 1741, -720), (Sum.inr 1750, -2160), (Sum.inr 1752, -720), (Sum.inr 2519, -2160), (Sum.inr 3486, -2160), (Sum.inr 3633, -720), (Sum.inr 3634, -720)]

theorem reindexCheck1194 : Integer.Sparse.reindex keyMap MixedData.row1194 = numericRow1194 := by decide +kernel

theorem numericCheck1194 (x : Master → ℝ) : Integer.Sparse.eval numericRow1194 x =
    (2880 : ℝ) * reducedSource1194 x := by
  norm_num [numericRow1194, reducedSource1194, Integer.Sparse.eval, Sparse.eval, nodeValue4128, nodeValue4134, nodeValue4138, nodeValue4309, nodeValue4315, nodeValue4319, nodeValue4463, nodeValue4468, nodeValue4503, nodeValue4510, nodeValue5109, nodeValue5296, nodeValue5310]; ring

noncomputable def reducedSource1195 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4084 x + ((3 : ℝ) * Sparse.eval nodeValue4177 x + ((1 : ℝ) * Sparse.eval nodeValue4187 x + ((1 : ℝ) * Sparse.eval nodeValue4191 x + ((6 : ℝ) * Sparse.eval nodeValue4346 x + ((3 : ℝ) * Sparse.eval nodeValue4356 x + ((3 : ℝ) * Sparse.eval nodeValue4360 x + ((3 : ℝ) * Sparse.eval nodeValue4460 x + ((1 : ℝ) * Sparse.eval nodeValue4468 x + ((3 : ℝ) * Sparse.eval nodeValue4498 x + ((1 : ℝ) * Sparse.eval nodeValue4511 x + ((3 : ℝ) * Sparse.eval nodeValue4841 x + ((1 : ℝ) * Sparse.eval nodeValue4897 x + 0))))))))))))

def numericRow1195 : Integer.Sparse Master := [(Sum.inr 605, -3), (Sum.inr 615, -1), (Sum.inr 619, -1), (Sum.inr 924, -6), (Sum.inr 934, -3), (Sum.inr 938, -3), (Sum.inr 1043, -3), (Sum.inr 1051, -1), (Sum.inr 1518, -3), (Sum.inr 1537, -1), (Sum.inr 1538, -1), (Sum.inr 1674, -6), (Sum.inr 1692, -3), (Sum.inr 1693, -3), (Sum.inr 1725, -3), (Sum.inr 1752, -1), (Sum.inr 4084, 4)]

theorem reindexCheck1195 : Integer.Sparse.reindex keyMap MixedData.row1195 = numericRow1195 := by decide +kernel

theorem numericCheck1195 (x : Master → ℝ) : Integer.Sparse.eval numericRow1195 x =
    (4 : ℝ) * reducedSource1195 x := by
  norm_num [numericRow1195, reducedSource1195, Integer.Sparse.eval, Sparse.eval, nodeValue4084, nodeValue4177, nodeValue4187, nodeValue4191, nodeValue4346, nodeValue4356, nodeValue4360, nodeValue4460, nodeValue4468, nodeValue4498, nodeValue4511, nodeValue4841, nodeValue4897]; ring

noncomputable def reducedSource1196 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1518 x + ((1 : ℝ) * Sparse.eval nodeValue1537 x + ((1 : ℝ) * Sparse.eval nodeValue1538 x + ((6 : ℝ) * Sparse.eval nodeValue1674 x + ((3 : ℝ) * Sparse.eval nodeValue1692 x + ((3 : ℝ) * Sparse.eval nodeValue1693 x + ((3 : ℝ) * Sparse.eval nodeValue1725 x + ((3 : ℝ) * Sparse.eval nodeValue1727 x + ((1 : ℝ) * Sparse.eval nodeValue1752 x + ((1 : ℝ) * Sparse.eval nodeValue1755 x + ((3 : ℝ) * Sparse.eval nodeValue2228 x + ((1 : ℝ) * Sparse.eval nodeValue2292 x + ((1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))))))))

def numericRow1196 : Integer.Sparse Master := [(Sum.inr 1518, 3), (Sum.inr 1537, 1), (Sum.inr 1538, 1), (Sum.inr 1674, 6), (Sum.inr 1692, 3), (Sum.inr 1693, 3), (Sum.inr 1725, 3), (Sum.inr 1752, 1), (Sum.inr 4084, 1)]

theorem reindexCheck1196 : Integer.Sparse.reindex keyMap MixedData.row1196 = numericRow1196 := by decide +kernel

theorem numericCheck1196 (x : Master → ℝ) : Integer.Sparse.eval numericRow1196 x =
    (1 : ℝ) * reducedSource1196 x := by
  norm_num [numericRow1196, reducedSource1196, Integer.Sparse.eval, Sparse.eval, nodeValue1518, nodeValue1537, nodeValue1538, nodeValue1674, nodeValue1692, nodeValue1693, nodeValue1725, nodeValue1727, nodeValue1752, nodeValue1755, nodeValue2228, nodeValue2292, nodeValue4084]

noncomputable def reducedSource1197 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4085 x + ((3 : ℝ) * Sparse.eval nodeValue4174 x + ((1 : ℝ) * Sparse.eval nodeValue4181 x + ((1 : ℝ) * Sparse.eval nodeValue4190 x + ((6 : ℝ) * Sparse.eval nodeValue4343 x + ((3 : ℝ) * Sparse.eval nodeValue4350 x + ((3 : ℝ) * Sparse.eval nodeValue4359 x + ((3 : ℝ) * Sparse.eval nodeValue4496 x + ((3 : ℝ) * Sparse.eval nodeValue4501 x + ((1 : ℝ) * Sparse.eval nodeValue4510 x + ((1 : ℝ) * Sparse.eval nodeValue4512 x + ((3 : ℝ) * Sparse.eval nodeValue4837 x + ((1 : ℝ) * Sparse.eval nodeValue4897 x + 0))))))))))))

def numericRow1197 : Integer.Sparse Master := [(Sum.inr 602, -3), (Sum.inr 609, -1), (Sum.inr 618, -1), (Sum.inr 921, -6), (Sum.inr 928, -3), (Sum.inr 937, -3), (Sum.inr 1080, -3), (Sum.inr 1094, -1), (Sum.inr 1509, -3), (Sum.inr 1521, -1), (Sum.inr 1527, -1), (Sum.inr 1666, -6), (Sum.inr 1677, -3), (Sum.inr 1683, -3), (Sum.inr 1710, -3), (Sum.inr 1741, -1), (Sum.inr 4085, 4)]

theorem reindexCheck1197 : Integer.Sparse.reindex keyMap MixedData.row1197 = numericRow1197 := by decide +kernel

theorem numericCheck1197 (x : Master → ℝ) : Integer.Sparse.eval numericRow1197 x =
    (4 : ℝ) * reducedSource1197 x := by
  norm_num [numericRow1197, reducedSource1197, Integer.Sparse.eval, Sparse.eval, nodeValue4085, nodeValue4174, nodeValue4181, nodeValue4190, nodeValue4343, nodeValue4350, nodeValue4359, nodeValue4496, nodeValue4501, nodeValue4510, nodeValue4512, nodeValue4837, nodeValue4897]; ring

noncomputable def reducedSource1198 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1509 x + ((1 : ℝ) * Sparse.eval nodeValue1521 x + ((1 : ℝ) * Sparse.eval nodeValue1527 x + ((6 : ℝ) * Sparse.eval nodeValue1666 x + ((3 : ℝ) * Sparse.eval nodeValue1677 x + ((3 : ℝ) * Sparse.eval nodeValue1683 x + ((3 : ℝ) * Sparse.eval nodeValue1710 x + ((3 : ℝ) * Sparse.eval nodeValue1730 x + ((1 : ℝ) * Sparse.eval nodeValue1741 x + ((1 : ℝ) * Sparse.eval nodeValue1758 x + ((3 : ℝ) * Sparse.eval nodeValue2208 x + ((1 : ℝ) * Sparse.eval nodeValue2268 x + ((1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))))))))))

def numericRow1198 : Integer.Sparse Master := [(Sum.inr 1509, 3), (Sum.inr 1521, 1), (Sum.inr 1527, 1), (Sum.inr 1666, 6), (Sum.inr 1677, 3), (Sum.inr 1683, 3), (Sum.inr 1710, 3), (Sum.inr 1741, 1), (Sum.inr 4085, 1)]

theorem reindexCheck1198 : Integer.Sparse.reindex keyMap MixedData.row1198 = numericRow1198 := by decide +kernel

theorem numericCheck1198 (x : Master → ℝ) : Integer.Sparse.eval numericRow1198 x =
    (1 : ℝ) * reducedSource1198 x := by
  norm_num [numericRow1198, reducedSource1198, Integer.Sparse.eval, Sparse.eval, nodeValue1509, nodeValue1521, nodeValue1527, nodeValue1666, nodeValue1677, nodeValue1683, nodeValue1710, nodeValue1730, nodeValue1741, nodeValue1758, nodeValue2208, nodeValue2268, nodeValue4085]

noncomputable def reducedSource1199 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue602 x + ((1 : ℝ) * Sparse.eval nodeValue609 x + ((1 : ℝ) * Sparse.eval nodeValue618 x + ((1 : ℝ) * Sparse.eval nodeValue1085 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

def numericRow1199 : Integer.Sparse Master := [(Sum.inr 602, 3), (Sum.inr 609, 1), (Sum.inr 618, 1), (Sum.inr 4085, -1)]

theorem reindexCheck1199 : Integer.Sparse.reindex keyMap MixedData.row1199 = numericRow1199 := by decide +kernel

theorem numericCheck1199 (x : Master → ℝ) : Integer.Sparse.eval numericRow1199 x =
    (1 : ℝ) * reducedSource1199 x := by
  norm_num [numericRow1199, reducedSource1199, Integer.Sparse.eval, Sparse.eval, nodeValue602, nodeValue609, nodeValue618, nodeValue1085, nodeValue4085]

end MUB6.Certificate.MixedSourceBridge

end OAI
