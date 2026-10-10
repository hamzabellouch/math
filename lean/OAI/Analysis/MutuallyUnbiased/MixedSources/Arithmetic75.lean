import OAI.Analysis.MutuallyUnbiased.MixedData.Source9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values9
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1200 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue602 x + ((2 : ℝ) * Sparse.eval nodeValue921 x + ((1 : ℝ) * Sparse.eval nodeValue1080 x + ((2 : ℝ) * Sparse.eval nodeValue1085 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

def numericRow1200 : Integer.Sparse Master := [(Sum.inr 602, 1), (Sum.inr 921, 2), (Sum.inr 1080, 1), (Sum.inr 4085, -1)]

theorem reindexCheck1200 : Integer.Sparse.reindex keyMap MixedData.row1200 = numericRow1200 := by decide +kernel

theorem numericCheck1200 (x : Master → ℝ) : Integer.Sparse.eval numericRow1200 x =
    (1 : ℝ) * reducedSource1200 x := by
  norm_num [numericRow1200, reducedSource1200, Integer.Sparse.eval, Sparse.eval, nodeValue602, nodeValue921, nodeValue1080, nodeValue1085, nodeValue4085]

noncomputable def reducedSource1201 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1010 x + ((1 : ℝ) * Sparse.eval nodeValue1951 x + ((2 : ℝ) * Sparse.eval nodeValue2004 x + ((1 : ℝ) * Sparse.eval nodeValue2222 x + ((1 : ℝ) * Sparse.eval nodeValue2230 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0)))))

def numericRow1201 : Integer.Sparse Master := [(Sum.inr 1010, 1), (Sum.inr 1951, 1), (Sum.inr 2004, 2), (Sum.inr 2222, 1), (Sum.inr 2230, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1201 : Integer.Sparse.reindex keyMap MixedData.row1201 = numericRow1201 := by decide +kernel

theorem numericCheck1201 (x : Master → ℝ) : Integer.Sparse.eval numericRow1201 x =
    (1 : ℝ) * reducedSource1201 x := by
  norm_num [numericRow1201, reducedSource1201, Integer.Sparse.eval, Sparse.eval, nodeValue1010, nodeValue1951, nodeValue2004, nodeValue2222, nodeValue2230, nodeValue4081]

noncomputable def reducedSource1202 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1001 x + ((1 : ℝ) * Sparse.eval nodeValue1010 x + ((1 : ℝ) * Sparse.eval nodeValue1012 x + ((1 : ℝ) * Sparse.eval nodeValue1076 x + ((1 : ℝ) * Sparse.eval nodeValue2230 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0)))))

def numericRow1202 : Integer.Sparse Master := [(Sum.inr 1001, 2), (Sum.inr 1010, 1), (Sum.inr 1012, 1), (Sum.inr 1076, 1), (Sum.inr 2230, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1202 : Integer.Sparse.reindex keyMap MixedData.row1202 = numericRow1202 := by decide +kernel

theorem numericCheck1202 (x : Master → ℝ) : Integer.Sparse.eval numericRow1202 x =
    (1 : ℝ) * reducedSource1202 x := by
  norm_num [numericRow1202, reducedSource1202, Integer.Sparse.eval, Sparse.eval, nodeValue1001, nodeValue1010, nodeValue1012, nodeValue1076, nodeValue2230, nodeValue4081]

noncomputable def reducedSource1203 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1009 x + ((1 : ℝ) * Sparse.eval nodeValue1950 x + ((2 : ℝ) * Sparse.eval nodeValue2003 x + ((1 : ℝ) * Sparse.eval nodeValue2218 x + ((1 : ℝ) * Sparse.eval nodeValue2229 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

def numericRow1203 : Integer.Sparse Master := [(Sum.inr 1009, 1), (Sum.inr 2003, 2), (Sum.inr 2218, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1203 : Integer.Sparse.reindex keyMap MixedData.row1203 = numericRow1203 := by decide +kernel

theorem numericCheck1203 (x : Master → ℝ) : Integer.Sparse.eval numericRow1203 x =
    (1 : ℝ) * reducedSource1203 x := by
  norm_num [numericRow1203, reducedSource1203, Integer.Sparse.eval, Sparse.eval, nodeValue1009, nodeValue1950, nodeValue2003, nodeValue2218, nodeValue2229, nodeValue4082]

noncomputable def reducedSource1204 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1000 x + ((1 : ℝ) * Sparse.eval nodeValue1009 x + ((1 : ℝ) * Sparse.eval nodeValue1013 x + ((1 : ℝ) * Sparse.eval nodeValue1075 x + ((1 : ℝ) * Sparse.eval nodeValue2229 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

def numericRow1204 : Integer.Sparse Master := [(Sum.inr 1000, 2), (Sum.inr 1009, 1), (Sum.inr 1075, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1204 : Integer.Sparse.reindex keyMap MixedData.row1204 = numericRow1204 := by decide +kernel

theorem numericCheck1204 (x : Master → ℝ) : Integer.Sparse.eval numericRow1204 x =
    (1 : ℝ) * reducedSource1204 x := by
  norm_num [numericRow1204, reducedSource1204, Integer.Sparse.eval, Sparse.eval, nodeValue1000, nodeValue1009, nodeValue1013, nodeValue1075, nodeValue2229, nodeValue4082]

noncomputable def reducedSource1205 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4081 x + ((2 : ℝ) * Sparse.eval nodeValue4140 x + ((1 : ℝ) * Sparse.eval nodeValue4146 x + ((1 : ℝ) * Sparse.eval nodeValue4147 x + ((1 : ℝ) * Sparse.eval nodeValue4166 x + ((2 : ℝ) * Sparse.eval nodeValue4289 x + ((2 : ℝ) * Sparse.eval nodeValue4302 x + ((1 : ℝ) * Sparse.eval nodeValue4312 x + ((1 : ℝ) * Sparse.eval nodeValue4317 x + ((2 : ℝ) * Sparse.eval nodeValue4320 x + ((2 : ℝ) * Sparse.eval nodeValue4324 x + ((2 : ℝ) * Sparse.eval nodeValue4338 x + ((2 : ℝ) * Sparse.eval nodeValue4398 x + ((1 : ℝ) * Sparse.eval nodeValue4405 x + ((2 : ℝ) * Sparse.eval nodeValue4418 x + ((1 : ℝ) * Sparse.eval nodeValue4431 x + ((1 : ℝ) * Sparse.eval nodeValue4454 x + ((1 : ℝ) * Sparse.eval nodeValue4490 x + ((2 : ℝ) * Sparse.eval nodeValue4738 x + ((1 : ℝ) * Sparse.eval nodeValue4837 x + ((1 : ℝ) * Sparse.eval nodeValue4841 x + 0))))))))))))))))))))

def numericRow1205 : Integer.Sparse Master := [(Sum.inr 568, -2), (Sum.inr 574, -1), (Sum.inr 575, -1), (Sum.inr 594, -1), (Sum.inr 867, -2), (Sum.inr 898, -2), (Sum.inr 902, -2), (Sum.inr 916, -2), (Sum.inr 979, -2), (Sum.inr 986, -1), (Sum.inr 999, -2), (Sum.inr 1012, -1), (Sum.inr 1037, -1), (Sum.inr 1074, -1), (Sum.inr 1489, -2), (Sum.inr 1494, -1), (Sum.inr 1495, -1), (Sum.inr 1499, -1), (Sum.inr 1555, -2), (Sum.inr 1586, -2), (Sum.inr 1590, -2), (Sum.inr 1599, -2), (Sum.inr 1602, -2), (Sum.inr 1620, -1), (Sum.inr 1627, -1), (Sum.inr 1633, -2), (Sum.inr 1647, -1), (Sum.inr 1650, -1), (Sum.inr 4081, 4)]

theorem reindexCheck1205 : Integer.Sparse.reindex keyMap MixedData.row1205 = numericRow1205 := by decide +kernel

theorem numericCheck1205 (x : Master → ℝ) : Integer.Sparse.eval numericRow1205 x =
    (4 : ℝ) * reducedSource1205 x := by
  norm_num [numericRow1205, reducedSource1205, Integer.Sparse.eval, Sparse.eval, nodeValue4081, nodeValue4140, nodeValue4146, nodeValue4147, nodeValue4166, nodeValue4289, nodeValue4302, nodeValue4312, nodeValue4317, nodeValue4320, nodeValue4324, nodeValue4338, nodeValue4398, nodeValue4405, nodeValue4418, nodeValue4431, nodeValue4454, nodeValue4490, nodeValue4738, nodeValue4837, nodeValue4841]
  ring

noncomputable def reducedSource1206 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1489 x + ((1 : ℝ) * Sparse.eval nodeValue1494 x + ((1 : ℝ) * Sparse.eval nodeValue1495 x + ((1 : ℝ) * Sparse.eval nodeValue1499 x + ((2 : ℝ) * Sparse.eval nodeValue1555 x + ((2 : ℝ) * Sparse.eval nodeValue1557 x + ((1 : ℝ) * Sparse.eval nodeValue1574 x + ((1 : ℝ) * Sparse.eval nodeValue1576 x + ((2 : ℝ) * Sparse.eval nodeValue1586 x + ((2 : ℝ) * Sparse.eval nodeValue1590 x + ((2 : ℝ) * Sparse.eval nodeValue1599 x + ((2 : ℝ) * Sparse.eval nodeValue1602 x + ((1 : ℝ) * Sparse.eval nodeValue1620 x + ((1 : ℝ) * Sparse.eval nodeValue1627 x + ((2 : ℝ) * Sparse.eval nodeValue1633 x + ((1 : ℝ) * Sparse.eval nodeValue1647 x + ((1 : ℝ) * Sparse.eval nodeValue1650 x + ((2 : ℝ) * Sparse.eval nodeValue1911 x + ((1 : ℝ) * Sparse.eval nodeValue2056 x + ((1 : ℝ) * Sparse.eval nodeValue2060 x + ((1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))))))))))))))))

def numericRow1206 : Integer.Sparse Master := [(Sum.inr 1489, 2), (Sum.inr 1494, 1), (Sum.inr 1495, 1), (Sum.inr 1499, 1), (Sum.inr 1555, 2), (Sum.inr 1586, 2), (Sum.inr 1590, 2), (Sum.inr 1599, 2), (Sum.inr 1602, 2), (Sum.inr 1620, 1), (Sum.inr 1627, 1), (Sum.inr 1633, 2), (Sum.inr 1647, 1), (Sum.inr 1650, 1), (Sum.inr 4081, 1)]

theorem reindexCheck1206 : Integer.Sparse.reindex keyMap MixedData.row1206 = numericRow1206 := by decide +kernel

theorem numericCheck1206 (x : Master → ℝ) : Integer.Sparse.eval numericRow1206 x =
    (1 : ℝ) * reducedSource1206 x := by
  norm_num [numericRow1206, reducedSource1206, Integer.Sparse.eval, Sparse.eval, nodeValue1489, nodeValue1494, nodeValue1495, nodeValue1499, nodeValue1555, nodeValue1557, nodeValue1574, nodeValue1576, nodeValue1586, nodeValue1590, nodeValue1599, nodeValue1602, nodeValue1620, nodeValue1627, nodeValue1633, nodeValue1647, nodeValue1650, nodeValue1911, nodeValue2056, nodeValue2060, nodeValue4081]

noncomputable def reducedSource1207 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue867 x + ((1 : ℝ) * Sparse.eval nodeValue898 x + ((1 : ℝ) * Sparse.eval nodeValue902 x + ((1 : ℝ) * Sparse.eval nodeValue916 x + ((1 : ℝ) * Sparse.eval nodeValue1007 x + ((1 : ℝ) * Sparse.eval nodeValue1911 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

def numericRow1207 : Integer.Sparse Master := [(Sum.inr 867, 1), (Sum.inr 898, 1), (Sum.inr 902, 1), (Sum.inr 916, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1207 : Integer.Sparse.reindex keyMap MixedData.row1207 = numericRow1207 := by decide +kernel

theorem numericCheck1207 (x : Master → ℝ) : Integer.Sparse.eval numericRow1207 x =
    (1 : ℝ) * reducedSource1207 x := by
  norm_num [numericRow1207, reducedSource1207, Integer.Sparse.eval, Sparse.eval, nodeValue867, nodeValue898, nodeValue902, nodeValue916, nodeValue1007, nodeValue1911, nodeValue4081]

noncomputable def reducedSource1208 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue793 x + ((1 : ℝ) * Sparse.eval nodeValue795 x + ((1 : ℝ) * Sparse.eval nodeValue796 x + ((1 : ℝ) * Sparse.eval nodeValue811 x + ((1 : ℝ) * Sparse.eval nodeValue827 x + ((1 : ℝ) * Sparse.eval nodeValue1715 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0))))))

def numericRow1208 : Integer.Sparse Master := [(Sum.inr 793, 1), (Sum.inr 795, 1), (Sum.inr 796, 1), (Sum.inr 811, 1), (Sum.inr 827, 1), (Sum.inr 1715, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1208 : Integer.Sparse.reindex keyMap MixedData.row1208 = numericRow1208 := by decide +kernel

theorem numericCheck1208 (x : Master → ℝ) : Integer.Sparse.eval numericRow1208 x =
    (1 : ℝ) * reducedSource1208 x := by
  norm_num [numericRow1208, reducedSource1208, Integer.Sparse.eval, Sparse.eval, nodeValue793, nodeValue795, nodeValue796, nodeValue811, nodeValue827, nodeValue1715, nodeValue4069]

noncomputable def reducedSource1209 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue825 x + ((1 : ℝ) * Sparse.eval nodeValue829 x + ((1 : ℝ) * Sparse.eval nodeValue830 x + ((1 : ℝ) * Sparse.eval nodeValue858 x + ((1 : ℝ) * Sparse.eval nodeValue1740 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0)))))

def numericRow1209 : Integer.Sparse Master := [(Sum.inr 825, 2), (Sum.inr 829, 1), (Sum.inr 830, 1), (Sum.inr 858, 1), (Sum.inr 1740, 1), (Sum.inr 4071, -1)]

theorem reindexCheck1209 : Integer.Sparse.reindex keyMap MixedData.row1209 = numericRow1209 := by decide +kernel

theorem numericCheck1209 (x : Master → ℝ) : Integer.Sparse.eval numericRow1209 x =
    (1 : ℝ) * reducedSource1209 x := by
  norm_num [numericRow1209, reducedSource1209, Integer.Sparse.eval, Sparse.eval, nodeValue825, nodeValue829, nodeValue830, nodeValue858, nodeValue1740, nodeValue4071]

noncomputable def reducedSource1210 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue828 x + ((2 : ℝ) * Sparse.eval nodeValue1610 x + ((1 : ℝ) * Sparse.eval nodeValue1659 x + ((1 : ℝ) * Sparse.eval nodeValue1716 x + ((1 : ℝ) * Sparse.eval nodeValue1739 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

def numericRow1210 : Integer.Sparse Master := [(Sum.inr 828, 1), (Sum.inr 1610, 2), (Sum.inr 1659, 1), (Sum.inr 1716, 1), (Sum.inr 1739, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1210 : Integer.Sparse.reindex keyMap MixedData.row1210 = numericRow1210 := by decide +kernel

theorem numericCheck1210 (x : Master → ℝ) : Integer.Sparse.eval numericRow1210 x =
    (1 : ℝ) * reducedSource1210 x := by
  norm_num [numericRow1210, reducedSource1210, Integer.Sparse.eval, Sparse.eval, nodeValue828, nodeValue1610, nodeValue1659, nodeValue1716, nodeValue1739, nodeValue4069]

noncomputable def reducedSource1211 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue824 x + ((1 : ℝ) * Sparse.eval nodeValue828 x + ((1 : ℝ) * Sparse.eval nodeValue831 x + ((1 : ℝ) * Sparse.eval nodeValue856 x + ((1 : ℝ) * Sparse.eval nodeValue1739 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

def numericRow1211 : Integer.Sparse Master := [(Sum.inr 824, 2), (Sum.inr 828, 1), (Sum.inr 831, 1), (Sum.inr 1739, 1), (Sum.inr 4069, -1)]

theorem reindexCheck1211 : Integer.Sparse.reindex keyMap MixedData.row1211 = numericRow1211 := by decide +kernel

theorem numericCheck1211 (x : Master → ℝ) : Integer.Sparse.eval numericRow1211 x =
    (1 : ℝ) * reducedSource1211 x := by
  norm_num [numericRow1211, reducedSource1211, Integer.Sparse.eval, Sparse.eval, nodeValue824, nodeValue828, nodeValue831, nodeValue856, nodeValue1739, nodeValue4069]

noncomputable def reducedSource1212 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue826 x + ((2 : ℝ) * Sparse.eval nodeValue1608 x + ((1 : ℝ) * Sparse.eval nodeValue1657 x + ((1 : ℝ) * Sparse.eval nodeValue1738 x + ((1 : ℝ) * Sparse.eval nodeValue1741 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0)))))

def numericRow1212 : Integer.Sparse Master := [(Sum.inr 826, 1), (Sum.inr 1608, 2), (Sum.inr 1657, 1), (Sum.inr 1738, 1), (Sum.inr 1741, 1), (Sum.inr 4071, -1)]

theorem reindexCheck1212 : Integer.Sparse.reindex keyMap MixedData.row1212 = numericRow1212 := by decide +kernel

theorem numericCheck1212 (x : Master → ℝ) : Integer.Sparse.eval numericRow1212 x =
    (1 : ℝ) * reducedSource1212 x := by
  norm_num [numericRow1212, reducedSource1212, Integer.Sparse.eval, Sparse.eval, nodeValue826, nodeValue1608, nodeValue1657, nodeValue1738, nodeValue1741, nodeValue4071]

noncomputable def reducedSource1213 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue555 x + ((2 : ℝ) * Sparse.eval nodeValue715 x + ((1 : ℝ) * Sparse.eval nodeValue826 x + ((1 : ℝ) * Sparse.eval nodeValue852 x + ((1 : ℝ) * Sparse.eval nodeValue859 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0)))))

def numericRow1213 : Integer.Sparse Master := [(Sum.inr 555, 1), (Sum.inr 715, 2), (Sum.inr 826, 1), (Sum.inr 4071, -1)]

theorem reindexCheck1213 : Integer.Sparse.reindex keyMap MixedData.row1213 = numericRow1213 := by decide +kernel

theorem numericCheck1213 (x : Master → ℝ) : Integer.Sparse.eval numericRow1213 x =
    (1 : ℝ) * reducedSource1213 x := by
  norm_num [numericRow1213, reducedSource1213, Integer.Sparse.eval, Sparse.eval, nodeValue555, nodeValue715, nodeValue826, nodeValue852, nodeValue859, nodeValue4071]

noncomputable def reducedSource1214 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue823 x + ((1 : ℝ) * Sparse.eval nodeValue826 x + ((1 : ℝ) * Sparse.eval nodeValue830 x + ((1 : ℝ) * Sparse.eval nodeValue852 x + ((1 : ℝ) * Sparse.eval nodeValue1738 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0)))))

def numericRow1214 : Integer.Sparse Master := [(Sum.inr 823, 2), (Sum.inr 826, 1), (Sum.inr 830, 1), (Sum.inr 1738, 1), (Sum.inr 4071, -1)]

theorem reindexCheck1214 : Integer.Sparse.reindex keyMap MixedData.row1214 = numericRow1214 := by decide +kernel

theorem numericCheck1214 (x : Master → ℝ) : Integer.Sparse.eval numericRow1214 x =
    (1 : ℝ) * reducedSource1214 x := by
  norm_num [numericRow1214, reducedSource1214, Integer.Sparse.eval, Sparse.eval, nodeValue823, nodeValue826, nodeValue830, nodeValue852, nodeValue1738, nodeValue4071]

noncomputable def reducedSource1215 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue546 x + ((2 : ℝ) * Sparse.eval nodeValue706 x + ((1 : ℝ) * Sparse.eval nodeValue741 x + ((1 : ℝ) * Sparse.eval nodeValue809 x + ((1 : ℝ) * Sparse.eval nodeValue815 x + ((-1 : ℝ) * Sparse.eval nodeValue4070 x + 0)))))

def numericRow1215 : Integer.Sparse Master := [(Sum.inr 546, 1), (Sum.inr 706, 2), (Sum.inr 741, 1), (Sum.inr 815, 1), (Sum.inr 4070, -1)]

theorem reindexCheck1215 : Integer.Sparse.reindex keyMap MixedData.row1215 = numericRow1215 := by decide +kernel

theorem numericCheck1215 (x : Master → ℝ) : Integer.Sparse.eval numericRow1215 x =
    (1 : ℝ) * reducedSource1215 x := by
  norm_num [numericRow1215, reducedSource1215, Integer.Sparse.eval, Sparse.eval, nodeValue546, nodeValue706, nodeValue741, nodeValue809, nodeValue815, nodeValue4070]

end MUB6.Certificate.MixedSourceBridge

end OAI
