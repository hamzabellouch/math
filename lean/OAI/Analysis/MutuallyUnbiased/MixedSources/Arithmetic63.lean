import OAI.Analysis.MutuallyUnbiased.MixedData.Source7
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values9
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1008 (x : Master → ℝ) : ℝ :=
  (8 : ℝ) * Sparse.eval nodeValue615 x + ((1 : ℝ) * Sparse.eval nodeValue622 x + ((12 : ℝ) * Sparse.eval nodeValue1140 x + ((8 : ℝ) * Sparse.eval nodeValue1307 x + ((1 : ℝ) * Sparse.eval nodeValue3126 x + 0))))

def numericRow1008 : Integer.Sparse Master := [(Sum.inl 0, -1), (Sum.inl 5, 4), (Sum.inl 6, 1), (Sum.inl 1, -4), (Sum.inr 615, 144), (Sum.inr 622, 18), (Sum.inr 1140, 216)]

theorem reindexCheck1008 : Integer.Sparse.reindex keyMap MixedData.row1008 = numericRow1008 := by decide +kernel

theorem numericCheck1008 (x : Master → ℝ) : Integer.Sparse.eval numericRow1008 x =
    (18 : ℝ) * reducedSource1008 x := by
  norm_num [numericRow1008, reducedSource1008, Integer.Sparse.eval, Sparse.eval, nodeValue615, nodeValue622, nodeValue1140, nodeValue1307, nodeValue3126]; ring

noncomputable def reducedSource1009 (x : Master → ℝ) : ℝ :=
  (16 : ℝ) * Sparse.eval nodeValue4468 x + ((2 : ℝ) * Sparse.eval nodeValue4512 x + ((12 : ℝ) * Sparse.eval nodeValue4594 x + 0))

def numericRow1009 : Integer.Sparse Master := [(Sum.inr 1051, -4), (Sum.inr 1752, -4), (Sum.inr 4594, 12)]

theorem reindexCheck1009 : Integer.Sparse.reindex keyMap MixedData.row1009 = numericRow1009 := by decide +kernel

theorem numericCheck1009 (x : Master → ℝ) : Integer.Sparse.eval numericRow1009 x =
    (1 : ℝ) * reducedSource1009 x := by
  norm_num [numericRow1009, reducedSource1009, Integer.Sparse.eval, Sparse.eval, nodeValue4468, nodeValue4512, nodeValue4594]; ring

noncomputable def reducedSource1010 (x : Master → ℝ) : ℝ :=
  (8 : ℝ) * Sparse.eval nodeValue1051 x + ((1 : ℝ) * Sparse.eval nodeValue1096 x + ((12 : ℝ) * Sparse.eval nodeValue1221 x + ((8 : ℝ) * Sparse.eval nodeValue1275 x + ((1 : ℝ) * Sparse.eval nodeValue1456 x + 0))))

def numericRow1010 : Integer.Sparse Master := [(Sum.inl 0, -1), (Sum.inl 5, 4), (Sum.inl 6, -5), (Sum.inl 1, 2), (Sum.inr 1051, 144), (Sum.inr 1221, 216)]

theorem reindexCheck1010 : Integer.Sparse.reindex keyMap MixedData.row1010 = numericRow1010 := by decide +kernel

theorem numericCheck1010 (x : Master → ℝ) : Integer.Sparse.eval numericRow1010 x =
    (18 : ℝ) * reducedSource1010 x := by
  norm_num [numericRow1010, reducedSource1010, Integer.Sparse.eval, Sparse.eval, nodeValue1051, nodeValue1096, nodeValue1221, nodeValue1275, nodeValue1456]; ring

noncomputable def reducedSource1011 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue1752 x + ((1 : ℝ) * Sparse.eval nodeValue1758 x + ((1 : ℝ) * Sparse.eval nodeValue3313 x + ((-1 : ℝ) * Sparse.eval nodeValue4072 x + 0)))

def numericRow1011 : Integer.Sparse Master := [(Sum.inr 1752, 4), (Sum.inr 3313, 1), (Sum.inr 4072, -1)]

theorem reindexCheck1011 : Integer.Sparse.reindex keyMap MixedData.row1011 = numericRow1011 := by decide +kernel

theorem numericCheck1011 (x : Master → ℝ) : Integer.Sparse.eval numericRow1011 x =
    (1 : ℝ) * reducedSource1011 x := by
  norm_num [numericRow1011, reducedSource1011, Integer.Sparse.eval, Sparse.eval, nodeValue1752, nodeValue1758, nodeValue3313, nodeValue4072]

noncomputable def reducedSource1012 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4156 x + ((3 : ℝ) * Sparse.eval nodeValue4159 x + ((1 : ℝ) * Sparse.eval nodeValue4163 x + ((1 : ℝ) * Sparse.eval nodeValue4187 x + ((1 : ℝ) * Sparse.eval nodeValue4189 x + ((6 : ℝ) * Sparse.eval nodeValue4330 x + ((3 : ℝ) * Sparse.eval nodeValue4356 x + ((3 : ℝ) * Sparse.eval nodeValue4370 x + ((3 : ℝ) * Sparse.eval nodeValue4460 x + ((1 : ℝ) * Sparse.eval nodeValue4505 x + ((3 : ℝ) * Sparse.eval nodeValue4605 x + ((1 : ℝ) * Sparse.eval nodeValue4621 x + ((1 : ℝ) * Sparse.eval nodeValue4897 x + 0))))))))))))

def numericRow1012 : Integer.Sparse Master := [(Sum.inr 615, -1), (Sum.inr 934, -3), (Sum.inr 1043, -3), (Sum.inr 1239, -3), (Sum.inr 1297, -1), (Sum.inr 1537, -1), (Sum.inr 1692, -3), (Sum.inr 1725, -3), (Sum.inr 2226, -3), (Sum.inr 2289, -1), (Sum.inr 4156, 12), (Sum.inr 4159, 12), (Sum.inr 4163, 4), (Sum.inr 4189, 4), (Sum.inr 4330, 24), (Sum.inr 4370, 12)]

theorem reindexCheck1012 : Integer.Sparse.reindex keyMap MixedData.row1012 = numericRow1012 := by decide +kernel

theorem numericCheck1012 (x : Master → ℝ) : Integer.Sparse.eval numericRow1012 x =
    (4 : ℝ) * reducedSource1012 x := by
  norm_num [numericRow1012, reducedSource1012, Integer.Sparse.eval, Sparse.eval, nodeValue4156, nodeValue4159, nodeValue4163, nodeValue4187, nodeValue4189, nodeValue4330, nodeValue4356, nodeValue4370, nodeValue4460, nodeValue4505, nodeValue4605, nodeValue4621, nodeValue4897]; ring

noncomputable def reducedSource1013 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue587 x + ((1 : ℝ) * Sparse.eval nodeValue591 x + ((1 : ℝ) * Sparse.eval nodeValue617 x + ((3 : ℝ) * Sparse.eval nodeValue633 x + ((1 : ℝ) * Sparse.eval nodeValue650 x + ((6 : ℝ) * Sparse.eval nodeValue1118 x + ((3 : ℝ) * Sparse.eval nodeValue1142 x + ((3 : ℝ) * Sparse.eval nodeValue1173 x + ((3 : ℝ) * Sparse.eval nodeValue1271 x + ((1 : ℝ) * Sparse.eval nodeValue1308 x + ((3 : ℝ) * Sparse.eval nodeValue1416 x + ((1 : ℝ) * Sparse.eval nodeValue1450 x + ((1 : ℝ) * Sparse.eval nodeValue3114 x + 0))))))))))))

def numericRow1013 : Integer.Sparse Master := [(Sum.inl 0, -19), (Sum.inl 5, -20), (Sum.inl 6, 25), (Sum.inl 2, 30), (Sum.inl 1, 20), (Sum.inr 587, 720), (Sum.inr 591, 240), (Sum.inr 617, 240), (Sum.inr 633, 720), (Sum.inr 1118, 1440), (Sum.inr 1142, 720)]

theorem reindexCheck1013 : Integer.Sparse.reindex keyMap MixedData.row1013 = numericRow1013 := by decide +kernel

theorem numericCheck1013 (x : Master → ℝ) : Integer.Sparse.eval numericRow1013 x =
    (240 : ℝ) * reducedSource1013 x := by
  norm_num [numericRow1013, reducedSource1013, Integer.Sparse.eval, Sparse.eval, nodeValue587, nodeValue591, nodeValue617, nodeValue633, nodeValue650, nodeValue1118, nodeValue1142, nodeValue1173, nodeValue1271, nodeValue1308, nodeValue1416, nodeValue1450, nodeValue3114]; ring

noncomputable def reducedSource1014 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1516 x + ((3 : ℝ) * Sparse.eval nodeValue1532 x + ((1 : ℝ) * Sparse.eval nodeValue1534 x + ((1 : ℝ) * Sparse.eval nodeValue1537 x + ((1 : ℝ) * Sparse.eval nodeValue1540 x + ((6 : ℝ) * Sparse.eval nodeValue1672 x + ((3 : ℝ) * Sparse.eval nodeValue1692 x + ((3 : ℝ) * Sparse.eval nodeValue1722 x + ((3 : ℝ) * Sparse.eval nodeValue1725 x + ((1 : ℝ) * Sparse.eval nodeValue1754 x + ((3 : ℝ) * Sparse.eval nodeValue2226 x + ((1 : ℝ) * Sparse.eval nodeValue2289 x + ((1 : ℝ) * Sparse.eval nodeValue2292 x + 0))))))))))))

def numericRow1014 : Integer.Sparse Master := [(Sum.inr 1516, 3), (Sum.inr 1532, 3), (Sum.inr 1534, 1), (Sum.inr 1537, 1), (Sum.inr 1540, 1), (Sum.inr 1672, 6), (Sum.inr 1692, 3), (Sum.inr 1722, 3), (Sum.inr 1725, 3), (Sum.inr 2226, 3), (Sum.inr 2289, 1)]

theorem reindexCheck1014 : Integer.Sparse.reindex keyMap MixedData.row1014 = numericRow1014 := by decide +kernel

theorem numericCheck1014 (x : Master → ℝ) : Integer.Sparse.eval numericRow1014 x =
    (1 : ℝ) * reducedSource1014 x := by
  norm_num [numericRow1014, reducedSource1014, Integer.Sparse.eval, Sparse.eval, nodeValue1516, nodeValue1532, nodeValue1534, nodeValue1537, nodeValue1540, nodeValue1672, nodeValue1692, nodeValue1722, nodeValue1725, nodeValue1754, nodeValue2226, nodeValue2289, nodeValue2292]

noncomputable def reducedSource1015 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue591 x + ((3 : ℝ) * Sparse.eval nodeValue628 x + ((1 : ℝ) * Sparse.eval nodeValue643 x + ((1 : ℝ) * Sparse.eval nodeValue1051 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

def numericRow1015 : Integer.Sparse Master := [(Sum.inr 591, 1), (Sum.inr 628, 3), (Sum.inr 643, 1), (Sum.inr 1051, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1015 : Integer.Sparse.reindex keyMap MixedData.row1015 = numericRow1015 := by decide +kernel

theorem numericCheck1015 (x : Master → ℝ) : Integer.Sparse.eval numericRow1015 x =
    (1 : ℝ) * reducedSource1015 x := by
  norm_num [numericRow1015, reducedSource1015, Integer.Sparse.eval, Sparse.eval, nodeValue591, nodeValue628, nodeValue643, nodeValue1051, nodeValue4084]

noncomputable def reducedSource1016 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue628 x + ((2 : ℝ) * Sparse.eval nodeValue908 x + ((1 : ℝ) * Sparse.eval nodeValue934 x + ((1 : ℝ) * Sparse.eval nodeValue1051 x + ((1 : ℝ) * Sparse.eval nodeValue1239 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1016 : Integer.Sparse Master := [(Sum.inr 628, 1), (Sum.inr 908, 2), (Sum.inr 934, 1), (Sum.inr 1051, 1), (Sum.inr 1239, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1016 : Integer.Sparse.reindex keyMap MixedData.row1016 = numericRow1016 := by decide +kernel

theorem numericCheck1016 (x : Master → ℝ) : Integer.Sparse.eval numericRow1016 x =
    (1 : ℝ) * reducedSource1016 x := by
  norm_num [numericRow1016, reducedSource1016, Integer.Sparse.eval, Sparse.eval, nodeValue628, nodeValue908, nodeValue934, nodeValue1051, nodeValue1239, nodeValue4084]

noncomputable def reducedSource1017 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue584 x + ((2 : ℝ) * Sparse.eval nodeValue908 x + ((1 : ℝ) * Sparse.eval nodeValue948 x + ((1 : ℝ) * Sparse.eval nodeValue1043 x + ((1 : ℝ) * Sparse.eval nodeValue1051 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1017 : Integer.Sparse Master := [(Sum.inr 584, 1), (Sum.inr 908, 2), (Sum.inr 948, 1), (Sum.inr 1043, 1), (Sum.inr 1051, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1017 : Integer.Sparse.reindex keyMap MixedData.row1017 = numericRow1017 := by decide +kernel

theorem numericCheck1017 (x : Master → ℝ) : Integer.Sparse.eval numericRow1017 x =
    (1 : ℝ) * reducedSource1017 x := by
  norm_num [numericRow1017, reducedSource1017, Integer.Sparse.eval, Sparse.eval, nodeValue584, nodeValue908, nodeValue948, nodeValue1043, nodeValue1051, nodeValue4084]

noncomputable def reducedSource1018 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue643 x + ((3 : ℝ) * Sparse.eval nodeValue948 x + ((1 : ℝ) * Sparse.eval nodeValue1051 x + ((1 : ℝ) * Sparse.eval nodeValue1297 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

def numericRow1018 : Integer.Sparse Master := [(Sum.inr 643, 1), (Sum.inr 948, 3), (Sum.inr 1051, 1), (Sum.inr 1297, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1018 : Integer.Sparse.reindex keyMap MixedData.row1018 = numericRow1018 := by decide +kernel

theorem numericCheck1018 (x : Master → ℝ) : Integer.Sparse.eval numericRow1018 x =
    (1 : ℝ) * reducedSource1018 x := by
  norm_num [numericRow1018, reducedSource1018, Integer.Sparse.eval, Sparse.eval, nodeValue643, nodeValue948, nodeValue1051, nodeValue1297, nodeValue4084]

noncomputable def reducedSource1019 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue615 x + ((3 : ℝ) * Sparse.eval nodeValue934 x + ((1 : ℝ) * Sparse.eval nodeValue1051 x + ((1 : ℝ) * Sparse.eval nodeValue1089 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

def numericRow1019 : Integer.Sparse Master := [(Sum.inr 615, 1), (Sum.inr 934, 3), (Sum.inr 1051, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1019 : Integer.Sparse.reindex keyMap MixedData.row1019 = numericRow1019 := by decide +kernel

theorem numericCheck1019 (x : Master → ℝ) : Integer.Sparse.eval numericRow1019 x =
    (1 : ℝ) * reducedSource1019 x := by
  norm_num [numericRow1019, reducedSource1019, Integer.Sparse.eval, Sparse.eval, nodeValue615, nodeValue934, nodeValue1051, nodeValue1089, nodeValue4084]

noncomputable def reducedSource1020 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4108 x + ((1 : ℝ) * Sparse.eval nodeValue4112 x + ((1 : ℝ) * Sparse.eval nodeValue4134 x + ((3 : ℝ) * Sparse.eval nodeValue4146 x + ((1 : ℝ) * Sparse.eval nodeValue4181 x + ((6 : ℝ) * Sparse.eval nodeValue4293 x + ((3 : ℝ) * Sparse.eval nodeValue4315 x + ((3 : ℝ) * Sparse.eval nodeValue4356 x + ((3 : ℝ) * Sparse.eval nodeValue4463 x + ((1 : ℝ) * Sparse.eval nodeValue4507 x + ((3 : ℝ) * Sparse.eval nodeValue4608 x + ((1 : ℝ) * Sparse.eval nodeValue4625 x + ((1 : ℝ) * Sparse.eval nodeValue5296 x + 0))))))))))))

def numericRow1020 : Integer.Sparse Master := [(Sum.inl 0, 11), (Sum.inl 5, -20), (Sum.inl 6, -5), (Sum.inl 2, 30), (Sum.inl 1, 20), (Sum.inr 545, -2160), (Sum.inr 549, -720), (Sum.inr 564, -720), (Sum.inr 574, -2160), (Sum.inr 609, -720), (Sum.inr 683, -2160), (Sum.inr 686, -720), (Sum.inr 695, -720), (Sum.inr 871, -4320), (Sum.inr 893, -2160), (Sum.inr 934, -2160), (Sum.inr 1046, -2160), (Sum.inr 1091, -720), (Sum.inr 1242, -2160), (Sum.inr 1494, -2160), (Sum.inr 1521, -720), (Sum.inr 1568, -4320), (Sum.inr 1578, -2160), (Sum.inr 1692, -2160), (Sum.inr 1750, -2160), (Sum.inr 1756, -720), (Sum.inr 3300, -2160), (Sum.inr 3310, -720), (Sum.inr 3634, -720)]

theorem reindexCheck1020 : Integer.Sparse.reindex keyMap MixedData.row1020 = numericRow1020 := by decide +kernel

theorem numericCheck1020 (x : Master → ℝ) : Integer.Sparse.eval numericRow1020 x =
    (2880 : ℝ) * reducedSource1020 x := by
  norm_num [numericRow1020, reducedSource1020, Integer.Sparse.eval, Sparse.eval, nodeValue4108, nodeValue4112, nodeValue4134, nodeValue4146, nodeValue4181, nodeValue4293, nodeValue4315, nodeValue4356, nodeValue4463, nodeValue4507, nodeValue4608, nodeValue4625, nodeValue5296]; ring

noncomputable def reducedSource1021 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue545 x + ((1 : ℝ) * Sparse.eval nodeValue549 x + ((1 : ℝ) * Sparse.eval nodeValue564 x + ((3 : ℝ) * Sparse.eval nodeValue574 x + ((1 : ℝ) * Sparse.eval nodeValue609 x + ((6 : ℝ) * Sparse.eval nodeValue871 x + ((3 : ℝ) * Sparse.eval nodeValue893 x + ((3 : ℝ) * Sparse.eval nodeValue934 x + ((3 : ℝ) * Sparse.eval nodeValue1046 x + ((1 : ℝ) * Sparse.eval nodeValue1091 x + ((3 : ℝ) * Sparse.eval nodeValue1242 x + ((1 : ℝ) * Sparse.eval nodeValue1304 x + ((1 : ℝ) * Sparse.eval nodeValue2770 x + 0))))))))))))

def numericRow1021 : Integer.Sparse Master := [(Sum.inl 0, -11), (Sum.inl 5, 20), (Sum.inl 6, 5), (Sum.inl 2, -30), (Sum.inl 1, -20), (Sum.inr 545, 2160), (Sum.inr 549, 720), (Sum.inr 564, 720), (Sum.inr 574, 2160), (Sum.inr 609, 720), (Sum.inr 871, 4320), (Sum.inr 893, 2160), (Sum.inr 934, 2160), (Sum.inr 1046, 2160), (Sum.inr 1091, 720), (Sum.inr 1242, 2160)]

theorem reindexCheck1021 : Integer.Sparse.reindex keyMap MixedData.row1021 = numericRow1021 := by decide +kernel

theorem numericCheck1021 (x : Master → ℝ) : Integer.Sparse.eval numericRow1021 x =
    (720 : ℝ) * reducedSource1021 x := by
  norm_num [numericRow1021, reducedSource1021, Integer.Sparse.eval, Sparse.eval, nodeValue545, nodeValue549, nodeValue564, nodeValue574, nodeValue609, nodeValue871, nodeValue893, nodeValue934, nodeValue1046, nodeValue1091, nodeValue1242, nodeValue1304, nodeValue2770]; ring

noncomputable def reducedSource1022 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue855 x + ((3 : ℝ) * Sparse.eval nodeValue1620 x + ((1 : ℝ) * Sparse.eval nodeValue1752 x + ((1 : ℝ) * Sparse.eval nodeValue1758 x + ((-1 : ℝ) * Sparse.eval nodeValue4072 x + 0))))

def numericRow1022 : Integer.Sparse Master := [(Sum.inr 1620, 3), (Sum.inr 1752, 1), (Sum.inr 4072, -1)]

theorem reindexCheck1022 : Integer.Sparse.reindex keyMap MixedData.row1022 = numericRow1022 := by decide +kernel

theorem numericCheck1022 (x : Master → ℝ) : Integer.Sparse.eval numericRow1022 x =
    (1 : ℝ) * reducedSource1022 x := by
  norm_num [numericRow1022, reducedSource1022, Integer.Sparse.eval, Sparse.eval, nodeValue855, nodeValue1620, nodeValue1752, nodeValue1758, nodeValue4072]

noncomputable def reducedSource1023 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue826 x + ((1 : ℝ) * Sparse.eval nodeValue832 x + ((1 : ℝ) * Sparse.eval nodeValue859 x + ((1 : ℝ) * Sparse.eval nodeValue1741 x + ((-1 : ℝ) * Sparse.eval nodeValue4071 x + 0))))

def numericRow1023 : Integer.Sparse Master := [(Sum.inr 826, 3), (Sum.inr 832, 1), (Sum.inr 1741, 1), (Sum.inr 4071, -1)]

theorem reindexCheck1023 : Integer.Sparse.reindex keyMap MixedData.row1023 = numericRow1023 := by decide +kernel

theorem numericCheck1023 (x : Master → ℝ) : Integer.Sparse.eval numericRow1023 x =
    (1 : ℝ) * reducedSource1023 x := by
  norm_num [numericRow1023, reducedSource1023, Integer.Sparse.eval, Sparse.eval, nodeValue826, nodeValue832, nodeValue859, nodeValue1741, nodeValue4071]

end MUB6.Certificate.MixedSourceBridge

end OAI
