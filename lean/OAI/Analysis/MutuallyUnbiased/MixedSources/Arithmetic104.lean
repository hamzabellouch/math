import OAI.Analysis.MutuallyUnbiased.MixedData.Source13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values84
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1664 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1320 x + ((1 : ℝ) * Sparse.eval nodeValue2815 x + ((1 : ℝ) * Sparse.eval nodeValue2847 x + ((2 : ℝ) * Sparse.eval nodeValue2865 x + ((1 : ℝ) * Sparse.eval nodeValue2884 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow1664 : Integer.Sparse Master := [(Sum.inr 1320, 1), (Sum.inr 2815, 1), (Sum.inr 2847, 1), (Sum.inr 2865, 2), (Sum.inr 2884, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1664 : Integer.Sparse.reindex keyMap MixedData.row1664 = numericRow1664 := by decide +kernel

theorem numericCheck1664 (x : Master → ℝ) : Integer.Sparse.eval numericRow1664 x =
    (1 : ℝ) * reducedSource1664 x := by
  norm_num [numericRow1664, reducedSource1664, Integer.Sparse.eval, Sparse.eval, nodeValue1320, nodeValue2815, nodeValue2847, nodeValue2865, nodeValue2884, nodeValue4091]

noncomputable def reducedSource1665 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1334 x + ((1 : ℝ) * Sparse.eval nodeValue2797 x + ((1 : ℝ) * Sparse.eval nodeValue2802 x + ((1 : ℝ) * Sparse.eval nodeValue2815 x + ((1 : ℝ) * Sparse.eval nodeValue2865 x + ((1 : ℝ) * Sparse.eval nodeValue2931 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow1665 : Integer.Sparse Master := [(Sum.inr 1334, 1), (Sum.inr 2797, 1), (Sum.inr 2802, 1), (Sum.inr 2815, 1), (Sum.inr 2865, 1), (Sum.inr 2931, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1665 : Integer.Sparse.reindex keyMap MixedData.row1665 = numericRow1665 := by decide +kernel

theorem numericCheck1665 (x : Master → ℝ) : Integer.Sparse.eval numericRow1665 x =
    (1 : ℝ) * reducedSource1665 x := by
  norm_num [numericRow1665, reducedSource1665, Integer.Sparse.eval, Sparse.eval, nodeValue1334, nodeValue2797, nodeValue2802, nodeValue2815, nodeValue2865, nodeValue2931, nodeValue4091]

noncomputable def reducedSource1666 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2018 x + ((1 : ℝ) * Sparse.eval nodeValue2074 x + ((1 : ℝ) * Sparse.eval nodeValue2081 x + ((1 : ℝ) * Sparse.eval nodeValue2099 x + ((1 : ℝ) * Sparse.eval nodeValue2203 x + ((1 : ℝ) * Sparse.eval nodeValue3530 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

def numericRow1666 : Integer.Sparse Master := [(Sum.inr 2018, 1), (Sum.inr 2074, 1), (Sum.inr 2081, 1), (Sum.inr 2099, 1), (Sum.inr 2203, 1), (Sum.inr 3530, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1666 : Integer.Sparse.reindex keyMap MixedData.row1666 = numericRow1666 := by decide +kernel

theorem numericCheck1666 (x : Master → ℝ) : Integer.Sparse.eval numericRow1666 x =
    (1 : ℝ) * reducedSource1666 x := by
  norm_num [numericRow1666, reducedSource1666, Integer.Sparse.eval, Sparse.eval, nodeValue2018, nodeValue2074, nodeValue2081, nodeValue2099, nodeValue2203, nodeValue3530, nodeValue4081]

noncomputable def reducedSource1667 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2015 x + ((1 : ℝ) * Sparse.eval nodeValue2018 x + ((1 : ℝ) * Sparse.eval nodeValue2027 x + ((1 : ℝ) * Sparse.eval nodeValue2047 x + ((1 : ℝ) * Sparse.eval nodeValue2261 x + ((1 : ℝ) * Sparse.eval nodeValue3530 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

def numericRow1667 : Integer.Sparse Master := [(Sum.inr 2015, 1), (Sum.inr 2018, 1), (Sum.inr 2027, 1), (Sum.inr 2047, 1), (Sum.inr 2261, 1), (Sum.inr 3530, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1667 : Integer.Sparse.reindex keyMap MixedData.row1667 = numericRow1667 := by decide +kernel

theorem numericCheck1667 (x : Master → ℝ) : Integer.Sparse.eval numericRow1667 x =
    (1 : ℝ) * reducedSource1667 x := by
  norm_num [numericRow1667, reducedSource1667, Integer.Sparse.eval, Sparse.eval, nodeValue2015, nodeValue2018, nodeValue2027, nodeValue2047, nodeValue2261, nodeValue3530, nodeValue4081]

noncomputable def reducedSource1668 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4327 x + ((1 : ℝ) * Sparse.eval nodeValue4330 x + ((1 : ℝ) * Sparse.eval nodeValue4335 x + ((1 : ℝ) * Sparse.eval nodeValue4347 x + ((1 : ℝ) * Sparse.eval nodeValue4440 x + ((1 : ℝ) * Sparse.eval nodeValue4528 x + ((1 : ℝ) * Sparse.eval nodeValue4535 x + ((1 : ℝ) * Sparse.eval nodeValue4551 x + ((1 : ℝ) * Sparse.eval nodeValue4591 x + ((2 : ℝ) * Sparse.eval nodeValue4930 x + ((1 : ℝ) * Sparse.eval nodeValue4935 x + ((1 : ℝ) * Sparse.eval nodeValue4944 x + ((1 : ℝ) * Sparse.eval nodeValue4948 x + ((1 : ℝ) * Sparse.eval nodeValue5034 x + ((1 : ℝ) * Sparse.eval nodeValue5037 x + ((1 : ℝ) * Sparse.eval nodeValue5065 x + ((1 : ℝ) * Sparse.eval nodeValue5073 x + ((1 : ℝ) * Sparse.eval nodeValue5078 x + ((1 : ℝ) * Sparse.eval nodeValue5081 x + ((1 : ℝ) * Sparse.eval nodeValue5104 x + ((1 : ℝ) * Sparse.eval nodeValue5128 x + ((1 : ℝ) * Sparse.eval nodeValue5139 x + ((1 : ℝ) * Sparse.eval nodeValue5149 x + ((1 : ℝ) * Sparse.eval nodeValue5152 x + ((1 : ℝ) * Sparse.eval nodeValue5170 x + ((1 : ℝ) * Sparse.eval nodeValue5252 x + ((1 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5284 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + 0))))))))))))))))))))))))))))

def numericRow1668 : Integer.Sparse Master := [(Sum.inr 1136, -1), (Sum.inr 2339, -1), (Sum.inr 2429, -1), (Sum.inr 2480, -1), (Sum.inr 2485, -1), (Sum.inr 2489, -1), (Sum.inr 2723, -1), (Sum.inr 2924, -1), (Sum.inr 2931, -1), (Sum.inr 2954, -1), (Sum.inr 3077, -1), (Sum.inr 3273, -1), (Sum.inr 3420, -1), (Sum.inr 3455, -1), (Sum.inr 3467, -1), (Sum.inr 3481, -1), (Sum.inr 3482, -1), (Sum.inr 3544, -1), (Sum.inr 3605, -1), (Sum.inr 3606, -1), (Sum.inr 3612, -1), (Sum.inr 3625, -1), (Sum.inr 4327, 4), (Sum.inr 4330, 4), (Sum.inr 4335, 4), (Sum.inr 4347, 4), (Sum.inr 4440, 4), (Sum.inr 4528, 4), (Sum.inr 4535, 4), (Sum.inr 4591, 4), (Sum.inr 4930, 8), (Sum.inr 4935, 4), (Sum.inr 4944, 4), (Sum.inr 5034, 4), (Sum.inr 5065, 4), (Sum.inr 5128, 4), (Sum.inr 5139, 4), (Sum.inr 5252, 4)]

theorem reindexCheck1668 : Integer.Sparse.reindex keyMap MixedData.row1668 = numericRow1668 := by decide +kernel

theorem numericCheck1668 (x : Master → ℝ) : Integer.Sparse.eval numericRow1668 x =
    (4 : ℝ) * reducedSource1668 x := by
  norm_num [numericRow1668, reducedSource1668, Integer.Sparse.eval, Sparse.eval, nodeValue4327, nodeValue4330, nodeValue4335, nodeValue4347, nodeValue4440, nodeValue4528, nodeValue4535, nodeValue4551, nodeValue4591, nodeValue4930, nodeValue4935, nodeValue4944, nodeValue4948, nodeValue5034, nodeValue5037, nodeValue5065, nodeValue5073, nodeValue5078, nodeValue5081, nodeValue5104, nodeValue5128, nodeValue5139, nodeValue5149, nodeValue5152, nodeValue5170, nodeValue5252, nodeValue5259, nodeValue5284, nodeValue5410]
  ring

noncomputable def reducedSource1669 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue905 x + ((1 : ℝ) * Sparse.eval nodeValue908 x + ((1 : ℝ) * Sparse.eval nodeValue913 x + ((1 : ℝ) * Sparse.eval nodeValue925 x + ((1 : ℝ) * Sparse.eval nodeValue1022 x + ((1 : ℝ) * Sparse.eval nodeValue1148 x + ((1 : ℝ) * Sparse.eval nodeValue1154 x + ((1 : ℝ) * Sparse.eval nodeValue1163 x + ((1 : ℝ) * Sparse.eval nodeValue1215 x + ((1 : ℝ) * Sparse.eval nodeValue2320 x + ((1 : ℝ) * Sparse.eval nodeValue2326 x + ((1 : ℝ) * Sparse.eval nodeValue2335 x + ((1 : ℝ) * Sparse.eval nodeValue2422 x + ((1 : ℝ) * Sparse.eval nodeValue2426 x + ((1 : ℝ) * Sparse.eval nodeValue2470 x + ((1 : ℝ) * Sparse.eval nodeValue2526 x + ((1 : ℝ) * Sparse.eval nodeValue2531 x + ((1 : ℝ) * Sparse.eval nodeValue2543 x + ((1 : ℝ) * Sparse.eval nodeValue2558 x + ((1 : ℝ) * Sparse.eval nodeValue2570 x + ((1 : ℝ) * Sparse.eval nodeValue2572 x + ((1 : ℝ) * Sparse.eval nodeValue2576 x + ((1 : ℝ) * Sparse.eval nodeValue2596 x + ((1 : ℝ) * Sparse.eval nodeValue2712 x + ((1 : ℝ) * Sparse.eval nodeValue2753 x + ((1 : ℝ) * Sparse.eval nodeValue2987 x + ((1 : ℝ) * Sparse.eval nodeValue2991 x + ((1 : ℝ) * Sparse.eval nodeValue3000 x + ((1 : ℝ) * Sparse.eval nodeValue3088 x + ((1 : ℝ) * Sparse.eval nodeValue3996 x + 0)))))))))))))))))))))))))))))

def numericRow1669 : Integer.Sparse Master := [(Sum.inl 0, -304), (Sum.inl 5, -160), (Sum.inl 6, 60), (Sum.inl 2, 180), (Sum.inl 3, 320), (Sum.inl 52, 320), (Sum.inl 1, -680), (Sum.inr 905, 5760), (Sum.inr 908, 5760), (Sum.inr 913, 5760), (Sum.inr 925, 5760), (Sum.inr 1022, 5760), (Sum.inr 1148, 5760), (Sum.inr 1154, 5760), (Sum.inr 1215, 5760), (Sum.inr 2320, 5760), (Sum.inr 2326, 5760), (Sum.inr 2335, 5760), (Sum.inr 2422, 5760), (Sum.inr 2426, 5760), (Sum.inr 2470, 5760), (Sum.inr 2543, 5760), (Sum.inr 2558, 5760), (Sum.inr 2712, 5760)]

theorem reindexCheck1669 : Integer.Sparse.reindex keyMap MixedData.row1669 = numericRow1669 := by decide +kernel

theorem numericCheck1669 (x : Master → ℝ) : Integer.Sparse.eval numericRow1669 x =
    (5760 : ℝ) * reducedSource1669 x := by
  norm_num [numericRow1669, reducedSource1669, Integer.Sparse.eval, Sparse.eval, nodeValue905, nodeValue908, nodeValue913, nodeValue925, nodeValue1022, nodeValue1148, nodeValue1154, nodeValue1163, nodeValue1215, nodeValue2320, nodeValue2326, nodeValue2335, nodeValue2422, nodeValue2426, nodeValue2470, nodeValue2526, nodeValue2531, nodeValue2543, nodeValue2558, nodeValue2570, nodeValue2572, nodeValue2576, nodeValue2596, nodeValue2712, nodeValue2753, nodeValue2987, nodeValue2991, nodeValue3000, nodeValue3088, nodeValue3996]
  ring

noncomputable def reducedSource1670 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1670 x + ((1 : ℝ) * Sparse.eval nodeValue1672 x + ((1 : ℝ) * Sparse.eval nodeValue1676 x + ((1 : ℝ) * Sparse.eval nodeValue1689 x + ((1 : ℝ) * Sparse.eval nodeValue1723 x + ((1 : ℝ) * Sparse.eval nodeValue3260 x + ((1 : ℝ) * Sparse.eval nodeValue3272 x + ((1 : ℝ) * Sparse.eval nodeValue3273 x + ((1 : ℝ) * Sparse.eval nodeValue3291 x + ((2 : ℝ) * Sparse.eval nodeValue3408 x + ((1 : ℝ) * Sparse.eval nodeValue3413 x + ((1 : ℝ) * Sparse.eval nodeValue3419 x + ((1 : ℝ) * Sparse.eval nodeValue3420 x + ((1 : ℝ) * Sparse.eval nodeValue3451 x + ((1 : ℝ) * Sparse.eval nodeValue3455 x + ((1 : ℝ) * Sparse.eval nodeValue3466 x + ((1 : ℝ) * Sparse.eval nodeValue3467 x + ((1 : ℝ) * Sparse.eval nodeValue3481 x + ((1 : ℝ) * Sparse.eval nodeValue3482 x + ((1 : ℝ) * Sparse.eval nodeValue3483 x + ((1 : ℝ) * Sparse.eval nodeValue3519 x + ((1 : ℝ) * Sparse.eval nodeValue3523 x + ((1 : ℝ) * Sparse.eval nodeValue3543 x + ((1 : ℝ) * Sparse.eval nodeValue3544 x + ((1 : ℝ) * Sparse.eval nodeValue3605 x + ((1 : ℝ) * Sparse.eval nodeValue3606 x + ((1 : ℝ) * Sparse.eval nodeValue3612 x + ((1 : ℝ) * Sparse.eval nodeValue3625 x + ((1 : ℝ) * Sparse.eval nodeValue3816 x + 0))))))))))))))))))))))))))))

def numericRow1670 : Integer.Sparse Master := [(Sum.inr 1670, 1), (Sum.inr 1672, 1), (Sum.inr 1676, 1), (Sum.inr 1689, 1), (Sum.inr 1723, 1), (Sum.inr 3260, 1), (Sum.inr 3272, 1), (Sum.inr 3273, 1), (Sum.inr 3291, 1), (Sum.inr 3408, 2), (Sum.inr 3413, 1), (Sum.inr 3419, 1), (Sum.inr 3420, 1), (Sum.inr 3451, 1), (Sum.inr 3455, 1), (Sum.inr 3466, 1), (Sum.inr 3467, 1), (Sum.inr 3481, 1), (Sum.inr 3482, 1), (Sum.inr 3519, 1), (Sum.inr 3523, 1), (Sum.inr 3543, 1), (Sum.inr 3544, 1), (Sum.inr 3605, 1), (Sum.inr 3606, 1), (Sum.inr 3612, 1), (Sum.inr 3625, 1)]

theorem reindexCheck1670 : Integer.Sparse.reindex keyMap MixedData.row1670 = numericRow1670 := by decide +kernel

theorem numericCheck1670 (x : Master → ℝ) : Integer.Sparse.eval numericRow1670 x =
    (1 : ℝ) * reducedSource1670 x := by
  norm_num [numericRow1670, reducedSource1670, Integer.Sparse.eval, Sparse.eval, nodeValue1670, nodeValue1672, nodeValue1676, nodeValue1689, nodeValue1723, nodeValue3260, nodeValue3272, nodeValue3273, nodeValue3291, nodeValue3408, nodeValue3413, nodeValue3419, nodeValue3420, nodeValue3451, nodeValue3455, nodeValue3466, nodeValue3467, nodeValue3481, nodeValue3482, nodeValue3483, nodeValue3519, nodeValue3523, nodeValue3543, nodeValue3544, nodeValue3605, nodeValue3606, nodeValue3612, nodeValue3625, nodeValue3816]

noncomputable def reducedSource1671 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1136 x + ((1 : ℝ) * Sparse.eval nodeValue2339 x + ((1 : ℝ) * Sparse.eval nodeValue2429 x + ((2 : ℝ) * Sparse.eval nodeValue2485 x + ((1 : ℝ) * Sparse.eval nodeValue2514 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow1671 : Integer.Sparse Master := [(Sum.inr 1136, 1), (Sum.inr 2339, 1), (Sum.inr 2429, 1), (Sum.inr 2485, 2), (Sum.inr 4091, -1)]

theorem reindexCheck1671 : Integer.Sparse.reindex keyMap MixedData.row1671 = numericRow1671 := by decide +kernel

theorem numericCheck1671 (x : Master → ℝ) : Integer.Sparse.eval numericRow1671 x =
    (1 : ℝ) * reducedSource1671 x := by
  norm_num [numericRow1671, reducedSource1671, Integer.Sparse.eval, Sparse.eval, nodeValue1136, nodeValue2339, nodeValue2429, nodeValue2485, nodeValue2514, nodeValue4091]

noncomputable def reducedSource1672 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4199 x + ((1 : ℝ) * Sparse.eval nodeValue4202 x + ((1 : ℝ) * Sparse.eval nodeValue4205 x + ((1 : ℝ) * Sparse.eval nodeValue4219 x + ((1 : ℝ) * Sparse.eval nodeValue4253 x + ((1 : ℝ) * Sparse.eval nodeValue4521 x + ((1 : ℝ) * Sparse.eval nodeValue4525 x + ((1 : ℝ) * Sparse.eval nodeValue4543 x + ((1 : ℝ) * Sparse.eval nodeValue4605 x + ((1 : ℝ) * Sparse.eval nodeValue4633 x + ((1 : ℝ) * Sparse.eval nodeValue4638 x + ((1 : ℝ) * Sparse.eval nodeValue4650 x + ((1 : ℝ) * Sparse.eval nodeValue4707 x + ((1 : ℝ) * Sparse.eval nodeValue4713 x + ((1 : ℝ) * Sparse.eval nodeValue4729 x + ((1 : ℝ) * Sparse.eval nodeValue4764 x + ((1 : ℝ) * Sparse.eval nodeValue4770 x + ((1 : ℝ) * Sparse.eval nodeValue4805 x + ((2 : ℝ) * Sparse.eval nodeValue4807 x + ((1 : ℝ) * Sparse.eval nodeValue4810 x + ((1 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4843 x + ((1 : ℝ) * Sparse.eval nodeValue4889 x + ((1 : ℝ) * Sparse.eval nodeValue4890 x + ((1 : ℝ) * Sparse.eval nodeValue5149 x + ((1 : ℝ) * Sparse.eval nodeValue5152 x + ((1 : ℝ) * Sparse.eval nodeValue5172 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5435 x + 0))))))))))))))))))))))))))))

def numericRow1672 : Integer.Sparse Master := [(Sum.inl 0, 111), (Sum.inl 6, -5), (Sum.inl 2, 20), (Sum.inl 7, 80), (Sum.inl 3, 160), (Sum.inl 12, 160), (Sum.inl 1, -310), (Sum.inr 702, -4320), (Sum.inr 705, -4320), (Sum.inr 708, -4320), (Sum.inr 720, -4320), (Sum.inr 760, -4320), (Sum.inr 762, -4320), (Sum.inr 764, -4320), (Sum.inr 769, -4320), (Sum.inr 787, -4320), (Sum.inr 847, -4320), (Sum.inr 1105, -4320), (Sum.inr 1109, -4320), (Sum.inr 1128, -4320), (Sum.inr 1239, -4320), (Sum.inr 1762, -4320), (Sum.inr 1767, -4320), (Sum.inr 1778, -4320), (Sum.inr 1847, -4320), (Sum.inr 1849, -4320), (Sum.inr 1851, -4320), (Sum.inr 1854, -4320), (Sum.inr 1861, -4320), (Sum.inr 1867, -4320), (Sum.inr 1887, -4320), (Sum.inr 1889, -4320), (Sum.inr 1891, -4320), (Sum.inr 1898, -4320), (Sum.inr 1940, -4320), (Sum.inr 1964, -4320), (Sum.inr 1970, -4320), (Sum.inr 2023, -4320), (Sum.inr 2025, -8640), (Sum.inr 2028, -4320), (Sum.inr 2058, -4320), (Sum.inr 2062, -4320), (Sum.inr 2182, -4320), (Sum.inr 2184, -4320), (Sum.inr 2186, -4320), (Sum.inr 2214, -4320), (Sum.inr 2215, -4320), (Sum.inr 2216, -4320), (Sum.inr 2224, -8640), (Sum.inr 2226, -4320), (Sum.inr 2230, -4320), (Sum.inr 2245, -4320), (Sum.inr 2247, -4320), (Sum.inr 2277, -4320), (Sum.inr 2290, -4320), (Sum.inr 2924, -4320), (Sum.inr 2931, -4320), (Sum.inr 3605, -4320), (Sum.inr 3612, -4320), (Sum.inr 3613, -4320), (Sum.inr 3632, -4320), (Sum.inr 3906, -4320)]

theorem reindexCheck1672 : Integer.Sparse.reindex keyMap MixedData.row1672 = numericRow1672 := by decide +kernel

theorem numericCheck1672 (x : Master → ℝ) : Integer.Sparse.eval numericRow1672 x =
    (17280 : ℝ) * reducedSource1672 x := by
  norm_num [numericRow1672, reducedSource1672, Integer.Sparse.eval, Sparse.eval, nodeValue4199, nodeValue4202, nodeValue4205, nodeValue4219, nodeValue4253, nodeValue4521, nodeValue4525, nodeValue4543, nodeValue4605, nodeValue4633, nodeValue4638, nodeValue4650, nodeValue4707, nodeValue4713, nodeValue4729, nodeValue4764, nodeValue4770, nodeValue4805, nodeValue4807, nodeValue4810, nodeValue4839, nodeValue4843, nodeValue4889, nodeValue4890, nodeValue5149, nodeValue5152, nodeValue5172, nodeValue5294, nodeValue5435]
  ring

noncomputable def reducedSource1673 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4327 x + ((1 : ℝ) * Sparse.eval nodeValue4331 x + ((1 : ℝ) * Sparse.eval nodeValue4333 x + ((1 : ℝ) * Sparse.eval nodeValue4335 x + ((1 : ℝ) * Sparse.eval nodeValue4336 x + ((1 : ℝ) * Sparse.eval nodeValue4352 x + ((1 : ℝ) * Sparse.eval nodeValue4353 x + ((1 : ℝ) * Sparse.eval nodeValue4442 x + ((1 : ℝ) * Sparse.eval nodeValue4463 x + ((1 : ℝ) * Sparse.eval nodeValue4664 x + ((1 : ℝ) * Sparse.eval nodeValue4670 x + ((1 : ℝ) * Sparse.eval nodeValue4686 x + ((1 : ℝ) * Sparse.eval nodeValue4757 x + ((1 : ℝ) * Sparse.eval nodeValue4764 x + ((1 : ℝ) * Sparse.eval nodeValue4772 x + ((1 : ℝ) * Sparse.eval nodeValue4777 x + ((1 : ℝ) * Sparse.eval nodeValue4792 x + ((1 : ℝ) * Sparse.eval nodeValue4802 x + ((2 : ℝ) * Sparse.eval nodeValue4807 x + ((1 : ℝ) * Sparse.eval nodeValue4811 x + ((1 : ℝ) * Sparse.eval nodeValue4838 x + ((1 : ℝ) * Sparse.eval nodeValue4871 x + ((1 : ℝ) * Sparse.eval nodeValue4890 x + ((1 : ℝ) * Sparse.eval nodeValue4895 x + ((1 : ℝ) * Sparse.eval nodeValue5150 x + ((1 : ℝ) * Sparse.eval nodeValue5151 x + ((1 : ℝ) * Sparse.eval nodeValue5173 x + ((1 : ℝ) * Sparse.eval nodeValue5270 x + ((1 : ℝ) * Sparse.eval nodeValue5271 x + 0))))))))))))))))))))))))))))

def numericRow1673 : Integer.Sparse Master := [(Sum.inr 930, -1), (Sum.inr 1046, -1), (Sum.inr 1690, -1), (Sum.inr 1750, -1), (Sum.inr 1812, -1), (Sum.inr 1964, -1), (Sum.inr 2020, -1), (Sum.inr 2025, -2), (Sum.inr 2029, -1), (Sum.inr 2112, -1), (Sum.inr 2165, -1), (Sum.inr 2182, -1), (Sum.inr 2202, -1), (Sum.inr 2224, -2), (Sum.inr 2225, -1), (Sum.inr 2247, -1), (Sum.inr 2287, -1), (Sum.inr 2290, -1), (Sum.inr 2739, -1), (Sum.inr 3534, -1), (Sum.inr 4327, 4), (Sum.inr 4331, 4), (Sum.inr 4333, 4), (Sum.inr 4335, 4), (Sum.inr 4336, 4), (Sum.inr 4353, 4), (Sum.inr 4442, 4), (Sum.inr 4664, 4), (Sum.inr 4670, 4), (Sum.inr 4757, 4), (Sum.inr 4772, 4), (Sum.inr 4777, 4), (Sum.inr 4792, 4), (Sum.inr 5150, 4), (Sum.inr 5151, 4), (Sum.inr 5173, 4), (Sum.inr 5270, 4)]

theorem reindexCheck1673 : Integer.Sparse.reindex keyMap MixedData.row1673 = numericRow1673 := by decide +kernel

theorem numericCheck1673 (x : Master → ℝ) : Integer.Sparse.eval numericRow1673 x =
    (4 : ℝ) * reducedSource1673 x := by
  norm_num [numericRow1673, reducedSource1673, Integer.Sparse.eval, Sparse.eval, nodeValue4327, nodeValue4331, nodeValue4333, nodeValue4335, nodeValue4336, nodeValue4352, nodeValue4353, nodeValue4442, nodeValue4463, nodeValue4664, nodeValue4670, nodeValue4686, nodeValue4757, nodeValue4764, nodeValue4772, nodeValue4777, nodeValue4792, nodeValue4802, nodeValue4807, nodeValue4811, nodeValue4838, nodeValue4871, nodeValue4890, nodeValue4895, nodeValue5150, nodeValue5151, nodeValue5173, nodeValue5270, nodeValue5271]
  ring

noncomputable def reducedSource1674 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue909 x + ((1 : ℝ) * Sparse.eval nodeValue911 x + ((1 : ℝ) * Sparse.eval nodeValue914 x + ((1 : ℝ) * Sparse.eval nodeValue931 x + ((1 : ℝ) * Sparse.eval nodeValue1024 x + ((1 : ℝ) * Sparse.eval nodeValue1327 x + ((1 : ℝ) * Sparse.eval nodeValue1333 x + ((1 : ℝ) * Sparse.eval nodeValue1340 x + ((1 : ℝ) * Sparse.eval nodeValue1413 x + ((1 : ℝ) * Sparse.eval nodeValue2323 x + ((1 : ℝ) * Sparse.eval nodeValue2327 x + ((1 : ℝ) * Sparse.eval nodeValue2340 x + ((1 : ℝ) * Sparse.eval nodeValue2423 x + ((1 : ℝ) * Sparse.eval nodeValue2430 x + ((1 : ℝ) * Sparse.eval nodeValue2471 x + ((1 : ℝ) * Sparse.eval nodeValue2528 x + ((1 : ℝ) * Sparse.eval nodeValue2532 x + ((1 : ℝ) * Sparse.eval nodeValue2573 x + ((2 : ℝ) * Sparse.eval nodeValue2574 x + ((1 : ℝ) * Sparse.eval nodeValue2575 x + ((1 : ℝ) * Sparse.eval nodeValue2600 x + ((1 : ℝ) * Sparse.eval nodeValue2602 x + ((1 : ℝ) * Sparse.eval nodeValue2754 x + ((1 : ℝ) * Sparse.eval nodeValue2755 x + ((1 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3204 x + ((1 : ℝ) * Sparse.eval nodeValue3207 x + ((1 : ℝ) * Sparse.eval nodeValue3213 x + ((1 : ℝ) * Sparse.eval nodeValue3229 x + 0))))))))))))))))))))))))))))

def numericRow1674 : Integer.Sparse Master := [(Sum.inl 0, -420), (Sum.inl 5, -80), (Sum.inl 6, 60), (Sum.inl 2, -460), (Sum.inl 35, 320), (Sum.inl 3, 320), (Sum.inl 13, 640), (Sum.inl 52, 320), (Sum.inl 1, -580), (Sum.inr 909, 5760), (Sum.inr 911, 5760), (Sum.inr 914, 5760), (Sum.inr 931, 5760), (Sum.inr 1024, 5760), (Sum.inr 1327, 5760), (Sum.inr 1333, 5760), (Sum.inr 2323, 5760), (Sum.inr 2327, 5760), (Sum.inr 2340, 5760), (Sum.inr 2423, 5760), (Sum.inr 2430, 5760), (Sum.inr 2471, 5760), (Sum.inr 2573, 5760), (Sum.inr 2575, 5760), (Sum.inr 2600, 5760), (Sum.inr 2754, 5760)]

theorem reindexCheck1674 : Integer.Sparse.reindex keyMap MixedData.row1674 = numericRow1674 := by decide +kernel

theorem numericCheck1674 (x : Master → ℝ) : Integer.Sparse.eval numericRow1674 x =
    (5760 : ℝ) * reducedSource1674 x := by
  norm_num [numericRow1674, reducedSource1674, Integer.Sparse.eval, Sparse.eval, nodeValue909, nodeValue911, nodeValue914, nodeValue931, nodeValue1024, nodeValue1327, nodeValue1333, nodeValue1340, nodeValue1413, nodeValue2323, nodeValue2327, nodeValue2340, nodeValue2423, nodeValue2430, nodeValue2471, nodeValue2528, nodeValue2532, nodeValue2573, nodeValue2574, nodeValue2575, nodeValue2600, nodeValue2602, nodeValue2754, nodeValue2755, nodeValue3109, nodeValue3204, nodeValue3207, nodeValue3213, nodeValue3229]
  ring

noncomputable def reducedSource1675 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1670 x + ((1 : ℝ) * Sparse.eval nodeValue1684 x + ((1 : ℝ) * Sparse.eval nodeValue1685 x + ((1 : ℝ) * Sparse.eval nodeValue1686 x + ((1 : ℝ) * Sparse.eval nodeValue1688 x + ((1 : ℝ) * Sparse.eval nodeValue1689 x + ((1 : ℝ) * Sparse.eval nodeValue1690 x + ((1 : ℝ) * Sparse.eval nodeValue1744 x + ((1 : ℝ) * Sparse.eval nodeValue1750 x + ((1 : ℝ) * Sparse.eval nodeValue2147 x + ((1 : ℝ) * Sparse.eval nodeValue2164 x + ((1 : ℝ) * Sparse.eval nodeValue2165 x + ((1 : ℝ) * Sparse.eval nodeValue2181 x + ((1 : ℝ) * Sparse.eval nodeValue2182 x + ((1 : ℝ) * Sparse.eval nodeValue2198 x + ((1 : ℝ) * Sparse.eval nodeValue2201 x + ((1 : ℝ) * Sparse.eval nodeValue2202 x + ((1 : ℝ) * Sparse.eval nodeValue2223 x + ((2 : ℝ) * Sparse.eval nodeValue2224 x + ((1 : ℝ) * Sparse.eval nodeValue2225 x + ((1 : ℝ) * Sparse.eval nodeValue2227 x + ((1 : ℝ) * Sparse.eval nodeValue2287 x + ((1 : ℝ) * Sparse.eval nodeValue2290 x + ((1 : ℝ) * Sparse.eval nodeValue2291 x + ((1 : ℝ) * Sparse.eval nodeValue2681 x + ((1 : ℝ) * Sparse.eval nodeValue2700 x + ((1 : ℝ) * Sparse.eval nodeValue2735 x + ((1 : ℝ) * Sparse.eval nodeValue2738 x + ((1 : ℝ) * Sparse.eval nodeValue2739 x + 0))))))))))))))))))))))))))))

def numericRow1675 : Integer.Sparse Master := [(Sum.inr 1670, 1), (Sum.inr 1684, 1), (Sum.inr 1685, 1), (Sum.inr 1686, 1), (Sum.inr 1688, 1), (Sum.inr 1689, 1), (Sum.inr 1690, 1), (Sum.inr 1744, 1), (Sum.inr 1750, 1), (Sum.inr 2147, 1), (Sum.inr 2164, 1), (Sum.inr 2165, 1), (Sum.inr 2181, 1), (Sum.inr 2182, 1), (Sum.inr 2198, 1), (Sum.inr 2201, 1), (Sum.inr 2202, 1), (Sum.inr 2223, 1), (Sum.inr 2224, 2), (Sum.inr 2225, 1), (Sum.inr 2287, 1), (Sum.inr 2290, 1), (Sum.inr 2681, 1), (Sum.inr 2700, 1), (Sum.inr 2735, 1), (Sum.inr 2738, 1), (Sum.inr 2739, 1)]

theorem reindexCheck1675 : Integer.Sparse.reindex keyMap MixedData.row1675 = numericRow1675 := by decide +kernel

theorem numericCheck1675 (x : Master → ℝ) : Integer.Sparse.eval numericRow1675 x =
    (1 : ℝ) * reducedSource1675 x := by
  norm_num [numericRow1675, reducedSource1675, Integer.Sparse.eval, Sparse.eval, nodeValue1670, nodeValue1684, nodeValue1685, nodeValue1686, nodeValue1688, nodeValue1689, nodeValue1690, nodeValue1744, nodeValue1750, nodeValue2147, nodeValue2164, nodeValue2165, nodeValue2181, nodeValue2182, nodeValue2198, nodeValue2201, nodeValue2202, nodeValue2223, nodeValue2224, nodeValue2225, nodeValue2227, nodeValue2287, nodeValue2290, nodeValue2291, nodeValue2681, nodeValue2700, nodeValue2735, nodeValue2738, nodeValue2739]

noncomputable def reducedSource1676 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue913 x + ((1 : ℝ) * Sparse.eval nodeValue1796 x + ((1 : ℝ) * Sparse.eval nodeValue1956 x + ((1 : ℝ) * Sparse.eval nodeValue1979 x + ((1 : ℝ) * Sparse.eval nodeValue2025 x + ((1 : ℝ) * Sparse.eval nodeValue2029 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

def numericRow1676 : Integer.Sparse Master := [(Sum.inr 913, 1), (Sum.inr 1796, 1), (Sum.inr 1956, 1), (Sum.inr 1979, 1), (Sum.inr 2025, 1), (Sum.inr 2029, 1), (Sum.inr 4083, -1)]

theorem reindexCheck1676 : Integer.Sparse.reindex keyMap MixedData.row1676 = numericRow1676 := by decide +kernel

theorem numericCheck1676 (x : Master → ℝ) : Integer.Sparse.eval numericRow1676 x =
    (1 : ℝ) * reducedSource1676 x := by
  norm_num [numericRow1676, reducedSource1676, Integer.Sparse.eval, Sparse.eval, nodeValue913, nodeValue1796, nodeValue1956, nodeValue1979, nodeValue2025, nodeValue2029, nodeValue4083]

noncomputable def reducedSource1677 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1326 x + ((1 : ℝ) * Sparse.eval nodeValue1956 x + ((1 : ℝ) * Sparse.eval nodeValue1964 x + ((2 : ℝ) * Sparse.eval nodeValue2025 x + ((1 : ℝ) * Sparse.eval nodeValue2923 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow1677 : Integer.Sparse Master := [(Sum.inr 1326, 1), (Sum.inr 1956, 1), (Sum.inr 1964, 1), (Sum.inr 2025, 2), (Sum.inr 2923, 1), (Sum.inr 4083, -1)]

theorem reindexCheck1677 : Integer.Sparse.reindex keyMap MixedData.row1677 = numericRow1677 := by decide +kernel

theorem numericCheck1677 (x : Master → ℝ) : Integer.Sparse.eval numericRow1677 x =
    (1 : ℝ) * reducedSource1677 x := by
  norm_num [numericRow1677, reducedSource1677, Integer.Sparse.eval, Sparse.eval, nodeValue1326, nodeValue1956, nodeValue1964, nodeValue2025, nodeValue2923, nodeValue4083]

noncomputable def reducedSource1678 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue930 x + ((1 : ℝ) * Sparse.eval nodeValue1812 x + ((1 : ℝ) * Sparse.eval nodeValue1964 x + ((2 : ℝ) * Sparse.eval nodeValue2025 x + ((1 : ℝ) * Sparse.eval nodeValue2057 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow1678 : Integer.Sparse Master := [(Sum.inr 930, 1), (Sum.inr 1812, 1), (Sum.inr 1964, 1), (Sum.inr 2025, 2), (Sum.inr 4083, -1)]

theorem reindexCheck1678 : Integer.Sparse.reindex keyMap MixedData.row1678 = numericRow1678 := by decide +kernel

theorem numericCheck1678 (x : Master → ℝ) : Integer.Sparse.eval numericRow1678 x =
    (1 : ℝ) * reducedSource1678 x := by
  norm_num [numericRow1678, reducedSource1678, Integer.Sparse.eval, Sparse.eval, nodeValue930, nodeValue1812, nodeValue1964, nodeValue2025, nodeValue2057, nodeValue4083]

noncomputable def reducedSource1679 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4414 x + ((1 : ℝ) * Sparse.eval nodeValue4418 x + ((1 : ℝ) * Sparse.eval nodeValue4420 x + ((1 : ℝ) * Sparse.eval nodeValue4425 x + ((1 : ℝ) * Sparse.eval nodeValue4486 x + ((1 : ℝ) * Sparse.eval nodeValue4729 x + ((1 : ℝ) * Sparse.eval nodeValue4741 x + ((1 : ℝ) * Sparse.eval nodeValue4742 x + ((1 : ℝ) * Sparse.eval nodeValue4747 x + ((1 : ℝ) * Sparse.eval nodeValue4779 x + ((1 : ℝ) * Sparse.eval nodeValue4780 x + ((1 : ℝ) * Sparse.eval nodeValue4783 x + ((1 : ℝ) * Sparse.eval nodeValue4792 x + ((1 : ℝ) * Sparse.eval nodeValue4793 x + ((1 : ℝ) * Sparse.eval nodeValue4804 x + ((2 : ℝ) * Sparse.eval nodeValue4807 x + ((2 : ℝ) * Sparse.eval nodeValue4808 x + ((1 : ℝ) * Sparse.eval nodeValue4817 x + ((1 : ℝ) * Sparse.eval nodeValue4819 x + ((1 : ℝ) * Sparse.eval nodeValue4824 x + ((1 : ℝ) * Sparse.eval nodeValue4841 x + ((1 : ℝ) * Sparse.eval nodeValue4843 x + ((1 : ℝ) * Sparse.eval nodeValue4853 x + ((1 : ℝ) * Sparse.eval nodeValue4871 x + ((2 : ℝ) * Sparse.eval nodeValue5078 x + ((1 : ℝ) * Sparse.eval nodeValue5128 x + ((1 : ℝ) * Sparse.eval nodeValue5174 x + 0))))))))))))))))))))))))))

def numericRow1679 : Integer.Sparse Master := [(Sum.inl 0, 19), (Sum.inl 5, 20), (Sum.inl 6, 5), (Sum.inl 2, -30), (Sum.inl 1, -50), (Sum.inr 999, -2160), (Sum.inr 1602, -2160), (Sum.inr 1898, -2160), (Sum.inr 1915, -2160), (Sum.inr 1926, -2160), (Sum.inr 1940, -2160), (Sum.inr 1946, -2160), (Sum.inr 1948, -2160), (Sum.inr 1987, -2160), (Sum.inr 1996, -2160), (Sum.inr 2022, -2160), (Sum.inr 2025, -4320), (Sum.inr 2062, -2160), (Sum.inr 2112, -2160), (Sum.inr 2203, -2160), (Sum.inr 2224, -4320), (Sum.inr 2230, -2160), (Sum.inr 2287, -2160), (Sum.inr 2485, -4320), (Sum.inr 3481, -4320), (Sum.inr 3615, -2160), (Sum.inr 4414, 8640), (Sum.inr 4420, 8640), (Sum.inr 4425, 8640), (Sum.inr 4486, 8640), (Sum.inr 4780, 8640), (Sum.inr 4783, 8640), (Sum.inr 4792, 8640), (Sum.inr 4793, 8640), (Sum.inr 4808, 17280), (Sum.inr 4817, 8640), (Sum.inr 4819, 8640), (Sum.inr 4824, 8640), (Sum.inr 4853, 8640), (Sum.inr 5128, 8640)]

theorem reindexCheck1679 : Integer.Sparse.reindex keyMap MixedData.row1679 = numericRow1679 := by decide +kernel

theorem numericCheck1679 (x : Master → ℝ) : Integer.Sparse.eval numericRow1679 x =
    (8640 : ℝ) * reducedSource1679 x := by
  norm_num [numericRow1679, reducedSource1679, Integer.Sparse.eval, Sparse.eval, nodeValue4414, nodeValue4418, nodeValue4420, nodeValue4425, nodeValue4486, nodeValue4729, nodeValue4741, nodeValue4742, nodeValue4747, nodeValue4779, nodeValue4780, nodeValue4783, nodeValue4792, nodeValue4793, nodeValue4804, nodeValue4807, nodeValue4808, nodeValue4817, nodeValue4819, nodeValue4824, nodeValue4841, nodeValue4843, nodeValue4853, nodeValue4871, nodeValue5078, nodeValue5128, nodeValue5174]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
