import OAI.Analysis.MutuallyUnbiased.MixedData.Source1
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values85
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource128 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1080 x + ((2 : ℝ) * Sparse.eval nodeValue2052 x + ((1 : ℝ) * Sparse.eval nodeValue2290 x + ((2 : ℝ) * Sparse.eval nodeValue2292 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

def numericRow128 : Integer.Sparse Master := [(Sum.inr 1080, 1), (Sum.inr 2052, 2), (Sum.inr 2290, 1), (Sum.inr 4085, -1)]

theorem reindexCheck128 : Integer.Sparse.reindex keyMap MixedData.row128 = numericRow128 := by decide +kernel

theorem numericCheck128 (x : Master → ℝ) : Integer.Sparse.eval numericRow128 x =
    (1 : ℝ) * reducedSource128 x := by
  norm_num [numericRow128, reducedSource128, Integer.Sparse.eval, Sparse.eval, nodeValue1080, nodeValue2052, nodeValue2290, nodeValue2292, nodeValue4085]

noncomputable def reducedSource129 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue4591 x + ((1 : ℝ) * Sparse.eval nodeValue4594 x + ((2 : ℝ) * Sparse.eval nodeValue4608 x + ((2 : ℝ) * Sparse.eval nodeValue4609 x + ((4 : ℝ) * Sparse.eval nodeValue5075 x + ((1 : ℝ) * Sparse.eval nodeValue5107 x + ((2 : ℝ) * Sparse.eval nodeValue5127 x + ((4 : ℝ) * Sparse.eval nodeValue5147 x + ((1 : ℝ) * Sparse.eval nodeValue5201 x + ((4 : ℝ) * Sparse.eval nodeValue5258 x + ((2 : ℝ) * Sparse.eval nodeValue5274 x + ((2 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5441 x + 0))))))))))))

def numericRow129 : Integer.Sparse Master := [(Sum.inr 1242, -1), (Sum.inr 2482, -2), (Sum.inr 2722, -2), (Sum.inr 2765, -1), (Sum.inr 3300, -1), (Sum.inr 3468, -2), (Sum.inr 3533, -2), (Sum.inr 3582, -1), (Sum.inr 4591, 8), (Sum.inr 4594, 2), (Sum.inr 4609, 4), (Sum.inr 5147, 8), (Sum.inr 5201, 2)]

theorem reindexCheck129 : Integer.Sparse.reindex keyMap MixedData.row129 = numericRow129 := by decide +kernel

theorem numericCheck129 (x : Master → ℝ) : Integer.Sparse.eval numericRow129 x =
    (2 : ℝ) * reducedSource129 x := by
  norm_num [numericRow129, reducedSource129, Integer.Sparse.eval, Sparse.eval, nodeValue4591, nodeValue4594, nodeValue4608, nodeValue4609, nodeValue5075, nodeValue5107, nodeValue5127, nodeValue5147, nodeValue5201, nodeValue5258, nodeValue5274, nodeValue5291, nodeValue5441]
  ring

noncomputable def reducedSource130 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue1217 x + ((1 : ℝ) * Sparse.eval nodeValue1221 x + ((2 : ℝ) * Sparse.eval nodeValue1243 x + ((2 : ℝ) * Sparse.eval nodeValue1269 x + ((4 : ℝ) * Sparse.eval nodeValue2865 x + ((1 : ℝ) * Sparse.eval nodeValue2886 x + ((2 : ℝ) * Sparse.eval nodeValue2914 x + ((4 : ℝ) * Sparse.eval nodeValue2939 x + ((1 : ℝ) * Sparse.eval nodeValue3002 x + ((4 : ℝ) * Sparse.eval nodeValue3089 x + ((2 : ℝ) * Sparse.eval nodeValue3103 x + ((2 : ℝ) * Sparse.eval nodeValue3112 x + ((1 : ℝ) * Sparse.eval nodeValue4037 x + 0))))))))))))

def numericRow130 : Integer.Sparse Master := [(Sum.inl 0, -4), (Sum.inl 2, 5), (Sum.inl 1, 5), (Sum.inr 1217, 180), (Sum.inr 1221, 45), (Sum.inr 1243, 90), (Sum.inr 2865, 180), (Sum.inr 2886, 45)]

theorem reindexCheck130 : Integer.Sparse.reindex keyMap MixedData.row130 = numericRow130 := by decide +kernel

theorem numericCheck130 (x : Master → ℝ) : Integer.Sparse.eval numericRow130 x =
    (45 : ℝ) * reducedSource130 x := by
  norm_num [numericRow130, reducedSource130, Integer.Sparse.eval, Sparse.eval, nodeValue1217, nodeValue1221, nodeValue1243, nodeValue1269, nodeValue2865, nodeValue2886, nodeValue2914, nodeValue2939, nodeValue3002, nodeValue3089, nodeValue3103, nodeValue3112, nodeValue4037]
  ring

noncomputable def reducedSource131 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue3291 x + ((1 : ℝ) * Sparse.eval nodeValue3298 x + ((2 : ℝ) * Sparse.eval nodeValue3300 x + ((2 : ℝ) * Sparse.eval nodeValue3302 x + ((4 : ℝ) * Sparse.eval nodeValue3468 x + ((1 : ℝ) * Sparse.eval nodeValue3484 x + ((2 : ℝ) * Sparse.eval nodeValue3513 x + ((4 : ℝ) * Sparse.eval nodeValue3530 x + ((4 : ℝ) * Sparse.eval nodeValue3533 x + ((2 : ℝ) * Sparse.eval nodeValue3547 x + ((1 : ℝ) * Sparse.eval nodeValue3579 x + ((2 : ℝ) * Sparse.eval nodeValue3582 x + ((1 : ℝ) * Sparse.eval nodeValue3860 x + 0))))))))))))

def numericRow131 : Integer.Sparse Master := [(Sum.inr 3291, 4), (Sum.inr 3298, 1), (Sum.inr 3300, 2), (Sum.inr 3302, 2), (Sum.inr 3468, 4), (Sum.inr 3530, 4), (Sum.inr 3533, 4), (Sum.inr 3579, 1), (Sum.inr 3582, 2)]

theorem reindexCheck131 : Integer.Sparse.reindex keyMap MixedData.row131 = numericRow131 := by decide +kernel

theorem numericCheck131 (x : Master → ℝ) : Integer.Sparse.eval numericRow131 x =
    (1 : ℝ) * reducedSource131 x := by
  norm_num [numericRow131, reducedSource131, Integer.Sparse.eval, Sparse.eval, nodeValue3291, nodeValue3298, nodeValue3300, nodeValue3302, nodeValue3468, nodeValue3484, nodeValue3513, nodeValue3530, nodeValue3533, nodeValue3547, nodeValue3579, nodeValue3582, nodeValue3860]

noncomputable def reducedSource132 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue2726 x + ((1 : ℝ) * Sparse.eval nodeValue2742 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((1 : ℝ) * Sparse.eval nodeValue3905 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow132 : Integer.Sparse Master := [(Sum.inr 2722, 2), (Sum.inr 2726, 1), (Sum.inr 2765, 1), (Sum.inr 4092, -1)]

theorem reindexCheck132 : Integer.Sparse.reindex keyMap MixedData.row132 = numericRow132 := by decide +kernel

theorem numericCheck132 (x : Master → ℝ) : Integer.Sparse.eval numericRow132 x =
    (1 : ℝ) * reducedSource132 x := by
  norm_num [numericRow132, reducedSource132, Integer.Sparse.eval, Sparse.eval, nodeValue2722, nodeValue2726, nodeValue2742, nodeValue2765, nodeValue3905, nodeValue4092]

noncomputable def reducedSource133 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1215 x + ((1 : ℝ) * Sparse.eval nodeValue1221 x + ((1 : ℝ) * Sparse.eval nodeValue1242 x + ((1 : ℝ) * Sparse.eval nodeValue1264 x + ((1 : ℝ) * Sparse.eval nodeValue2726 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow133 : Integer.Sparse Master := [(Sum.inr 1215, 2), (Sum.inr 1221, 1), (Sum.inr 1242, 1), (Sum.inr 1264, 1), (Sum.inr 2726, 1), (Sum.inr 4092, -1)]

theorem reindexCheck133 : Integer.Sparse.reindex keyMap MixedData.row133 = numericRow133 := by decide +kernel

theorem numericCheck133 (x : Master → ℝ) : Integer.Sparse.eval numericRow133 x =
    (1 : ℝ) * reducedSource133 x := by
  norm_num [numericRow133, reducedSource133, Integer.Sparse.eval, Sparse.eval, nodeValue1215, nodeValue1221, nodeValue1242, nodeValue1264, nodeValue2726, nodeValue4092]

noncomputable def reducedSource134 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1242 x + ((2 : ℝ) * Sparse.eval nodeValue2482 x + ((1 : ℝ) * Sparse.eval nodeValue2517 x + ((1 : ℝ) * Sparse.eval nodeValue2726 x + ((1 : ℝ) * Sparse.eval nodeValue2742 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow134 : Integer.Sparse Master := [(Sum.inr 1242, 1), (Sum.inr 2482, 2), (Sum.inr 2726, 1), (Sum.inr 4092, -1)]

theorem reindexCheck134 : Integer.Sparse.reindex keyMap MixedData.row134 = numericRow134 := by decide +kernel

theorem numericCheck134 (x : Master → ℝ) : Integer.Sparse.eval numericRow134 x =
    (1 : ℝ) * reducedSource134 x := by
  norm_num [numericRow134, reducedSource134, Integer.Sparse.eval, Sparse.eval, nodeValue1242, nodeValue2482, nodeValue2517, nodeValue2726, nodeValue2742, nodeValue4092]

noncomputable def reducedSource135 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1264 x + ((2 : ℝ) * Sparse.eval nodeValue2569 x + ((1 : ℝ) * Sparse.eval nodeValue2635 x + ((1 : ℝ) * Sparse.eval nodeValue2726 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow135 : Integer.Sparse Master := [(Sum.inr 1264, 1), (Sum.inr 2569, 2), (Sum.inr 2635, 1), (Sum.inr 2726, 1), (Sum.inr 2765, 1), (Sum.inr 4092, -1)]

theorem reindexCheck135 : Integer.Sparse.reindex keyMap MixedData.row135 = numericRow135 := by decide +kernel

theorem numericCheck135 (x : Master → ℝ) : Integer.Sparse.eval numericRow135 x =
    (1 : ℝ) * reducedSource135 x := by
  norm_num [numericRow135, reducedSource135, Integer.Sparse.eval, Sparse.eval, nodeValue1264, nodeValue2569, nodeValue2635, nodeValue2726, nodeValue2765, nodeValue4092]

noncomputable def reducedSource136 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1215 x + ((1 : ℝ) * Sparse.eval nodeValue2482 x + ((1 : ℝ) * Sparse.eval nodeValue2542 x + ((1 : ℝ) * Sparse.eval nodeValue2569 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue2726 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow136 : Integer.Sparse Master := [(Sum.inr 1215, 1), (Sum.inr 2482, 1), (Sum.inr 2569, 1), (Sum.inr 2722, 1), (Sum.inr 2726, 1), (Sum.inr 4092, -1)]

theorem reindexCheck136 : Integer.Sparse.reindex keyMap MixedData.row136 = numericRow136 := by decide +kernel

theorem numericCheck136 (x : Master → ℝ) : Integer.Sparse.eval numericRow136 x =
    (1 : ℝ) * reducedSource136 x := by
  norm_num [numericRow136, reducedSource136, Integer.Sparse.eval, Sparse.eval, nodeValue1215, nodeValue2482, nodeValue2542, nodeValue2569, nodeValue2722, nodeValue2726, nodeValue4092]

noncomputable def reducedSource137 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue4401 x + ((1 : ℝ) * Sparse.eval nodeValue4405 x + ((2 : ℝ) * Sparse.eval nodeValue4428 x + ((2 : ℝ) * Sparse.eval nodeValue4460 x + ((4 : ℝ) * Sparse.eval nodeValue5000 x + ((1 : ℝ) * Sparse.eval nodeValue5021 x + ((2 : ℝ) * Sparse.eval nodeValue5047 x + ((4 : ℝ) * Sparse.eval nodeValue5075 x + ((1 : ℝ) * Sparse.eval nodeValue5171 x + ((4 : ℝ) * Sparse.eval nodeValue5259 x + ((2 : ℝ) * Sparse.eval nodeValue5275 x + ((2 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5491 x + 0))))))))))))

def numericRow137 : Integer.Sparse Master := [(Sum.inl 0, 23), (Sum.inl 5, 4), (Sum.inl 6, 1), (Sum.inl 2, -12), (Sum.inl 1, 56), (Sum.inr 982, -1728), (Sum.inr 986, -432), (Sum.inr 1009, -864), (Sum.inr 1043, -864), (Sum.inr 1617, -1728), (Sum.inr 1620, -432), (Sum.inr 1630, -864), (Sum.inr 1725, -864), (Sum.inr 2385, -1728), (Sum.inr 2407, -432), (Sum.inr 2449, -864), (Sum.inr 2482, -1728), (Sum.inr 2723, -1728), (Sum.inr 2743, -864), (Sum.inr 3353, -1728), (Sum.inr 3360, -432), (Sum.inr 3432, -864), (Sum.inr 3468, -1728), (Sum.inr 3544, -1728), (Sum.inr 3548, -864), (Sum.inr 3608, -432), (Sum.inr 3627, -864)]

theorem reindexCheck137 : Integer.Sparse.reindex keyMap MixedData.row137 = numericRow137 := by decide +kernel

theorem numericCheck137 (x : Master → ℝ) : Integer.Sparse.eval numericRow137 x =
    (1728 : ℝ) * reducedSource137 x := by
  norm_num [numericRow137, reducedSource137, Integer.Sparse.eval, Sparse.eval, nodeValue4401, nodeValue4405, nodeValue4428, nodeValue4460, nodeValue5000, nodeValue5021, nodeValue5047, nodeValue5075, nodeValue5171, nodeValue5259, nodeValue5275, nodeValue5293, nodeValue5491]
  ring

noncomputable def reducedSource138 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue982 x + ((1 : ℝ) * Sparse.eval nodeValue986 x + ((2 : ℝ) * Sparse.eval nodeValue1009 x + ((2 : ℝ) * Sparse.eval nodeValue1043 x + ((4 : ℝ) * Sparse.eval nodeValue2385 x + ((1 : ℝ) * Sparse.eval nodeValue2407 x + ((2 : ℝ) * Sparse.eval nodeValue2449 x + ((4 : ℝ) * Sparse.eval nodeValue2482 x + ((1 : ℝ) * Sparse.eval nodeValue2598 x + ((4 : ℝ) * Sparse.eval nodeValue2723 x + ((2 : ℝ) * Sparse.eval nodeValue2743 x + ((2 : ℝ) * Sparse.eval nodeValue2767 x + ((1 : ℝ) * Sparse.eval nodeValue4014 x + 0))))))))))))

def numericRow138 : Integer.Sparse Master := [(Sum.inl 0, -91), (Sum.inl 5, -20), (Sum.inl 6, -5), (Sum.inl 2, 60), (Sum.inl 1, -160), (Sum.inr 982, 8640), (Sum.inr 986, 2160), (Sum.inr 1009, 4320), (Sum.inr 1043, 4320), (Sum.inr 2385, 8640), (Sum.inr 2407, 2160), (Sum.inr 2449, 4320), (Sum.inr 2482, 8640), (Sum.inr 2723, 8640), (Sum.inr 2743, 4320)]

theorem reindexCheck138 : Integer.Sparse.reindex keyMap MixedData.row138 = numericRow138 := by decide +kernel

theorem numericCheck138 (x : Master → ℝ) : Integer.Sparse.eval numericRow138 x =
    (2160 : ℝ) * reducedSource138 x := by
  norm_num [numericRow138, reducedSource138, Integer.Sparse.eval, Sparse.eval, nodeValue982, nodeValue986, nodeValue1009, nodeValue1043, nodeValue2385, nodeValue2407, nodeValue2449, nodeValue2482, nodeValue2598, nodeValue2723, nodeValue2743, nodeValue2767, nodeValue4014]
  ring

noncomputable def reducedSource139 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue4832 x + ((1 : ℝ) * Sparse.eval nodeValue4837 x + ((2 : ℝ) * Sparse.eval nodeValue4845 x + ((2 : ℝ) * Sparse.eval nodeValue4897 x + ((4 : ℝ) * Sparse.eval nodeValue5222 x + ((1 : ℝ) * Sparse.eval nodeValue5235 x + ((2 : ℝ) * Sparse.eval nodeValue5239 x + ((4 : ℝ) * Sparse.eval nodeValue5252 x + ((5 : ℝ) * Sparse.eval nodeValue5261 x + ((2 : ℝ) * Sparse.eval nodeValue5268 x + ((2 : ℝ) * Sparse.eval nodeValue5296 x + ((1 : ℝ) * Sparse.eval nodeValue5312 x + 0)))))))))))

def numericRow139 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 2, 5), (Sum.inr 2052, -240), (Sum.inr 2065, -120), (Sum.inr 2193, -240), (Sum.inr 2218, -120), (Sum.inr 2726, -300), (Sum.inr 3545, -300), (Sum.inr 3634, -120), (Sum.inr 5222, 960), (Sum.inr 5235, 240), (Sum.inr 5252, 960), (Sum.inr 5268, 480)]

theorem reindexCheck139 : Integer.Sparse.reindex keyMap MixedData.row139 = numericRow139 := by decide +kernel

theorem numericCheck139 (x : Master → ℝ) : Integer.Sparse.eval numericRow139 x =
    (240 : ℝ) * reducedSource139 x := by
  norm_num [numericRow139, reducedSource139, Integer.Sparse.eval, Sparse.eval, nodeValue4832, nodeValue4837, nodeValue4845, nodeValue4897, nodeValue5222, nodeValue5235, nodeValue5239, nodeValue5252, nodeValue5261, nodeValue5268, nodeValue5296, nodeValue5312]
  ring

noncomputable def reducedSource140 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue2193 x + ((1 : ℝ) * Sparse.eval nodeValue2208 x + ((2 : ℝ) * Sparse.eval nodeValue2218 x + ((2 : ℝ) * Sparse.eval nodeValue2268 x + ((4 : ℝ) * Sparse.eval nodeValue2664 x + ((1 : ℝ) * Sparse.eval nodeValue2680 x + ((2 : ℝ) * Sparse.eval nodeValue2691 x + ((4 : ℝ) * Sparse.eval nodeValue2712 x + ((4 : ℝ) * Sparse.eval nodeValue2726 x + ((2 : ℝ) * Sparse.eval nodeValue2734 x + ((2 : ℝ) * Sparse.eval nodeValue2770 x + ((1 : ℝ) * Sparse.eval nodeValue2790 x + ((1 : ℝ) * Sparse.eval nodeValue3090 x + 0))))))))))))

def numericRow140 : Integer.Sparse Master := [(Sum.inl 0, -1), (Sum.inl 2, -5), (Sum.inr 2193, 160), (Sum.inr 2218, 80), (Sum.inr 2664, 160), (Sum.inr 2680, 40), (Sum.inr 2712, 160), (Sum.inr 2726, 160), (Sum.inr 2734, 80)]

theorem reindexCheck140 : Integer.Sparse.reindex keyMap MixedData.row140 = numericRow140 := by decide +kernel

theorem numericCheck140 (x : Master → ℝ) : Integer.Sparse.eval numericRow140 x =
    (40 : ℝ) * reducedSource140 x := by
  norm_num [numericRow140, reducedSource140, Integer.Sparse.eval, Sparse.eval, nodeValue2193, nodeValue2208, nodeValue2218, nodeValue2268, nodeValue2664, nodeValue2680, nodeValue2691, nodeValue2712, nodeValue2726, nodeValue2734, nodeValue2770, nodeValue2790, nodeValue3090]
  ring

noncomputable def reducedSource141 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue2712 x + ((1 : ℝ) * Sparse.eval nodeValue2726 x + ((2 : ℝ) * Sparse.eval nodeValue2734 x + ((2 : ℝ) * Sparse.eval nodeValue2770 x + ((4 : ℝ) * Sparse.eval nodeValue3031 x + ((1 : ℝ) * Sparse.eval nodeValue3046 x + ((2 : ℝ) * Sparse.eval nodeValue3061 x + ((4 : ℝ) * Sparse.eval nodeValue3082 x + ((4 : ℝ) * Sparse.eval nodeValue3090 x + ((2 : ℝ) * Sparse.eval nodeValue3095 x + ((2 : ℝ) * Sparse.eval nodeValue3114 x + ((1 : ℝ) * Sparse.eval nodeValue3126 x + ((1 : ℝ) * Sparse.eval nodeValue3215 x + 0))))))))))))

def numericRow141 : Integer.Sparse Master := [(Sum.inl 0, -1), (Sum.inl 2, -5), (Sum.inr 2712, 40), (Sum.inr 2726, 10), (Sum.inr 2734, 20), (Sum.inr 3031, 40), (Sum.inr 3046, 10)]

theorem reindexCheck141 : Integer.Sparse.reindex keyMap MixedData.row141 = numericRow141 := by decide +kernel

theorem numericCheck141 (x : Master → ℝ) : Integer.Sparse.eval numericRow141 x =
    (10 : ℝ) * reducedSource141 x := by
  norm_num [numericRow141, reducedSource141, Integer.Sparse.eval, Sparse.eval, nodeValue2712, nodeValue2726, nodeValue2734, nodeValue2770, nodeValue3031, nodeValue3046, nodeValue3061, nodeValue3082, nodeValue3090, nodeValue3095, nodeValue3114, nodeValue3126, nodeValue3215]
  ring

noncomputable def reducedSource142 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2052 x + ((1 : ℝ) * Sparse.eval nodeValue2056 x + ((1 : ℝ) * Sparse.eval nodeValue2065 x + ((1 : ℝ) * Sparse.eval nodeValue2292 x + ((1 : ℝ) * Sparse.eval nodeValue3545 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0)))))

def numericRow142 : Integer.Sparse Master := [(Sum.inr 2052, 2), (Sum.inr 2065, 1), (Sum.inr 3545, 1), (Sum.inr 4085, -1)]

theorem reindexCheck142 : Integer.Sparse.reindex keyMap MixedData.row142 = numericRow142 := by decide +kernel

theorem numericCheck142 (x : Master → ℝ) : Integer.Sparse.eval numericRow142 x =
    (1 : ℝ) * reducedSource142 x := by
  norm_num [numericRow142, reducedSource142, Integer.Sparse.eval, Sparse.eval, nodeValue2052, nodeValue2056, nodeValue2065, nodeValue2292, nodeValue3545, nodeValue4085]

noncomputable def reducedSource143 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4094 x + ((8 : ℝ) * Sparse.eval nodeValue4625 x + ((1 : ℝ) * Sparse.eval nodeValue4629 x + ((12 : ℝ) * Sparse.eval nodeValue5171 x + ((8 : ℝ) * Sparse.eval nodeValue5308 x + 0))))

def numericRow143 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 1, 5), (Sum.inr 3310, -240), (Sum.inr 3313, -30), (Sum.inr 3608, -360)]

theorem reindexCheck143 : Integer.Sparse.reindex keyMap MixedData.row143 = numericRow143 := by decide +kernel

theorem numericCheck143 (x : Master → ℝ) : Integer.Sparse.eval numericRow143 x =
    (120 : ℝ) * reducedSource143 x := by
  norm_num [numericRow143, reducedSource143, Integer.Sparse.eval, Sparse.eval, nodeValue4094, nodeValue4625, nodeValue4629, nodeValue5171, nodeValue5308]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
