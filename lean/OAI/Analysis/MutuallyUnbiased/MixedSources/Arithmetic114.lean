import OAI.Analysis.MutuallyUnbiased.MixedData.Source14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values84
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1824 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2456 x + ((1 : ℝ) * Sparse.eval nodeValue2756 x + ((1 : ℝ) * Sparse.eval nodeValue3680 x + ((1 : ℝ) * Sparse.eval nodeValue3776 x + ((2 : ℝ) * Sparse.eval nodeValue3796 x + ((-1 : ℝ) * Sparse.eval nodeValue4090 x + 0)))))

def numericRow1824 : Integer.Sparse Master := [(Sum.inr 2456, 1), (Sum.inr 2756, 1), (Sum.inr 3680, 1), (Sum.inr 3776, 1), (Sum.inr 3796, 2), (Sum.inr 4090, -1)]

theorem reindexCheck1824 : Integer.Sparse.reindex keyMap MixedData.row1824 = numericRow1824 := by decide +kernel

theorem numericCheck1824 (x : Master → ℝ) : Integer.Sparse.eval numericRow1824 x =
    (1 : ℝ) * reducedSource1824 x := by
  norm_num [numericRow1824, reducedSource1824, Integer.Sparse.eval, Sparse.eval, nodeValue2456, nodeValue2756, nodeValue3680, nodeValue3776, nodeValue3796, nodeValue4090]

noncomputable def reducedSource1825 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4529 x + ((1 : ℝ) * Sparse.eval nodeValue4534 x + ((1 : ℝ) * Sparse.eval nodeValue4536 x + ((1 : ℝ) * Sparse.eval nodeValue4553 x + ((1 : ℝ) * Sparse.eval nodeValue4592 x + ((1 : ℝ) * Sparse.eval nodeValue4664 x + ((1 : ℝ) * Sparse.eval nodeValue4670 x + ((1 : ℝ) * Sparse.eval nodeValue4682 x + ((1 : ℝ) * Sparse.eval nodeValue4853 x + ((1 : ℝ) * Sparse.eval nodeValue4931 x + ((1 : ℝ) * Sparse.eval nodeValue4934 x + ((1 : ℝ) * Sparse.eval nodeValue4949 x + ((1 : ℝ) * Sparse.eval nodeValue4954 x + ((1 : ℝ) * Sparse.eval nodeValue4965 x + ((1 : ℝ) * Sparse.eval nodeValue5038 x + ((1 : ℝ) * Sparse.eval nodeValue5042 x + ((1 : ℝ) * Sparse.eval nodeValue5072 x + ((1 : ℝ) * Sparse.eval nodeValue5074 x + ((1 : ℝ) * Sparse.eval nodeValue5075 x + ((1 : ℝ) * Sparse.eval nodeValue5101 x + ((1 : ℝ) * Sparse.eval nodeValue5105 x + ((1 : ℝ) * Sparse.eval nodeValue5129 x + ((1 : ℝ) * Sparse.eval nodeValue5188 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5260 x + ((1 : ℝ) * Sparse.eval nodeValue5355 x + ((1 : ℝ) * Sparse.eval nodeValue5378 x + ((1 : ℝ) * Sparse.eval nodeValue5384 x + ((1 : ℝ) * Sparse.eval nodeValue5409 x + ((1 : ℝ) * Sparse.eval nodeValue5411 x + 0)))))))))))))))))))))))))))))

def numericRow1825 : Integer.Sparse Master := [(Sum.inr 1138, -1), (Sum.inr 2341, -1), (Sum.inr 2431, -1), (Sum.inr 2479, -1), (Sum.inr 2482, -1), (Sum.inr 2515, -1), (Sum.inr 2722, -1), (Sum.inr 3270, -1), (Sum.inr 3417, -1), (Sum.inr 3453, -1), (Sum.inr 3459, -1), (Sum.inr 3468, -1), (Sum.inr 3479, -1), (Sum.inr 3533, -1), (Sum.inr 3693, -1), (Sum.inr 3719, -1), (Sum.inr 3732, -1), (Sum.inr 3770, -1), (Sum.inr 3795, -1), (Sum.inr 3809, -1), (Sum.inr 3811, -1), (Sum.inr 3813, -1), (Sum.inr 4529, 4), (Sum.inr 4534, 4), (Sum.inr 4536, 4), (Sum.inr 4592, 4), (Sum.inr 4664, 4), (Sum.inr 4670, 4), (Sum.inr 4682, 4), (Sum.inr 4853, 4), (Sum.inr 4931, 4), (Sum.inr 4934, 4), (Sum.inr 4954, 4), (Sum.inr 4965, 4), (Sum.inr 5042, 4), (Sum.inr 5074, 4), (Sum.inr 5129, 4), (Sum.inr 5188, 4), (Sum.inr 5260, 4)]

theorem reindexCheck1825 : Integer.Sparse.reindex keyMap MixedData.row1825 = numericRow1825 := by decide +kernel

theorem numericCheck1825 (x : Master → ℝ) : Integer.Sparse.eval numericRow1825 x =
    (4 : ℝ) * reducedSource1825 x := by
  norm_num [numericRow1825, reducedSource1825, Integer.Sparse.eval, Sparse.eval, nodeValue4529, nodeValue4534, nodeValue4536, nodeValue4553, nodeValue4592, nodeValue4664, nodeValue4670, nodeValue4682, nodeValue4853, nodeValue4931, nodeValue4934, nodeValue4949, nodeValue4954, nodeValue4965, nodeValue5038, nodeValue5042, nodeValue5072, nodeValue5074, nodeValue5075, nodeValue5101, nodeValue5105, nodeValue5129, nodeValue5188, nodeValue5258, nodeValue5260, nodeValue5355, nodeValue5378, nodeValue5384, nodeValue5409, nodeValue5411]
  ring

noncomputable def reducedSource1826 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2147 x + ((1 : ℝ) * Sparse.eval nodeValue2149 x + ((1 : ℝ) * Sparse.eval nodeValue2153 x + ((1 : ℝ) * Sparse.eval nodeValue2164 x + ((1 : ℝ) * Sparse.eval nodeValue2259 x + ((1 : ℝ) * Sparse.eval nodeValue3258 x + ((1 : ℝ) * Sparse.eval nodeValue3268 x + ((1 : ℝ) * Sparse.eval nodeValue3270 x + ((1 : ℝ) * Sparse.eval nodeValue3295 x + ((1 : ℝ) * Sparse.eval nodeValue3406 x + ((1 : ℝ) * Sparse.eval nodeValue3415 x + ((1 : ℝ) * Sparse.eval nodeValue3417 x + ((1 : ℝ) * Sparse.eval nodeValue3452 x + ((1 : ℝ) * Sparse.eval nodeValue3453 x + ((1 : ℝ) * Sparse.eval nodeValue3459 x + ((1 : ℝ) * Sparse.eval nodeValue3462 x + ((1 : ℝ) * Sparse.eval nodeValue3463 x + ((1 : ℝ) * Sparse.eval nodeValue3468 x + ((1 : ℝ) * Sparse.eval nodeValue3470 x + ((1 : ℝ) * Sparse.eval nodeValue3475 x + ((1 : ℝ) * Sparse.eval nodeValue3479 x + ((1 : ℝ) * Sparse.eval nodeValue3516 x + ((1 : ℝ) * Sparse.eval nodeValue3533 x + ((1 : ℝ) * Sparse.eval nodeValue3538 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3770 x + ((1 : ℝ) * Sparse.eval nodeValue3795 x + ((1 : ℝ) * Sparse.eval nodeValue3807 x + ((1 : ℝ) * Sparse.eval nodeValue3811 x + ((1 : ℝ) * Sparse.eval nodeValue3813 x + 0)))))))))))))))))))))))))))))

def numericRow1826 : Integer.Sparse Master := [(Sum.inr 2147, 1), (Sum.inr 2149, 1), (Sum.inr 2153, 1), (Sum.inr 2164, 1), (Sum.inr 2259, 1), (Sum.inr 3258, 1), (Sum.inr 3268, 1), (Sum.inr 3270, 1), (Sum.inr 3295, 1), (Sum.inr 3406, 1), (Sum.inr 3415, 1), (Sum.inr 3417, 1), (Sum.inr 3452, 1), (Sum.inr 3453, 1), (Sum.inr 3459, 1), (Sum.inr 3462, 1), (Sum.inr 3463, 1), (Sum.inr 3468, 1), (Sum.inr 3475, 1), (Sum.inr 3479, 1), (Sum.inr 3516, 1), (Sum.inr 3533, 1), (Sum.inr 3538, 1), (Sum.inr 3540, 1), (Sum.inr 3770, 1), (Sum.inr 3795, 1), (Sum.inr 3811, 1), (Sum.inr 3813, 1)]

theorem reindexCheck1826 : Integer.Sparse.reindex keyMap MixedData.row1826 = numericRow1826 := by decide +kernel

theorem numericCheck1826 (x : Master → ℝ) : Integer.Sparse.eval numericRow1826 x =
    (1 : ℝ) * reducedSource1826 x := by
  norm_num [numericRow1826, reducedSource1826, Integer.Sparse.eval, Sparse.eval, nodeValue2147, nodeValue2149, nodeValue2153, nodeValue2164, nodeValue2259, nodeValue3258, nodeValue3268, nodeValue3270, nodeValue3295, nodeValue3406, nodeValue3415, nodeValue3417, nodeValue3452, nodeValue3453, nodeValue3459, nodeValue3462, nodeValue3463, nodeValue3468, nodeValue3470, nodeValue3475, nodeValue3479, nodeValue3516, nodeValue3533, nodeValue3538, nodeValue3540, nodeValue3770, nodeValue3795, nodeValue3807, nodeValue3811, nodeValue3813]

noncomputable def reducedSource1827 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2321 x + ((1 : ℝ) * Sparse.eval nodeValue2325 x + ((1 : ℝ) * Sparse.eval nodeValue2327 x + ((1 : ℝ) * Sparse.eval nodeValue2341 x + ((1 : ℝ) * Sparse.eval nodeValue2488 x + ((1 : ℝ) * Sparse.eval nodeValue3693 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1827 : Integer.Sparse Master := [(Sum.inr 2321, 1), (Sum.inr 2325, 1), (Sum.inr 2327, 1), (Sum.inr 2341, 1), (Sum.inr 2488, 1), (Sum.inr 3693, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1827 : Integer.Sparse.reindex keyMap MixedData.row1827 = numericRow1827 := by decide +kernel

theorem numericCheck1827 (x : Master → ℝ) : Integer.Sparse.eval numericRow1827 x =
    (1 : ℝ) * reducedSource1827 x := by
  norm_num [numericRow1827, reducedSource1827, Integer.Sparse.eval, Sparse.eval, nodeValue2321, nodeValue2325, nodeValue2327, nodeValue2341, nodeValue2488, nodeValue3693, nodeValue4092]

noncomputable def reducedSource1828 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4530 x + ((2 : ℝ) * Sparse.eval nodeValue4535 x + ((1 : ℝ) * Sparse.eval nodeValue4554 x + ((1 : ℝ) * Sparse.eval nodeValue4593 x + ((2 : ℝ) * Sparse.eval nodeValue4930 x + ((1 : ℝ) * Sparse.eval nodeValue4932 x + ((2 : ℝ) * Sparse.eval nodeValue4935 x + ((2 : ℝ) * Sparse.eval nodeValue4944 x + ((1 : ℝ) * Sparse.eval nodeValue4950 x + ((1 : ℝ) * Sparse.eval nodeValue5039 x + ((1 : ℝ) * Sparse.eval nodeValue5043 x + ((2 : ℝ) * Sparse.eval nodeValue5073 x + ((2 : ℝ) * Sparse.eval nodeValue5078 x + ((2 : ℝ) * Sparse.eval nodeValue5104 x + ((1 : ℝ) * Sparse.eval nodeValue5130 x + ((1 : ℝ) * Sparse.eval nodeValue5189 x + ((2 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5356 x + ((1 : ℝ) * Sparse.eval nodeValue5393 x + ((1 : ℝ) * Sparse.eval nodeValue5404 x + ((2 : ℝ) * Sparse.eval nodeValue5410 x + 0))))))))))))))))))))

def numericRow1828 : Integer.Sparse Master := [(Sum.inr 1139, -1), (Sum.inr 2342, -1), (Sum.inr 2432, -1), (Sum.inr 2480, -2), (Sum.inr 2485, -2), (Sum.inr 2723, -2), (Sum.inr 3274, -1), (Sum.inr 3421, -1), (Sum.inr 3456, -1), (Sum.inr 3467, -2), (Sum.inr 3481, -2), (Sum.inr 3544, -2), (Sum.inr 3694, -1), (Sum.inr 3773, -1), (Sum.inr 3779, -1), (Sum.inr 3790, -1), (Sum.inr 3797, -1), (Sum.inr 3815, -1), (Sum.inr 4530, 4), (Sum.inr 4535, 8), (Sum.inr 4593, 4), (Sum.inr 4930, 8), (Sum.inr 4935, 8), (Sum.inr 4944, 8), (Sum.inr 5043, 4), (Sum.inr 5189, 4)]

theorem reindexCheck1828 : Integer.Sparse.reindex keyMap MixedData.row1828 = numericRow1828 := by decide +kernel

theorem numericCheck1828 (x : Master → ℝ) : Integer.Sparse.eval numericRow1828 x =
    (4 : ℝ) * reducedSource1828 x := by
  norm_num [numericRow1828, reducedSource1828, Integer.Sparse.eval, Sparse.eval, nodeValue4530, nodeValue4535, nodeValue4554, nodeValue4593, nodeValue4930, nodeValue4932, nodeValue4935, nodeValue4944, nodeValue4950, nodeValue5039, nodeValue5043, nodeValue5073, nodeValue5078, nodeValue5104, nodeValue5130, nodeValue5189, nodeValue5259, nodeValue5356, nodeValue5393, nodeValue5404, nodeValue5410]
  ring

noncomputable def reducedSource1829 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3261 x + ((2 : ℝ) * Sparse.eval nodeValue3272 x + ((1 : ℝ) * Sparse.eval nodeValue3274 x + ((1 : ℝ) * Sparse.eval nodeValue3297 x + ((2 : ℝ) * Sparse.eval nodeValue3408 x + ((1 : ℝ) * Sparse.eval nodeValue3409 x + ((2 : ℝ) * Sparse.eval nodeValue3413 x + ((2 : ℝ) * Sparse.eval nodeValue3419 x + ((1 : ℝ) * Sparse.eval nodeValue3421 x + ((1 : ℝ) * Sparse.eval nodeValue3456 x + ((1 : ℝ) * Sparse.eval nodeValue3465 x + ((2 : ℝ) * Sparse.eval nodeValue3467 x + ((2 : ℝ) * Sparse.eval nodeValue3481 x + ((2 : ℝ) * Sparse.eval nodeValue3483 x + ((1 : ℝ) * Sparse.eval nodeValue3520 x + ((1 : ℝ) * Sparse.eval nodeValue3542 x + ((2 : ℝ) * Sparse.eval nodeValue3544 x + ((1 : ℝ) * Sparse.eval nodeValue3773 x + ((1 : ℝ) * Sparse.eval nodeValue3797 x + ((1 : ℝ) * Sparse.eval nodeValue3815 x + ((2 : ℝ) * Sparse.eval nodeValue3816 x + 0))))))))))))))))))))

def numericRow1829 : Integer.Sparse Master := [(Sum.inr 3261, 1), (Sum.inr 3272, 2), (Sum.inr 3274, 1), (Sum.inr 3297, 1), (Sum.inr 3408, 2), (Sum.inr 3413, 2), (Sum.inr 3419, 2), (Sum.inr 3421, 1), (Sum.inr 3456, 1), (Sum.inr 3465, 1), (Sum.inr 3467, 2), (Sum.inr 3481, 2), (Sum.inr 3542, 1), (Sum.inr 3544, 2), (Sum.inr 3773, 1), (Sum.inr 3797, 1), (Sum.inr 3815, 1)]

theorem reindexCheck1829 : Integer.Sparse.reindex keyMap MixedData.row1829 = numericRow1829 := by decide +kernel

theorem numericCheck1829 (x : Master → ℝ) : Integer.Sparse.eval numericRow1829 x =
    (1 : ℝ) * reducedSource1829 x := by
  norm_num [numericRow1829, reducedSource1829, Integer.Sparse.eval, Sparse.eval, nodeValue3261, nodeValue3272, nodeValue3274, nodeValue3297, nodeValue3408, nodeValue3409, nodeValue3413, nodeValue3419, nodeValue3421, nodeValue3456, nodeValue3465, nodeValue3467, nodeValue3481, nodeValue3483, nodeValue3520, nodeValue3542, nodeValue3544, nodeValue3773, nodeValue3797, nodeValue3815, nodeValue3816]

noncomputable def reducedSource1830 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2322 x + ((2 : ℝ) * Sparse.eval nodeValue2326 x + ((1 : ℝ) * Sparse.eval nodeValue2342 x + ((1 : ℝ) * Sparse.eval nodeValue2489 x + ((1 : ℝ) * Sparse.eval nodeValue3694 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow1830 : Integer.Sparse Master := [(Sum.inr 2326, 2), (Sum.inr 2342, 1), (Sum.inr 2489, 1), (Sum.inr 3694, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1830 : Integer.Sparse.reindex keyMap MixedData.row1830 = numericRow1830 := by decide +kernel

theorem numericCheck1830 (x : Master → ℝ) : Integer.Sparse.eval numericRow1830 x =
    (1 : ℝ) * reducedSource1830 x := by
  norm_num [numericRow1830, reducedSource1830, Integer.Sparse.eval, Sparse.eval, nodeValue2322, nodeValue2326, nodeValue2342, nodeValue2489, nodeValue3694, nodeValue4091]

noncomputable def reducedSource1831 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4548 x + ((1 : ℝ) * Sparse.eval nodeValue4557 x + ((1 : ℝ) * Sparse.eval nodeValue4560 x + ((1 : ℝ) * Sparse.eval nodeValue4611 x + ((2 : ℝ) * Sparse.eval nodeValue4681 x + ((1 : ℝ) * Sparse.eval nodeValue4692 x + ((2 : ℝ) * Sparse.eval nodeValue4699 x + ((1 : ℝ) * Sparse.eval nodeValue4705 x + ((1 : ℝ) * Sparse.eval nodeValue4841 x + ((1 : ℝ) * Sparse.eval nodeValue4881 x + ((2 : ℝ) * Sparse.eval nodeValue4945 x + ((2 : ℝ) * Sparse.eval nodeValue5035 x + ((2 : ℝ) * Sparse.eval nodeValue5099 x + ((2 : ℝ) * Sparse.eval nodeValue5103 x + ((2 : ℝ) * Sparse.eval nodeValue5140 x + ((2 : ℝ) * Sparse.eval nodeValue5228 x + ((1 : ℝ) * Sparse.eval nodeValue5238 x + ((1 : ℝ) * Sparse.eval nodeValue5272 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5276 x + ((1 : ℝ) * Sparse.eval nodeValue5302 x + 0))))))))))))))))))))

def numericRow1831 : Integer.Sparse Master := [(Sum.inr 1143, -1), (Sum.inr 1807, -2), (Sum.inr 1818, -1), (Sum.inr 2151, -2), (Sum.inr 2167, -1), (Sum.inr 2168, -1), (Sum.inr 2509, -2), (Sum.inr 2672, -2), (Sum.inr 2686, -1), (Sum.inr 2704, -2), (Sum.inr 2740, -2), (Sum.inr 3054, -1), (Sum.inr 3391, -2), (Sum.inr 3397, -1), (Sum.inr 3626, -1), (Sum.inr 4548, 8), (Sum.inr 4560, 4), (Sum.inr 4611, 4), (Sum.inr 4699, 8), (Sum.inr 4705, 4), (Sum.inr 4881, 4), (Sum.inr 4945, 8), (Sum.inr 5035, 8), (Sum.inr 5103, 8), (Sum.inr 5140, 8), (Sum.inr 5276, 4)]

theorem reindexCheck1831 : Integer.Sparse.reindex keyMap MixedData.row1831 = numericRow1831 := by decide +kernel

theorem numericCheck1831 (x : Master → ℝ) : Integer.Sparse.eval numericRow1831 x =
    (4 : ℝ) * reducedSource1831 x := by
  norm_num [numericRow1831, reducedSource1831, Integer.Sparse.eval, Sparse.eval, nodeValue4548, nodeValue4557, nodeValue4560, nodeValue4611, nodeValue4681, nodeValue4692, nodeValue4699, nodeValue4705, nodeValue4841, nodeValue4881, nodeValue4945, nodeValue5035, nodeValue5099, nodeValue5103, nodeValue5140, nodeValue5228, nodeValue5238, nodeValue5272, nodeValue5274, nodeValue5276, nodeValue5302]
  ring

noncomputable def reducedSource1832 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2151 x + ((1 : ℝ) * Sparse.eval nodeValue2167 x + ((1 : ℝ) * Sparse.eval nodeValue2168 x + ((1 : ℝ) * Sparse.eval nodeValue2228 x + ((2 : ℝ) * Sparse.eval nodeValue2256 x + ((1 : ℝ) * Sparse.eval nodeValue2258 x + ((1 : ℝ) * Sparse.eval nodeValue2267 x + ((1 : ℝ) * Sparse.eval nodeValue2286 x + ((2 : ℝ) * Sparse.eval nodeValue2652 x + ((2 : ℝ) * Sparse.eval nodeValue2657 x + ((2 : ℝ) * Sparse.eval nodeValue2658 x + ((2 : ℝ) * Sparse.eval nodeValue2670 x + ((2 : ℝ) * Sparse.eval nodeValue2672 x + ((1 : ℝ) * Sparse.eval nodeValue2683 x + ((1 : ℝ) * Sparse.eval nodeValue2686 x + ((2 : ℝ) * Sparse.eval nodeValue2704 x + ((1 : ℝ) * Sparse.eval nodeValue2740 x + ((1 : ℝ) * Sparse.eval nodeValue2742 x + ((2 : ℝ) * Sparse.eval nodeValue3024 x + ((1 : ℝ) * Sparse.eval nodeValue3052 x + ((1 : ℝ) * Sparse.eval nodeValue3054 x + 0))))))))))))))))))))

def numericRow1832 : Integer.Sparse Master := [(Sum.inr 2151, 2), (Sum.inr 2167, 1), (Sum.inr 2168, 1), (Sum.inr 2256, 2), (Sum.inr 2258, 1), (Sum.inr 2267, 1), (Sum.inr 2286, 1), (Sum.inr 2652, 2), (Sum.inr 2657, 2), (Sum.inr 2658, 2), (Sum.inr 2670, 2), (Sum.inr 2672, 2), (Sum.inr 2683, 1), (Sum.inr 2686, 1), (Sum.inr 2704, 2), (Sum.inr 2740, 1), (Sum.inr 3024, 2), (Sum.inr 3052, 1), (Sum.inr 3054, 1)]

theorem reindexCheck1832 : Integer.Sparse.reindex keyMap MixedData.row1832 = numericRow1832 := by decide +kernel

theorem numericCheck1832 (x : Master → ℝ) : Integer.Sparse.eval numericRow1832 x =
    (1 : ℝ) * reducedSource1832 x := by
  norm_num [numericRow1832, reducedSource1832, Integer.Sparse.eval, Sparse.eval, nodeValue2151, nodeValue2167, nodeValue2168, nodeValue2228, nodeValue2256, nodeValue2258, nodeValue2267, nodeValue2286, nodeValue2652, nodeValue2657, nodeValue2658, nodeValue2670, nodeValue2672, nodeValue2683, nodeValue2686, nodeValue2704, nodeValue2740, nodeValue2742, nodeValue3024, nodeValue3052, nodeValue3054]

noncomputable def reducedSource1833 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4092 x + ((2 : ℝ) * Sparse.eval nodeValue4549 x + ((1 : ℝ) * Sparse.eval nodeValue4558 x + ((1 : ℝ) * Sparse.eval nodeValue4559 x + ((1 : ℝ) * Sparse.eval nodeValue4612 x + ((2 : ℝ) * Sparse.eval nodeValue4943 x + ((2 : ℝ) * Sparse.eval nodeValue4946 x + ((1 : ℝ) * Sparse.eval nodeValue4952 x + ((1 : ℝ) * Sparse.eval nodeValue4953 x + ((2 : ℝ) * Sparse.eval nodeValue4972 x + ((2 : ℝ) * Sparse.eval nodeValue5036 x + ((2 : ℝ) * Sparse.eval nodeValue5101 x + ((2 : ℝ) * Sparse.eval nodeValue5102 x + ((1 : ℝ) * Sparse.eval nodeValue5107 x + ((1 : ℝ) * Sparse.eval nodeValue5109 x + ((2 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + ((2 : ℝ) * Sparse.eval nodeValue5367 x + ((1 : ℝ) * Sparse.eval nodeValue5371 x + ((1 : ℝ) * Sparse.eval nodeValue5413 x + 0))))))))))))))))))))

def numericRow1833 : Integer.Sparse Master := [(Sum.inr 1134, -2), (Sum.inr 1144, -1), (Sum.inr 1145, -1), (Sum.inr 1246, -1), (Sum.inr 2334, -2), (Sum.inr 2337, -2), (Sum.inr 2344, -1), (Sum.inr 2345, -1), (Sum.inr 2428, -2), (Sum.inr 2434, -2), (Sum.inr 2512, -2), (Sum.inr 2519, -1), (Sum.inr 2561, -2), (Sum.inr 2743, -1), (Sum.inr 3265, -2), (Sum.inr 3276, -1), (Sum.inr 3277, -1), (Sum.inr 3301, -1), (Sum.inr 3411, -2), (Sum.inr 3412, -2), (Sum.inr 3422, -1), (Sum.inr 3423, -1), (Sum.inr 3450, -2), (Sum.inr 3457, -2), (Sum.inr 3471, -2), (Sum.inr 3486, -1), (Sum.inr 3522, -2), (Sum.inr 3548, -1), (Sum.inr 4092, 4)]

theorem reindexCheck1833 : Integer.Sparse.reindex keyMap MixedData.row1833 = numericRow1833 := by decide +kernel

theorem numericCheck1833 (x : Master → ℝ) : Integer.Sparse.eval numericRow1833 x =
    (4 : ℝ) * reducedSource1833 x := by
  norm_num [numericRow1833, reducedSource1833, Integer.Sparse.eval, Sparse.eval, nodeValue4092, nodeValue4549, nodeValue4558, nodeValue4559, nodeValue4612, nodeValue4943, nodeValue4946, nodeValue4952, nodeValue4953, nodeValue4972, nodeValue5036, nodeValue5101, nodeValue5102, nodeValue5107, nodeValue5109, nodeValue5141, nodeValue5274, nodeValue5275, nodeValue5367, nodeValue5371, nodeValue5413]
  ring

noncomputable def reducedSource1834 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue3265 x + ((1 : ℝ) * Sparse.eval nodeValue3276 x + ((1 : ℝ) * Sparse.eval nodeValue3277 x + ((1 : ℝ) * Sparse.eval nodeValue3301 x + ((2 : ℝ) * Sparse.eval nodeValue3411 x + ((2 : ℝ) * Sparse.eval nodeValue3412 x + ((1 : ℝ) * Sparse.eval nodeValue3422 x + ((1 : ℝ) * Sparse.eval nodeValue3423 x + ((2 : ℝ) * Sparse.eval nodeValue3450 x + ((2 : ℝ) * Sparse.eval nodeValue3457 x + ((2 : ℝ) * Sparse.eval nodeValue3470 x + ((2 : ℝ) * Sparse.eval nodeValue3471 x + ((1 : ℝ) * Sparse.eval nodeValue3484 x + ((1 : ℝ) * Sparse.eval nodeValue3486 x + ((2 : ℝ) * Sparse.eval nodeValue3522 x + ((1 : ℝ) * Sparse.eval nodeValue3547 x + ((1 : ℝ) * Sparse.eval nodeValue3548 x + ((2 : ℝ) * Sparse.eval nodeValue3766 x + ((1 : ℝ) * Sparse.eval nodeValue3775 x + ((1 : ℝ) * Sparse.eval nodeValue3817 x + ((1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))))))))))))))))

def numericRow1834 : Integer.Sparse Master := [(Sum.inr 3265, 2), (Sum.inr 3276, 1), (Sum.inr 3277, 1), (Sum.inr 3301, 1), (Sum.inr 3411, 2), (Sum.inr 3412, 2), (Sum.inr 3422, 1), (Sum.inr 3423, 1), (Sum.inr 3450, 2), (Sum.inr 3457, 2), (Sum.inr 3471, 2), (Sum.inr 3486, 1), (Sum.inr 3522, 2), (Sum.inr 3548, 1), (Sum.inr 4092, 1)]

theorem reindexCheck1834 : Integer.Sparse.reindex keyMap MixedData.row1834 = numericRow1834 := by decide +kernel

theorem numericCheck1834 (x : Master → ℝ) : Integer.Sparse.eval numericRow1834 x =
    (1 : ℝ) * reducedSource1834 x := by
  norm_num [numericRow1834, reducedSource1834, Integer.Sparse.eval, Sparse.eval, nodeValue3265, nodeValue3276, nodeValue3277, nodeValue3301, nodeValue3411, nodeValue3412, nodeValue3422, nodeValue3423, nodeValue3450, nodeValue3457, nodeValue3470, nodeValue3471, nodeValue3484, nodeValue3486, nodeValue3522, nodeValue3547, nodeValue3548, nodeValue3766, nodeValue3775, nodeValue3817, nodeValue4092]

noncomputable def reducedSource1835 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4088 x + ((1 : ℝ) * Sparse.eval nodeValue4522 x + ((2 : ℝ) * Sparse.eval nodeValue4526 x + ((1 : ℝ) * Sparse.eval nodeValue4539 x + ((1 : ℝ) * Sparse.eval nodeValue4586 x + ((2 : ℝ) * Sparse.eval nodeValue4902 x + ((2 : ℝ) * Sparse.eval nodeValue4907 x + ((2 : ℝ) * Sparse.eval nodeValue4918 x + ((1 : ℝ) * Sparse.eval nodeValue4926 x + ((1 : ℝ) * Sparse.eval nodeValue4937 x + ((2 : ℝ) * Sparse.eval nodeValue5000 x + ((1 : ℝ) * Sparse.eval nodeValue5025 x + ((1 : ℝ) * Sparse.eval nodeValue5032 x + ((2 : ℝ) * Sparse.eval nodeValue5056 x + ((1 : ℝ) * Sparse.eval nodeValue5063 x + ((2 : ℝ) * Sparse.eval nodeValue5095 x + ((1 : ℝ) * Sparse.eval nodeValue5126 x + ((2 : ℝ) * Sparse.eval nodeValue5248 x + ((1 : ℝ) * Sparse.eval nodeValue5323 x + ((1 : ℝ) * Sparse.eval nodeValue5327 x + ((2 : ℝ) * Sparse.eval nodeValue5367 x + 0))))))))))))))))))))

def numericRow1835 : Integer.Sparse Master := [(Sum.inr 1106, -1), (Sum.inr 1110, -2), (Sum.inr 1124, -1), (Sum.inr 1205, -1), (Sum.inr 2295, -2), (Sum.inr 2300, -2), (Sum.inr 2316, -1), (Sum.inr 2329, -1), (Sum.inr 2385, -2), (Sum.inr 2424, -1), (Sum.inr 2459, -2), (Sum.inr 2505, -2), (Sum.inr 2541, -1), (Sum.inr 2705, -2), (Sum.inr 3249, -1), (Sum.inr 3252, -2), (Sum.inr 3254, -1), (Sum.inr 3284, -1), (Sum.inr 3315, -2), (Sum.inr 3325, -2), (Sum.inr 3353, -2), (Sum.inr 3398, -1), (Sum.inr 3402, -1), (Sum.inr 3429, -2), (Sum.inr 3440, -1), (Sum.inr 3448, -2), (Sum.inr 3487, -1), (Sum.inr 3498, -2), (Sum.inr 4088, 4)]

theorem reindexCheck1835 : Integer.Sparse.reindex keyMap MixedData.row1835 = numericRow1835 := by decide +kernel

theorem numericCheck1835 (x : Master → ℝ) : Integer.Sparse.eval numericRow1835 x =
    (4 : ℝ) * reducedSource1835 x := by
  norm_num [numericRow1835, reducedSource1835, Integer.Sparse.eval, Sparse.eval, nodeValue4088, nodeValue4522, nodeValue4526, nodeValue4539, nodeValue4586, nodeValue4902, nodeValue4907, nodeValue4918, nodeValue4926, nodeValue4937, nodeValue5000, nodeValue5025, nodeValue5032, nodeValue5056, nodeValue5063, nodeValue5095, nodeValue5126, nodeValue5248, nodeValue5323, nodeValue5327, nodeValue5367]
  ring

noncomputable def reducedSource1836 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2379 x + ((1 : ℝ) * Sparse.eval nodeValue3646 x + ((2 : ℝ) * Sparse.eval nodeValue3718 x + ((1 : ℝ) * Sparse.eval nodeValue3757 x + ((1 : ℝ) * Sparse.eval nodeValue3759 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0)))))

def numericRow1836 : Integer.Sparse Master := [(Sum.inr 2379, 1), (Sum.inr 3646, 1), (Sum.inr 3718, 2), (Sum.inr 3757, 1), (Sum.inr 3759, 1), (Sum.inr 4088, -1)]

theorem reindexCheck1836 : Integer.Sparse.reindex keyMap MixedData.row1836 = numericRow1836 := by decide +kernel

theorem numericCheck1836 (x : Master → ℝ) : Integer.Sparse.eval numericRow1836 x =
    (1 : ℝ) * reducedSource1836 x := by
  norm_num [numericRow1836, reducedSource1836, Integer.Sparse.eval, Sparse.eval, nodeValue2379, nodeValue3646, nodeValue3718, nodeValue3757, nodeValue3759, nodeValue4088]

noncomputable def reducedSource1837 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2388 x + ((1 : ℝ) * Sparse.eval nodeValue3654 x + ((1 : ℝ) * Sparse.eval nodeValue3681 x + ((1 : ℝ) * Sparse.eval nodeValue3702 x + ((1 : ℝ) * Sparse.eval nodeValue3766 x + ((1 : ℝ) * Sparse.eval nodeValue3767 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0))))))

def numericRow1837 : Integer.Sparse Master := [(Sum.inr 2388, 1), (Sum.inr 3681, 1), (Sum.inr 3702, 1), (Sum.inr 3767, 1), (Sum.inr 4088, -1)]

theorem reindexCheck1837 : Integer.Sparse.reindex keyMap MixedData.row1837 = numericRow1837 := by decide +kernel

theorem numericCheck1837 (x : Master → ℝ) : Integer.Sparse.eval numericRow1837 x =
    (1 : ℝ) * reducedSource1837 x := by
  norm_num [numericRow1837, reducedSource1837, Integer.Sparse.eval, Sparse.eval, nodeValue2388, nodeValue3654, nodeValue3681, nodeValue3702, nodeValue3766, nodeValue3767, nodeValue4088]

noncomputable def reducedSource1838 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4089 x + ((2 : ℝ) * Sparse.eval nodeValue4515 x + ((2 : ℝ) * Sparse.eval nodeValue4520 x + ((1 : ℝ) * Sparse.eval nodeValue4575 x + ((4 : ℝ) * Sparse.eval nodeValue4913 x + ((2 : ℝ) * Sparse.eval nodeValue4915 x + ((2 : ℝ) * Sparse.eval nodeValue4924 x + ((2 : ℝ) * Sparse.eval nodeValue4985 x + ((4 : ℝ) * Sparse.eval nodeValue5015 x + ((2 : ℝ) * Sparse.eval nodeValue5021 x + ((2 : ℝ) * Sparse.eval nodeValue5125 x + ((2 : ℝ) * Sparse.eval nodeValue5238 x + ((2 : ℝ) * Sparse.eval nodeValue5327 x + ((2 : ℝ) * Sparse.eval nodeValue5371 x + 0)))))))))))))

def numericRow1838 : Integer.Sparse Master := [(Sum.inr 1099, -2), (Sum.inr 1104, -2), (Sum.inr 1193, -1), (Sum.inr 2306, -4), (Sum.inr 2370, -2), (Sum.inr 2400, -4), (Sum.inr 2407, -2), (Sum.inr 2539, -2), (Sum.inr 2686, -2), (Sum.inr 3233, -2), (Sum.inr 3237, -2), (Sum.inr 3248, -1), (Sum.inr 3318, -4), (Sum.inr 3334, -2), (Sum.inr 3344, -4), (Sum.inr 3360, -2), (Sum.inr 3372, -2), (Sum.inr 3397, -2), (Sum.inr 4089, 4)]

theorem reindexCheck1838 : Integer.Sparse.reindex keyMap MixedData.row1838 = numericRow1838 := by decide +kernel

theorem numericCheck1838 (x : Master → ℝ) : Integer.Sparse.eval numericRow1838 x =
    (4 : ℝ) * reducedSource1838 x := by
  norm_num [numericRow1838, reducedSource1838, Integer.Sparse.eval, Sparse.eval, nodeValue4089, nodeValue4515, nodeValue4520, nodeValue4575, nodeValue4913, nodeValue4915, nodeValue4924, nodeValue4985, nodeValue5015, nodeValue5021, nodeValue5125, nodeValue5238, nodeValue5327, nodeValue5371]
  ring

noncomputable def reducedSource1839 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4368 x + ((1 : ℝ) * Sparse.eval nodeValue4373 x + ((1 : ℝ) * Sparse.eval nodeValue4375 x + ((1 : ℝ) * Sparse.eval nodeValue4466 x + ((2 : ℝ) * Sparse.eval nodeValue4687 x + ((1 : ℝ) * Sparse.eval nodeValue4694 x + ((2 : ℝ) * Sparse.eval nodeValue4700 x + ((1 : ℝ) * Sparse.eval nodeValue4704 x + ((2 : ℝ) * Sparse.eval nodeValue4773 x + ((2 : ℝ) * Sparse.eval nodeValue4776 x + ((2 : ℝ) * Sparse.eval nodeValue4810 x + ((2 : ℝ) * Sparse.eval nodeValue4865 x + ((2 : ℝ) * Sparse.eval nodeValue4867 x + ((1 : ℝ) * Sparse.eval nodeValue4868 x + ((1 : ℝ) * Sparse.eval nodeValue4872 x + ((1 : ℝ) * Sparse.eval nodeValue4894 x + ((1 : ℝ) * Sparse.eval nodeValue4896 x + ((2 : ℝ) * Sparse.eval nodeValue5264 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5297 x + ((1 : ℝ) * Sparse.eval nodeValue5300 x + 0))))))))))))))))))))

def numericRow1839 : Integer.Sparse Master := [(Sum.inr 1049, -1), (Sum.inr 1738, -1), (Sum.inr 2028, -2), (Sum.inr 2106, -2), (Sum.inr 2109, -1), (Sum.inr 2215, -2), (Sum.inr 2242, -2), (Sum.inr 2261, -1), (Sum.inr 2266, -1), (Sum.inr 2278, -1), (Sum.inr 2765, -1), (Sum.inr 3582, -1), (Sum.inr 4368, 8), (Sum.inr 4373, 4), (Sum.inr 4375, 4), (Sum.inr 4687, 8), (Sum.inr 4694, 4), (Sum.inr 4700, 8), (Sum.inr 4704, 4), (Sum.inr 4773, 8), (Sum.inr 4776, 8), (Sum.inr 4867, 8), (Sum.inr 4872, 4), (Sum.inr 5264, 8), (Sum.inr 5297, 4), (Sum.inr 5300, 4)]

theorem reindexCheck1839 : Integer.Sparse.reindex keyMap MixedData.row1839 = numericRow1839 := by decide +kernel

theorem numericCheck1839 (x : Master → ℝ) : Integer.Sparse.eval numericRow1839 x =
    (4 : ℝ) * reducedSource1839 x := by
  norm_num [numericRow1839, reducedSource1839, Integer.Sparse.eval, Sparse.eval, nodeValue4368, nodeValue4373, nodeValue4375, nodeValue4466, nodeValue4687, nodeValue4694, nodeValue4700, nodeValue4704, nodeValue4773, nodeValue4776, nodeValue4810, nodeValue4865, nodeValue4867, nodeValue4868, nodeValue4872, nodeValue4894, nodeValue4896, nodeValue5264, nodeValue5291, nodeValue5297, nodeValue5300]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
