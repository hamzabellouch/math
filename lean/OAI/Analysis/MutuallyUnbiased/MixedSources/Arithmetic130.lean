import OAI.Analysis.MutuallyUnbiased.MixedData.Source16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values85
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource2080 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4930 x + ((2 : ℝ) * Sparse.eval nodeValue4931 x + ((2 : ℝ) * Sparse.eval nodeValue4933 x + ((2 : ℝ) * Sparse.eval nodeValue4942 x + ((1 : ℝ) * Sparse.eval nodeValue5039 x + ((1 : ℝ) * Sparse.eval nodeValue5081 x + ((1 : ℝ) * Sparse.eval nodeValue5130 x + ((2 : ℝ) * Sparse.eval nodeValue5149 x + ((1 : ℝ) * Sparse.eval nodeValue5337 x + ((1 : ℝ) * Sparse.eval nodeValue5356 x + ((1 : ℝ) * Sparse.eval nodeValue5373 x + ((1 : ℝ) * Sparse.eval nodeValue5377 x + ((2 : ℝ) * Sparse.eval nodeValue5396 x + ((1 : ℝ) * Sparse.eval nodeValue5404 x + ((2 : ℝ) * Sparse.eval nodeValue5410 x + ((2 : ℝ) * Sparse.eval nodeValue5419 x + ((2 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5459 x + ((1 : ℝ) * Sparse.eval nodeValue5461 x + ((2 : ℝ) * Sparse.eval nodeValue5478 x + 0)))))))))))))))))))

def numericRow2080 : Integer.Sparse Master := [(Sum.inr 2432, -1), (Sum.inr 2489, -1), (Sum.inr 2924, -2), (Sum.inr 3456, -1), (Sum.inr 3482, -1), (Sum.inr 3605, -2), (Sum.inr 3672, -1), (Sum.inr 3694, -1), (Sum.inr 3709, -1), (Sum.inr 3756, -1), (Sum.inr 3773, -1), (Sum.inr 3790, -1), (Sum.inr 3792, -1), (Sum.inr 3815, -1), (Sum.inr 3838, -2), (Sum.inr 3843, -2), (Sum.inr 3974, -4), (Sum.inr 4930, 8), (Sum.inr 4931, 8), (Sum.inr 4933, 8), (Sum.inr 4942, 8), (Sum.inr 5377, 4), (Sum.inr 5419, 8), (Sum.inr 5461, 4)]

theorem reindexCheck2080 : Integer.Sparse.reindex keyMap MixedData.row2080 = numericRow2080 := by decide +kernel

theorem numericCheck2080 (x : Master → ℝ) : Integer.Sparse.eval numericRow2080 x =
    (4 : ℝ) * reducedSource2080 x := by
  norm_num [numericRow2080, reducedSource2080, Integer.Sparse.eval, Sparse.eval, nodeValue4930, nodeValue4931, nodeValue4933, nodeValue4942, nodeValue5039, nodeValue5081, nodeValue5130, nodeValue5149, nodeValue5337, nodeValue5356, nodeValue5373, nodeValue5377, nodeValue5396, nodeValue5404, nodeValue5410, nodeValue5419, nodeValue5424, nodeValue5459, nodeValue5461, nodeValue5478]
  ring

noncomputable def reducedSource2081 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue3406 x + ((2 : ℝ) * Sparse.eval nodeValue3407 x + ((2 : ℝ) * Sparse.eval nodeValue3408 x + ((2 : ℝ) * Sparse.eval nodeValue3414 x + ((1 : ℝ) * Sparse.eval nodeValue3456 x + ((1 : ℝ) * Sparse.eval nodeValue3482 x + ((1 : ℝ) * Sparse.eval nodeValue3520 x + ((2 : ℝ) * Sparse.eval nodeValue3605 x + ((1 : ℝ) * Sparse.eval nodeValue3756 x + ((1 : ℝ) * Sparse.eval nodeValue3773 x + ((1 : ℝ) * Sparse.eval nodeValue3792 x + ((2 : ℝ) * Sparse.eval nodeValue3798 x + ((1 : ℝ) * Sparse.eval nodeValue3815 x + ((2 : ℝ) * Sparse.eval nodeValue3816 x + ((1 : ℝ) * Sparse.eval nodeValue3835 x + ((2 : ℝ) * Sparse.eval nodeValue3842 x + ((2 : ℝ) * Sparse.eval nodeValue3843 x + ((1 : ℝ) * Sparse.eval nodeValue3951 x + ((1 : ℝ) * Sparse.eval nodeValue3973 x + ((2 : ℝ) * Sparse.eval nodeValue3974 x + 0)))))))))))))))))))

def numericRow2081 : Integer.Sparse Master := [(Sum.inr 3406, 2), (Sum.inr 3407, 2), (Sum.inr 3408, 2), (Sum.inr 3414, 2), (Sum.inr 3456, 1), (Sum.inr 3482, 1), (Sum.inr 3605, 2), (Sum.inr 3756, 1), (Sum.inr 3773, 1), (Sum.inr 3792, 1), (Sum.inr 3815, 1), (Sum.inr 3835, 1), (Sum.inr 3842, 2), (Sum.inr 3843, 2), (Sum.inr 3973, 1), (Sum.inr 3974, 2)]

theorem reindexCheck2081 : Integer.Sparse.reindex keyMap MixedData.row2081 = numericRow2081 := by decide +kernel

theorem numericCheck2081 (x : Master → ℝ) : Integer.Sparse.eval numericRow2081 x =
    (1 : ℝ) * reducedSource2081 x := by
  norm_num [numericRow2081, reducedSource2081, Integer.Sparse.eval, Sparse.eval, nodeValue3406, nodeValue3407, nodeValue3408, nodeValue3414, nodeValue3456, nodeValue3482, nodeValue3520, nodeValue3605, nodeValue3756, nodeValue3773, nodeValue3792, nodeValue3798, nodeValue3815, nodeValue3816, nodeValue3835, nodeValue3842, nodeValue3843, nodeValue3951, nodeValue3973, nodeValue3974]

noncomputable def reducedSource2082 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4756 x + ((1 : ℝ) * Sparse.eval nodeValue4757 x + ((1 : ℝ) * Sparse.eval nodeValue4768 x + ((2 : ℝ) * Sparse.eval nodeValue4795 x + ((2 : ℝ) * Sparse.eval nodeValue4933 x + ((1 : ℝ) * Sparse.eval nodeValue4947 x + ((2 : ℝ) * Sparse.eval nodeValue4955 x + ((1 : ℝ) * Sparse.eval nodeValue4967 x + ((1 : ℝ) * Sparse.eval nodeValue5076 x + ((1 : ℝ) * Sparse.eval nodeValue5184 x + ((2 : ℝ) * Sparse.eval nodeValue5338 x + ((2 : ℝ) * Sparse.eval nodeValue5348 x + ((2 : ℝ) * Sparse.eval nodeValue5352 x + ((2 : ℝ) * Sparse.eval nodeValue5354 x + ((1 : ℝ) * Sparse.eval nodeValue5366 x + ((1 : ℝ) * Sparse.eval nodeValue5403 x + ((2 : ℝ) * Sparse.eval nodeValue5406 x + ((1 : ℝ) * Sparse.eval nodeValue5408 x + ((1 : ℝ) * Sparse.eval nodeValue5414 x + ((2 : ℝ) * Sparse.eval nodeValue5429 x + ((1 : ℝ) * Sparse.eval nodeValue5472 x + 0))))))))))))))))))))

def numericRow2082 : Integer.Sparse Master := [(Sum.inr 2338, -1), (Sum.inr 2483, -1), (Sum.inr 2814, -1), (Sum.inr 3416, -1), (Sum.inr 3477, -1), (Sum.inr 3585, -1), (Sum.inr 3690, -2), (Sum.inr 3692, -2), (Sum.inr 3764, -2), (Sum.inr 3769, -2), (Sum.inr 3789, -1), (Sum.inr 3801, -2), (Sum.inr 3810, -1), (Sum.inr 3812, -2), (Sum.inr 3957, -2), (Sum.inr 4756, 4), (Sum.inr 4757, 4), (Sum.inr 4768, 4), (Sum.inr 4795, 8), (Sum.inr 4933, 8), (Sum.inr 4955, 8), (Sum.inr 5184, 4), (Sum.inr 5338, 8), (Sum.inr 5348, 8), (Sum.inr 5414, 4), (Sum.inr 5429, 8)]

theorem reindexCheck2082 : Integer.Sparse.reindex keyMap MixedData.row2082 = numericRow2082 := by decide +kernel

theorem numericCheck2082 (x : Master → ℝ) : Integer.Sparse.eval numericRow2082 x =
    (4 : ℝ) * reducedSource2082 x := by
  norm_num [numericRow2082, reducedSource2082, Integer.Sparse.eval, Sparse.eval, nodeValue4756, nodeValue4757, nodeValue4768, nodeValue4795, nodeValue4933, nodeValue4947, nodeValue4955, nodeValue4967, nodeValue5076, nodeValue5184, nodeValue5338, nodeValue5348, nodeValue5352, nodeValue5354, nodeValue5366, nodeValue5403, nodeValue5406, nodeValue5408, nodeValue5414, nodeValue5429, nodeValue5472]
  ring

noncomputable def reducedSource2083 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2176 x + ((1 : ℝ) * Sparse.eval nodeValue2178 x + ((1 : ℝ) * Sparse.eval nodeValue2181 x + ((2 : ℝ) * Sparse.eval nodeValue2213 x + ((2 : ℝ) * Sparse.eval nodeValue3414 x + ((1 : ℝ) * Sparse.eval nodeValue3416 x + ((1 : ℝ) * Sparse.eval nodeValue3477 x + ((2 : ℝ) * Sparse.eval nodeValue3508 x + ((1 : ℝ) * Sparse.eval nodeValue3524 x + ((1 : ℝ) * Sparse.eval nodeValue3585 x + ((2 : ℝ) * Sparse.eval nodeValue3755 x + ((2 : ℝ) * Sparse.eval nodeValue3764 x + ((1 : ℝ) * Sparse.eval nodeValue3765 x + ((2 : ℝ) * Sparse.eval nodeValue3768 x + ((2 : ℝ) * Sparse.eval nodeValue3769 x + ((1 : ℝ) * Sparse.eval nodeValue3806 x + ((1 : ℝ) * Sparse.eval nodeValue3810 x + ((2 : ℝ) * Sparse.eval nodeValue3812 x + ((1 : ℝ) * Sparse.eval nodeValue3869 x + ((2 : ℝ) * Sparse.eval nodeValue3874 x + ((1 : ℝ) * Sparse.eval nodeValue3957 x + 0))))))))))))))))))))

def numericRow2083 : Integer.Sparse Master := [(Sum.inr 2176, 1), (Sum.inr 2178, 1), (Sum.inr 2181, 1), (Sum.inr 2213, 2), (Sum.inr 3414, 2), (Sum.inr 3416, 1), (Sum.inr 3477, 1), (Sum.inr 3508, 2), (Sum.inr 3524, 1), (Sum.inr 3585, 1), (Sum.inr 3755, 2), (Sum.inr 3764, 2), (Sum.inr 3768, 2), (Sum.inr 3769, 2), (Sum.inr 3810, 1), (Sum.inr 3812, 2), (Sum.inr 3869, 1), (Sum.inr 3874, 2), (Sum.inr 3957, 1)]

theorem reindexCheck2083 : Integer.Sparse.reindex keyMap MixedData.row2083 = numericRow2083 := by decide +kernel

theorem numericCheck2083 (x : Master → ℝ) : Integer.Sparse.eval numericRow2083 x =
    (1 : ℝ) * reducedSource2083 x := by
  norm_num [numericRow2083, reducedSource2083, Integer.Sparse.eval, Sparse.eval, nodeValue2176, nodeValue2178, nodeValue2181, nodeValue2213, nodeValue3414, nodeValue3416, nodeValue3477, nodeValue3508, nodeValue3524, nodeValue3585, nodeValue3755, nodeValue3764, nodeValue3765, nodeValue3768, nodeValue3769, nodeValue3806, nodeValue3810, nodeValue3812, nodeValue3869, nodeValue3874, nodeValue3957]

noncomputable def reducedSource2084 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4930 x + ((1 : ℝ) * Sparse.eval nodeValue4932 x + ((1 : ℝ) * Sparse.eval nodeValue4933 x + ((1 : ℝ) * Sparse.eval nodeValue4941 x + ((1 : ℝ) * Sparse.eval nodeValue4954 x + ((1 : ℝ) * Sparse.eval nodeValue4955 x + ((1 : ℝ) * Sparse.eval nodeValue4958 x + ((1 : ℝ) * Sparse.eval nodeValue4968 x + ((1 : ℝ) * Sparse.eval nodeValue5040 x + ((1 : ℝ) * Sparse.eval nodeValue5067 x + ((1 : ℝ) * Sparse.eval nodeValue5073 x + ((1 : ℝ) * Sparse.eval nodeValue5152 x + ((1 : ℝ) * Sparse.eval nodeValue5185 x + ((1 : ℝ) * Sparse.eval nodeValue5338 x + ((1 : ℝ) * Sparse.eval nodeValue5340 x + ((1 : ℝ) * Sparse.eval nodeValue5348 x + ((2 : ℝ) * Sparse.eval nodeValue5352 x + ((1 : ℝ) * Sparse.eval nodeValue5354 x + ((1 : ℝ) * Sparse.eval nodeValue5356 x + ((1 : ℝ) * Sparse.eval nodeValue5366 x + ((1 : ℝ) * Sparse.eval nodeValue5369 x + ((1 : ℝ) * Sparse.eval nodeValue5401 x + ((1 : ℝ) * Sparse.eval nodeValue5405 x + ((1 : ℝ) * Sparse.eval nodeValue5408 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5470 x + ((1 : ℝ) * Sparse.eval nodeValue5471 x + ((1 : ℝ) * Sparse.eval nodeValue5472 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + 0))))))))))))))))))))))))))))

def numericRow2084 : Integer.Sparse Master := [(Sum.inr 2332, -1), (Sum.inr 2480, -1), (Sum.inr 2809, -1), (Sum.inr 2931, -1), (Sum.inr 3410, -1), (Sum.inr 3467, -1), (Sum.inr 3587, -1), (Sum.inr 3612, -1), (Sum.inr 3690, -2), (Sum.inr 3692, -1), (Sum.inr 3694, -1), (Sum.inr 3764, -2), (Sum.inr 3769, -1), (Sum.inr 3773, -1), (Sum.inr 3787, -1), (Sum.inr 3800, -1), (Sum.inr 3804, -1), (Sum.inr 3805, -1), (Sum.inr 3957, -2), (Sum.inr 3958, -1), (Sum.inr 3961, -1), (Sum.inr 4930, 4), (Sum.inr 4933, 4), (Sum.inr 4954, 4), (Sum.inr 4955, 4), (Sum.inr 4958, 4), (Sum.inr 5040, 4), (Sum.inr 5067, 4), (Sum.inr 5185, 4), (Sum.inr 5338, 4), (Sum.inr 5340, 4), (Sum.inr 5348, 4), (Sum.inr 5470, 4)]

theorem reindexCheck2084 : Integer.Sparse.reindex keyMap MixedData.row2084 = numericRow2084 := by decide +kernel

theorem numericCheck2084 (x : Master → ℝ) : Integer.Sparse.eval numericRow2084 x =
    (4 : ℝ) * reducedSource2084 x := by
  norm_num [numericRow2084, reducedSource2084, Integer.Sparse.eval, Sparse.eval, nodeValue4930, nodeValue4932, nodeValue4933, nodeValue4941, nodeValue4954, nodeValue4955, nodeValue4958, nodeValue4968, nodeValue5040, nodeValue5067, nodeValue5073, nodeValue5152, nodeValue5185, nodeValue5338, nodeValue5340, nodeValue5348, nodeValue5352, nodeValue5354, nodeValue5356, nodeValue5366, nodeValue5369, nodeValue5401, nodeValue5405, nodeValue5408, nodeValue5410, nodeValue5470, nodeValue5471, nodeValue5472, nodeValue5473]
  ring

noncomputable def reducedSource2085 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3408 x + ((1 : ℝ) * Sparse.eval nodeValue3409 x + ((1 : ℝ) * Sparse.eval nodeValue3410 x + ((1 : ℝ) * Sparse.eval nodeValue3414 x + ((1 : ℝ) * Sparse.eval nodeValue3452 x + ((1 : ℝ) * Sparse.eval nodeValue3454 x + ((1 : ℝ) * Sparse.eval nodeValue3467 x + ((1 : ℝ) * Sparse.eval nodeValue3476 x + ((1 : ℝ) * Sparse.eval nodeValue3508 x + ((1 : ℝ) * Sparse.eval nodeValue3511 x + ((1 : ℝ) * Sparse.eval nodeValue3529 x + ((1 : ℝ) * Sparse.eval nodeValue3587 x + ((1 : ℝ) * Sparse.eval nodeValue3612 x + ((1 : ℝ) * Sparse.eval nodeValue3755 x + ((1 : ℝ) * Sparse.eval nodeValue3763 x + ((2 : ℝ) * Sparse.eval nodeValue3764 x + ((1 : ℝ) * Sparse.eval nodeValue3765 x + ((1 : ℝ) * Sparse.eval nodeValue3768 x + ((1 : ℝ) * Sparse.eval nodeValue3769 x + ((1 : ℝ) * Sparse.eval nodeValue3773 x + ((1 : ℝ) * Sparse.eval nodeValue3774 x + ((1 : ℝ) * Sparse.eval nodeValue3804 x + ((1 : ℝ) * Sparse.eval nodeValue3805 x + ((1 : ℝ) * Sparse.eval nodeValue3806 x + ((1 : ℝ) * Sparse.eval nodeValue3816 x + ((1 : ℝ) * Sparse.eval nodeValue3955 x + ((1 : ℝ) * Sparse.eval nodeValue3956 x + ((1 : ℝ) * Sparse.eval nodeValue3957 x + ((1 : ℝ) * Sparse.eval nodeValue3961 x + 0))))))))))))))))))))))))))))

def numericRow2085 : Integer.Sparse Master := [(Sum.inr 3408, 1), (Sum.inr 3410, 1), (Sum.inr 3414, 1), (Sum.inr 3452, 1), (Sum.inr 3454, 1), (Sum.inr 3467, 1), (Sum.inr 3476, 1), (Sum.inr 3508, 1), (Sum.inr 3511, 1), (Sum.inr 3529, 1), (Sum.inr 3587, 1), (Sum.inr 3612, 1), (Sum.inr 3755, 1), (Sum.inr 3763, 1), (Sum.inr 3764, 2), (Sum.inr 3768, 1), (Sum.inr 3769, 1), (Sum.inr 3773, 1), (Sum.inr 3804, 1), (Sum.inr 3805, 1), (Sum.inr 3955, 1), (Sum.inr 3957, 1), (Sum.inr 3961, 1)]

theorem reindexCheck2085 : Integer.Sparse.reindex keyMap MixedData.row2085 = numericRow2085 := by decide +kernel

theorem numericCheck2085 (x : Master → ℝ) : Integer.Sparse.eval numericRow2085 x =
    (1 : ℝ) * reducedSource2085 x := by
  norm_num [numericRow2085, reducedSource2085, Integer.Sparse.eval, Sparse.eval, nodeValue3408, nodeValue3409, nodeValue3410, nodeValue3414, nodeValue3452, nodeValue3454, nodeValue3467, nodeValue3476, nodeValue3508, nodeValue3511, nodeValue3529, nodeValue3587, nodeValue3612, nodeValue3755, nodeValue3763, nodeValue3764, nodeValue3765, nodeValue3768, nodeValue3769, nodeValue3773, nodeValue3774, nodeValue3804, nodeValue3805, nodeValue3806, nodeValue3816, nodeValue3955, nodeValue3956, nodeValue3957, nodeValue3961]

noncomputable def reducedSource2086 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4929 x + ((2 : ℝ) * Sparse.eval nodeValue4931 x + ((1 : ℝ) * Sparse.eval nodeValue4939 x + ((1 : ℝ) * Sparse.eval nodeValue4956 x + ((2 : ℝ) * Sparse.eval nodeValue4957 x + ((1 : ℝ) * Sparse.eval nodeValue4971 x + ((1 : ℝ) * Sparse.eval nodeValue5072 x + ((1 : ℝ) * Sparse.eval nodeValue5112 x + ((2 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5187 x + ((2 : ℝ) * Sparse.eval nodeValue5339 x + ((2 : ℝ) * Sparse.eval nodeValue5353 x + ((2 : ℝ) * Sparse.eval nodeValue5355 x + ((1 : ℝ) * Sparse.eval nodeValue5365 x + ((2 : ℝ) * Sparse.eval nodeValue5367 x + ((1 : ℝ) * Sparse.eval nodeValue5400 x + ((1 : ℝ) * Sparse.eval nodeValue5405 x + ((2 : ℝ) * Sparse.eval nodeValue5409 x + ((1 : ℝ) * Sparse.eval nodeValue5414 x + ((2 : ℝ) * Sparse.eval nodeValue5428 x + ((1 : ℝ) * Sparse.eval nodeValue5471 x + 0))))))))))))))))))))

def numericRow2086 : Integer.Sparse Master := [(Sum.inr 2330, -1), (Sum.inr 2479, -1), (Sum.inr 2561, -2), (Sum.inr 2807, -1), (Sum.inr 3404, -1), (Sum.inr 3459, -1), (Sum.inr 3522, -2), (Sum.inr 3590, -1), (Sum.inr 3693, -2), (Sum.inr 3703, -1), (Sum.inr 3758, -1), (Sum.inr 3770, -2), (Sum.inr 3786, -1), (Sum.inr 3799, -1), (Sum.inr 3800, -1), (Sum.inr 3805, -1), (Sum.inr 3845, -4), (Sum.inr 4931, 8), (Sum.inr 4956, 4), (Sum.inr 4957, 8), (Sum.inr 5112, 4), (Sum.inr 5187, 4), (Sum.inr 5339, 8), (Sum.inr 5353, 8), (Sum.inr 5414, 4)]

theorem reindexCheck2086 : Integer.Sparse.reindex keyMap MixedData.row2086 = numericRow2086 := by decide +kernel

theorem numericCheck2086 (x : Master → ℝ) : Integer.Sparse.eval numericRow2086 x =
    (4 : ℝ) * reducedSource2086 x := by
  norm_num [numericRow2086, reducedSource2086, Integer.Sparse.eval, Sparse.eval, nodeValue4929, nodeValue4931, nodeValue4939, nodeValue4956, nodeValue4957, nodeValue4971, nodeValue5072, nodeValue5112, nodeValue5141, nodeValue5187, nodeValue5339, nodeValue5353, nodeValue5355, nodeValue5365, nodeValue5367, nodeValue5400, nodeValue5405, nodeValue5409, nodeValue5414, nodeValue5428, nodeValue5471]
  ring

noncomputable def reducedSource2087 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3403 x + ((1 : ℝ) * Sparse.eval nodeValue3404 x + ((2 : ℝ) * Sparse.eval nodeValue3406 x + ((1 : ℝ) * Sparse.eval nodeValue3459 x + ((2 : ℝ) * Sparse.eval nodeValue3509 x + ((1 : ℝ) * Sparse.eval nodeValue3510 x + ((2 : ℝ) * Sparse.eval nodeValue3522 x + ((1 : ℝ) * Sparse.eval nodeValue3537 x + ((1 : ℝ) * Sparse.eval nodeValue3556 x + ((1 : ℝ) * Sparse.eval nodeValue3590 x + ((1 : ℝ) * Sparse.eval nodeValue3758 x + ((2 : ℝ) * Sparse.eval nodeValue3760 x + ((2 : ℝ) * Sparse.eval nodeValue3761 x + ((2 : ℝ) * Sparse.eval nodeValue3766 x + ((2 : ℝ) * Sparse.eval nodeValue3770 x + ((1 : ℝ) * Sparse.eval nodeValue3799 x + ((1 : ℝ) * Sparse.eval nodeValue3800 x + ((2 : ℝ) * Sparse.eval nodeValue3807 x + ((2 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3869 x + ((1 : ℝ) * Sparse.eval nodeValue3953 x + 0))))))))))))))))))))

def numericRow2087 : Integer.Sparse Master := [(Sum.inr 3404, 1), (Sum.inr 3406, 2), (Sum.inr 3459, 1), (Sum.inr 3509, 2), (Sum.inr 3510, 1), (Sum.inr 3522, 2), (Sum.inr 3537, 1), (Sum.inr 3556, 1), (Sum.inr 3590, 1), (Sum.inr 3758, 1), (Sum.inr 3760, 2), (Sum.inr 3761, 2), (Sum.inr 3770, 2), (Sum.inr 3799, 1), (Sum.inr 3800, 1), (Sum.inr 3845, 2), (Sum.inr 3869, 1)]

theorem reindexCheck2087 : Integer.Sparse.reindex keyMap MixedData.row2087 = numericRow2087 := by decide +kernel

theorem numericCheck2087 (x : Master → ℝ) : Integer.Sparse.eval numericRow2087 x =
    (1 : ℝ) * reducedSource2087 x := by
  norm_num [numericRow2087, reducedSource2087, Integer.Sparse.eval, Sparse.eval, nodeValue3403, nodeValue3404, nodeValue3406, nodeValue3459, nodeValue3509, nodeValue3510, nodeValue3522, nodeValue3537, nodeValue3556, nodeValue3590, nodeValue3758, nodeValue3760, nodeValue3761, nodeValue3766, nodeValue3770, nodeValue3799, nodeValue3800, nodeValue3807, nodeValue3845, nodeValue3869, nodeValue3953]

noncomputable def reducedSource2088 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4775 x + ((1 : ℝ) * Sparse.eval nodeValue4776 x + ((1 : ℝ) * Sparse.eval nodeValue4777 x + ((1 : ℝ) * Sparse.eval nodeValue4821 x + ((1 : ℝ) * Sparse.eval nodeValue4856 x + ((1 : ℝ) * Sparse.eval nodeValue4942 x + ((1 : ℝ) * Sparse.eval nodeValue4949 x + ((1 : ℝ) * Sparse.eval nodeValue4951 x + ((1 : ℝ) * Sparse.eval nodeValue4963 x + ((1 : ℝ) * Sparse.eval nodeValue4966 x + ((1 : ℝ) * Sparse.eval nodeValue4973 x + ((1 : ℝ) * Sparse.eval nodeValue5105 x + ((1 : ℝ) * Sparse.eval nodeValue5198 x + ((1 : ℝ) * Sparse.eval nodeValue5336 x + ((1 : ℝ) * Sparse.eval nodeValue5338 x + ((1 : ℝ) * Sparse.eval nodeValue5353 x + ((1 : ℝ) * Sparse.eval nodeValue5355 x + ((1 : ℝ) * Sparse.eval nodeValue5360 x + ((1 : ℝ) * Sparse.eval nodeValue5361 x + ((1 : ℝ) * Sparse.eval nodeValue5365 x + ((1 : ℝ) * Sparse.eval nodeValue5367 x + ((1 : ℝ) * Sparse.eval nodeValue5368 x + ((1 : ℝ) * Sparse.eval nodeValue5397 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5412 x + ((1 : ℝ) * Sparse.eval nodeValue5421 x + ((1 : ℝ) * Sparse.eval nodeValue5436 x + ((1 : ℝ) * Sparse.eval nodeValue5446 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + 0)))))))))))))))))))))))))))))

def numericRow2088 : Integer.Sparse Master := [(Sum.inr 2341, -1), (Sum.inr 2515, -1), (Sum.inr 2817, -1), (Sum.inr 3417, -1), (Sum.inr 3479, -1), (Sum.inr 3591, -1), (Sum.inr 3671, -1), (Sum.inr 3693, -1), (Sum.inr 3703, -1), (Sum.inr 3705, -1), (Sum.inr 3754, -1), (Sum.inr 3758, -1), (Sum.inr 3767, -1), (Sum.inr 3770, -1), (Sum.inr 3782, -1), (Sum.inr 3796, -1), (Sum.inr 3809, -1), (Sum.inr 3813, -1), (Sum.inr 3814, -2), (Sum.inr 3958, -1), (Sum.inr 3961, -1), (Sum.inr 4775, 4), (Sum.inr 4776, 4), (Sum.inr 4777, 4), (Sum.inr 4821, 4), (Sum.inr 4856, 4), (Sum.inr 4942, 4), (Sum.inr 4951, 4), (Sum.inr 4963, 4), (Sum.inr 4966, 4), (Sum.inr 5198, 4), (Sum.inr 5338, 4), (Sum.inr 5353, 4), (Sum.inr 5360, 4), (Sum.inr 5361, 4), (Sum.inr 5421, 4), (Sum.inr 5436, 4), (Sum.inr 5446, 4)]

theorem reindexCheck2088 : Integer.Sparse.reindex keyMap MixedData.row2088 = numericRow2088 := by decide +kernel

theorem numericCheck2088 (x : Master → ℝ) : Integer.Sparse.eval numericRow2088 x =
    (4 : ℝ) * reducedSource2088 x := by
  norm_num [numericRow2088, reducedSource2088, Integer.Sparse.eval, Sparse.eval, nodeValue4775, nodeValue4776, nodeValue4777, nodeValue4821, nodeValue4856, nodeValue4942, nodeValue4949, nodeValue4951, nodeValue4963, nodeValue4966, nodeValue4973, nodeValue5105, nodeValue5198, nodeValue5336, nodeValue5338, nodeValue5353, nodeValue5355, nodeValue5360, nodeValue5361, nodeValue5365, nodeValue5367, nodeValue5368, nodeValue5397, nodeValue5410, nodeValue5411, nodeValue5412, nodeValue5421, nodeValue5436, nodeValue5446, nodeValue5473]
  ring

noncomputable def reducedSource2089 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2211 x + ((1 : ℝ) * Sparse.eval nodeValue2212 x + ((1 : ℝ) * Sparse.eval nodeValue2217 x + ((1 : ℝ) * Sparse.eval nodeValue2223 x + ((1 : ℝ) * Sparse.eval nodeValue2274 x + ((1 : ℝ) * Sparse.eval nodeValue3407 x + ((1 : ℝ) * Sparse.eval nodeValue3417 x + ((1 : ℝ) * Sparse.eval nodeValue3418 x + ((1 : ℝ) * Sparse.eval nodeValue3479 x + ((1 : ℝ) * Sparse.eval nodeValue3553 x + ((1 : ℝ) * Sparse.eval nodeValue3555 x + ((1 : ℝ) * Sparse.eval nodeValue3570 x + ((1 : ℝ) * Sparse.eval nodeValue3591 x + ((1 : ℝ) * Sparse.eval nodeValue3754 x + ((1 : ℝ) * Sparse.eval nodeValue3755 x + ((1 : ℝ) * Sparse.eval nodeValue3758 x + ((1 : ℝ) * Sparse.eval nodeValue3761 x + ((1 : ℝ) * Sparse.eval nodeValue3762 x + ((1 : ℝ) * Sparse.eval nodeValue3766 x + ((1 : ℝ) * Sparse.eval nodeValue3767 x + ((1 : ℝ) * Sparse.eval nodeValue3770 x + ((1 : ℝ) * Sparse.eval nodeValue3772 x + ((1 : ℝ) * Sparse.eval nodeValue3796 x + ((1 : ℝ) * Sparse.eval nodeValue3808 x + ((1 : ℝ) * Sparse.eval nodeValue3813 x + ((1 : ℝ) * Sparse.eval nodeValue3814 x + ((1 : ℝ) * Sparse.eval nodeValue3873 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3958 x + 0)))))))))))))))))))))))))))))

def numericRow2089 : Integer.Sparse Master := [(Sum.inr 2211, 1), (Sum.inr 2212, 1), (Sum.inr 2217, 1), (Sum.inr 2223, 1), (Sum.inr 2274, 1), (Sum.inr 3407, 1), (Sum.inr 3417, 1), (Sum.inr 3418, 1), (Sum.inr 3479, 1), (Sum.inr 3553, 1), (Sum.inr 3555, 1), (Sum.inr 3570, 1), (Sum.inr 3591, 1), (Sum.inr 3754, 1), (Sum.inr 3755, 1), (Sum.inr 3758, 1), (Sum.inr 3761, 1), (Sum.inr 3762, 1), (Sum.inr 3767, 1), (Sum.inr 3770, 1), (Sum.inr 3772, 1), (Sum.inr 3796, 1), (Sum.inr 3813, 1), (Sum.inr 3814, 1), (Sum.inr 3873, 1), (Sum.inr 3877, 1), (Sum.inr 3884, 1), (Sum.inr 3958, 1)]

theorem reindexCheck2089 : Integer.Sparse.reindex keyMap MixedData.row2089 = numericRow2089 := by decide +kernel

theorem numericCheck2089 (x : Master → ℝ) : Integer.Sparse.eval numericRow2089 x =
    (1 : ℝ) * reducedSource2089 x := by
  norm_num [numericRow2089, reducedSource2089, Integer.Sparse.eval, Sparse.eval, nodeValue2211, nodeValue2212, nodeValue2217, nodeValue2223, nodeValue2274, nodeValue3407, nodeValue3417, nodeValue3418, nodeValue3479, nodeValue3553, nodeValue3555, nodeValue3570, nodeValue3591, nodeValue3754, nodeValue3755, nodeValue3758, nodeValue3761, nodeValue3762, nodeValue3766, nodeValue3767, nodeValue3770, nodeValue3772, nodeValue3796, nodeValue3808, nodeValue3813, nodeValue3814, nodeValue3873, nodeValue3877, nodeValue3884, nodeValue3958]

noncomputable def reducedSource2090 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4940 x + ((1 : ℝ) * Sparse.eval nodeValue4944 x + ((1 : ℝ) * Sparse.eval nodeValue4946 x + ((1 : ℝ) * Sparse.eval nodeValue4951 x + ((1 : ℝ) * Sparse.eval nodeValue4964 x + ((1 : ℝ) * Sparse.eval nodeValue4965 x + ((1 : ℝ) * Sparse.eval nodeValue4966 x + ((1 : ℝ) * Sparse.eval nodeValue4977 x + ((1 : ℝ) * Sparse.eval nodeValue5044 x + ((1 : ℝ) * Sparse.eval nodeValue5090 x + ((1 : ℝ) * Sparse.eval nodeValue5102 x + ((1 : ℝ) * Sparse.eval nodeValue5199 x + ((1 : ℝ) * Sparse.eval nodeValue5207 x + ((1 : ℝ) * Sparse.eval nodeValue5335 x + ((1 : ℝ) * Sparse.eval nodeValue5338 x + ((1 : ℝ) * Sparse.eval nodeValue5359 x + ((1 : ℝ) * Sparse.eval nodeValue5361 x + ((1 : ℝ) * Sparse.eval nodeValue5365 x + ((1 : ℝ) * Sparse.eval nodeValue5367 x + ((1 : ℝ) * Sparse.eval nodeValue5368 x + ((1 : ℝ) * Sparse.eval nodeValue5370 x + ((1 : ℝ) * Sparse.eval nodeValue5371 x + ((1 : ℝ) * Sparse.eval nodeValue5395 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5413 x + ((1 : ℝ) * Sparse.eval nodeValue5446 x + ((1 : ℝ) * Sparse.eval nodeValue5468 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5475 x + 0)))))))))))))))))))))))))))))

def numericRow2090 : Integer.Sparse Master := [(Sum.inr 2337, -1), (Sum.inr 2512, -1), (Sum.inr 2813, -1), (Sum.inr 2889, -1), (Sum.inr 3412, -1), (Sum.inr 3471, -1), (Sum.inr 3595, -1), (Sum.inr 3631, -1), (Sum.inr 3670, -1), (Sum.inr 3703, -1), (Sum.inr 3705, -1), (Sum.inr 3706, -1), (Sum.inr 3753, -1), (Sum.inr 3758, -1), (Sum.inr 3767, -1), (Sum.inr 3771, -1), (Sum.inr 3781, -1), (Sum.inr 3794, -1), (Sum.inr 3809, -1), (Sum.inr 3813, -1), (Sum.inr 3958, -1), (Sum.inr 3961, -1), (Sum.inr 3963, -2), (Sum.inr 4944, 4), (Sum.inr 4951, 4), (Sum.inr 4964, 4), (Sum.inr 4965, 4), (Sum.inr 4966, 4), (Sum.inr 5044, 4), (Sum.inr 5090, 4), (Sum.inr 5199, 4), (Sum.inr 5338, 4), (Sum.inr 5359, 4), (Sum.inr 5361, 4), (Sum.inr 5446, 4)]

theorem reindexCheck2090 : Integer.Sparse.reindex keyMap MixedData.row2090 = numericRow2090 := by decide +kernel

theorem numericCheck2090 (x : Master → ℝ) : Integer.Sparse.eval numericRow2090 x =
    (4 : ℝ) * reducedSource2090 x := by
  norm_num [numericRow2090, reducedSource2090, Integer.Sparse.eval, Sparse.eval, nodeValue4940, nodeValue4944, nodeValue4946, nodeValue4951, nodeValue4964, nodeValue4965, nodeValue4966, nodeValue4977, nodeValue5044, nodeValue5090, nodeValue5102, nodeValue5199, nodeValue5207, nodeValue5335, nodeValue5338, nodeValue5359, nodeValue5361, nodeValue5365, nodeValue5367, nodeValue5368, nodeValue5370, nodeValue5371, nodeValue5395, nodeValue5410, nodeValue5411, nodeValue5413, nodeValue5446, nodeValue5468, nodeValue5473, nodeValue5475]
  ring

noncomputable def reducedSource2091 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3405 x + ((1 : ℝ) * Sparse.eval nodeValue3412 x + ((1 : ℝ) * Sparse.eval nodeValue3413 x + ((1 : ℝ) * Sparse.eval nodeValue3418 x + ((1 : ℝ) * Sparse.eval nodeValue3471 x + ((1 : ℝ) * Sparse.eval nodeValue3474 x + ((1 : ℝ) * Sparse.eval nodeValue3475 x + ((1 : ℝ) * Sparse.eval nodeValue3480 x + ((1 : ℝ) * Sparse.eval nodeValue3554 x + ((1 : ℝ) * Sparse.eval nodeValue3555 x + ((1 : ℝ) * Sparse.eval nodeValue3578 x + ((1 : ℝ) * Sparse.eval nodeValue3595 x + ((1 : ℝ) * Sparse.eval nodeValue3631 x + ((1 : ℝ) * Sparse.eval nodeValue3753 x + ((1 : ℝ) * Sparse.eval nodeValue3755 x + ((1 : ℝ) * Sparse.eval nodeValue3758 x + ((1 : ℝ) * Sparse.eval nodeValue3759 x + ((1 : ℝ) * Sparse.eval nodeValue3766 x + ((1 : ℝ) * Sparse.eval nodeValue3767 x + ((1 : ℝ) * Sparse.eval nodeValue3771 x + ((1 : ℝ) * Sparse.eval nodeValue3772 x + ((1 : ℝ) * Sparse.eval nodeValue3775 x + ((1 : ℝ) * Sparse.eval nodeValue3794 x + ((1 : ℝ) * Sparse.eval nodeValue3808 x + ((1 : ℝ) * Sparse.eval nodeValue3809 x + ((1 : ℝ) * Sparse.eval nodeValue3817 x + ((1 : ℝ) * Sparse.eval nodeValue3950 x + ((1 : ℝ) * Sparse.eval nodeValue3958 x + ((1 : ℝ) * Sparse.eval nodeValue3959 x + ((1 : ℝ) * Sparse.eval nodeValue3963 x + 0)))))))))))))))))))))))))))))

def numericRow2091 : Integer.Sparse Master := [(Sum.inr 3412, 1), (Sum.inr 3413, 1), (Sum.inr 3418, 1), (Sum.inr 3471, 1), (Sum.inr 3474, 1), (Sum.inr 3475, 1), (Sum.inr 3480, 1), (Sum.inr 3554, 1), (Sum.inr 3555, 1), (Sum.inr 3578, 1), (Sum.inr 3595, 1), (Sum.inr 3631, 1), (Sum.inr 3753, 1), (Sum.inr 3755, 1), (Sum.inr 3758, 1), (Sum.inr 3759, 1), (Sum.inr 3767, 1), (Sum.inr 3771, 1), (Sum.inr 3772, 1), (Sum.inr 3794, 1), (Sum.inr 3809, 1), (Sum.inr 3958, 1), (Sum.inr 3959, 1), (Sum.inr 3963, 1)]

theorem reindexCheck2091 : Integer.Sparse.reindex keyMap MixedData.row2091 = numericRow2091 := by decide +kernel

theorem numericCheck2091 (x : Master → ℝ) : Integer.Sparse.eval numericRow2091 x =
    (1 : ℝ) * reducedSource2091 x := by
  norm_num [numericRow2091, reducedSource2091, Integer.Sparse.eval, Sparse.eval, nodeValue3405, nodeValue3412, nodeValue3413, nodeValue3418, nodeValue3471, nodeValue3474, nodeValue3475, nodeValue3480, nodeValue3554, nodeValue3555, nodeValue3578, nodeValue3595, nodeValue3631, nodeValue3753, nodeValue3755, nodeValue3758, nodeValue3759, nodeValue3766, nodeValue3767, nodeValue3771, nodeValue3772, nodeValue3775, nodeValue3794, nodeValue3808, nodeValue3809, nodeValue3817, nodeValue3950, nodeValue3958, nodeValue3959, nodeValue3963]

noncomputable def reducedSource2092 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4091 x + ((1 : ℝ) * Sparse.eval nodeValue4941 x + ((1 : ℝ) * Sparse.eval nodeValue4948 x + ((2 : ℝ) * Sparse.eval nodeValue4950 x + ((1 : ℝ) * Sparse.eval nodeValue4968 x + ((1 : ℝ) * Sparse.eval nodeValue4970 x + ((2 : ℝ) * Sparse.eval nodeValue4974 x + ((1 : ℝ) * Sparse.eval nodeValue5104 x + ((1 : ℝ) * Sparse.eval nodeValue5117 x + ((2 : ℝ) * Sparse.eval nodeValue5152 x + ((1 : ℝ) * Sparse.eval nodeValue5203 x + ((2 : ℝ) * Sparse.eval nodeValue5337 x + ((2 : ℝ) * Sparse.eval nodeValue5352 x + ((2 : ℝ) * Sparse.eval nodeValue5356 x + ((1 : ℝ) * Sparse.eval nodeValue5366 x + ((2 : ℝ) * Sparse.eval nodeValue5369 x + ((1 : ℝ) * Sparse.eval nodeValue5396 x + ((2 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5469 x + ((2 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5474 x + 0))))))))))))))))))))

def numericRow2092 : Integer.Sparse Master := [(Sum.inr 2332, -1), (Sum.inr 2339, -1), (Sum.inr 2342, -2), (Sum.inr 2809, -1), (Sum.inr 2815, -1), (Sum.inr 2818, -2), (Sum.inr 2884, -1), (Sum.inr 2893, -1), (Sum.inr 2931, -2), (Sum.inr 3410, -1), (Sum.inr 3420, -1), (Sum.inr 3421, -2), (Sum.inr 3587, -1), (Sum.inr 3588, -1), (Sum.inr 3592, -2), (Sum.inr 3599, -1), (Sum.inr 3612, -2), (Sum.inr 3621, -1), (Sum.inr 3672, -2), (Sum.inr 3690, -2), (Sum.inr 3694, -2), (Sum.inr 3756, -2), (Sum.inr 3764, -2), (Sum.inr 3773, -2), (Sum.inr 3945, -1), (Sum.inr 3952, -1), (Sum.inr 3958, -2), (Sum.inr 3961, -2), (Sum.inr 4091, 4)]

theorem reindexCheck2092 : Integer.Sparse.reindex keyMap MixedData.row2092 = numericRow2092 := by decide +kernel

theorem numericCheck2092 (x : Master → ℝ) : Integer.Sparse.eval numericRow2092 x =
    (4 : ℝ) * reducedSource2092 x := by
  norm_num [numericRow2092, reducedSource2092, Integer.Sparse.eval, Sparse.eval, nodeValue4091, nodeValue4941, nodeValue4948, nodeValue4950, nodeValue4968, nodeValue4970, nodeValue4974, nodeValue5104, nodeValue5117, nodeValue5152, nodeValue5203, nodeValue5337, nodeValue5352, nodeValue5356, nodeValue5366, nodeValue5369, nodeValue5396, nodeValue5410, nodeValue5469, nodeValue5473, nodeValue5474]
  ring

noncomputable def reducedSource2093 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4092 x + ((1 : ℝ) * Sparse.eval nodeValue4939 x + ((1 : ℝ) * Sparse.eval nodeValue4943 x + ((1 : ℝ) * Sparse.eval nodeValue4946 x + ((1 : ℝ) * Sparse.eval nodeValue4949 x + ((1 : ℝ) * Sparse.eval nodeValue4971 x + ((1 : ℝ) * Sparse.eval nodeValue4972 x + ((1 : ℝ) * Sparse.eval nodeValue4973 x + ((1 : ℝ) * Sparse.eval nodeValue4977 x + ((1 : ℝ) * Sparse.eval nodeValue5036 x + ((1 : ℝ) * Sparse.eval nodeValue5101 x + ((1 : ℝ) * Sparse.eval nodeValue5111 x + ((1 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5204 x + ((1 : ℝ) * Sparse.eval nodeValue5335 x + ((1 : ℝ) * Sparse.eval nodeValue5336 x + ((1 : ℝ) * Sparse.eval nodeValue5351 x + ((1 : ℝ) * Sparse.eval nodeValue5355 x + ((1 : ℝ) * Sparse.eval nodeValue5365 x + ((1 : ℝ) * Sparse.eval nodeValue5367 x + ((1 : ℝ) * Sparse.eval nodeValue5368 x + ((1 : ℝ) * Sparse.eval nodeValue5370 x + ((1 : ℝ) * Sparse.eval nodeValue5371 x + ((1 : ℝ) * Sparse.eval nodeValue5394 x + ((1 : ℝ) * Sparse.eval nodeValue5395 x + ((1 : ℝ) * Sparse.eval nodeValue5409 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5413 x + ((1 : ℝ) * Sparse.eval nodeValue5428 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + 0)))))))))))))))))))))))))))))

def numericRow2093 : Integer.Sparse Master := [(Sum.inr 2330, -1), (Sum.inr 2334, -1), (Sum.inr 2337, -1), (Sum.inr 2341, -1), (Sum.inr 2428, -1), (Sum.inr 2434, -1), (Sum.inr 2561, -1), (Sum.inr 2807, -1), (Sum.inr 2813, -1), (Sum.inr 2817, -1), (Sum.inr 2881, -1), (Sum.inr 3404, -1), (Sum.inr 3411, -1), (Sum.inr 3412, -1), (Sum.inr 3417, -1), (Sum.inr 3450, -1), (Sum.inr 3457, -1), (Sum.inr 3522, -1), (Sum.inr 3590, -1), (Sum.inr 3591, -1), (Sum.inr 3595, -1), (Sum.inr 3624, -1), (Sum.inr 3670, -1), (Sum.inr 3671, -1), (Sum.inr 3689, -1), (Sum.inr 3693, -1), (Sum.inr 3703, -1), (Sum.inr 3705, -1), (Sum.inr 3706, -1), (Sum.inr 3753, -1), (Sum.inr 3754, -1), (Sum.inr 3757, -1), (Sum.inr 3758, -1), (Sum.inr 3767, -1), (Sum.inr 3770, -1), (Sum.inr 3771, -1), (Sum.inr 3781, -1), (Sum.inr 3794, -1), (Sum.inr 3845, -2), (Sum.inr 3958, -1), (Sum.inr 3961, -1), (Sum.inr 4092, 4)]

theorem reindexCheck2093 : Integer.Sparse.reindex keyMap MixedData.row2093 = numericRow2093 := by decide +kernel

theorem numericCheck2093 (x : Master → ℝ) : Integer.Sparse.eval numericRow2093 x =
    (4 : ℝ) * reducedSource2093 x := by
  norm_num [numericRow2093, reducedSource2093, Integer.Sparse.eval, Sparse.eval, nodeValue4092, nodeValue4939, nodeValue4943, nodeValue4946, nodeValue4949, nodeValue4971, nodeValue4972, nodeValue4973, nodeValue4977, nodeValue5036, nodeValue5101, nodeValue5111, nodeValue5141, nodeValue5204, nodeValue5335, nodeValue5336, nodeValue5351, nodeValue5355, nodeValue5365, nodeValue5367, nodeValue5368, nodeValue5370, nodeValue5371, nodeValue5394, nodeValue5395, nodeValue5409, nodeValue5410, nodeValue5413, nodeValue5428, nodeValue5473]
  ring

noncomputable def reducedSource2094 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4763 x + ((1 : ℝ) * Sparse.eval nodeValue4769 x + ((1 : ℝ) * Sparse.eval nodeValue4770 x + ((2 : ℝ) * Sparse.eval nodeValue4846 x + ((1 : ℝ) * Sparse.eval nodeValue4938 x + ((2 : ℝ) * Sparse.eval nodeValue4945 x + ((1 : ℝ) * Sparse.eval nodeValue4975 x + ((2 : ℝ) * Sparse.eval nodeValue4976 x + ((1 : ℝ) * Sparse.eval nodeValue5099 x + ((1 : ℝ) * Sparse.eval nodeValue5205 x + ((2 : ℝ) * Sparse.eval nodeValue5215 x + ((2 : ℝ) * Sparse.eval nodeValue5238 x + ((1 : ℝ) * Sparse.eval nodeValue5241 x + ((1 : ℝ) * Sparse.eval nodeValue5242 x + ((2 : ℝ) * Sparse.eval nodeValue5248 x + ((2 : ℝ) * Sparse.eval nodeValue5274 x + ((2 : ℝ) * Sparse.eval nodeValue5275 x + ((1 : ℝ) * Sparse.eval nodeValue5277 x + ((1 : ℝ) * Sparse.eval nodeValue5282 x + ((1 : ℝ) * Sparse.eval nodeValue5284 x + ((2 : ℝ) * Sparse.eval nodeValue5287 x + 0))))))))))))))))))))

def numericRow2094 : Integer.Sparse Master := [(Sum.inr 1963, -1), (Sum.inr 1969, -1), (Sum.inr 1970, -1), (Sum.inr 2174, -1), (Sum.inr 2185, -1), (Sum.inr 2186, -1), (Sum.inr 2509, -1), (Sum.inr 2686, -2), (Sum.inr 2694, -1), (Sum.inr 2704, -1), (Sum.inr 2705, -2), (Sum.inr 2743, -2), (Sum.inr 3077, -1), (Sum.inr 3397, -2), (Sum.inr 3493, -1), (Sum.inr 3498, -2), (Sum.inr 3548, -2), (Sum.inr 3625, -1), (Sum.inr 4945, 8), (Sum.inr 4975, 4), (Sum.inr 4976, 8), (Sum.inr 5205, 4), (Sum.inr 5215, 8), (Sum.inr 5277, 4), (Sum.inr 5282, 4), (Sum.inr 5287, 8)]

theorem reindexCheck2094 : Integer.Sparse.reindex keyMap MixedData.row2094 = numericRow2094 := by decide +kernel

theorem numericCheck2094 (x : Master → ℝ) : Integer.Sparse.eval numericRow2094 x =
    (4 : ℝ) * reducedSource2094 x := by
  norm_num [numericRow2094, reducedSource2094, Integer.Sparse.eval, Sparse.eval, nodeValue4763, nodeValue4769, nodeValue4770, nodeValue4846, nodeValue4938, nodeValue4945, nodeValue4975, nodeValue4976, nodeValue5099, nodeValue5205, nodeValue5215, nodeValue5238, nodeValue5241, nodeValue5242, nodeValue5248, nodeValue5274, nodeValue5275, nodeValue5277, nodeValue5282, nodeValue5284, nodeValue5287]
  ring

noncomputable def reducedSource2095 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2174 x + ((1 : ℝ) * Sparse.eval nodeValue2185 x + ((1 : ℝ) * Sparse.eval nodeValue2186 x + ((2 : ℝ) * Sparse.eval nodeValue2229 x + ((2 : ℝ) * Sparse.eval nodeValue2653 x + ((2 : ℝ) * Sparse.eval nodeValue2658 x + ((2 : ℝ) * Sparse.eval nodeValue2659 x + ((2 : ℝ) * Sparse.eval nodeValue2686 x + ((1 : ℝ) * Sparse.eval nodeValue2689 x + ((1 : ℝ) * Sparse.eval nodeValue2690 x + ((1 : ℝ) * Sparse.eval nodeValue2694 x + ((1 : ℝ) * Sparse.eval nodeValue2695 x + ((1 : ℝ) * Sparse.eval nodeValue2704 x + ((2 : ℝ) * Sparse.eval nodeValue2705 x + ((1 : ℝ) * Sparse.eval nodeValue2706 x + ((2 : ℝ) * Sparse.eval nodeValue2742 x + ((2 : ℝ) * Sparse.eval nodeValue2743 x + ((2 : ℝ) * Sparse.eval nodeValue3025 x + ((1 : ℝ) * Sparse.eval nodeValue3059 x + ((1 : ℝ) * Sparse.eval nodeValue3077 x + ((1 : ℝ) * Sparse.eval nodeValue3078 x + 0))))))))))))))))))))

def numericRow2095 : Integer.Sparse Master := [(Sum.inr 2174, 1), (Sum.inr 2185, 1), (Sum.inr 2186, 1), (Sum.inr 2653, 2), (Sum.inr 2658, 2), (Sum.inr 2659, 2), (Sum.inr 2686, 2), (Sum.inr 2690, 1), (Sum.inr 2694, 1), (Sum.inr 2704, 1), (Sum.inr 2705, 2), (Sum.inr 2706, 1), (Sum.inr 2743, 2), (Sum.inr 3025, 2), (Sum.inr 3059, 1), (Sum.inr 3077, 1), (Sum.inr 3078, 1)]

theorem reindexCheck2095 : Integer.Sparse.reindex keyMap MixedData.row2095 = numericRow2095 := by decide +kernel

theorem numericCheck2095 (x : Master → ℝ) : Integer.Sparse.eval numericRow2095 x =
    (1 : ℝ) * reducedSource2095 x := by
  norm_num [numericRow2095, reducedSource2095, Integer.Sparse.eval, Sparse.eval, nodeValue2174, nodeValue2185, nodeValue2186, nodeValue2229, nodeValue2653, nodeValue2658, nodeValue2659, nodeValue2686, nodeValue2689, nodeValue2690, nodeValue2694, nodeValue2695, nodeValue2704, nodeValue2705, nodeValue2706, nodeValue2742, nodeValue2743, nodeValue3025, nodeValue3059, nodeValue3077, nodeValue3078]

end MUB6.Certificate.MixedSourceBridge

end OAI
