import OAI.Analysis.MutuallyUnbiased.MixedData.Source2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource288 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3854 x + ((1 : ℝ) * Sparse.eval nodeValue3857 x + ((1 : ℝ) * Sparse.eval nodeValue3907 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow288 : Integer.Sparse Master := [(Sum.inr 3038, 1), (Sum.inr 3840, 1), (Sum.inr 3845, 1), (Sum.inr 3854, 1), (Sum.inr 3857, 1), (Sum.inr 3907, 1), (Sum.inr 4092, -1)]

theorem reindexCheck288 : Integer.Sparse.reindex keyMap MixedData.row288 = numericRow288 := by decide +kernel

theorem numericCheck288 (x : Master → ℝ) : Integer.Sparse.eval numericRow288 x =
    (1 : ℝ) * reducedSource288 x := by
  norm_num [numericRow288, reducedSource288, Integer.Sparse.eval, Sparse.eval, nodeValue3038, nodeValue3840, nodeValue3845, nodeValue3854, nodeValue3857, nodeValue3907, nodeValue4092]

noncomputable def reducedSource289 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1357 x + ((1 : ℝ) * Sparse.eval nodeValue1359 x + ((1 : ℝ) * Sparse.eval nodeValue1362 x + ((1 : ℝ) * Sparse.eval nodeValue1367 x + ((1 : ℝ) * Sparse.eval nodeValue1422 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow289 : Integer.Sparse Master := [(Sum.inr 1357, 1), (Sum.inr 1359, 1), (Sum.inr 1362, 1), (Sum.inr 1367, 1), (Sum.inr 1422, 1), (Sum.inr 3038, 1), (Sum.inr 4092, -1)]

theorem reindexCheck289 : Integer.Sparse.reindex keyMap MixedData.row289 = numericRow289 := by decide +kernel

theorem numericCheck289 (x : Master → ℝ) : Integer.Sparse.eval numericRow289 x =
    (1 : ℝ) * reducedSource289 x := by
  norm_num [numericRow289, reducedSource289, Integer.Sparse.eval, Sparse.eval, nodeValue1357, nodeValue1359, nodeValue1362, nodeValue1367, nodeValue1422, nodeValue3038, nodeValue4092]

noncomputable def reducedSource290 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1367 x + ((1 : ℝ) * Sparse.eval nodeValue2881 x + ((1 : ℝ) * Sparse.eval nodeValue2974 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3054 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow290 : Integer.Sparse Master := [(Sum.inr 1367, 1), (Sum.inr 2881, 1), (Sum.inr 2974, 1), (Sum.inr 3038, 1), (Sum.inr 3051, 1), (Sum.inr 3054, 1), (Sum.inr 4092, -1)]

theorem reindexCheck290 : Integer.Sparse.reindex keyMap MixedData.row290 = numericRow290 := by decide +kernel

theorem numericCheck290 (x : Master → ℝ) : Integer.Sparse.eval numericRow290 x =
    (1 : ℝ) * reducedSource290 x := by
  norm_num [numericRow290, reducedSource290, Integer.Sparse.eval, Sparse.eval, nodeValue1367, nodeValue2881, nodeValue2974, nodeValue3038, nodeValue3051, nodeValue3054, nodeValue4092]

noncomputable def reducedSource291 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2579 x + ((1 : ℝ) * Sparse.eval nodeValue2582 x + ((1 : ℝ) * Sparse.eval nodeValue3007 x + ((1 : ℝ) * Sparse.eval nodeValue3010 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3854 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow291 : Integer.Sparse Master := [(Sum.inr 2579, 1), (Sum.inr 2582, 1), (Sum.inr 3007, 1), (Sum.inr 3010, 1), (Sum.inr 3038, 1), (Sum.inr 3854, 1), (Sum.inr 4092, -1)]

theorem reindexCheck291 : Integer.Sparse.reindex keyMap MixedData.row291 = numericRow291 := by decide +kernel

theorem numericCheck291 (x : Master → ℝ) : Integer.Sparse.eval numericRow291 x =
    (1 : ℝ) * reducedSource291 x := by
  norm_num [numericRow291, reducedSource291, Integer.Sparse.eval, Sparse.eval, nodeValue2579, nodeValue2582, nodeValue3007, nodeValue3010, nodeValue3038, nodeValue3854, nodeValue4092]

noncomputable def reducedSource292 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1357 x + ((1 : ℝ) * Sparse.eval nodeValue2861 x + ((1 : ℝ) * Sparse.eval nodeValue3007 x + ((1 : ℝ) * Sparse.eval nodeValue3036 x + ((2 : ℝ) * Sparse.eval nodeValue3038 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow292 : Integer.Sparse Master := [(Sum.inr 1357, 1), (Sum.inr 2861, 1), (Sum.inr 3007, 1), (Sum.inr 3036, 1), (Sum.inr 3038, 2), (Sum.inr 4092, -1)]

theorem reindexCheck292 : Integer.Sparse.reindex keyMap MixedData.row292 = numericRow292 := by decide +kernel

theorem numericCheck292 (x : Master → ℝ) : Integer.Sparse.eval numericRow292 x =
    (1 : ℝ) * reducedSource292 x := by
  norm_num [numericRow292, reducedSource292, Integer.Sparse.eval, Sparse.eval, nodeValue1357, nodeValue2861, nodeValue3007, nodeValue3036, nodeValue3038, nodeValue4092]

noncomputable def reducedSource293 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2547 x + ((1 : ℝ) * Sparse.eval nodeValue2580 x + ((1 : ℝ) * Sparse.eval nodeValue2971 x + ((1 : ℝ) * Sparse.eval nodeValue2974 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3840 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow293 : Integer.Sparse Master := [(Sum.inr 2547, 1), (Sum.inr 2580, 1), (Sum.inr 2971, 1), (Sum.inr 2974, 1), (Sum.inr 3038, 1), (Sum.inr 3840, 1), (Sum.inr 4092, -1)]

theorem reindexCheck293 : Integer.Sparse.reindex keyMap MixedData.row293 = numericRow293 := by decide +kernel

theorem numericCheck293 (x : Master → ℝ) : Integer.Sparse.eval numericRow293 x =
    (1 : ℝ) * reducedSource293 x := by
  norm_num [numericRow293, reducedSource293, Integer.Sparse.eval, Sparse.eval, nodeValue2547, nodeValue2580, nodeValue2971, nodeValue2974, nodeValue3038, nodeValue3840, nodeValue4092]

noncomputable def reducedSource294 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2558 x + ((1 : ℝ) * Sparse.eval nodeValue2861 x + ((1 : ℝ) * Sparse.eval nodeValue2867 x + ((1 : ℝ) * Sparse.eval nodeValue2881 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow294 : Integer.Sparse Master := [(Sum.inr 2558, 1), (Sum.inr 2861, 1), (Sum.inr 2867, 1), (Sum.inr 2881, 1), (Sum.inr 3038, 1), (Sum.inr 3845, 1), (Sum.inr 4092, -1)]

theorem reindexCheck294 : Integer.Sparse.reindex keyMap MixedData.row294 = numericRow294 := by decide +kernel

theorem numericCheck294 (x : Master → ℝ) : Integer.Sparse.eval numericRow294 x =
    (1 : ℝ) * reducedSource294 x := by
  norm_num [numericRow294, reducedSource294, Integer.Sparse.eval, Sparse.eval, nodeValue2558, nodeValue2861, nodeValue2867, nodeValue2881, nodeValue3038, nodeValue3845, nodeValue4092]

noncomputable def reducedSource295 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1362 x + ((1 : ℝ) * Sparse.eval nodeValue2867 x + ((1 : ℝ) * Sparse.eval nodeValue2971 x + ((1 : ℝ) * Sparse.eval nodeValue3010 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3040 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow295 : Integer.Sparse Master := [(Sum.inr 1362, 1), (Sum.inr 2867, 1), (Sum.inr 2971, 1), (Sum.inr 3010, 1), (Sum.inr 3038, 1), (Sum.inr 3040, 1), (Sum.inr 4092, -1)]

theorem reindexCheck295 : Integer.Sparse.reindex keyMap MixedData.row295 = numericRow295 := by decide +kernel

theorem numericCheck295 (x : Master → ℝ) : Integer.Sparse.eval numericRow295 x =
    (1 : ℝ) * reducedSource295 x := by
  norm_num [numericRow295, reducedSource295, Integer.Sparse.eval, Sparse.eval, nodeValue1362, nodeValue2867, nodeValue2971, nodeValue3010, nodeValue3038, nodeValue3040, nodeValue4092]

noncomputable def reducedSource296 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2036 x + ((1 : ℝ) * Sparse.eval nodeValue2037 x + ((1 : ℝ) * Sparse.eval nodeValue2038 x + ((1 : ℝ) * Sparse.eval nodeValue2059 x + ((1 : ℝ) * Sparse.eval nodeValue2254 x + ((1 : ℝ) * Sparse.eval nodeValue2661 x + ((1 : ℝ) * Sparse.eval nodeValue2670 x + ((1 : ℝ) * Sparse.eval nodeValue2672 x + ((1 : ℝ) * Sparse.eval nodeValue2677 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue3015 x + ((1 : ℝ) * Sparse.eval nodeValue3016 x + ((1 : ℝ) * Sparse.eval nodeValue3018 x + ((1 : ℝ) * Sparse.eval nodeValue3028 x + ((1 : ℝ) * Sparse.eval nodeValue3029 x + ((1 : ℝ) * Sparse.eval nodeValue3035 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3042 x + ((1 : ℝ) * Sparse.eval nodeValue3044 x + ((1 : ℝ) * Sparse.eval nodeValue3052 x + ((1 : ℝ) * Sparse.eval nodeValue3054 x + ((1 : ℝ) * Sparse.eval nodeValue3064 x + ((1 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3088 x + ((1 : ℝ) * Sparse.eval nodeValue3101 x + ((1 : ℝ) * Sparse.eval nodeValue3196 x + ((1 : ℝ) * Sparse.eval nodeValue3198 x + ((1 : ℝ) * Sparse.eval nodeValue3210 x + ((1 : ℝ) * Sparse.eval nodeValue3224 x + 0)))))))))))))))))))))))))))))

def numericRow296 : Integer.Sparse Master := [(Sum.inl 0, -484), (Sum.inl 5, -80), (Sum.inl 6, 20), (Sum.inl 2, 640), (Sum.inl 35, -320), (Sum.inl 3, -320), (Sum.inl 13, 320), (Sum.inl 52, -320), (Sum.inl 12, 320), (Sum.inl 1, 320), (Sum.inr 2036, 17280), (Sum.inr 2037, 17280), (Sum.inr 2038, 17280), (Sum.inr 2059, 17280), (Sum.inr 2254, 17280), (Sum.inr 2661, 17280), (Sum.inr 2670, 17280), (Sum.inr 2672, 17280), (Sum.inr 2677, 17280), (Sum.inr 2722, 17280), (Sum.inr 3015, 17280), (Sum.inr 3016, 17280), (Sum.inr 3018, 17280), (Sum.inr 3028, 17280), (Sum.inr 3029, 17280), (Sum.inr 3035, 17280), (Sum.inr 3038, 17280), (Sum.inr 3039, 17280), (Sum.inr 3042, 17280), (Sum.inr 3044, 17280), (Sum.inr 3052, 17280), (Sum.inr 3054, 17280), (Sum.inr 3064, 17280), (Sum.inr 3086, 17280), (Sum.inr 3196, 17280), (Sum.inr 3198, 17280)]

theorem reindexCheck296 : Integer.Sparse.reindex keyMap MixedData.row296 = numericRow296 := by decide +kernel

theorem numericCheck296 (x : Master → ℝ) : Integer.Sparse.eval numericRow296 x =
    (17280 : ℝ) * reducedSource296 x := by
  norm_num [numericRow296, reducedSource296, Integer.Sparse.eval, Sparse.eval, nodeValue2036, nodeValue2037, nodeValue2038, nodeValue2059, nodeValue2254, nodeValue2661, nodeValue2670, nodeValue2672, nodeValue2677, nodeValue2722, nodeValue3015, nodeValue3016, nodeValue3018, nodeValue3028, nodeValue3029, nodeValue3035, nodeValue3038, nodeValue3039, nodeValue3042, nodeValue3044, nodeValue3052, nodeValue3054, nodeValue3064, nodeValue3086, nodeValue3088, nodeValue3101, nodeValue3196, nodeValue3198, nodeValue3210, nodeValue3224]
  ring

noncomputable def reducedSource297 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2560 x + ((1 : ℝ) * Sparse.eval nodeValue3375 x + ((1 : ℝ) * Sparse.eval nodeValue3379 x + ((1 : ℝ) * Sparse.eval nodeValue3391 x + ((1 : ℝ) * Sparse.eval nodeValue3533 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow297 : Integer.Sparse Master := [(Sum.inr 2560, 1), (Sum.inr 3375, 1), (Sum.inr 3379, 1), (Sum.inr 3391, 1), (Sum.inr 3533, 1), (Sum.inr 3541, 1), (Sum.inr 4084, -1)]

theorem reindexCheck297 : Integer.Sparse.reindex keyMap MixedData.row297 = numericRow297 := by decide +kernel

theorem numericCheck297 (x : Master → ℝ) : Integer.Sparse.eval numericRow297 x =
    (1 : ℝ) * reducedSource297 x := by
  norm_num [numericRow297, reducedSource297, Integer.Sparse.eval, Sparse.eval, nodeValue2560, nodeValue3375, nodeValue3379, nodeValue3391, nodeValue3533, nodeValue3541, nodeValue4084]

noncomputable def reducedSource298 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2034 x + ((1 : ℝ) * Sparse.eval nodeValue2037 x + ((1 : ℝ) * Sparse.eval nodeValue2039 x + ((1 : ℝ) * Sparse.eval nodeValue2058 x + ((1 : ℝ) * Sparse.eval nodeValue2279 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow298 : Integer.Sparse Master := [(Sum.inr 2034, 1), (Sum.inr 2037, 1), (Sum.inr 2039, 1), (Sum.inr 2058, 1), (Sum.inr 2279, 1), (Sum.inr 3541, 1), (Sum.inr 4084, -1)]

theorem reindexCheck298 : Integer.Sparse.reindex keyMap MixedData.row298 = numericRow298 := by decide +kernel

theorem numericCheck298 (x : Master → ℝ) : Integer.Sparse.eval numericRow298 x =
    (1 : ℝ) * reducedSource298 x := by
  norm_num [numericRow298, reducedSource298, Integer.Sparse.eval, Sparse.eval, nodeValue2034, nodeValue2037, nodeValue2039, nodeValue2058, nodeValue2279, nodeValue3541, nodeValue4084]

noncomputable def reducedSource299 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3151 x + ((1 : ℝ) * Sparse.eval nodeValue3379 x + ((1 : ℝ) * Sparse.eval nodeValue3382 x + ((1 : ℝ) * Sparse.eval nodeValue3383 x + ((1 : ℝ) * Sparse.eval nodeValue3395 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow299 : Integer.Sparse Master := [(Sum.inr 3151, 1), (Sum.inr 3379, 1), (Sum.inr 3382, 1), (Sum.inr 3383, 1), (Sum.inr 3395, 1), (Sum.inr 3541, 1), (Sum.inr 4084, -1)]

theorem reindexCheck299 : Integer.Sparse.reindex keyMap MixedData.row299 = numericRow299 := by decide +kernel

theorem numericCheck299 (x : Master → ℝ) : Integer.Sparse.eval numericRow299 x =
    (1 : ℝ) * reducedSource299 x := by
  norm_num [numericRow299, reducedSource299, Integer.Sparse.eval, Sparse.eval, nodeValue3151, nodeValue3379, nodeValue3382, nodeValue3383, nodeValue3395, nodeValue3541, nodeValue4084]

noncomputable def reducedSource300 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2034 x + ((1 : ℝ) * Sparse.eval nodeValue2555 x + ((1 : ℝ) * Sparse.eval nodeValue3382 x + ((1 : ℝ) * Sparse.eval nodeValue3528 x + ((1 : ℝ) * Sparse.eval nodeValue3539 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow300 : Integer.Sparse Master := [(Sum.inr 2034, 1), (Sum.inr 2555, 1), (Sum.inr 3382, 1), (Sum.inr 3528, 1), (Sum.inr 3539, 1), (Sum.inr 3541, 1), (Sum.inr 4084, -1)]

theorem reindexCheck300 : Integer.Sparse.reindex keyMap MixedData.row300 = numericRow300 := by decide +kernel

theorem numericCheck300 (x : Master → ℝ) : Integer.Sparse.eval numericRow300 x =
    (1 : ℝ) * reducedSource300 x := by
  norm_num [numericRow300, reducedSource300, Integer.Sparse.eval, Sparse.eval, nodeValue2034, nodeValue2555, nodeValue3382, nodeValue3528, nodeValue3539, nodeValue3541, nodeValue4084]

noncomputable def reducedSource301 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3279 x + ((1 : ℝ) * Sparse.eval nodeValue3280 x + ((1 : ℝ) * Sparse.eval nodeValue3282 x + ((2 : ℝ) * Sparse.eval nodeValue3290 x + ((2 : ℝ) * Sparse.eval nodeValue3434 x + ((1 : ℝ) * Sparse.eval nodeValue3466 x + ((2 : ℝ) * Sparse.eval nodeValue3467 x + ((1 : ℝ) * Sparse.eval nodeValue3476 x + ((2 : ℝ) * Sparse.eval nodeValue3529 x + ((2 : ℝ) * Sparse.eval nodeValue3532 x + ((2 : ℝ) * Sparse.eval nodeValue3536 x + ((1 : ℝ) * Sparse.eval nodeValue3539 x + ((1 : ℝ) * Sparse.eval nodeValue3543 x + ((2 : ℝ) * Sparse.eval nodeValue3544 x + ((2 : ℝ) * Sparse.eval nodeValue3568 x + ((1 : ℝ) * Sparse.eval nodeValue3571 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((1 : ℝ) * Sparse.eval nodeValue3805 x + ((2 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3851 x + ((1 : ℝ) * Sparse.eval nodeValue3858 x + 0))))))))))))))))))))

def numericRow301 : Integer.Sparse Master := [(Sum.inl 0, -31), (Sum.inl 2, 25), (Sum.inl 3, 80), (Sum.inl 12, 40), (Sum.inl 4, 80), (Sum.inl 1, -140), (Sum.inr 3279, 2160), (Sum.inr 3280, 2160), (Sum.inr 3282, 2160), (Sum.inr 3290, 4320), (Sum.inr 3434, 4320), (Sum.inr 3466, 2160), (Sum.inr 3467, 4320), (Sum.inr 3476, 2160), (Sum.inr 3529, 4320), (Sum.inr 3532, 4320), (Sum.inr 3536, 4320), (Sum.inr 3539, 2160), (Sum.inr 3543, 2160), (Sum.inr 3544, 4320), (Sum.inr 3568, 4320), (Sum.inr 3571, 2160), (Sum.inr 3580, 2160), (Sum.inr 3805, 2160), (Sum.inr 3848, 4320)]

theorem reindexCheck301 : Integer.Sparse.reindex keyMap MixedData.row301 = numericRow301 := by decide +kernel

theorem numericCheck301 (x : Master → ℝ) : Integer.Sparse.eval numericRow301 x =
    (2160 : ℝ) * reducedSource301 x := by
  norm_num [numericRow301, reducedSource301, Integer.Sparse.eval, Sparse.eval, nodeValue3279, nodeValue3280, nodeValue3282, nodeValue3290, nodeValue3434, nodeValue3466, nodeValue3467, nodeValue3476, nodeValue3529, nodeValue3532, nodeValue3536, nodeValue3539, nodeValue3543, nodeValue3544, nodeValue3568, nodeValue3571, nodeValue3580, nodeValue3805, nodeValue3848, nodeValue3851, nodeValue3858]
  ring

noncomputable def reducedSource302 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2709 x + ((1 : ℝ) * Sparse.eval nodeValue3800 x + ((2 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3901 x + ((1 : ℝ) * Sparse.eval nodeValue3902 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow302 : Integer.Sparse Master := [(Sum.inr 3800, 1), (Sum.inr 3871, 2), (Sum.inr 3901, 1), (Sum.inr 3902, 1), (Sum.inr 4091, -1)]

theorem reindexCheck302 : Integer.Sparse.reindex keyMap MixedData.row302 = numericRow302 := by decide +kernel

theorem numericCheck302 (x : Master → ℝ) : Integer.Sparse.eval numericRow302 x =
    (1 : ℝ) * reducedSource302 x := by
  norm_num [numericRow302, reducedSource302, Integer.Sparse.eval, Sparse.eval, nodeValue2709, nodeValue3800, nodeValue3871, nodeValue3901, nodeValue3902, nodeValue4091]

noncomputable def reducedSource303 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1206 x + ((1 : ℝ) * Sparse.eval nodeValue1208 x + ((2 : ℝ) * Sparse.eval nodeValue1213 x + ((1 : ℝ) * Sparse.eval nodeValue1247 x + ((1 : ℝ) * Sparse.eval nodeValue2709 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow303 : Integer.Sparse Master := [(Sum.inr 1206, 1), (Sum.inr 1208, 1), (Sum.inr 1213, 2), (Sum.inr 1247, 1), (Sum.inr 4091, -1)]

theorem reindexCheck303 : Integer.Sparse.reindex keyMap MixedData.row303 = numericRow303 := by decide +kernel

theorem numericCheck303 (x : Master → ℝ) : Integer.Sparse.eval numericRow303 x =
    (1 : ℝ) * reducedSource303 x := by
  norm_num [numericRow303, reducedSource303, Integer.Sparse.eval, Sparse.eval, nodeValue1206, nodeValue1208, nodeValue1213, nodeValue1247, nodeValue2709, nodeValue4091]

end MUB6.Certificate.MixedSourceBridge

end OAI
