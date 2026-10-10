import OAI.Analysis.MutuallyUnbiased.MixedData.Source1
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource240 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2973 x + ((1 : ℝ) * Sparse.eval nodeValue3490 x + ((1 : ℝ) * Sparse.eval nodeValue3494 x + ((1 : ℝ) * Sparse.eval nodeValue3502 x + ((2 : ℝ) * Sparse.eval nodeValue3540 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow240 : Integer.Sparse Master := [(Sum.inr 2973, 1), (Sum.inr 3490, 1), (Sum.inr 3502, 1), (Sum.inr 3540, 2), (Sum.inr 4084, -1)]

theorem reindexCheck240 : Integer.Sparse.reindex keyMap MixedData.row240 = numericRow240 := by decide +kernel

theorem numericCheck240 (x : Master → ℝ) : Integer.Sparse.eval numericRow240 x =
    (1 : ℝ) * reducedSource240 x := by
  norm_num [numericRow240, reducedSource240, Integer.Sparse.eval, Sparse.eval, nodeValue2973, nodeValue3490, nodeValue3494, nodeValue3502, nodeValue3540, nodeValue4084]

noncomputable def reducedSource241 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2039 x + ((1 : ℝ) * Sparse.eval nodeValue2592 x + ((1 : ℝ) * Sparse.eval nodeValue3383 x + ((1 : ℝ) * Sparse.eval nodeValue3490 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow241 : Integer.Sparse Master := [(Sum.inr 2039, 1), (Sum.inr 2592, 1), (Sum.inr 3383, 1), (Sum.inr 3490, 1), (Sum.inr 3540, 1), (Sum.inr 3541, 1), (Sum.inr 4084, -1)]

theorem reindexCheck241 : Integer.Sparse.reindex keyMap MixedData.row241 = numericRow241 := by decide +kernel

theorem numericCheck241 (x : Master → ℝ) : Integer.Sparse.eval numericRow241 x =
    (1 : ℝ) * reducedSource241 x := by
  norm_num [numericRow241, reducedSource241, Integer.Sparse.eval, Sparse.eval, nodeValue2039, nodeValue2592, nodeValue3383, nodeValue3490, nodeValue3540, nodeValue3541, nodeValue4084]

noncomputable def reducedSource242 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3533 x + ((1 : ℝ) * Sparse.eval nodeValue3539 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((1 : ℝ) * Sparse.eval nodeValue3544 x + ((1 : ℝ) * Sparse.eval nodeValue3632 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow242 : Integer.Sparse Master := [(Sum.inr 3533, 1), (Sum.inr 3539, 1), (Sum.inr 3540, 1), (Sum.inr 3541, 1), (Sum.inr 3544, 1), (Sum.inr 3632, 1), (Sum.inr 4084, -1)]

theorem reindexCheck242 : Integer.Sparse.reindex keyMap MixedData.row242 = numericRow242 := by decide +kernel

theorem numericCheck242 (x : Master → ℝ) : Integer.Sparse.eval numericRow242 x =
    (1 : ℝ) * reducedSource242 x := by
  norm_num [numericRow242, reducedSource242, Integer.Sparse.eval, Sparse.eval, nodeValue3533, nodeValue3539, nodeValue3540, nodeValue3541, nodeValue3544, nodeValue3632, nodeValue4084]

noncomputable def reducedSource243 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2054 x + ((1 : ℝ) * Sparse.eval nodeValue3392 x + ((1 : ℝ) * Sparse.eval nodeValue3494 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3544 x + ((1 : ℝ) * Sparse.eval nodeValue3548 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow243 : Integer.Sparse Master := [(Sum.inr 2054, 1), (Sum.inr 3392, 1), (Sum.inr 3540, 1), (Sum.inr 3544, 1), (Sum.inr 3548, 1), (Sum.inr 4084, -1)]

theorem reindexCheck243 : Integer.Sparse.reindex keyMap MixedData.row243 = numericRow243 := by decide +kernel

theorem numericCheck243 (x : Master → ℝ) : Integer.Sparse.eval numericRow243 x =
    (1 : ℝ) * reducedSource243 x := by
  norm_num [numericRow243, reducedSource243, Integer.Sparse.eval, Sparse.eval, nodeValue2054, nodeValue3392, nodeValue3494, nodeValue3540, nodeValue3544, nodeValue3548, nodeValue4084]

noncomputable def reducedSource244 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1180 x + ((1 : ℝ) * Sparse.eval nodeValue1181 x + ((1 : ℝ) * Sparse.eval nodeValue1182 x + ((1 : ℝ) * Sparse.eval nodeValue1189 x + ((1 : ℝ) * Sparse.eval nodeValue1262 x + ((1 : ℝ) * Sparse.eval nodeValue2454 x + ((1 : ℝ) * Sparse.eval nodeValue2465 x + ((1 : ℝ) * Sparse.eval nodeValue2495 x + ((1 : ℝ) * Sparse.eval nodeValue2734 x + ((1 : ℝ) * Sparse.eval nodeValue2834 x + ((1 : ℝ) * Sparse.eval nodeValue2835 x + ((1 : ℝ) * Sparse.eval nodeValue2841 x + ((1 : ℝ) * Sparse.eval nodeValue2905 x + ((1 : ℝ) * Sparse.eval nodeValue2909 x + ((1 : ℝ) * Sparse.eval nodeValue2934 x + ((1 : ℝ) * Sparse.eval nodeValue2976 x + ((1 : ℝ) * Sparse.eval nodeValue2979 x + ((1 : ℝ) * Sparse.eval nodeValue2998 x + ((1 : ℝ) * Sparse.eval nodeValue3037 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((1 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3110 x + ((1 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3889 x + 0)))))))))))))))))))))))))))))

def numericRow244 : Integer.Sparse Master := [(Sum.inl 0, -772), (Sum.inl 6, 20), (Sum.inl 2, -480), (Sum.inl 3, -1600), (Sum.inl 13, -320), (Sum.inl 52, -320), (Sum.inl 12, -640), (Sum.inl 26, -320), (Sum.inl 4, -640), (Sum.inl 1, 1040), (Sum.inr 1180, 17280), (Sum.inr 1181, 17280), (Sum.inr 1182, 17280), (Sum.inr 1189, 17280), (Sum.inr 1262, 17280), (Sum.inr 2454, 17280), (Sum.inr 2465, 17280), (Sum.inr 2495, 17280), (Sum.inr 2734, 17280), (Sum.inr 2834, 17280), (Sum.inr 2835, 17280), (Sum.inr 2841, 17280), (Sum.inr 2905, 17280), (Sum.inr 2909, 17280), (Sum.inr 2976, 17280), (Sum.inr 2979, 17280), (Sum.inr 3037, 17280), (Sum.inr 3038, 17280), (Sum.inr 3039, 17280), (Sum.inr 3051, 17280), (Sum.inr 3055, 17280), (Sum.inr 3573, 17280), (Sum.inr 3872, 17280)]

theorem reindexCheck244 : Integer.Sparse.reindex keyMap MixedData.row244 = numericRow244 := by decide +kernel

theorem numericCheck244 (x : Master → ℝ) : Integer.Sparse.eval numericRow244 x =
    (17280 : ℝ) * reducedSource244 x := by
  norm_num [numericRow244, reducedSource244, Integer.Sparse.eval, Sparse.eval, nodeValue1180, nodeValue1181, nodeValue1182, nodeValue1189, nodeValue1262, nodeValue2454, nodeValue2465, nodeValue2495, nodeValue2734, nodeValue2834, nodeValue2835, nodeValue2841, nodeValue2905, nodeValue2909, nodeValue2934, nodeValue2976, nodeValue2979, nodeValue2998, nodeValue3037, nodeValue3038, nodeValue3039, nodeValue3051, nodeValue3055, nodeValue3109, nodeValue3110, nodeValue3573, nodeValue3853, nodeValue3872, nodeValue3883, nodeValue3889]; ring

noncomputable def reducedSource245 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2836 x + ((1 : ℝ) * Sparse.eval nodeValue2837 x + ((1 : ℝ) * Sparse.eval nodeValue2838 x + ((1 : ℝ) * Sparse.eval nodeValue2841 x + ((1 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3241 x + ((1 : ℝ) * Sparse.eval nodeValue3242 x + ((1 : ℝ) * Sparse.eval nodeValue3243 x + ((1 : ℝ) * Sparse.eval nodeValue3246 x + ((1 : ℝ) * Sparse.eval nodeValue3294 x + ((1 : ℝ) * Sparse.eval nodeValue3437 x + ((1 : ℝ) * Sparse.eval nodeValue3461 x + ((1 : ℝ) * Sparse.eval nodeValue3471 x + ((1 : ℝ) * Sparse.eval nodeValue3472 x + ((1 : ℝ) * Sparse.eval nodeValue3480 x + ((1 : ℝ) * Sparse.eval nodeValue3515 x + ((1 : ℝ) * Sparse.eval nodeValue3518 x + ((1 : ℝ) * Sparse.eval nodeValue3526 x + ((1 : ℝ) * Sparse.eval nodeValue3534 x + ((1 : ℝ) * Sparse.eval nodeValue3535 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((1 : ℝ) * Sparse.eval nodeValue3548 x + ((1 : ℝ) * Sparse.eval nodeValue3549 x + ((1 : ℝ) * Sparse.eval nodeValue3559 x + ((1 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((1 : ℝ) * Sparse.eval nodeValue3809 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3862 x + 0)))))))))))))))))))))))))))))

def numericRow245 : Integer.Sparse Master := [(Sum.inl 0, -11), (Sum.inl 2, -5), (Sum.inl 1, 10), (Sum.inr 2836, 720), (Sum.inr 2837, 720), (Sum.inr 2838, 720), (Sum.inr 2841, 720), (Sum.inr 3051, 720), (Sum.inr 3241, 720), (Sum.inr 3242, 720), (Sum.inr 3243, 720), (Sum.inr 3246, 720), (Sum.inr 3294, 720), (Sum.inr 3437, 720), (Sum.inr 3461, 720), (Sum.inr 3471, 720), (Sum.inr 3472, 720), (Sum.inr 3480, 720), (Sum.inr 3518, 720), (Sum.inr 3526, 720), (Sum.inr 3534, 720), (Sum.inr 3535, 720), (Sum.inr 3541, 720), (Sum.inr 3548, 720), (Sum.inr 3549, 720), (Sum.inr 3559, 720), (Sum.inr 3573, 720), (Sum.inr 3584, 720), (Sum.inr 3809, 720), (Sum.inr 3839, 720)]

theorem reindexCheck245 : Integer.Sparse.reindex keyMap MixedData.row245 = numericRow245 := by decide +kernel

theorem numericCheck245 (x : Master → ℝ) : Integer.Sparse.eval numericRow245 x =
    (720 : ℝ) * reducedSource245 x := by
  norm_num [numericRow245, reducedSource245, Integer.Sparse.eval, Sparse.eval, nodeValue2836, nodeValue2837, nodeValue2838, nodeValue2841, nodeValue3051, nodeValue3241, nodeValue3242, nodeValue3243, nodeValue3246, nodeValue3294, nodeValue3437, nodeValue3461, nodeValue3471, nodeValue3472, nodeValue3480, nodeValue3515, nodeValue3518, nodeValue3526, nodeValue3534, nodeValue3535, nodeValue3541, nodeValue3548, nodeValue3549, nodeValue3559, nodeValue3573, nodeValue3584, nodeValue3809, nodeValue3839, nodeValue3853, nodeValue3862]; ring

noncomputable def reducedSource246 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2731 x + ((1 : ℝ) * Sparse.eval nodeValue2773 x + ((1 : ℝ) * Sparse.eval nodeValue3813 x + ((1 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3906 x + ((1 : ℝ) * Sparse.eval nodeValue3907 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow246 : Integer.Sparse Master := [(Sum.inr 2731, 1), (Sum.inr 2773, 1), (Sum.inr 3813, 1), (Sum.inr 3840, 1), (Sum.inr 3906, 1), (Sum.inr 3907, 1), (Sum.inr 4092, -1)]

theorem reindexCheck246 : Integer.Sparse.reindex keyMap MixedData.row246 = numericRow246 := by decide +kernel

theorem numericCheck246 (x : Master → ℝ) : Integer.Sparse.eval numericRow246 x =
    (1 : ℝ) * reducedSource246 x := by
  norm_num [numericRow246, reducedSource246, Integer.Sparse.eval, Sparse.eval, nodeValue2731, nodeValue2773, nodeValue3813, nodeValue3840, nodeValue3906, nodeValue3907, nodeValue4092]

noncomputable def reducedSource247 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1222 x + ((1 : ℝ) * Sparse.eval nodeValue1224 x + ((1 : ℝ) * Sparse.eval nodeValue1226 x + ((1 : ℝ) * Sparse.eval nodeValue1237 x + ((1 : ℝ) * Sparse.eval nodeValue1277 x + ((1 : ℝ) * Sparse.eval nodeValue2731 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow247 : Integer.Sparse Master := [(Sum.inr 1222, 1), (Sum.inr 1224, 1), (Sum.inr 1226, 1), (Sum.inr 1237, 1), (Sum.inr 1277, 1), (Sum.inr 2731, 1), (Sum.inr 4092, -1)]

theorem reindexCheck247 : Integer.Sparse.reindex keyMap MixedData.row247 = numericRow247 := by decide +kernel

theorem numericCheck247 (x : Master → ℝ) : Integer.Sparse.eval numericRow247 x =
    (1 : ℝ) * reducedSource247 x := by
  norm_num [numericRow247, reducedSource247, Integer.Sparse.eval, Sparse.eval, nodeValue1222, nodeValue1224, nodeValue1226, nodeValue1237, nodeValue1277, nodeValue2731, nodeValue4092]

noncomputable def reducedSource248 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1277 x + ((1 : ℝ) * Sparse.eval nodeValue2577 x + ((1 : ℝ) * Sparse.eval nodeValue2650 x + ((1 : ℝ) * Sparse.eval nodeValue2731 x + ((1 : ℝ) * Sparse.eval nodeValue2773 x + ((1 : ℝ) * Sparse.eval nodeValue2774 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow248 : Integer.Sparse Master := [(Sum.inr 1277, 1), (Sum.inr 2577, 1), (Sum.inr 2650, 1), (Sum.inr 2731, 1), (Sum.inr 2773, 1), (Sum.inr 2774, 1), (Sum.inr 4092, -1)]

theorem reindexCheck248 : Integer.Sparse.reindex keyMap MixedData.row248 = numericRow248 := by decide +kernel

theorem numericCheck248 (x : Master → ℝ) : Integer.Sparse.eval numericRow248 x =
    (1 : ℝ) * reducedSource248 x := by
  norm_num [numericRow248, reducedSource248, Integer.Sparse.eval, Sparse.eval, nodeValue1277, nodeValue2577, nodeValue2650, nodeValue2731, nodeValue2773, nodeValue2774, nodeValue4092]

noncomputable def reducedSource249 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2493 x + ((1 : ℝ) * Sparse.eval nodeValue2495 x + ((1 : ℝ) * Sparse.eval nodeValue2499 x + ((1 : ℝ) * Sparse.eval nodeValue2512 x + ((1 : ℝ) * Sparse.eval nodeValue2731 x + ((1 : ℝ) * Sparse.eval nodeValue3813 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow249 : Integer.Sparse Master := [(Sum.inr 2493, 1), (Sum.inr 2495, 1), (Sum.inr 2499, 1), (Sum.inr 2512, 1), (Sum.inr 2731, 1), (Sum.inr 3813, 1), (Sum.inr 4092, -1)]

theorem reindexCheck249 : Integer.Sparse.reindex keyMap MixedData.row249 = numericRow249 := by decide +kernel

theorem numericCheck249 (x : Master → ℝ) : Integer.Sparse.eval numericRow249 x =
    (1 : ℝ) * reducedSource249 x := by
  norm_num [numericRow249, reducedSource249, Integer.Sparse.eval, Sparse.eval, nodeValue2493, nodeValue2495, nodeValue2499, nodeValue2512, nodeValue2731, nodeValue3813, nodeValue4092]

noncomputable def reducedSource250 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1222 x + ((1 : ℝ) * Sparse.eval nodeValue2493 x + ((1 : ℝ) * Sparse.eval nodeValue2645 x + ((1 : ℝ) * Sparse.eval nodeValue2730 x + ((2 : ℝ) * Sparse.eval nodeValue2731 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow250 : Integer.Sparse Master := [(Sum.inr 1222, 1), (Sum.inr 2493, 1), (Sum.inr 2645, 1), (Sum.inr 2730, 1), (Sum.inr 2731, 2), (Sum.inr 4092, -1)]

theorem reindexCheck250 : Integer.Sparse.reindex keyMap MixedData.row250 = numericRow250 := by decide +kernel

theorem numericCheck250 (x : Master → ℝ) : Integer.Sparse.eval numericRow250 x =
    (1 : ℝ) * reducedSource250 x := by
  norm_num [numericRow250, reducedSource250, Integer.Sparse.eval, Sparse.eval, nodeValue1222, nodeValue2493, nodeValue2645, nodeValue2730, nodeValue2731, nodeValue4092]

noncomputable def reducedSource251 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2547 x + ((1 : ℝ) * Sparse.eval nodeValue2549 x + ((1 : ℝ) * Sparse.eval nodeValue2554 x + ((1 : ℝ) * Sparse.eval nodeValue2577 x + ((1 : ℝ) * Sparse.eval nodeValue2731 x + ((1 : ℝ) * Sparse.eval nodeValue3840 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow251 : Integer.Sparse Master := [(Sum.inr 2547, 1), (Sum.inr 2549, 1), (Sum.inr 2577, 1), (Sum.inr 2731, 1), (Sum.inr 3840, 1), (Sum.inr 4092, -1)]

theorem reindexCheck251 : Integer.Sparse.reindex keyMap MixedData.row251 = numericRow251 := by decide +kernel

theorem numericCheck251 (x : Master → ℝ) : Integer.Sparse.eval numericRow251 x =
    (1 : ℝ) * reducedSource251 x := by
  norm_num [numericRow251, reducedSource251, Integer.Sparse.eval, Sparse.eval, nodeValue2547, nodeValue2549, nodeValue2554, nodeValue2577, nodeValue2731, nodeValue3840, nodeValue4092]

noncomputable def reducedSource252 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1237 x + ((1 : ℝ) * Sparse.eval nodeValue2512 x + ((1 : ℝ) * Sparse.eval nodeValue2554 x + ((1 : ℝ) * Sparse.eval nodeValue2731 x + ((1 : ℝ) * Sparse.eval nodeValue2739 x + ((1 : ℝ) * Sparse.eval nodeValue2743 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow252 : Integer.Sparse Master := [(Sum.inr 1237, 1), (Sum.inr 2512, 1), (Sum.inr 2731, 1), (Sum.inr 2739, 1), (Sum.inr 2743, 1), (Sum.inr 4092, -1)]

theorem reindexCheck252 : Integer.Sparse.reindex keyMap MixedData.row252 = numericRow252 := by decide +kernel

theorem numericCheck252 (x : Master → ℝ) : Integer.Sparse.eval numericRow252 x =
    (1 : ℝ) * reducedSource252 x := by
  norm_num [numericRow252, reducedSource252, Integer.Sparse.eval, Sparse.eval, nodeValue1237, nodeValue2512, nodeValue2554, nodeValue2731, nodeValue2739, nodeValue2743, nodeValue4092]

noncomputable def reducedSource253 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2645 x + ((1 : ℝ) * Sparse.eval nodeValue2647 x + ((1 : ℝ) * Sparse.eval nodeValue2649 x + ((1 : ℝ) * Sparse.eval nodeValue2650 x + ((1 : ℝ) * Sparse.eval nodeValue2731 x + ((1 : ℝ) * Sparse.eval nodeValue2773 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow253 : Integer.Sparse Master := [(Sum.inr 2645, 1), (Sum.inr 2647, 1), (Sum.inr 2649, 1), (Sum.inr 2650, 1), (Sum.inr 2731, 1), (Sum.inr 2773, 1), (Sum.inr 4092, -1)]

theorem reindexCheck253 : Integer.Sparse.reindex keyMap MixedData.row253 = numericRow253 := by decide +kernel

theorem numericCheck253 (x : Master → ℝ) : Integer.Sparse.eval numericRow253 x =
    (1 : ℝ) * reducedSource253 x := by
  norm_num [numericRow253, reducedSource253, Integer.Sparse.eval, Sparse.eval, nodeValue2645, nodeValue2647, nodeValue2649, nodeValue2650, nodeValue2731, nodeValue2773, nodeValue4092]

noncomputable def reducedSource254 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1226 x + ((1 : ℝ) * Sparse.eval nodeValue2499 x + ((1 : ℝ) * Sparse.eval nodeValue2549 x + ((1 : ℝ) * Sparse.eval nodeValue2649 x + ((1 : ℝ) * Sparse.eval nodeValue2731 x + ((1 : ℝ) * Sparse.eval nodeValue2732 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow254 : Integer.Sparse Master := [(Sum.inr 1226, 1), (Sum.inr 2499, 1), (Sum.inr 2549, 1), (Sum.inr 2649, 1), (Sum.inr 2731, 1), (Sum.inr 2732, 1), (Sum.inr 4092, -1)]

theorem reindexCheck254 : Integer.Sparse.reindex keyMap MixedData.row254 = numericRow254 := by decide +kernel

theorem numericCheck254 (x : Master → ℝ) : Integer.Sparse.eval numericRow254 x =
    (1 : ℝ) * reducedSource254 x := by
  norm_num [numericRow254, reducedSource254, Integer.Sparse.eval, Sparse.eval, nodeValue1226, nodeValue2499, nodeValue2549, nodeValue2649, nodeValue2731, nodeValue2732, nodeValue4092]

noncomputable def reducedSource255 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue988 x + ((1 : ℝ) * Sparse.eval nodeValue989 x + ((1 : ℝ) * Sparse.eval nodeValue993 x + ((1 : ℝ) * Sparse.eval nodeValue1001 x + ((1 : ℝ) * Sparse.eval nodeValue1057 x + ((1 : ℝ) * Sparse.eval nodeValue2390 x + ((1 : ℝ) * Sparse.eval nodeValue2391 x + ((1 : ℝ) * Sparse.eval nodeValue2395 x + ((1 : ℝ) * Sparse.eval nodeValue2401 x + ((1 : ℝ) * Sparse.eval nodeValue2453 x + ((1 : ℝ) * Sparse.eval nodeValue2456 x + ((1 : ℝ) * Sparse.eval nodeValue2460 x + ((1 : ℝ) * Sparse.eval nodeValue2493 x + ((1 : ℝ) * Sparse.eval nodeValue2569 x + ((1 : ℝ) * Sparse.eval nodeValue2615 x + ((1 : ℝ) * Sparse.eval nodeValue2621 x + ((1 : ℝ) * Sparse.eval nodeValue2637 x + ((1 : ℝ) * Sparse.eval nodeValue2664 x + ((1 : ℝ) * Sparse.eval nodeValue2698 x + ((1 : ℝ) * Sparse.eval nodeValue2706 x + ((1 : ℝ) * Sparse.eval nodeValue2730 x + ((2 : ℝ) * Sparse.eval nodeValue2731 x + ((1 : ℝ) * Sparse.eval nodeValue2738 x + ((1 : ℝ) * Sparse.eval nodeValue2775 x + ((1 : ℝ) * Sparse.eval nodeValue3880 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3885 x + ((1 : ℝ) * Sparse.eval nodeValue3887 x + ((1 : ℝ) * Sparse.eval nodeValue3995 x + 0))))))))))))))))))))))))))))

def numericRow255 : Integer.Sparse Master := [(Sum.inl 0, -192), (Sum.inl 5, -40), (Sum.inl 6, 10), (Sum.inl 2, -90), (Sum.inl 51, 480), (Sum.inl 3, -1280), (Sum.inl 13, -320), (Sum.inl 52, -160), (Sum.inl 12, -640), (Sum.inl 4, -640), (Sum.inl 1, -20), (Sum.inl 31, 480), (Sum.inr 988, 8640), (Sum.inr 989, 8640), (Sum.inr 993, 8640), (Sum.inr 1001, 8640), (Sum.inr 1057, 8640), (Sum.inr 2390, 8640), (Sum.inr 2391, 8640), (Sum.inr 2395, 8640), (Sum.inr 2401, 8640), (Sum.inr 2453, 8640), (Sum.inr 2456, 8640), (Sum.inr 2460, 8640), (Sum.inr 2493, 8640), (Sum.inr 2569, 8640), (Sum.inr 2615, 8640), (Sum.inr 2621, 8640), (Sum.inr 2664, 8640), (Sum.inr 2698, 8640), (Sum.inr 2706, 8640), (Sum.inr 2730, 8640), (Sum.inr 2731, 17280), (Sum.inr 2738, 8640), (Sum.inr 3880, 8640), (Sum.inr 3884, 8640), (Sum.inr 3885, 8640)]

theorem reindexCheck255 : Integer.Sparse.reindex keyMap MixedData.row255 = numericRow255 := by decide +kernel

theorem numericCheck255 (x : Master → ℝ) : Integer.Sparse.eval numericRow255 x =
    (8640 : ℝ) * reducedSource255 x := by
  norm_num [numericRow255, reducedSource255, Integer.Sparse.eval, Sparse.eval, nodeValue988, nodeValue989, nodeValue993, nodeValue1001, nodeValue1057, nodeValue2390, nodeValue2391, nodeValue2395, nodeValue2401, nodeValue2453, nodeValue2456, nodeValue2460, nodeValue2493, nodeValue2569, nodeValue2615, nodeValue2621, nodeValue2637, nodeValue2664, nodeValue2698, nodeValue2706, nodeValue2730, nodeValue2731, nodeValue2738, nodeValue2775, nodeValue3880, nodeValue3884, nodeValue3885, nodeValue3887, nodeValue3995]; ring

end MUB6.Certificate.MixedSourceBridge

end OAI
