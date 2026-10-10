import OAI.Analysis.MutuallyUnbiased.MixedData.Source1
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource208 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2603 x + ((2 : ℝ) * Sparse.eval nodeValue3050 x + ((1 : ℝ) * Sparse.eval nodeValue3052 x + ((1 : ℝ) * Sparse.eval nodeValue3056 x + ((1 : ℝ) * Sparse.eval nodeValue3582 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow208 : Integer.Sparse Master := [(Sum.inr 2603, 1), (Sum.inr 3050, 2), (Sum.inr 3052, 1), (Sum.inr 3056, 1), (Sum.inr 3582, 1), (Sum.inr 4084, -1)]

theorem reindexCheck208 : Integer.Sparse.reindex keyMap MixedData.row208 = numericRow208 := by decide +kernel

theorem numericCheck208 (x : Master → ℝ) : Integer.Sparse.eval numericRow208 x =
    (1 : ℝ) * reducedSource208 x := by
  norm_num [numericRow208, reducedSource208, Integer.Sparse.eval, Sparse.eval, nodeValue2603, nodeValue3050, nodeValue3052, nodeValue3056, nodeValue3582, nodeValue4084]

noncomputable def reducedSource209 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1374 x + ((1 : ℝ) * Sparse.eval nodeValue2888 x + ((2 : ℝ) * Sparse.eval nodeValue2978 x + ((1 : ℝ) * Sparse.eval nodeValue3052 x + ((1 : ℝ) * Sparse.eval nodeValue3056 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow209 : Integer.Sparse Master := [(Sum.inr 1374, 1), (Sum.inr 2888, 1), (Sum.inr 2978, 2), (Sum.inr 3052, 1), (Sum.inr 3056, 1), (Sum.inr 4084, -1)]

theorem reindexCheck209 : Integer.Sparse.reindex keyMap MixedData.row209 = numericRow209 := by decide +kernel

theorem numericCheck209 (x : Master → ℝ) : Integer.Sparse.eval numericRow209 x =
    (1 : ℝ) * reducedSource209 x := by
  norm_num [numericRow209, reducedSource209, Integer.Sparse.eval, Sparse.eval, nodeValue1374, nodeValue2888, nodeValue2978, nodeValue3052, nodeValue3056, nodeValue4084]

noncomputable def reducedSource210 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2035 x + ((1 : ℝ) * Sparse.eval nodeValue2597 x + ((1 : ℝ) * Sparse.eval nodeValue2973 x + ((1 : ℝ) * Sparse.eval nodeValue2978 x + ((1 : ℝ) * Sparse.eval nodeValue3052 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow210 : Integer.Sparse Master := [(Sum.inr 2035, 1), (Sum.inr 2597, 1), (Sum.inr 2973, 1), (Sum.inr 2978, 1), (Sum.inr 3052, 1), (Sum.inr 3540, 1), (Sum.inr 4084, -1)]

theorem reindexCheck210 : Integer.Sparse.reindex keyMap MixedData.row210 = numericRow210 := by decide +kernel

theorem numericCheck210 (x : Master → ℝ) : Integer.Sparse.eval numericRow210 x =
    (1 : ℝ) * reducedSource210 x := by
  norm_num [numericRow210, reducedSource210, Integer.Sparse.eval, Sparse.eval, nodeValue2035, nodeValue2597, nodeValue2973, nodeValue2978, nodeValue3052, nodeValue3540, nodeValue4084]

noncomputable def reducedSource211 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3052 x + ((2 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3548 x + ((1 : ℝ) * Sparse.eval nodeValue3582 x + ((1 : ℝ) * Sparse.eval nodeValue3633 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow211 : Integer.Sparse Master := [(Sum.inr 3052, 1), (Sum.inr 3540, 2), (Sum.inr 3548, 1), (Sum.inr 3582, 1), (Sum.inr 3633, 1), (Sum.inr 4084, -1)]

theorem reindexCheck211 : Integer.Sparse.reindex keyMap MixedData.row211 = numericRow211 := by decide +kernel

theorem numericCheck211 (x : Master → ℝ) : Integer.Sparse.eval numericRow211 x =
    (1 : ℝ) * reducedSource211 x := by
  norm_num [numericRow211, reducedSource211, Integer.Sparse.eval, Sparse.eval, nodeValue3052, nodeValue3540, nodeValue3548, nodeValue3582, nodeValue3633, nodeValue4084]

noncomputable def reducedSource212 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2062 x + ((2 : ℝ) * Sparse.eval nodeValue2879 x + ((1 : ℝ) * Sparse.eval nodeValue2888 x + ((1 : ℝ) * Sparse.eval nodeValue3052 x + ((1 : ℝ) * Sparse.eval nodeValue3548 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow212 : Integer.Sparse Master := [(Sum.inr 2062, 1), (Sum.inr 2879, 2), (Sum.inr 2888, 1), (Sum.inr 3052, 1), (Sum.inr 3548, 1), (Sum.inr 4084, -1)]

theorem reindexCheck212 : Integer.Sparse.reindex keyMap MixedData.row212 = numericRow212 := by decide +kernel

theorem numericCheck212 (x : Master → ℝ) : Integer.Sparse.eval numericRow212 x =
    (1 : ℝ) * reducedSource212 x := by
  norm_num [numericRow212, reducedSource212, Integer.Sparse.eval, Sparse.eval, nodeValue2062, nodeValue2879, nodeValue2888, nodeValue3052, nodeValue3548, nodeValue4084]

noncomputable def reducedSource213 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1210 x + ((1 : ℝ) * Sparse.eval nodeValue1211 x + ((1 : ℝ) * Sparse.eval nodeValue1219 x + ((1 : ℝ) * Sparse.eval nodeValue1230 x + ((1 : ℝ) * Sparse.eval nodeValue1261 x + ((1 : ℝ) * Sparse.eval nodeValue2071 x + ((1 : ℝ) * Sparse.eval nodeValue2080 x + ((1 : ℝ) * Sparse.eval nodeValue2090 x + ((1 : ℝ) * Sparse.eval nodeValue2197 x + ((1 : ℝ) * Sparse.eval nodeValue2860 x + ((1 : ℝ) * Sparse.eval nodeValue2867 x + ((1 : ℝ) * Sparse.eval nodeValue2876 x + ((1 : ℝ) * Sparse.eval nodeValue2916 x + ((1 : ℝ) * Sparse.eval nodeValue2922 x + ((1 : ℝ) * Sparse.eval nodeValue2933 x + ((1 : ℝ) * Sparse.eval nodeValue2984 x + ((1 : ℝ) * Sparse.eval nodeValue2990 x + ((1 : ℝ) * Sparse.eval nodeValue2997 x + ((1 : ℝ) * Sparse.eval nodeValue3016 x + ((1 : ℝ) * Sparse.eval nodeValue3025 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3085 x + ((1 : ℝ) * Sparse.eval nodeValue3089 x + ((1 : ℝ) * Sparse.eval nodeValue3097 x + ((1 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3814 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3982 x + 0)))))))))))))))))))))))))))))

def numericRow213 : Integer.Sparse Master := [(Sum.inl 0, -772), (Sum.inl 5, 160), (Sum.inl 6, 20), (Sum.inl 2, -540), (Sum.inl 7, -640), (Sum.inl 35, -640), (Sum.inl 3, -3200), (Sum.inl 13, -320), (Sum.inl 52, -320), (Sum.inl 12, -640), (Sum.inl 26, -1280), (Sum.inl 4, -1280), (Sum.inl 1, 1220), (Sum.inr 1210, 17280), (Sum.inr 1211, 17280), (Sum.inr 1219, 17280), (Sum.inr 1230, 17280), (Sum.inr 1261, 17280), (Sum.inr 2071, 17280), (Sum.inr 2080, 17280), (Sum.inr 2090, 17280), (Sum.inr 2197, 17280), (Sum.inr 2860, 17280), (Sum.inr 2867, 17280), (Sum.inr 2876, 17280), (Sum.inr 2916, 17280), (Sum.inr 2922, 17280), (Sum.inr 2933, 17280), (Sum.inr 2984, 17280), (Sum.inr 3016, 17280), (Sum.inr 3025, 17280), (Sum.inr 3038, 17280), (Sum.inr 3097, 17280), (Sum.inr 3814, 17280), (Sum.inr 3872, 17280), (Sum.inr 3877, 17280)]

theorem reindexCheck213 : Integer.Sparse.reindex keyMap MixedData.row213 = numericRow213 := by decide +kernel

theorem numericCheck213 (x : Master → ℝ) : Integer.Sparse.eval numericRow213 x =
    (17280 : ℝ) * reducedSource213 x := by
  norm_num [numericRow213, reducedSource213, Integer.Sparse.eval, Sparse.eval, nodeValue1210, nodeValue1211, nodeValue1219, nodeValue1230, nodeValue1261, nodeValue2071, nodeValue2080, nodeValue2090, nodeValue2197, nodeValue2860, nodeValue2867, nodeValue2876, nodeValue2916, nodeValue2922, nodeValue2933, nodeValue2984, nodeValue2990, nodeValue2997, nodeValue3016, nodeValue3025, nodeValue3038, nodeValue3085, nodeValue3089, nodeValue3097, nodeValue3109, nodeValue3814, nodeValue3872, nodeValue3877, nodeValue3883, nodeValue3982]
  ring

noncomputable def reducedSource214 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2043 x + ((1 : ℝ) * Sparse.eval nodeValue2045 x + ((1 : ℝ) * Sparse.eval nodeValue2049 x + ((1 : ℝ) * Sparse.eval nodeValue2055 x + ((1 : ℝ) * Sparse.eval nodeValue2259 x + ((1 : ℝ) * Sparse.eval nodeValue3285 x + ((1 : ℝ) * Sparse.eval nodeValue3287 x + ((1 : ℝ) * Sparse.eval nodeValue3295 x + ((1 : ℝ) * Sparse.eval nodeValue3296 x + ((1 : ℝ) * Sparse.eval nodeValue3463 x + ((1 : ℝ) * Sparse.eval nodeValue3478 x + ((1 : ℝ) * Sparse.eval nodeValue3479 x + ((1 : ℝ) * Sparse.eval nodeValue3516 x + ((1 : ℝ) * Sparse.eval nodeValue3517 x + ((1 : ℝ) * Sparse.eval nodeValue3525 x + ((1 : ℝ) * Sparse.eval nodeValue3527 x + ((1 : ℝ) * Sparse.eval nodeValue3528 x + ((1 : ℝ) * Sparse.eval nodeValue3533 x + ((1 : ℝ) * Sparse.eval nodeValue3534 x + ((1 : ℝ) * Sparse.eval nodeValue3538 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((1 : ℝ) * Sparse.eval nodeValue3560 x + ((1 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3575 x + ((1 : ℝ) * Sparse.eval nodeValue3577 x + ((1 : ℝ) * Sparse.eval nodeValue3813 x + ((1 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3854 x + ((1 : ℝ) * Sparse.eval nodeValue3856 x + 0)))))))))))))))))))))))))))))

def numericRow214 : Integer.Sparse Master := [(Sum.inl 0, -66), (Sum.inl 2, -45), (Sum.inl 3, -240), (Sum.inl 13, -160), (Sum.inl 4, -80), (Sum.inl 1, -15), (Sum.inr 2043, 4320), (Sum.inr 2045, 4320), (Sum.inr 2049, 4320), (Sum.inr 2055, 4320), (Sum.inr 2259, 4320), (Sum.inr 3285, 4320), (Sum.inr 3287, 4320), (Sum.inr 3295, 4320), (Sum.inr 3296, 4320), (Sum.inr 3463, 4320), (Sum.inr 3478, 4320), (Sum.inr 3479, 4320), (Sum.inr 3516, 4320), (Sum.inr 3517, 4320), (Sum.inr 3527, 4320), (Sum.inr 3528, 4320), (Sum.inr 3533, 4320), (Sum.inr 3534, 4320), (Sum.inr 3538, 4320), (Sum.inr 3541, 4320), (Sum.inr 3560, 4320), (Sum.inr 3572, 4320), (Sum.inr 3575, 4320), (Sum.inr 3577, 4320), (Sum.inr 3813, 4320), (Sum.inr 3840, 4320), (Sum.inr 3854, 4320)]

theorem reindexCheck214 : Integer.Sparse.reindex keyMap MixedData.row214 = numericRow214 := by decide +kernel

theorem numericCheck214 (x : Master → ℝ) : Integer.Sparse.eval numericRow214 x =
    (4320 : ℝ) * reducedSource214 x := by
  norm_num [numericRow214, reducedSource214, Integer.Sparse.eval, Sparse.eval, nodeValue2043, nodeValue2045, nodeValue2049, nodeValue2055, nodeValue2259, nodeValue3285, nodeValue3287, nodeValue3295, nodeValue3296, nodeValue3463, nodeValue3478, nodeValue3479, nodeValue3516, nodeValue3517, nodeValue3525, nodeValue3527, nodeValue3528, nodeValue3533, nodeValue3534, nodeValue3538, nodeValue3541, nodeValue3560, nodeValue3572, nodeValue3575, nodeValue3577, nodeValue3813, nodeValue3840, nodeValue3852, nodeValue3854, nodeValue3856]
  ring

noncomputable def reducedSource215 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2724 x + ((1 : ℝ) * Sparse.eval nodeValue3809 x + ((1 : ℝ) * Sparse.eval nodeValue3814 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3903 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow215 : Integer.Sparse Master := [(Sum.inr 2724, 1), (Sum.inr 3809, 1), (Sum.inr 3814, 1), (Sum.inr 3839, 1), (Sum.inr 3877, 1), (Sum.inr 3903, 1), (Sum.inr 4092, -1)]

theorem reindexCheck215 : Integer.Sparse.reindex keyMap MixedData.row215 = numericRow215 := by decide +kernel

theorem numericCheck215 (x : Master → ℝ) : Integer.Sparse.eval numericRow215 x =
    (1 : ℝ) * reducedSource215 x := by
  norm_num [numericRow215, reducedSource215, Integer.Sparse.eval, Sparse.eval, nodeValue2724, nodeValue3809, nodeValue3814, nodeValue3839, nodeValue3877, nodeValue3903, nodeValue4092]

noncomputable def reducedSource216 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1214 x + ((1 : ℝ) * Sparse.eval nodeValue1218 x + ((1 : ℝ) * Sparse.eval nodeValue1219 x + ((1 : ℝ) * Sparse.eval nodeValue1241 x + ((1 : ℝ) * Sparse.eval nodeValue1263 x + ((1 : ℝ) * Sparse.eval nodeValue2724 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow216 : Integer.Sparse Master := [(Sum.inr 1214, 1), (Sum.inr 1218, 1), (Sum.inr 1219, 1), (Sum.inr 1241, 1), (Sum.inr 1263, 1), (Sum.inr 2724, 1), (Sum.inr 4092, -1)]

theorem reindexCheck216 : Integer.Sparse.reindex keyMap MixedData.row216 = numericRow216 := by decide +kernel

theorem numericCheck216 (x : Master → ℝ) : Integer.Sparse.eval numericRow216 x =
    (1 : ℝ) * reducedSource216 x := by
  norm_num [numericRow216, reducedSource216, Integer.Sparse.eval, Sparse.eval, nodeValue1214, nodeValue1218, nodeValue1219, nodeValue1241, nodeValue1263, nodeValue2724, nodeValue4092]

noncomputable def reducedSource217 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1263 x + ((1 : ℝ) * Sparse.eval nodeValue2568 x + ((1 : ℝ) * Sparse.eval nodeValue2634 x + ((1 : ℝ) * Sparse.eval nodeValue2724 x + ((1 : ℝ) * Sparse.eval nodeValue2758 x + ((1 : ℝ) * Sparse.eval nodeValue2763 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow217 : Integer.Sparse Master := [(Sum.inr 1263, 1), (Sum.inr 2568, 1), (Sum.inr 2634, 1), (Sum.inr 2724, 1), (Sum.inr 2758, 1), (Sum.inr 2763, 1), (Sum.inr 4092, -1)]

theorem reindexCheck217 : Integer.Sparse.reindex keyMap MixedData.row217 = numericRow217 := by decide +kernel

theorem numericCheck217 (x : Master → ℝ) : Integer.Sparse.eval numericRow217 x =
    (1 : ℝ) * reducedSource217 x := by
  norm_num [numericRow217, reducedSource217, Integer.Sparse.eval, Sparse.eval, nodeValue1263, nodeValue2568, nodeValue2634, nodeValue2724, nodeValue2758, nodeValue2763, nodeValue4092]

noncomputable def reducedSource218 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2481 x + ((1 : ℝ) * Sparse.eval nodeValue2486 x + ((1 : ℝ) * Sparse.eval nodeValue2488 x + ((1 : ℝ) * Sparse.eval nodeValue2515 x + ((1 : ℝ) * Sparse.eval nodeValue2724 x + ((1 : ℝ) * Sparse.eval nodeValue3809 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow218 : Integer.Sparse Master := [(Sum.inr 2481, 1), (Sum.inr 2486, 1), (Sum.inr 2488, 1), (Sum.inr 2515, 1), (Sum.inr 2724, 1), (Sum.inr 3809, 1), (Sum.inr 4092, -1)]

theorem reindexCheck218 : Integer.Sparse.reindex keyMap MixedData.row218 = numericRow218 := by decide +kernel

theorem numericCheck218 (x : Master → ℝ) : Integer.Sparse.eval numericRow218 x =
    (1 : ℝ) * reducedSource218 x := by
  norm_num [numericRow218, reducedSource218, Integer.Sparse.eval, Sparse.eval, nodeValue2481, nodeValue2486, nodeValue2488, nodeValue2515, nodeValue2724, nodeValue3809, nodeValue4092]

noncomputable def reducedSource219 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1214 x + ((1 : ℝ) * Sparse.eval nodeValue2481 x + ((1 : ℝ) * Sparse.eval nodeValue2616 x + ((1 : ℝ) * Sparse.eval nodeValue2714 x + ((1 : ℝ) * Sparse.eval nodeValue2720 x + ((1 : ℝ) * Sparse.eval nodeValue2724 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow219 : Integer.Sparse Master := [(Sum.inr 1214, 1), (Sum.inr 2481, 1), (Sum.inr 2616, 1), (Sum.inr 2714, 1), (Sum.inr 2724, 1), (Sum.inr 4092, -1)]

theorem reindexCheck219 : Integer.Sparse.reindex keyMap MixedData.row219 = numericRow219 := by decide +kernel

theorem numericCheck219 (x : Master → ℝ) : Integer.Sparse.eval numericRow219 x =
    (1 : ℝ) * reducedSource219 x := by
  norm_num [numericRow219, reducedSource219, Integer.Sparse.eval, Sparse.eval, nodeValue1214, nodeValue2481, nodeValue2616, nodeValue2714, nodeValue2720, nodeValue2724, nodeValue4092]

noncomputable def reducedSource220 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2544 x + ((1 : ℝ) * Sparse.eval nodeValue2545 x + ((1 : ℝ) * Sparse.eval nodeValue2557 x + ((1 : ℝ) * Sparse.eval nodeValue2568 x + ((1 : ℝ) * Sparse.eval nodeValue2724 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow220 : Integer.Sparse Master := [(Sum.inr 2544, 1), (Sum.inr 2545, 1), (Sum.inr 2557, 1), (Sum.inr 2568, 1), (Sum.inr 2724, 1), (Sum.inr 3839, 1), (Sum.inr 4092, -1)]

theorem reindexCheck220 : Integer.Sparse.reindex keyMap MixedData.row220 = numericRow220 := by decide +kernel

theorem numericCheck220 (x : Master → ℝ) : Integer.Sparse.eval numericRow220 x =
    (1 : ℝ) * reducedSource220 x := by
  norm_num [numericRow220, reducedSource220, Integer.Sparse.eval, Sparse.eval, nodeValue2544, nodeValue2545, nodeValue2557, nodeValue2568, nodeValue2724, nodeValue3839, nodeValue4092]

noncomputable def reducedSource221 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1241 x + ((1 : ℝ) * Sparse.eval nodeValue2515 x + ((1 : ℝ) * Sparse.eval nodeValue2557 x + ((1 : ℝ) * Sparse.eval nodeValue2724 x + ((1 : ℝ) * Sparse.eval nodeValue2732 x + ((1 : ℝ) * Sparse.eval nodeValue2739 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow221 : Integer.Sparse Master := [(Sum.inr 1241, 1), (Sum.inr 2515, 1), (Sum.inr 2557, 1), (Sum.inr 2724, 1), (Sum.inr 2732, 1), (Sum.inr 2739, 1), (Sum.inr 4092, -1)]

theorem reindexCheck221 : Integer.Sparse.reindex keyMap MixedData.row221 = numericRow221 := by decide +kernel

theorem numericCheck221 (x : Master → ℝ) : Integer.Sparse.eval numericRow221 x =
    (1 : ℝ) * reducedSource221 x := by
  norm_num [numericRow221, reducedSource221, Integer.Sparse.eval, Sparse.eval, nodeValue1241, nodeValue2515, nodeValue2557, nodeValue2724, nodeValue2732, nodeValue2739, nodeValue4092]

noncomputable def reducedSource222 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2616 x + ((1 : ℝ) * Sparse.eval nodeValue2619 x + ((1 : ℝ) * Sparse.eval nodeValue2620 x + ((1 : ℝ) * Sparse.eval nodeValue2634 x + ((1 : ℝ) * Sparse.eval nodeValue2724 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow222 : Integer.Sparse Master := [(Sum.inr 2616, 1), (Sum.inr 2619, 1), (Sum.inr 2620, 1), (Sum.inr 2634, 1), (Sum.inr 2724, 1), (Sum.inr 3877, 1), (Sum.inr 4092, -1)]

theorem reindexCheck222 : Integer.Sparse.reindex keyMap MixedData.row222 = numericRow222 := by decide +kernel

theorem numericCheck222 (x : Master → ℝ) : Integer.Sparse.eval numericRow222 x =
    (1 : ℝ) * reducedSource222 x := by
  norm_num [numericRow222, reducedSource222, Integer.Sparse.eval, Sparse.eval, nodeValue2616, nodeValue2619, nodeValue2620, nodeValue2634, nodeValue2724, nodeValue3877, nodeValue4092]

noncomputable def reducedSource223 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1219 x + ((1 : ℝ) * Sparse.eval nodeValue2488 x + ((1 : ℝ) * Sparse.eval nodeValue2545 x + ((1 : ℝ) * Sparse.eval nodeValue2620 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue2724 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow223 : Integer.Sparse Master := [(Sum.inr 1219, 1), (Sum.inr 2488, 1), (Sum.inr 2545, 1), (Sum.inr 2620, 1), (Sum.inr 2722, 1), (Sum.inr 2724, 1), (Sum.inr 4092, -1)]

theorem reindexCheck223 : Integer.Sparse.reindex keyMap MixedData.row223 = numericRow223 := by decide +kernel

theorem numericCheck223 (x : Master → ℝ) : Integer.Sparse.eval numericRow223 x =
    (1 : ℝ) * reducedSource223 x := by
  norm_num [numericRow223, reducedSource223, Integer.Sparse.eval, Sparse.eval, nodeValue1219, nodeValue2488, nodeValue2545, nodeValue2620, nodeValue2722, nodeValue2724, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
