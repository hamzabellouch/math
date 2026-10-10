import OAI.Analysis.MutuallyUnbiased.MixedData.Source2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values49
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

noncomputable def reducedSource272 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2266 x + ((2 : ℝ) * Sparse.eval nodeValue3535 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((1 : ℝ) * Sparse.eval nodeValue3626 x + ((1 : ℝ) * Sparse.eval nodeValue3627 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow272 : Integer.Sparse Master := [(Sum.inr 2266, 1), (Sum.inr 3535, 2), (Sum.inr 3584, 1), (Sum.inr 3626, 1), (Sum.inr 3627, 1), (Sum.inr 4084, -1)]

theorem reindexCheck272 : Integer.Sparse.reindex keyMap MixedData.row272 = numericRow272 := by decide +kernel

theorem numericCheck272 (x : Master → ℝ) : Integer.Sparse.eval numericRow272 x =
    (1 : ℝ) * reducedSource272 x := by
  norm_num [numericRow272, reducedSource272, Integer.Sparse.eval, Sparse.eval, nodeValue2266, nodeValue3535, nodeValue3584, nodeValue3626, nodeValue3627, nodeValue4084]

noncomputable def reducedSource273 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3159 x + ((1 : ℝ) * Sparse.eval nodeValue3377 x + ((1 : ℝ) * Sparse.eval nodeValue3379 x + ((2 : ℝ) * Sparse.eval nodeValue3395 x + ((1 : ℝ) * Sparse.eval nodeValue3535 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow273 : Integer.Sparse Master := [(Sum.inr 3159, 1), (Sum.inr 3377, 1), (Sum.inr 3379, 1), (Sum.inr 3395, 2), (Sum.inr 3535, 1), (Sum.inr 4084, -1)]

theorem reindexCheck273 : Integer.Sparse.reindex keyMap MixedData.row273 = numericRow273 := by decide +kernel

theorem numericCheck273 (x : Master → ℝ) : Integer.Sparse.eval numericRow273 x =
    (1 : ℝ) * reducedSource273 x := by
  norm_num [numericRow273, reducedSource273, Integer.Sparse.eval, Sparse.eval, nodeValue3159, nodeValue3377, nodeValue3379, nodeValue3395, nodeValue3535, nodeValue4084]

noncomputable def reducedSource274 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2021 x + ((1 : ℝ) * Sparse.eval nodeValue3377 x + ((1 : ℝ) * Sparse.eval nodeValue3504 x + ((1 : ℝ) * Sparse.eval nodeValue3528 x + ((1 : ℝ) * Sparse.eval nodeValue3531 x + ((1 : ℝ) * Sparse.eval nodeValue3535 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow274 : Integer.Sparse Master := [(Sum.inr 2021, 1), (Sum.inr 3377, 1), (Sum.inr 3504, 1), (Sum.inr 3528, 1), (Sum.inr 3535, 1), (Sum.inr 4084, -1)]

theorem reindexCheck274 : Integer.Sparse.reindex keyMap MixedData.row274 = numericRow274 := by decide +kernel

theorem numericCheck274 (x : Master → ℝ) : Integer.Sparse.eval numericRow274 x =
    (1 : ℝ) * reducedSource274 x := by
  norm_num [numericRow274, reducedSource274, Integer.Sparse.eval, Sparse.eval, nodeValue2021, nodeValue3377, nodeValue3504, nodeValue3528, nodeValue3531, nodeValue3535, nodeValue4084]

noncomputable def reducedSource275 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3153 x + ((1 : ℝ) * Sparse.eval nodeValue3388 x + ((1 : ℝ) * Sparse.eval nodeValue3488 x + ((1 : ℝ) * Sparse.eval nodeValue3497 x + ((2 : ℝ) * Sparse.eval nodeValue3535 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow275 : Integer.Sparse Master := [(Sum.inr 3153, 1), (Sum.inr 3388, 1), (Sum.inr 3488, 1), (Sum.inr 3497, 1), (Sum.inr 3535, 2), (Sum.inr 4084, -1)]

theorem reindexCheck275 : Integer.Sparse.reindex keyMap MixedData.row275 = numericRow275 := by decide +kernel

theorem numericCheck275 (x : Master → ℝ) : Integer.Sparse.eval numericRow275 x =
    (1 : ℝ) * reducedSource275 x := by
  norm_num [numericRow275, reducedSource275, Integer.Sparse.eval, Sparse.eval, nodeValue3153, nodeValue3388, nodeValue3488, nodeValue3497, nodeValue3535, nodeValue4084]

noncomputable def reducedSource276 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2026 x + ((1 : ℝ) * Sparse.eval nodeValue3153 x + ((1 : ℝ) * Sparse.eval nodeValue3156 x + ((1 : ℝ) * Sparse.eval nodeValue3157 x + ((1 : ℝ) * Sparse.eval nodeValue3159 x + ((1 : ℝ) * Sparse.eval nodeValue3535 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow276 : Integer.Sparse Master := [(Sum.inr 2026, 1), (Sum.inr 3153, 1), (Sum.inr 3156, 1), (Sum.inr 3157, 1), (Sum.inr 3159, 1), (Sum.inr 3535, 1), (Sum.inr 4084, -1)]

theorem reindexCheck276 : Integer.Sparse.reindex keyMap MixedData.row276 = numericRow276 := by decide +kernel

theorem numericCheck276 (x : Master → ℝ) : Integer.Sparse.eval numericRow276 x =
    (1 : ℝ) * reducedSource276 x := by
  norm_num [numericRow276, reducedSource276, Integer.Sparse.eval, Sparse.eval, nodeValue2026, nodeValue3153, nodeValue3156, nodeValue3157, nodeValue3159, nodeValue3535, nodeValue4084]

noncomputable def reducedSource277 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3531 x + ((1 : ℝ) * Sparse.eval nodeValue3533 x + ((1 : ℝ) * Sparse.eval nodeValue3535 x + ((2 : ℝ) * Sparse.eval nodeValue3544 x + ((1 : ℝ) * Sparse.eval nodeValue3627 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow277 : Integer.Sparse Master := [(Sum.inr 3533, 1), (Sum.inr 3535, 1), (Sum.inr 3544, 2), (Sum.inr 3627, 1), (Sum.inr 4084, -1)]

theorem reindexCheck277 : Integer.Sparse.reindex keyMap MixedData.row277 = numericRow277 := by decide +kernel

theorem numericCheck277 (x : Master → ℝ) : Integer.Sparse.eval numericRow277 x =
    (1 : ℝ) * reducedSource277 x := by
  norm_num [numericRow277, reducedSource277, Integer.Sparse.eval, Sparse.eval, nodeValue3531, nodeValue3533, nodeValue3535, nodeValue3544, nodeValue3627, nodeValue4084]

noncomputable def reducedSource278 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2058 x + ((1 : ℝ) * Sparse.eval nodeValue3395 x + ((1 : ℝ) * Sparse.eval nodeValue3497 x + ((1 : ℝ) * Sparse.eval nodeValue3535 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((1 : ℝ) * Sparse.eval nodeValue3544 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow278 : Integer.Sparse Master := [(Sum.inr 2058, 1), (Sum.inr 3395, 1), (Sum.inr 3497, 1), (Sum.inr 3535, 1), (Sum.inr 3541, 1), (Sum.inr 3544, 1), (Sum.inr 4084, -1)]

theorem reindexCheck278 : Integer.Sparse.reindex keyMap MixedData.row278 = numericRow278 := by decide +kernel

theorem numericCheck278 (x : Master → ℝ) : Integer.Sparse.eval numericRow278 x =
    (1 : ℝ) * reducedSource278 x := by
  norm_num [numericRow278, reducedSource278, Integer.Sparse.eval, Sparse.eval, nodeValue2058, nodeValue3395, nodeValue3497, nodeValue3535, nodeValue3541, nodeValue3544, nodeValue4084]

noncomputable def reducedSource279 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3157 x + ((1 : ℝ) * Sparse.eval nodeValue3392 x + ((1 : ℝ) * Sparse.eval nodeValue3504 x + ((1 : ℝ) * Sparse.eval nodeValue3506 x + ((1 : ℝ) * Sparse.eval nodeValue3535 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow279 : Integer.Sparse Master := [(Sum.inr 3157, 1), (Sum.inr 3392, 1), (Sum.inr 3504, 1), (Sum.inr 3506, 1), (Sum.inr 3535, 1), (Sum.inr 3584, 1), (Sum.inr 4084, -1)]

theorem reindexCheck279 : Integer.Sparse.reindex keyMap MixedData.row279 = numericRow279 := by decide +kernel

theorem numericCheck279 (x : Master → ℝ) : Integer.Sparse.eval numericRow279 x =
    (1 : ℝ) * reducedSource279 x := by
  norm_num [numericRow279, reducedSource279, Integer.Sparse.eval, Sparse.eval, nodeValue3157, nodeValue3392, nodeValue3504, nodeValue3506, nodeValue3535, nodeValue3584, nodeValue4084]

noncomputable def reducedSource280 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2028 x + ((1 : ℝ) * Sparse.eval nodeValue3379 x + ((1 : ℝ) * Sparse.eval nodeValue3488 x + ((1 : ℝ) * Sparse.eval nodeValue3506 x + ((1 : ℝ) * Sparse.eval nodeValue3533 x + ((1 : ℝ) * Sparse.eval nodeValue3535 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow280 : Integer.Sparse Master := [(Sum.inr 2028, 1), (Sum.inr 3379, 1), (Sum.inr 3488, 1), (Sum.inr 3506, 1), (Sum.inr 3533, 1), (Sum.inr 3535, 1), (Sum.inr 4084, -1)]

theorem reindexCheck280 : Integer.Sparse.reindex keyMap MixedData.row280 = numericRow280 := by decide +kernel

theorem numericCheck280 (x : Master → ℝ) : Integer.Sparse.eval numericRow280 x =
    (1 : ℝ) * reducedSource280 x := by
  norm_num [numericRow280, reducedSource280, Integer.Sparse.eval, Sparse.eval, nodeValue2028, nodeValue3379, nodeValue3488, nodeValue3506, nodeValue3533, nodeValue3535, nodeValue4084]

noncomputable def reducedSource281 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1178 x + ((1 : ℝ) * Sparse.eval nodeValue1179 x + ((1 : ℝ) * Sparse.eval nodeValue1182 x + ((1 : ℝ) * Sparse.eval nodeValue1185 x + ((1 : ℝ) * Sparse.eval nodeValue1261 x + ((1 : ℝ) * Sparse.eval nodeValue1992 x + ((1 : ℝ) * Sparse.eval nodeValue2004 x + ((1 : ℝ) * Sparse.eval nodeValue2035 x + ((1 : ℝ) * Sparse.eval nodeValue2197 x + ((1 : ℝ) * Sparse.eval nodeValue2833 x + ((1 : ℝ) * Sparse.eval nodeValue2835 x + ((1 : ℝ) * Sparse.eval nodeValue2838 x + ((1 : ℝ) * Sparse.eval nodeValue2905 x + ((1 : ℝ) * Sparse.eval nodeValue2907 x + ((1 : ℝ) * Sparse.eval nodeValue2933 x + ((1 : ℝ) * Sparse.eval nodeValue2974 x + ((1 : ℝ) * Sparse.eval nodeValue2979 x + ((1 : ℝ) * Sparse.eval nodeValue2997 x + ((1 : ℝ) * Sparse.eval nodeValue3016 x + ((1 : ℝ) * Sparse.eval nodeValue3025 x + ((1 : ℝ) * Sparse.eval nodeValue3037 x + ((1 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((1 : ℝ) * Sparse.eval nodeValue3814 x + ((1 : ℝ) * Sparse.eval nodeValue3841 x + ((1 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3856 x + 0)))))))))))))))))))))))))))))

def numericRow281 : Integer.Sparse Master := [(Sum.inl 0, -464), (Sum.inl 5, -80), (Sum.inl 6, 20), (Sum.inl 2, -440), (Sum.inl 35, -320), (Sum.inl 3, -1920), (Sum.inl 13, -640), (Sum.inl 52, -320), (Sum.inl 12, -640), (Sum.inl 26, -640), (Sum.inl 4, -640), (Sum.inl 1, 660), (Sum.inr 1178, 17280), (Sum.inr 1179, 17280), (Sum.inr 1182, 17280), (Sum.inr 1185, 17280), (Sum.inr 1261, 17280), (Sum.inr 1992, 17280), (Sum.inr 2004, 17280), (Sum.inr 2035, 17280), (Sum.inr 2197, 17280), (Sum.inr 2833, 17280), (Sum.inr 2835, 17280), (Sum.inr 2838, 17280), (Sum.inr 2905, 17280), (Sum.inr 2907, 17280), (Sum.inr 2933, 17280), (Sum.inr 2974, 17280), (Sum.inr 2979, 17280), (Sum.inr 3016, 17280), (Sum.inr 3025, 17280), (Sum.inr 3037, 17280), (Sum.inr 3039, 17280), (Sum.inr 3051, 17280), (Sum.inr 3086, 17280), (Sum.inr 3541, 17280), (Sum.inr 3814, 17280), (Sum.inr 3841, 17280)]

theorem reindexCheck281 : Integer.Sparse.reindex keyMap MixedData.row281 = numericRow281 := by decide +kernel

theorem numericCheck281 (x : Master → ℝ) : Integer.Sparse.eval numericRow281 x =
    (17280 : ℝ) * reducedSource281 x := by
  norm_num [numericRow281, reducedSource281, Integer.Sparse.eval, Sparse.eval, nodeValue1178, nodeValue1179, nodeValue1182, nodeValue1185, nodeValue1261, nodeValue1992, nodeValue2004, nodeValue2035, nodeValue2197, nodeValue2833, nodeValue2835, nodeValue2838, nodeValue2905, nodeValue2907, nodeValue2933, nodeValue2974, nodeValue2979, nodeValue2997, nodeValue3016, nodeValue3025, nodeValue3037, nodeValue3039, nodeValue3051, nodeValue3086, nodeValue3109, nodeValue3541, nodeValue3814, nodeValue3841, nodeValue3853, nodeValue3856]
  ring

noncomputable def reducedSource282 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2001 x + ((1 : ℝ) * Sparse.eval nodeValue2004 x + ((1 : ℝ) * Sparse.eval nodeValue2005 x + ((1 : ℝ) * Sparse.eval nodeValue2055 x + ((1 : ℝ) * Sparse.eval nodeValue2207 x + ((1 : ℝ) * Sparse.eval nodeValue2833 x + ((1 : ℝ) * Sparse.eval nodeValue2835 x + ((1 : ℝ) * Sparse.eval nodeValue2838 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3238 x + ((1 : ℝ) * Sparse.eval nodeValue3240 x + ((1 : ℝ) * Sparse.eval nodeValue3243 x + ((1 : ℝ) * Sparse.eval nodeValue3296 x + ((1 : ℝ) * Sparse.eval nodeValue3464 x + ((1 : ℝ) * Sparse.eval nodeValue3479 x + ((1 : ℝ) * Sparse.eval nodeValue3480 x + ((1 : ℝ) * Sparse.eval nodeValue3517 x + ((1 : ℝ) * Sparse.eval nodeValue3518 x + ((1 : ℝ) * Sparse.eval nodeValue3526 x + ((1 : ℝ) * Sparse.eval nodeValue3528 x + ((1 : ℝ) * Sparse.eval nodeValue3534 x + ((1 : ℝ) * Sparse.eval nodeValue3535 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3561 x + ((1 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3577 x + ((1 : ℝ) * Sparse.eval nodeValue3814 x + ((1 : ℝ) * Sparse.eval nodeValue3841 x + ((1 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3856 x + 0)))))))))))))))))))))))))))))

def numericRow282 : Integer.Sparse Master := [(Sum.inl 0, -27), (Sum.inl 2, -20), (Sum.inl 3, -160), (Sum.inl 13, -80), (Sum.inl 12, -80), (Sum.inl 1, 55), (Sum.inr 2001, 2160), (Sum.inr 2004, 2160), (Sum.inr 2005, 2160), (Sum.inr 2055, 2160), (Sum.inr 2207, 2160), (Sum.inr 2833, 2160), (Sum.inr 2835, 2160), (Sum.inr 2838, 2160), (Sum.inr 3038, 2160), (Sum.inr 3238, 2160), (Sum.inr 3240, 2160), (Sum.inr 3243, 2160), (Sum.inr 3296, 2160), (Sum.inr 3464, 2160), (Sum.inr 3479, 2160), (Sum.inr 3480, 2160), (Sum.inr 3517, 2160), (Sum.inr 3518, 2160), (Sum.inr 3526, 2160), (Sum.inr 3528, 2160), (Sum.inr 3534, 2160), (Sum.inr 3535, 2160), (Sum.inr 3540, 2160), (Sum.inr 3561, 2160), (Sum.inr 3573, 2160), (Sum.inr 3577, 2160), (Sum.inr 3814, 2160), (Sum.inr 3841, 2160)]

theorem reindexCheck282 : Integer.Sparse.reindex keyMap MixedData.row282 = numericRow282 := by decide +kernel

theorem numericCheck282 (x : Master → ℝ) : Integer.Sparse.eval numericRow282 x =
    (2160 : ℝ) * reducedSource282 x := by
  norm_num [numericRow282, reducedSource282, Integer.Sparse.eval, Sparse.eval, nodeValue2001, nodeValue2004, nodeValue2005, nodeValue2055, nodeValue2207, nodeValue2833, nodeValue2835, nodeValue2838, nodeValue3038, nodeValue3238, nodeValue3240, nodeValue3243, nodeValue3296, nodeValue3464, nodeValue3479, nodeValue3480, nodeValue3517, nodeValue3518, nodeValue3526, nodeValue3528, nodeValue3534, nodeValue3535, nodeValue3540, nodeValue3561, nodeValue3573, nodeValue3577, nodeValue3814, nodeValue3841, nodeValue3853, nodeValue3856]
  ring

noncomputable def reducedSource283 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2732 x + ((2 : ℝ) * Sparse.eval nodeValue3814 x + ((1 : ℝ) * Sparse.eval nodeValue3841 x + ((1 : ℝ) * Sparse.eval nodeValue3906 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))

def numericRow283 : Integer.Sparse Master := [(Sum.inr 2732, 2), (Sum.inr 3814, 2), (Sum.inr 3841, 1), (Sum.inr 3906, 1), (Sum.inr 4092, -1)]

theorem reindexCheck283 : Integer.Sparse.reindex keyMap MixedData.row283 = numericRow283 := by decide +kernel

theorem numericCheck283 (x : Master → ℝ) : Integer.Sparse.eval numericRow283 x =
    (1 : ℝ) * reducedSource283 x := by
  norm_num [numericRow283, reducedSource283, Integer.Sparse.eval, Sparse.eval, nodeValue2732, nodeValue3814, nodeValue3841, nodeValue3906, nodeValue4092]

noncomputable def reducedSource284 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1278 x + ((1 : ℝ) * Sparse.eval nodeValue2578 x + ((1 : ℝ) * Sparse.eval nodeValue2649 x + ((1 : ℝ) * Sparse.eval nodeValue2732 x + ((1 : ℝ) * Sparse.eval nodeValue2758 x + ((1 : ℝ) * Sparse.eval nodeValue2773 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow284 : Integer.Sparse Master := [(Sum.inr 1278, 1), (Sum.inr 2578, 1), (Sum.inr 2649, 1), (Sum.inr 2732, 1), (Sum.inr 2758, 1), (Sum.inr 2773, 1), (Sum.inr 4092, -1)]

theorem reindexCheck284 : Integer.Sparse.reindex keyMap MixedData.row284 = numericRow284 := by decide +kernel

theorem numericCheck284 (x : Master → ℝ) : Integer.Sparse.eval numericRow284 x =
    (1 : ℝ) * reducedSource284 x := by
  norm_num [numericRow284, reducedSource284, Integer.Sparse.eval, Sparse.eval, nodeValue1278, nodeValue2578, nodeValue2649, nodeValue2732, nodeValue2758, nodeValue2773, nodeValue4092]

noncomputable def reducedSource285 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2494 x + ((1 : ℝ) * Sparse.eval nodeValue2497 x + ((1 : ℝ) * Sparse.eval nodeValue2499 x + ((1 : ℝ) * Sparse.eval nodeValue2515 x + ((1 : ℝ) * Sparse.eval nodeValue2732 x + ((1 : ℝ) * Sparse.eval nodeValue3814 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow285 : Integer.Sparse Master := [(Sum.inr 2494, 1), (Sum.inr 2497, 1), (Sum.inr 2499, 1), (Sum.inr 2515, 1), (Sum.inr 2732, 1), (Sum.inr 3814, 1), (Sum.inr 4092, -1)]

theorem reindexCheck285 : Integer.Sparse.reindex keyMap MixedData.row285 = numericRow285 := by decide +kernel

theorem numericCheck285 (x : Master → ℝ) : Integer.Sparse.eval numericRow285 x =
    (1 : ℝ) * reducedSource285 x := by
  norm_num [numericRow285, reducedSource285, Integer.Sparse.eval, Sparse.eval, nodeValue2494, nodeValue2497, nodeValue2499, nodeValue2515, nodeValue2732, nodeValue3814, nodeValue4092]

noncomputable def reducedSource286 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue990 x + ((1 : ℝ) * Sparse.eval nodeValue991 x + ((1 : ℝ) * Sparse.eval nodeValue992 x + ((1 : ℝ) * Sparse.eval nodeValue1006 x + ((1 : ℝ) * Sparse.eval nodeValue1058 x + ((1 : ℝ) * Sparse.eval nodeValue2392 x + ((1 : ℝ) * Sparse.eval nodeValue2393 x + ((1 : ℝ) * Sparse.eval nodeValue2394 x + ((1 : ℝ) * Sparse.eval nodeValue2405 x + ((1 : ℝ) * Sparse.eval nodeValue2454 x + ((1 : ℝ) * Sparse.eval nodeValue2455 x + ((1 : ℝ) * Sparse.eval nodeValue2463 x + ((1 : ℝ) * Sparse.eval nodeValue2494 x + ((1 : ℝ) * Sparse.eval nodeValue2617 x + ((1 : ℝ) * Sparse.eval nodeValue2618 x + ((1 : ℝ) * Sparse.eval nodeValue2620 x + ((1 : ℝ) * Sparse.eval nodeValue2638 x + ((1 : ℝ) * Sparse.eval nodeValue2728 x + ((1 : ℝ) * Sparse.eval nodeValue2729 x + ((1 : ℝ) * Sparse.eval nodeValue2732 x + ((1 : ℝ) * Sparse.eval nodeValue2734 x + ((1 : ℝ) * Sparse.eval nodeValue2735 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + ((1 : ℝ) * Sparse.eval nodeValue2773 x + ((1 : ℝ) * Sparse.eval nodeValue2776 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3889 x + ((1 : ℝ) * Sparse.eval nodeValue4003 x + 0)))))))))))))))))))))))))))))

def numericRow286 : Integer.Sparse Master := [(Sum.inl 0, -111), (Sum.inl 5, -20), (Sum.inl 6, 5), (Sum.inl 2, -80), (Sum.inl 51, 240), (Sum.inl 13, 80), (Sum.inl 52, -80), (Sum.inl 12, 160), (Sum.inl 1, -50), (Sum.inr 990, 4320), (Sum.inr 991, 4320), (Sum.inr 992, 4320), (Sum.inr 1006, 4320), (Sum.inr 1058, 4320), (Sum.inr 2392, 4320), (Sum.inr 2393, 4320), (Sum.inr 2394, 4320), (Sum.inr 2405, 4320), (Sum.inr 2454, 4320), (Sum.inr 2455, 4320), (Sum.inr 2463, 4320), (Sum.inr 2494, 4320), (Sum.inr 2617, 4320), (Sum.inr 2618, 4320), (Sum.inr 2620, 4320), (Sum.inr 2728, 4320), (Sum.inr 2729, 4320), (Sum.inr 2732, 4320), (Sum.inr 2734, 4320), (Sum.inr 2735, 4320), (Sum.inr 2744, 4320), (Sum.inr 2773, 4320), (Sum.inr 3872, 4320), (Sum.inr 3876, 4320), (Sum.inr 3877, 4320)]

theorem reindexCheck286 : Integer.Sparse.reindex keyMap MixedData.row286 = numericRow286 := by decide +kernel

theorem numericCheck286 (x : Master → ℝ) : Integer.Sparse.eval numericRow286 x =
    (4320 : ℝ) * reducedSource286 x := by
  norm_num [numericRow286, reducedSource286, Integer.Sparse.eval, Sparse.eval, nodeValue990, nodeValue991, nodeValue992, nodeValue1006, nodeValue1058, nodeValue2392, nodeValue2393, nodeValue2394, nodeValue2405, nodeValue2454, nodeValue2455, nodeValue2463, nodeValue2494, nodeValue2617, nodeValue2618, nodeValue2620, nodeValue2638, nodeValue2728, nodeValue2729, nodeValue2732, nodeValue2734, nodeValue2735, nodeValue2744, nodeValue2773, nodeValue2776, nodeValue3872, nodeValue3876, nodeValue3877, nodeValue3889, nodeValue4003]
  ring

noncomputable def reducedSource287 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1609 x + ((1 : ℝ) * Sparse.eval nodeValue1610 x + ((1 : ℝ) * Sparse.eval nodeValue1611 x + ((1 : ℝ) * Sparse.eval nodeValue1624 x + ((1 : ℝ) * Sparse.eval nodeValue1715 x + ((1 : ℝ) * Sparse.eval nodeValue2906 x + ((1 : ℝ) * Sparse.eval nodeValue2910 x + ((1 : ℝ) * Sparse.eval nodeValue2952 x + ((1 : ℝ) * Sparse.eval nodeValue3052 x + ((1 : ℝ) * Sparse.eval nodeValue3347 x + ((1 : ℝ) * Sparse.eval nodeValue3348 x + ((1 : ℝ) * Sparse.eval nodeValue3358 x + ((1 : ℝ) * Sparse.eval nodeValue3430 x + ((1 : ℝ) * Sparse.eval nodeValue3437 x + ((1 : ℝ) * Sparse.eval nodeValue3464 x + ((1 : ℝ) * Sparse.eval nodeValue3505 x + ((1 : ℝ) * Sparse.eval nodeValue3506 x + ((1 : ℝ) * Sparse.eval nodeValue3523 x + ((1 : ℝ) * Sparse.eval nodeValue3537 x + ((1 : ℝ) * Sparse.eval nodeValue3538 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((1 : ℝ) * Sparse.eval nodeValue3549 x + ((1 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3624 x + ((1 : ℝ) * Sparse.eval nodeValue3626 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3862 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3993 x + 0)))))))))))))))))))))))))))))

def numericRow287 : Integer.Sparse Master := [(Sum.inl 0, -100), (Sum.inl 2, -30), (Sum.inl 3, -160), (Sum.inl 12, 160), (Sum.inl 26, -160), (Sum.inl 4, -320), (Sum.inl 1, -50), (Sum.inr 1609, 8640), (Sum.inr 1610, 8640), (Sum.inr 1611, 8640), (Sum.inr 1624, 8640), (Sum.inr 1715, 8640), (Sum.inr 2906, 8640), (Sum.inr 2910, 8640), (Sum.inr 2952, 8640), (Sum.inr 3052, 8640), (Sum.inr 3347, 8640), (Sum.inr 3348, 8640), (Sum.inr 3358, 8640), (Sum.inr 3430, 8640), (Sum.inr 3437, 8640), (Sum.inr 3464, 8640), (Sum.inr 3505, 8640), (Sum.inr 3506, 8640), (Sum.inr 3523, 8640), (Sum.inr 3537, 8640), (Sum.inr 3538, 8640), (Sum.inr 3541, 8640), (Sum.inr 3549, 8640), (Sum.inr 3573, 8640), (Sum.inr 3624, 8640), (Sum.inr 3626, 8640), (Sum.inr 3839, 8640), (Sum.inr 3845, 8640), (Sum.inr 3877, 8640)]

theorem reindexCheck287 : Integer.Sparse.reindex keyMap MixedData.row287 = numericRow287 := by decide +kernel

theorem numericCheck287 (x : Master → ℝ) : Integer.Sparse.eval numericRow287 x =
    (8640 : ℝ) * reducedSource287 x := by
  norm_num [numericRow287, reducedSource287, Integer.Sparse.eval, Sparse.eval, nodeValue1609, nodeValue1610, nodeValue1611, nodeValue1624, nodeValue1715, nodeValue2906, nodeValue2910, nodeValue2952, nodeValue3052, nodeValue3347, nodeValue3348, nodeValue3358, nodeValue3430, nodeValue3437, nodeValue3464, nodeValue3505, nodeValue3506, nodeValue3523, nodeValue3537, nodeValue3538, nodeValue3541, nodeValue3549, nodeValue3573, nodeValue3624, nodeValue3626, nodeValue3839, nodeValue3845, nodeValue3862, nodeValue3877, nodeValue3993]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
