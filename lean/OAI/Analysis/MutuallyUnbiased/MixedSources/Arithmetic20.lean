import OAI.Analysis.MutuallyUnbiased.MixedData.Source2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values85
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource320 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2710 x + ((1 : ℝ) * Sparse.eval nodeValue3801 x + ((2 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3899 x + ((1 : ℝ) * Sparse.eval nodeValue3901 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow320 : Integer.Sparse Master := [(Sum.inr 2710, 1), (Sum.inr 3801, 1), (Sum.inr 3872, 2), (Sum.inr 3899, 1), (Sum.inr 3901, 1), (Sum.inr 4091, -1)]

theorem reindexCheck320 : Integer.Sparse.reindex keyMap MixedData.row320 = numericRow320 := by decide +kernel

theorem numericCheck320 (x : Master → ℝ) : Integer.Sparse.eval numericRow320 x =
    (1 : ℝ) * reducedSource320 x := by
  norm_num [numericRow320, reducedSource320, Integer.Sparse.eval, Sparse.eval, nodeValue2710, nodeValue3801, nodeValue3872, nodeValue3899, nodeValue3901, nodeValue4091]

noncomputable def reducedSource321 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1248 x + ((2 : ℝ) * Sparse.eval nodeValue2623 x + ((1 : ℝ) * Sparse.eval nodeValue2710 x + ((1 : ℝ) * Sparse.eval nodeValue2745 x + ((1 : ℝ) * Sparse.eval nodeValue2750 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow321 : Integer.Sparse Master := [(Sum.inr 1248, 1), (Sum.inr 2623, 2), (Sum.inr 2710, 1), (Sum.inr 2745, 1), (Sum.inr 2750, 1), (Sum.inr 4091, -1)]

theorem reindexCheck321 : Integer.Sparse.reindex keyMap MixedData.row321 = numericRow321 := by decide +kernel

theorem numericCheck321 (x : Master → ℝ) : Integer.Sparse.eval numericRow321 x =
    (1 : ℝ) * reducedSource321 x := by
  norm_num [numericRow321, reducedSource321, Integer.Sparse.eval, Sparse.eval, nodeValue1248, nodeValue2623, nodeValue2710, nodeValue2745, nodeValue2750, nodeValue4091]

noncomputable def reducedSource322 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2471 x + ((1 : ℝ) * Sparse.eval nodeValue2473 x + ((2 : ℝ) * Sparse.eval nodeValue2483 x + ((1 : ℝ) * Sparse.eval nodeValue2710 x + ((1 : ℝ) * Sparse.eval nodeValue3801 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow322 : Integer.Sparse Master := [(Sum.inr 2471, 1), (Sum.inr 2473, 1), (Sum.inr 2483, 2), (Sum.inr 2710, 1), (Sum.inr 3801, 1), (Sum.inr 4091, -1)]

theorem reindexCheck322 : Integer.Sparse.reindex keyMap MixedData.row322 = numericRow322 := by decide +kernel

theorem numericCheck322 (x : Master → ℝ) : Integer.Sparse.eval numericRow322 x =
    (1 : ℝ) * reducedSource322 x := by
  norm_num [numericRow322, reducedSource322, Integer.Sparse.eval, Sparse.eval, nodeValue2471, nodeValue2473, nodeValue2483, nodeValue2710, nodeValue3801, nodeValue4091]

noncomputable def reducedSource323 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1216 x + ((1 : ℝ) * Sparse.eval nodeValue2483 x + ((1 : ℝ) * Sparse.eval nodeValue2617 x + ((2 : ℝ) * Sparse.eval nodeValue2710 x + ((1 : ℝ) * Sparse.eval nodeValue2721 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow323 : Integer.Sparse Master := [(Sum.inr 1216, 1), (Sum.inr 2483, 1), (Sum.inr 2617, 1), (Sum.inr 2710, 2), (Sum.inr 2721, 1), (Sum.inr 4091, -1)]

theorem reindexCheck323 : Integer.Sparse.reindex keyMap MixedData.row323 = numericRow323 := by decide +kernel

theorem numericCheck323 (x : Master → ℝ) : Integer.Sparse.eval numericRow323 x =
    (1 : ℝ) * reducedSource323 x := by
  norm_num [numericRow323, reducedSource323, Integer.Sparse.eval, Sparse.eval, nodeValue1216, nodeValue2483, nodeValue2617, nodeValue2710, nodeValue2721, nodeValue4091]

noncomputable def reducedSource324 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2611 x + ((1 : ℝ) * Sparse.eval nodeValue2612 x + ((1 : ℝ) * Sparse.eval nodeValue2617 x + ((1 : ℝ) * Sparse.eval nodeValue2623 x + ((1 : ℝ) * Sparse.eval nodeValue2710 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow324 : Integer.Sparse Master := [(Sum.inr 2611, 1), (Sum.inr 2612, 1), (Sum.inr 2617, 1), (Sum.inr 2623, 1), (Sum.inr 2710, 1), (Sum.inr 3872, 1), (Sum.inr 4091, -1)]

theorem reindexCheck324 : Integer.Sparse.reindex keyMap MixedData.row324 = numericRow324 := by decide +kernel

theorem numericCheck324 (x : Master → ℝ) : Integer.Sparse.eval numericRow324 x =
    (1 : ℝ) * reducedSource324 x := by
  norm_num [numericRow324, reducedSource324, Integer.Sparse.eval, Sparse.eval, nodeValue2611, nodeValue2612, nodeValue2617, nodeValue2623, nodeValue2710, nodeValue3872, nodeValue4091]

noncomputable def reducedSource325 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2707 x + ((3 : ℝ) * Sparse.eval nodeValue2710 x + ((1 : ℝ) * Sparse.eval nodeValue2745 x + ((1 : ℝ) * Sparse.eval nodeValue3899 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))

def numericRow325 : Integer.Sparse Master := [(Sum.inr 2707, 1), (Sum.inr 2710, 3), (Sum.inr 2745, 1), (Sum.inr 3899, 1), (Sum.inr 4091, -1)]

theorem reindexCheck325 : Integer.Sparse.reindex keyMap MixedData.row325 = numericRow325 := by decide +kernel

theorem numericCheck325 (x : Master → ℝ) : Integer.Sparse.eval numericRow325 x =
    (1 : ℝ) * reducedSource325 x := by
  norm_num [numericRow325, reducedSource325, Integer.Sparse.eval, Sparse.eval, nodeValue2707, nodeValue2710, nodeValue2745, nodeValue3899, nodeValue4091]

noncomputable def reducedSource326 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4391 x + ((1 : ℝ) * Sparse.eval nodeValue4392 x + ((2 : ℝ) * Sparse.eval nodeValue4400 x + ((1 : ℝ) * Sparse.eval nodeValue4439 x + ((1 : ℝ) * Sparse.eval nodeValue4992 x + ((1 : ℝ) * Sparse.eval nodeValue4993 x + ((2 : ℝ) * Sparse.eval nodeValue4999 x + ((2 : ℝ) * Sparse.eval nodeValue5128 x + ((2 : ℝ) * Sparse.eval nodeValue5129 x + ((2 : ℝ) * Sparse.eval nodeValue5138 x + ((2 : ℝ) * Sparse.eval nodeValue5149 x + ((1 : ℝ) * Sparse.eval nodeValue5249 x + ((1 : ℝ) * Sparse.eval nodeValue5252 x + ((2 : ℝ) * Sparse.eval nodeValue5255 x + ((2 : ℝ) * Sparse.eval nodeValue5260 x + ((1 : ℝ) * Sparse.eval nodeValue5281 x + ((1 : ℝ) * Sparse.eval nodeValue5284 x + ((2 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5429 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((1 : ℝ) * Sparse.eval nodeValue5481 x + 0))))))))))))))))))))

def numericRow326 : Integer.Sparse Master := [(Sum.inl 0, 33), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, 80), (Sum.inl 1, 190), (Sum.inr 2924, -8640), (Sum.inr 3077, -4320), (Sum.inr 3605, -8640), (Sum.inr 3625, -4320), (Sum.inr 3838, -8640), (Sum.inr 3843, -8640), (Sum.inr 3902, -4320), (Sum.inr 4391, 17280), (Sum.inr 4392, 17280), (Sum.inr 4400, 34560), (Sum.inr 4439, 17280), (Sum.inr 4992, 17280), (Sum.inr 4993, 17280), (Sum.inr 4999, 34560), (Sum.inr 5128, 34560), (Sum.inr 5129, 34560), (Sum.inr 5138, 34560), (Sum.inr 5249, 17280), (Sum.inr 5252, 17280), (Sum.inr 5255, 34560), (Sum.inr 5260, 34560), (Sum.inr 5281, 17280), (Sum.inr 5429, 17280)]

theorem reindexCheck326 : Integer.Sparse.reindex keyMap MixedData.row326 = numericRow326 := by decide +kernel

theorem numericCheck326 (x : Master → ℝ) : Integer.Sparse.eval numericRow326 x =
    (17280 : ℝ) * reducedSource326 x := by
  norm_num [numericRow326, reducedSource326, Integer.Sparse.eval, Sparse.eval, nodeValue4391, nodeValue4392, nodeValue4400, nodeValue4439, nodeValue4992, nodeValue4993, nodeValue4999, nodeValue5128, nodeValue5129, nodeValue5138, nodeValue5149, nodeValue5249, nodeValue5252, nodeValue5255, nodeValue5260, nodeValue5281, nodeValue5284, nodeValue5424, nodeValue5429, nodeValue5439, nodeValue5481]
  ring

noncomputable def reducedSource327 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue972 x + ((1 : ℝ) * Sparse.eval nodeValue973 x + ((2 : ℝ) * Sparse.eval nodeValue981 x + ((1 : ℝ) * Sparse.eval nodeValue1021 x + ((1 : ℝ) * Sparse.eval nodeValue2378 x + ((1 : ℝ) * Sparse.eval nodeValue2379 x + ((2 : ℝ) * Sparse.eval nodeValue2384 x + ((2 : ℝ) * Sparse.eval nodeValue2543 x + ((2 : ℝ) * Sparse.eval nodeValue2545 x + ((2 : ℝ) * Sparse.eval nodeValue2557 x + ((2 : ℝ) * Sparse.eval nodeValue2570 x + ((1 : ℝ) * Sparse.eval nodeValue2708 x + ((1 : ℝ) * Sparse.eval nodeValue2712 x + ((2 : ℝ) * Sparse.eval nodeValue2718 x + ((2 : ℝ) * Sparse.eval nodeValue2724 x + ((1 : ℝ) * Sparse.eval nodeValue2750 x + ((1 : ℝ) * Sparse.eval nodeValue2753 x + ((1 : ℝ) * Sparse.eval nodeValue3954 x + ((1 : ℝ) * Sparse.eval nodeValue3979 x + ((2 : ℝ) * Sparse.eval nodeValue3990 x + ((1 : ℝ) * Sparse.eval nodeValue4012 x + 0))))))))))))))))))))

def numericRow327 : Integer.Sparse Master := [(Sum.inl 0, -125), (Sum.inl 5, -160), (Sum.inl 6, 20), (Sum.inl 2, 210), (Sum.inl 7, 320), (Sum.inl 35, 160), (Sum.inl 8, 160), (Sum.inl 51, -480), (Sum.inl 3, 1200), (Sum.inl 13, 240), (Sum.inl 52, 160), (Sum.inl 12, 480), (Sum.inl 26, 160), (Sum.inl 4, 320), (Sum.inl 1, -445), (Sum.inr 972, 4320), (Sum.inr 973, 4320), (Sum.inr 981, 8640), (Sum.inr 1021, 4320), (Sum.inr 2378, 4320), (Sum.inr 2379, 4320), (Sum.inr 2384, 8640), (Sum.inr 2543, 8640), (Sum.inr 2545, 8640), (Sum.inr 2557, 8640), (Sum.inr 2708, 4320), (Sum.inr 2712, 4320), (Sum.inr 2718, 8640), (Sum.inr 2724, 8640), (Sum.inr 2750, 4320), (Sum.inr 3954, 4320)]

theorem reindexCheck327 : Integer.Sparse.reindex keyMap MixedData.row327 = numericRow327 := by decide +kernel

theorem numericCheck327 (x : Master → ℝ) : Integer.Sparse.eval numericRow327 x =
    (4320 : ℝ) * reducedSource327 x := by
  norm_num [numericRow327, reducedSource327, Integer.Sparse.eval, Sparse.eval, nodeValue972, nodeValue973, nodeValue981, nodeValue1021, nodeValue2378, nodeValue2379, nodeValue2384, nodeValue2543, nodeValue2545, nodeValue2557, nodeValue2570, nodeValue2708, nodeValue2712, nodeValue2718, nodeValue2724, nodeValue2750, nodeValue2753, nodeValue3954, nodeValue3979, nodeValue3990, nodeValue4012]
  ring

noncomputable def reducedSource328 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1606 x + ((2 : ℝ) * Sparse.eval nodeValue1607 x + ((1 : ℝ) * Sparse.eval nodeValue1613 x + ((1 : ℝ) * Sparse.eval nodeValue1713 x + ((1 : ℝ) * Sparse.eval nodeValue3345 x + ((2 : ℝ) * Sparse.eval nodeValue3346 x + ((1 : ℝ) * Sparse.eval nodeValue3350 x + ((1 : ℝ) * Sparse.eval nodeValue3502 x + ((2 : ℝ) * Sparse.eval nodeValue3503 x + ((2 : ℝ) * Sparse.eval nodeValue3516 x + ((2 : ℝ) * Sparse.eval nodeValue3517 x + ((2 : ℝ) * Sparse.eval nodeValue3519 x + ((2 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3543 x + ((1 : ℝ) * Sparse.eval nodeValue3571 x + ((2 : ℝ) * Sparse.eval nodeValue3605 x + ((1 : ℝ) * Sparse.eval nodeValue3625 x + ((2 : ℝ) * Sparse.eval nodeValue3843 x + ((1 : ℝ) * Sparse.eval nodeValue3858 x + ((1 : ℝ) * Sparse.eval nodeValue3874 x + ((1 : ℝ) * Sparse.eval nodeValue3991 x + 0))))))))))))))))))))

def numericRow328 : Integer.Sparse Master := [(Sum.inl 0, -33), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 12, -80), (Sum.inl 1, -190), (Sum.inr 1606, 4320), (Sum.inr 1607, 8640), (Sum.inr 1613, 4320), (Sum.inr 1713, 4320), (Sum.inr 3345, 4320), (Sum.inr 3346, 8640), (Sum.inr 3350, 4320), (Sum.inr 3502, 4320), (Sum.inr 3503, 8640), (Sum.inr 3516, 8640), (Sum.inr 3517, 8640), (Sum.inr 3519, 8640), (Sum.inr 3540, 8640), (Sum.inr 3543, 4320), (Sum.inr 3571, 4320), (Sum.inr 3605, 8640), (Sum.inr 3625, 4320), (Sum.inr 3843, 8640), (Sum.inr 3874, 4320)]

theorem reindexCheck328 : Integer.Sparse.reindex keyMap MixedData.row328 = numericRow328 := by decide +kernel

theorem numericCheck328 (x : Master → ℝ) : Integer.Sparse.eval numericRow328 x =
    (4320 : ℝ) * reducedSource328 x := by
  norm_num [numericRow328, reducedSource328, Integer.Sparse.eval, Sparse.eval, nodeValue1606, nodeValue1607, nodeValue1613, nodeValue1713, nodeValue3345, nodeValue3346, nodeValue3350, nodeValue3502, nodeValue3503, nodeValue3516, nodeValue3517, nodeValue3519, nodeValue3540, nodeValue3543, nodeValue3571, nodeValue3605, nodeValue3625, nodeValue3843, nodeValue3858, nodeValue3874, nodeValue3991]
  ring

noncomputable def reducedSource329 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3064 x + ((2 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3846 x + ((1 : ℝ) * Sparse.eval nodeValue3902 x + ((1 : ℝ) * Sparse.eval nodeValue4008 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow329 : Integer.Sparse Master := [(Sum.inr 3064, 1), (Sum.inr 3838, 2), (Sum.inr 3846, 1), (Sum.inr 3902, 1), (Sum.inr 4091, -1)]

theorem reindexCheck329 : Integer.Sparse.reindex keyMap MixedData.row329 = numericRow329 := by decide +kernel

theorem numericCheck329 (x : Master → ℝ) : Integer.Sparse.eval numericRow329 x =
    (1 : ℝ) * reducedSource329 x := by
  norm_num [numericRow329, reducedSource329, Integer.Sparse.eval, Sparse.eval, nodeValue3064, nodeValue3838, nodeValue3846, nodeValue3902, nodeValue4008, nodeValue4091]

noncomputable def reducedSource330 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1378 x + ((1 : ℝ) * Sparse.eval nodeValue1380 x + ((1 : ℝ) * Sparse.eval nodeValue1383 x + ((2 : ℝ) * Sparse.eval nodeValue1392 x + ((1 : ℝ) * Sparse.eval nodeValue3064 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow330 : Integer.Sparse Master := [(Sum.inr 1378, 1), (Sum.inr 1380, 1), (Sum.inr 1383, 1), (Sum.inr 1392, 2), (Sum.inr 3064, 1), (Sum.inr 4091, -1)]

theorem reindexCheck330 : Integer.Sparse.reindex keyMap MixedData.row330 = numericRow330 := by decide +kernel

theorem numericCheck330 (x : Master → ℝ) : Integer.Sparse.eval numericRow330 x =
    (1 : ℝ) * reducedSource330 x := by
  norm_num [numericRow330, reducedSource330, Integer.Sparse.eval, Sparse.eval, nodeValue1378, nodeValue1380, nodeValue1383, nodeValue1392, nodeValue3064, nodeValue4091]

noncomputable def reducedSource331 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1383 x + ((2 : ℝ) * Sparse.eval nodeValue2924 x + ((1 : ℝ) * Sparse.eval nodeValue3064 x + ((1 : ℝ) * Sparse.eval nodeValue3074 x + ((1 : ℝ) * Sparse.eval nodeValue3077 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow331 : Integer.Sparse Master := [(Sum.inr 1383, 1), (Sum.inr 2924, 2), (Sum.inr 3064, 1), (Sum.inr 3074, 1), (Sum.inr 3077, 1), (Sum.inr 4091, -1)]

theorem reindexCheck331 : Integer.Sparse.reindex keyMap MixedData.row331 = numericRow331 := by decide +kernel

theorem numericCheck331 (x : Master → ℝ) : Integer.Sparse.eval numericRow331 x =
    (1 : ℝ) * reducedSource331 x := by
  norm_num [numericRow331, reducedSource331, Integer.Sparse.eval, Sparse.eval, nodeValue1383, nodeValue2924, nodeValue3064, nodeValue3074, nodeValue3077, nodeValue4091]

noncomputable def reducedSource332 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2562 x + ((1 : ℝ) * Sparse.eval nodeValue3012 x + ((2 : ℝ) * Sparse.eval nodeValue3013 x + ((1 : ℝ) * Sparse.eval nodeValue3064 x + ((1 : ℝ) * Sparse.eval nodeValue3846 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow332 : Integer.Sparse Master := [(Sum.inr 2562, 1), (Sum.inr 3012, 1), (Sum.inr 3013, 2), (Sum.inr 3064, 1), (Sum.inr 3846, 1), (Sum.inr 4091, -1)]

theorem reindexCheck332 : Integer.Sparse.reindex keyMap MixedData.row332 = numericRow332 := by decide +kernel

theorem numericCheck332 (x : Master → ℝ) : Integer.Sparse.eval numericRow332 x =
    (1 : ℝ) * reducedSource332 x := by
  norm_num [numericRow332, reducedSource332, Integer.Sparse.eval, Sparse.eval, nodeValue2562, nodeValue3012, nodeValue3013, nodeValue3064, nodeValue3846, nodeValue4091]

noncomputable def reducedSource333 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2543 x + ((1 : ℝ) * Sparse.eval nodeValue2916 x + ((1 : ℝ) * Sparse.eval nodeValue2924 x + ((1 : ℝ) * Sparse.eval nodeValue2933 x + ((1 : ℝ) * Sparse.eval nodeValue3064 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow333 : Integer.Sparse Master := [(Sum.inr 2543, 1), (Sum.inr 2916, 1), (Sum.inr 2924, 1), (Sum.inr 2933, 1), (Sum.inr 3064, 1), (Sum.inr 3838, 1), (Sum.inr 4091, -1)]

theorem reindexCheck333 : Integer.Sparse.reindex keyMap MixedData.row333 = numericRow333 := by decide +kernel

theorem numericCheck333 (x : Master → ℝ) : Integer.Sparse.eval numericRow333 x =
    (1 : ℝ) * reducedSource333 x := by
  norm_num [numericRow333, reducedSource333, Integer.Sparse.eval, Sparse.eval, nodeValue2543, nodeValue2916, nodeValue2924, nodeValue2933, nodeValue3064, nodeValue3838, nodeValue4091]

noncomputable def reducedSource334 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1380 x + ((2 : ℝ) * Sparse.eval nodeValue2916 x + ((1 : ℝ) * Sparse.eval nodeValue3012 x + ((1 : ℝ) * Sparse.eval nodeValue3064 x + ((1 : ℝ) * Sparse.eval nodeValue3066 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow334 : Integer.Sparse Master := [(Sum.inr 1380, 1), (Sum.inr 2916, 2), (Sum.inr 3012, 1), (Sum.inr 3064, 1), (Sum.inr 3066, 1), (Sum.inr 4091, -1)]

theorem reindexCheck334 : Integer.Sparse.reindex keyMap MixedData.row334 = numericRow334 := by decide +kernel

theorem numericCheck334 (x : Master → ℝ) : Integer.Sparse.eval numericRow334 x =
    (1 : ℝ) * reducedSource334 x := by
  norm_num [numericRow334, reducedSource334, Integer.Sparse.eval, Sparse.eval, nodeValue1380, nodeValue2916, nodeValue3012, nodeValue3064, nodeValue3066, nodeValue4091]

noncomputable def reducedSource335 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2693 x + ((1 : ℝ) * Sparse.eval nodeValue2694 x + ((1 : ℝ) * Sparse.eval nodeValue2697 x + ((2 : ℝ) * Sparse.eval nodeValue2722 x + ((2 : ℝ) * Sparse.eval nodeValue3015 x + ((2 : ℝ) * Sparse.eval nodeValue3016 x + ((2 : ℝ) * Sparse.eval nodeValue3018 x + ((2 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3063 x + ((1 : ℝ) * Sparse.eval nodeValue3065 x + ((1 : ℝ) * Sparse.eval nodeValue3067 x + ((1 : ℝ) * Sparse.eval nodeValue3068 x + ((1 : ℝ) * Sparse.eval nodeValue3075 x + ((1 : ℝ) * Sparse.eval nodeValue3077 x + ((2 : ℝ) * Sparse.eval nodeValue3086 x + ((2 : ℝ) * Sparse.eval nodeValue3088 x + ((2 : ℝ) * Sparse.eval nodeValue3101 x + ((2 : ℝ) * Sparse.eval nodeValue3196 x + ((1 : ℝ) * Sparse.eval nodeValue3197 x + ((1 : ℝ) * Sparse.eval nodeValue3209 x + ((1 : ℝ) * Sparse.eval nodeValue3223 x + 0))))))))))))))))))))

def numericRow335 : Integer.Sparse Master := [(Sum.inl 0, -207), (Sum.inl 5, 20), (Sum.inl 6, -10), (Sum.inl 2, 265), (Sum.inl 35, 80), (Sum.inl 3, 320), (Sum.inl 13, 80), (Sum.inl 52, 160), (Sum.inl 1, 330), (Sum.inr 2694, 4320), (Sum.inr 2697, 4320), (Sum.inr 2722, 8640), (Sum.inr 3015, 8640), (Sum.inr 3016, 8640), (Sum.inr 3018, 8640), (Sum.inr 3038, 8640), (Sum.inr 3063, 4320), (Sum.inr 3067, 4320), (Sum.inr 3068, 4320), (Sum.inr 3075, 4320), (Sum.inr 3077, 4320), (Sum.inr 3086, 8640), (Sum.inr 3196, 8640), (Sum.inr 3197, 4320)]

theorem reindexCheck335 : Integer.Sparse.reindex keyMap MixedData.row335 = numericRow335 := by decide +kernel

theorem numericCheck335 (x : Master → ℝ) : Integer.Sparse.eval numericRow335 x =
    (4320 : ℝ) * reducedSource335 x := by
  norm_num [numericRow335, reducedSource335, Integer.Sparse.eval, Sparse.eval, nodeValue2693, nodeValue2694, nodeValue2697, nodeValue2722, nodeValue3015, nodeValue3016, nodeValue3018, nodeValue3038, nodeValue3063, nodeValue3065, nodeValue3067, nodeValue3068, nodeValue3075, nodeValue3077, nodeValue3086, nodeValue3088, nodeValue3101, nodeValue3196, nodeValue3197, nodeValue3209, nodeValue3223]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
