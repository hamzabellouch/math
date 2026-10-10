import OAI.Analysis.MutuallyUnbiased.MixedData.Source3
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values85
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource464 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3075 x + ((1 : ℝ) * Sparse.eval nodeValue3525 x + ((2 : ℝ) * Sparse.eval nodeValue3534 x + ((1 : ℝ) * Sparse.eval nodeValue3581 x + ((1 : ℝ) * Sparse.eval nodeValue3623 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow464 : Integer.Sparse Master := [(Sum.inr 3075, 1), (Sum.inr 3534, 2), (Sum.inr 3581, 1), (Sum.inr 3623, 1), (Sum.inr 4083, -1)]

theorem reindexCheck464 : Integer.Sparse.reindex keyMap MixedData.row464 = numericRow464 := by decide +kernel

theorem numericCheck464 (x : Master → ℝ) : Integer.Sparse.eval numericRow464 x =
    (1 : ℝ) * reducedSource464 x := by
  norm_num [numericRow464, reducedSource464, Integer.Sparse.eval, Sparse.eval, nodeValue3075, nodeValue3525, nodeValue3534, nodeValue3581, nodeValue3623, nodeValue4083]

noncomputable def reducedSource465 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1382 x + ((1 : ℝ) * Sparse.eval nodeValue1385 x + ((1 : ℝ) * Sparse.eval nodeValue1390 x + ((2 : ℝ) * Sparse.eval nodeValue1404 x + ((1 : ℝ) * Sparse.eval nodeValue3075 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow465 : Integer.Sparse Master := [(Sum.inr 1382, 1), (Sum.inr 1385, 1), (Sum.inr 1390, 1), (Sum.inr 1404, 2), (Sum.inr 3075, 1), (Sum.inr 4083, -1)]

theorem reindexCheck465 : Integer.Sparse.reindex keyMap MixedData.row465 = numericRow465 := by decide +kernel

theorem numericCheck465 (x : Master → ℝ) : Integer.Sparse.eval numericRow465 x =
    (1 : ℝ) * reducedSource465 x := by
  norm_num [numericRow465, reducedSource465, Integer.Sparse.eval, Sparse.eval, nodeValue1382, nodeValue1385, nodeValue1390, nodeValue1404, nodeValue3075, nodeValue4083]

noncomputable def reducedSource466 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1382 x + ((2 : ℝ) * Sparse.eval nodeValue2923 x + ((1 : ℝ) * Sparse.eval nodeValue3073 x + ((2 : ℝ) * Sparse.eval nodeValue3075 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

def numericRow466 : Integer.Sparse Master := [(Sum.inr 1382, 1), (Sum.inr 2923, 2), (Sum.inr 3073, 1), (Sum.inr 3075, 2), (Sum.inr 4083, -1)]

theorem reindexCheck466 : Integer.Sparse.reindex keyMap MixedData.row466 = numericRow466 := by decide +kernel

theorem numericCheck466 (x : Master → ℝ) : Integer.Sparse.eval numericRow466 x =
    (1 : ℝ) * reducedSource466 x := by
  norm_num [numericRow466, reducedSource466, Integer.Sparse.eval, Sparse.eval, nodeValue1382, nodeValue2923, nodeValue3073, nodeValue3075, nodeValue4083]

noncomputable def reducedSource467 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2009 x + ((1 : ℝ) * Sparse.eval nodeValue2980 x + ((2 : ℝ) * Sparse.eval nodeValue2983 x + ((1 : ℝ) * Sparse.eval nodeValue3075 x + ((1 : ℝ) * Sparse.eval nodeValue3525 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow467 : Integer.Sparse Master := [(Sum.inr 2009, 1), (Sum.inr 2980, 1), (Sum.inr 2983, 2), (Sum.inr 3075, 1), (Sum.inr 4083, -1)]

theorem reindexCheck467 : Integer.Sparse.reindex keyMap MixedData.row467 = numericRow467 := by decide +kernel

theorem numericCheck467 (x : Master → ℝ) : Integer.Sparse.eval numericRow467 x =
    (1 : ℝ) * reducedSource467 x := by
  norm_num [numericRow467, reducedSource467, Integer.Sparse.eval, Sparse.eval, nodeValue2009, nodeValue2980, nodeValue2983, nodeValue3075, nodeValue3525, nodeValue4083]

noncomputable def reducedSource468 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2025 x + ((1 : ℝ) * Sparse.eval nodeValue2923 x + ((1 : ℝ) * Sparse.eval nodeValue2930 x + ((1 : ℝ) * Sparse.eval nodeValue2952 x + ((1 : ℝ) * Sparse.eval nodeValue3075 x + ((1 : ℝ) * Sparse.eval nodeValue3534 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

def numericRow468 : Integer.Sparse Master := [(Sum.inr 2025, 1), (Sum.inr 2923, 1), (Sum.inr 2930, 1), (Sum.inr 2952, 1), (Sum.inr 3075, 1), (Sum.inr 3534, 1), (Sum.inr 4083, -1)]

theorem reindexCheck468 : Integer.Sparse.reindex keyMap MixedData.row468 = numericRow468 := by decide +kernel

theorem numericCheck468 (x : Master → ℝ) : Integer.Sparse.eval numericRow468 x =
    (1 : ℝ) * reducedSource468 x := by
  norm_num [numericRow468, reducedSource468, Integer.Sparse.eval, Sparse.eval, nodeValue2025, nodeValue2923, nodeValue2930, nodeValue2952, nodeValue3075, nodeValue3534, nodeValue4083]

noncomputable def reducedSource469 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1390 x + ((2 : ℝ) * Sparse.eval nodeValue2930 x + ((1 : ℝ) * Sparse.eval nodeValue2980 x + ((1 : ℝ) * Sparse.eval nodeValue3075 x + ((1 : ℝ) * Sparse.eval nodeValue3079 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow469 : Integer.Sparse Master := [(Sum.inr 1390, 1), (Sum.inr 2930, 2), (Sum.inr 2980, 1), (Sum.inr 3075, 1), (Sum.inr 3079, 1), (Sum.inr 4083, -1)]

theorem reindexCheck469 : Integer.Sparse.reindex keyMap MixedData.row469 = numericRow469 := by decide +kernel

theorem numericCheck469 (x : Master → ℝ) : Integer.Sparse.eval numericRow469 x =
    (1 : ℝ) * reducedSource469 x := by
  norm_num [numericRow469, reducedSource469, Integer.Sparse.eval, Sparse.eval, nodeValue1390, nodeValue2930, nodeValue2980, nodeValue3075, nodeValue3079, nodeValue4083]

noncomputable def reducedSource470 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2693 x + ((1 : ℝ) * Sparse.eval nodeValue2702 x + ((1 : ℝ) * Sparse.eval nodeValue2704 x + ((2 : ℝ) * Sparse.eval nodeValue2740 x + ((2 : ℝ) * Sparse.eval nodeValue3015 x + ((2 : ℝ) * Sparse.eval nodeValue3022 x + ((2 : ℝ) * Sparse.eval nodeValue3024 x + ((2 : ℝ) * Sparse.eval nodeValue3052 x + ((1 : ℝ) * Sparse.eval nodeValue3057 x + ((1 : ℝ) * Sparse.eval nodeValue3058 x + ((1 : ℝ) * Sparse.eval nodeValue3063 x + ((1 : ℝ) * Sparse.eval nodeValue3064 x + ((1 : ℝ) * Sparse.eval nodeValue3072 x + ((2 : ℝ) * Sparse.eval nodeValue3075 x + ((1 : ℝ) * Sparse.eval nodeValue3077 x + ((2 : ℝ) * Sparse.eval nodeValue3098 x + ((2 : ℝ) * Sparse.eval nodeValue3101 x + ((1 : ℝ) * Sparse.eval nodeValue3155 x + ((2 : ℝ) * Sparse.eval nodeValue3156 x + ((1 : ℝ) * Sparse.eval nodeValue3158 x + ((1 : ℝ) * Sparse.eval nodeValue3223 x + 0))))))))))))))))))))

def numericRow470 : Integer.Sparse Master := [(Sum.inl 0, -102), (Sum.inl 2, 95), (Sum.inl 3, 160), (Sum.inl 13, -240), (Sum.inl 12, -80), (Sum.inl 1, 185), (Sum.inr 2702, 4320), (Sum.inr 2704, 4320), (Sum.inr 2740, 8640), (Sum.inr 3015, 8640), (Sum.inr 3022, 8640), (Sum.inr 3024, 8640), (Sum.inr 3052, 8640), (Sum.inr 3057, 4320), (Sum.inr 3058, 4320), (Sum.inr 3063, 4320), (Sum.inr 3064, 4320), (Sum.inr 3072, 4320), (Sum.inr 3075, 8640), (Sum.inr 3077, 4320), (Sum.inr 3098, 8640), (Sum.inr 3155, 4320), (Sum.inr 3156, 8640), (Sum.inr 3158, 4320)]

theorem reindexCheck470 : Integer.Sparse.reindex keyMap MixedData.row470 = numericRow470 := by decide +kernel

theorem numericCheck470 (x : Master → ℝ) : Integer.Sparse.eval numericRow470 x =
    (4320 : ℝ) * reducedSource470 x := by
  norm_num [numericRow470, reducedSource470, Integer.Sparse.eval, Sparse.eval, nodeValue2693, nodeValue2702, nodeValue2704, nodeValue2740, nodeValue3015, nodeValue3022, nodeValue3024, nodeValue3052, nodeValue3057, nodeValue3058, nodeValue3063, nodeValue3064, nodeValue3072, nodeValue3075, nodeValue3077, nodeValue3098, nodeValue3101, nodeValue3155, nodeValue3156, nodeValue3158, nodeValue3223]
  ring

noncomputable def reducedSource471 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1234 x + ((1 : ℝ) * Sparse.eval nodeValue2509 x + ((1 : ℝ) * Sparse.eval nodeValue2552 x + ((1 : ℝ) * Sparse.eval nodeValue2738 x + ((2 : ℝ) * Sparse.eval nodeValue2740 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow471 : Integer.Sparse Master := [(Sum.inr 1234, 1), (Sum.inr 2509, 1), (Sum.inr 2738, 1), (Sum.inr 2740, 2), (Sum.inr 4084, -1)]

theorem reindexCheck471 : Integer.Sparse.reindex keyMap MixedData.row471 = numericRow471 := by decide +kernel

theorem numericCheck471 (x : Master → ℝ) : Integer.Sparse.eval numericRow471 x =
    (1 : ℝ) * reducedSource471 x := by
  norm_num [numericRow471, reducedSource471, Integer.Sparse.eval, Sparse.eval, nodeValue1234, nodeValue2509, nodeValue2552, nodeValue2738, nodeValue2740, nodeValue4084]

noncomputable def reducedSource472 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2131 x + ((1 : ℝ) * Sparse.eval nodeValue2132 x + ((2 : ℝ) * Sparse.eval nodeValue2133 x + ((1 : ℝ) * Sparse.eval nodeValue2277 x + ((1 : ℝ) * Sparse.eval nodeValue2738 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow472 : Integer.Sparse Master := [(Sum.inr 2131, 1), (Sum.inr 2132, 1), (Sum.inr 2133, 2), (Sum.inr 2277, 1), (Sum.inr 2738, 1), (Sum.inr 4084, -1)]

theorem reindexCheck472 : Integer.Sparse.reindex keyMap MixedData.row472 = numericRow472 := by decide +kernel

theorem numericCheck472 (x : Master → ℝ) : Integer.Sparse.eval numericRow472 x =
    (1 : ℝ) * reducedSource472 x := by
  norm_num [numericRow472, reducedSource472, Integer.Sparse.eval, Sparse.eval, nodeValue2131, nodeValue2132, nodeValue2133, nodeValue2277, nodeValue2738, nodeValue4084]

noncomputable def reducedSource473 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4607 x + ((1 : ℝ) * Sparse.eval nodeValue4609 x + ((1 : ℝ) * Sparse.eval nodeValue4611 x + ((1 : ℝ) * Sparse.eval nodeValue4619 x + ((2 : ℝ) * Sparse.eval nodeValue5144 x + ((2 : ℝ) * Sparse.eval nodeValue5147 x + ((2 : ℝ) * Sparse.eval nodeValue5151 x + ((2 : ℝ) * Sparse.eval nodeValue5163 x + ((2 : ℝ) * Sparse.eval nodeValue5198 x + ((1 : ℝ) * Sparse.eval nodeValue5201 x + ((1 : ℝ) * Sparse.eval nodeValue5206 x + ((2 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5261 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((2 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5295 x + ((1 : ℝ) * Sparse.eval nodeValue5304 x + ((2 : ℝ) * Sparse.eval nodeValue5432 x + ((1 : ℝ) * Sparse.eval nodeValue5441 x + ((1 : ℝ) * Sparse.eval nodeValue5449 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + 0))))))))))))))))))))

def numericRow473 : Integer.Sparse Master := [(Sum.inl 0, 18), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 4, -80), (Sum.inl 1, -25), (Sum.inr 1294, -2160), (Sum.inr 2590, -4320), (Sum.inr 2722, -4320), (Sum.inr 2726, -2160), (Sum.inr 2782, -2160), (Sum.inr 3305, -2160), (Sum.inr 3533, -4320), (Sum.inr 3545, -2160), (Sum.inr 3564, -4320), (Sum.inr 3583, -2160), (Sum.inr 3850, -8640), (Sum.inr 3886, -4320), (Sum.inr 3913, -2160), (Sum.inr 4607, 17280), (Sum.inr 4609, 8640), (Sum.inr 4611, 8640), (Sum.inr 5144, 17280), (Sum.inr 5147, 17280), (Sum.inr 5151, 17280), (Sum.inr 5198, 17280), (Sum.inr 5201, 8640), (Sum.inr 5206, 8640), (Sum.inr 5289, 17280), (Sum.inr 5295, 8640)]

theorem reindexCheck473 : Integer.Sparse.reindex keyMap MixedData.row473 = numericRow473 := by decide +kernel

theorem numericCheck473 (x : Master → ℝ) : Integer.Sparse.eval numericRow473 x =
    (8640 : ℝ) * reducedSource473 x := by
  norm_num [numericRow473, reducedSource473, Integer.Sparse.eval, Sparse.eval, nodeValue4607, nodeValue4609, nodeValue4611, nodeValue4619, nodeValue5144, nodeValue5147, nodeValue5151, nodeValue5163, nodeValue5198, nodeValue5201, nodeValue5206, nodeValue5258, nodeValue5261, nodeValue5274, nodeValue5289, nodeValue5295, nodeValue5304, nodeValue5432, nodeValue5441, nodeValue5449, nodeValue5451]
  ring

noncomputable def reducedSource474 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1241 x + ((1 : ℝ) * Sparse.eval nodeValue1243 x + ((1 : ℝ) * Sparse.eval nodeValue1245 x + ((1 : ℝ) * Sparse.eval nodeValue1302 x + ((2 : ℝ) * Sparse.eval nodeValue2865 x + ((2 : ℝ) * Sparse.eval nodeValue2885 x + ((1 : ℝ) * Sparse.eval nodeValue2886 x + ((1 : ℝ) * Sparse.eval nodeValue2888 x + ((2 : ℝ) * Sparse.eval nodeValue2928 x + ((2 : ℝ) * Sparse.eval nodeValue2930 x + ((2 : ℝ) * Sparse.eval nodeValue2961 x + ((2 : ℝ) * Sparse.eval nodeValue3089 x + ((1 : ℝ) * Sparse.eval nodeValue3090 x + ((2 : ℝ) * Sparse.eval nodeValue3097 x + ((1 : ℝ) * Sparse.eval nodeValue3098 x + ((1 : ℝ) * Sparse.eval nodeValue3112 x + ((1 : ℝ) * Sparse.eval nodeValue3119 x + ((1 : ℝ) * Sparse.eval nodeValue3987 x + ((2 : ℝ) * Sparse.eval nodeValue4027 x + ((1 : ℝ) * Sparse.eval nodeValue4030 x + ((1 : ℝ) * Sparse.eval nodeValue4037 x + 0))))))))))))))))))))

def numericRow474 : Integer.Sparse Master := [(Sum.inl 0, -104), (Sum.inl 2, -90), (Sum.inl 3, -160), (Sum.inl 26, -160), (Sum.inl 1, 70), (Sum.inr 1241, 2880), (Sum.inr 1243, 1440), (Sum.inr 1245, 1440), (Sum.inr 2865, 2880), (Sum.inr 2885, 2880), (Sum.inr 2886, 1440), (Sum.inr 2888, 1440), (Sum.inr 2928, 2880), (Sum.inr 2930, 2880), (Sum.inr 3097, 2880), (Sum.inr 3098, 1440)]

theorem reindexCheck474 : Integer.Sparse.reindex keyMap MixedData.row474 = numericRow474 := by decide +kernel

theorem numericCheck474 (x : Master → ℝ) : Integer.Sparse.eval numericRow474 x =
    (1440 : ℝ) * reducedSource474 x := by
  norm_num [numericRow474, reducedSource474, Integer.Sparse.eval, Sparse.eval, nodeValue1241, nodeValue1243, nodeValue1245, nodeValue1302, nodeValue2865, nodeValue2885, nodeValue2886, nodeValue2888, nodeValue2928, nodeValue2930, nodeValue2961, nodeValue3089, nodeValue3090, nodeValue3097, nodeValue3098, nodeValue3112, nodeValue3119, nodeValue3987, nodeValue4027, nodeValue4030, nodeValue4037]
  ring

noncomputable def reducedSource475 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2681 x + ((1 : ℝ) * Sparse.eval nodeValue2683 x + ((1 : ℝ) * Sparse.eval nodeValue2687 x + ((1 : ℝ) * Sparse.eval nodeValue2781 x + ((2 : ℝ) * Sparse.eval nodeValue3296 x + ((1 : ℝ) * Sparse.eval nodeValue3302 x + ((1 : ℝ) * Sparse.eval nodeValue3305 x + ((2 : ℝ) * Sparse.eval nodeValue3530 x + ((2 : ℝ) * Sparse.eval nodeValue3533 x + ((1 : ℝ) * Sparse.eval nodeValue3545 x + ((1 : ℝ) * Sparse.eval nodeValue3547 x + ((2 : ℝ) * Sparse.eval nodeValue3557 x + ((2 : ℝ) * Sparse.eval nodeValue3564 x + ((2 : ℝ) * Sparse.eval nodeValue3570 x + ((2 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3579 x + ((1 : ℝ) * Sparse.eval nodeValue3583 x + ((2 : ℝ) * Sparse.eval nodeValue3850 x + ((1 : ℝ) * Sparse.eval nodeValue3860 x + ((1 : ℝ) * Sparse.eval nodeValue3886 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + 0))))))))))))))))))))

def numericRow475 : Integer.Sparse Master := [(Sum.inl 0, -18), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 4, 80), (Sum.inl 1, 25), (Sum.inr 2681, 4320), (Sum.inr 2683, 2160), (Sum.inr 2687, 2160), (Sum.inr 2781, 2160), (Sum.inr 3296, 4320), (Sum.inr 3302, 2160), (Sum.inr 3305, 2160), (Sum.inr 3530, 4320), (Sum.inr 3533, 4320), (Sum.inr 3545, 2160), (Sum.inr 3557, 4320), (Sum.inr 3564, 4320), (Sum.inr 3570, 4320), (Sum.inr 3572, 4320), (Sum.inr 3579, 2160), (Sum.inr 3583, 2160), (Sum.inr 3850, 4320), (Sum.inr 3886, 2160)]

theorem reindexCheck475 : Integer.Sparse.reindex keyMap MixedData.row475 = numericRow475 := by decide +kernel

theorem numericCheck475 (x : Master → ℝ) : Integer.Sparse.eval numericRow475 x =
    (2160 : ℝ) * reducedSource475 x := by
  norm_num [numericRow475, reducedSource475, Integer.Sparse.eval, Sparse.eval, nodeValue2681, nodeValue2683, nodeValue2687, nodeValue2781, nodeValue3296, nodeValue3302, nodeValue3305, nodeValue3530, nodeValue3533, nodeValue3545, nodeValue3547, nodeValue3557, nodeValue3564, nodeValue3570, nodeValue3572, nodeValue3579, nodeValue3583, nodeValue3850, nodeValue3860, nodeValue3886, nodeValue3888]
  ring

noncomputable def reducedSource476 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2765 x + ((2 : ℝ) * Sparse.eval nodeValue3850 x + ((1 : ℝ) * Sparse.eval nodeValue3886 x + ((1 : ℝ) * Sparse.eval nodeValue3905 x + ((1 : ℝ) * Sparse.eval nodeValue3913 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow476 : Integer.Sparse Master := [(Sum.inr 2765, 1), (Sum.inr 3850, 2), (Sum.inr 3886, 1), (Sum.inr 3913, 1), (Sum.inr 4092, -1)]

theorem reindexCheck476 : Integer.Sparse.reindex keyMap MixedData.row476 = numericRow476 := by decide +kernel

theorem numericCheck476 (x : Master → ℝ) : Integer.Sparse.eval numericRow476 x =
    (1 : ℝ) * reducedSource476 x := by
  norm_num [numericRow476, reducedSource476, Integer.Sparse.eval, Sparse.eval, nodeValue2765, nodeValue3850, nodeValue3886, nodeValue3905, nodeValue3913, nodeValue4092]

noncomputable def reducedSource477 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1261 x + ((1 : ℝ) * Sparse.eval nodeValue1264 x + ((1 : ℝ) * Sparse.eval nodeValue1273 x + ((1 : ℝ) * Sparse.eval nodeValue1294 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow477 : Integer.Sparse Master := [(Sum.inr 1261, 2), (Sum.inr 1264, 1), (Sum.inr 1273, 1), (Sum.inr 1294, 1), (Sum.inr 2765, 1), (Sum.inr 4092, -1)]

theorem reindexCheck477 : Integer.Sparse.reindex keyMap MixedData.row477 = numericRow477 := by decide +kernel

theorem numericCheck477 (x : Master → ℝ) : Integer.Sparse.eval numericRow477 x =
    (1 : ℝ) * reducedSource477 x := by
  norm_num [numericRow477, reducedSource477, Integer.Sparse.eval, Sparse.eval, nodeValue1261, nodeValue1264, nodeValue1273, nodeValue1294, nodeValue2765, nodeValue4092]

noncomputable def reducedSource478 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1294 x + ((2 : ℝ) * Sparse.eval nodeValue2590 x + ((1 : ℝ) * Sparse.eval nodeValue2742 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((1 : ℝ) * Sparse.eval nodeValue2782 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow478 : Integer.Sparse Master := [(Sum.inr 1294, 1), (Sum.inr 2590, 2), (Sum.inr 2765, 1), (Sum.inr 2782, 1), (Sum.inr 4092, -1)]

theorem reindexCheck478 : Integer.Sparse.reindex keyMap MixedData.row478 = numericRow478 := by decide +kernel

theorem numericCheck478 (x : Master → ℝ) : Integer.Sparse.eval numericRow478 x =
    (1 : ℝ) * reducedSource478 x := by
  norm_num [numericRow478, reducedSource478, Integer.Sparse.eval, Sparse.eval, nodeValue1294, nodeValue2590, nodeValue2742, nodeValue2765, nodeValue2782, nodeValue4092]

noncomputable def reducedSource479 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2632 x + ((1 : ℝ) * Sparse.eval nodeValue2635 x + ((1 : ℝ) * Sparse.eval nodeValue2643 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((1 : ℝ) * Sparse.eval nodeValue3886 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow479 : Integer.Sparse Master := [(Sum.inr 2632, 2), (Sum.inr 2635, 1), (Sum.inr 2643, 1), (Sum.inr 2765, 1), (Sum.inr 3886, 1), (Sum.inr 4092, -1)]

theorem reindexCheck479 : Integer.Sparse.reindex keyMap MixedData.row479 = numericRow479 := by decide +kernel

theorem numericCheck479 (x : Master → ℝ) : Integer.Sparse.eval numericRow479 x =
    (1 : ℝ) * reducedSource479 x := by
  norm_num [numericRow479, reducedSource479, Integer.Sparse.eval, Sparse.eval, nodeValue2632, nodeValue2635, nodeValue2643, nodeValue2765, nodeValue3886, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
