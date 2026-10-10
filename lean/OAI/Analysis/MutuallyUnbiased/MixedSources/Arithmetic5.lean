import OAI.Analysis.MutuallyUnbiased.MixedData.Source0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values85
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource80 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1388 x + ((1 : ℝ) * Sparse.eval nodeValue2470 x + ((2 : ℝ) * Sparse.eval nodeValue2485 x + ((1 : ℝ) * Sparse.eval nodeValue2712 x + ((1 : ℝ) * Sparse.eval nodeValue3077 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow80 : Integer.Sparse Master := [(Sum.inr 1388, 1), (Sum.inr 2470, 1), (Sum.inr 2485, 2), (Sum.inr 2712, 1), (Sum.inr 3077, 1), (Sum.inr 4091, -1)]

theorem reindexCheck80 : Integer.Sparse.reindex keyMap MixedData.row80 = numericRow80 := by decide +kernel

theorem numericCheck80 (x : Master → ℝ) : Integer.Sparse.eval numericRow80 x =
    (1 : ℝ) * reducedSource80 x := by
  norm_num [numericRow80, reducedSource80, Integer.Sparse.eval, Sparse.eval, nodeValue1388, nodeValue2470, nodeValue2485, nodeValue2712, nodeValue3077, nodeValue4091]

noncomputable def reducedSource81 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1206 x + ((1 : ℝ) * Sparse.eval nodeValue2470 x + ((2 : ℝ) * Sparse.eval nodeValue2610 x + ((1 : ℝ) * Sparse.eval nodeValue2709 x + ((1 : ℝ) * Sparse.eval nodeValue2712 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow81 : Integer.Sparse Master := [(Sum.inr 1206, 1), (Sum.inr 2470, 1), (Sum.inr 2610, 2), (Sum.inr 2712, 1), (Sum.inr 4091, -1)]

theorem reindexCheck81 : Integer.Sparse.reindex keyMap MixedData.row81 = numericRow81 := by decide +kernel

theorem numericCheck81 (x : Master → ℝ) : Integer.Sparse.eval numericRow81 x =
    (1 : ℝ) * reducedSource81 x := by
  norm_num [numericRow81, reducedSource81, Integer.Sparse.eval, Sparse.eval, nodeValue1206, nodeValue2470, nodeValue2610, nodeValue2709, nodeValue2712, nodeValue4091]

noncomputable def reducedSource82 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1378 x + ((2 : ℝ) * Sparse.eval nodeValue2543 x + ((1 : ℝ) * Sparse.eval nodeValue2562 x + ((1 : ℝ) * Sparse.eval nodeValue2712 x + ((1 : ℝ) * Sparse.eval nodeValue3064 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow82 : Integer.Sparse Master := [(Sum.inr 1378, 1), (Sum.inr 2543, 2), (Sum.inr 2562, 1), (Sum.inr 2712, 1), (Sum.inr 3064, 1), (Sum.inr 4091, -1)]

theorem reindexCheck82 : Integer.Sparse.reindex keyMap MixedData.row82 = numericRow82 := by decide +kernel

theorem numericCheck82 (x : Master → ℝ) : Integer.Sparse.eval numericRow82 x =
    (1 : ℝ) * reducedSource82 x := by
  norm_num [numericRow82, reducedSource82, Integer.Sparse.eval, Sparse.eval, nodeValue1378, nodeValue2543, nodeValue2562, nodeValue2712, nodeValue3064, nodeValue4091]

noncomputable def reducedSource83 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1217 x + ((1 : ℝ) * Sparse.eval nodeValue2485 x + ((1 : ℝ) * Sparse.eval nodeValue2543 x + ((1 : ℝ) * Sparse.eval nodeValue2618 x + ((1 : ℝ) * Sparse.eval nodeValue2712 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow83 : Integer.Sparse Master := [(Sum.inr 1217, 1), (Sum.inr 2485, 1), (Sum.inr 2543, 1), (Sum.inr 2618, 1), (Sum.inr 2712, 1), (Sum.inr 2723, 1), (Sum.inr 4091, -1)]

theorem reindexCheck83 : Integer.Sparse.reindex keyMap MixedData.row83 = numericRow83 := by decide +kernel

theorem numericCheck83 (x : Master → ℝ) : Integer.Sparse.eval numericRow83 x =
    (1 : ℝ) * reducedSource83 x := by
  norm_num [numericRow83, reducedSource83, Integer.Sparse.eval, Sparse.eval, nodeValue1217, nodeValue2485, nodeValue2543, nodeValue2618, nodeValue2712, nodeValue2723, nodeValue4091]

noncomputable def reducedSource84 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1394 x + ((1 : ℝ) * Sparse.eval nodeValue2610 x + ((1 : ℝ) * Sparse.eval nodeValue2618 x + ((1 : ℝ) * Sparse.eval nodeValue2624 x + ((1 : ℝ) * Sparse.eval nodeValue2712 x + ((1 : ℝ) * Sparse.eval nodeValue3086 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow84 : Integer.Sparse Master := [(Sum.inr 1394, 1), (Sum.inr 2610, 1), (Sum.inr 2618, 1), (Sum.inr 2624, 1), (Sum.inr 2712, 1), (Sum.inr 3086, 1), (Sum.inr 4091, -1)]

theorem reindexCheck84 : Integer.Sparse.reindex keyMap MixedData.row84 = numericRow84 := by decide +kernel

theorem numericCheck84 (x : Master → ℝ) : Integer.Sparse.eval numericRow84 x =
    (1 : ℝ) * reducedSource84 x := by
  norm_num [numericRow84, reducedSource84, Integer.Sparse.eval, Sparse.eval, nodeValue1394, nodeValue2610, nodeValue2618, nodeValue2624, nodeValue2712, nodeValue3086, nodeValue4091]

noncomputable def reducedSource85 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1209 x + ((1 : ℝ) * Sparse.eval nodeValue1378 x + ((1 : ℝ) * Sparse.eval nodeValue1388 x + ((2 : ℝ) * Sparse.eval nodeValue1394 x + ((1 : ℝ) * Sparse.eval nodeValue2712 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow85 : Integer.Sparse Master := [(Sum.inr 1209, 1), (Sum.inr 1378, 1), (Sum.inr 1388, 1), (Sum.inr 1394, 2), (Sum.inr 2712, 1), (Sum.inr 4091, -1)]

theorem reindexCheck85 : Integer.Sparse.reindex keyMap MixedData.row85 = numericRow85 := by decide +kernel

theorem numericCheck85 (x : Master → ℝ) : Integer.Sparse.eval numericRow85 x =
    (1 : ℝ) * reducedSource85 x := by
  norm_num [numericRow85, reducedSource85, Integer.Sparse.eval, Sparse.eval, nodeValue1209, nodeValue1378, nodeValue1388, nodeValue1394, nodeValue2712, nodeValue4091]

noncomputable def reducedSource86 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2052 x + ((1 : ℝ) * Sparse.eval nodeValue3389 x + ((1 : ℝ) * Sparse.eval nodeValue3492 x + ((1 : ℝ) * Sparse.eval nodeValue3543 x + ((2 : ℝ) * Sparse.eval nodeValue3545 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0)))))

def numericRow86 : Integer.Sparse Master := [(Sum.inr 2052, 1), (Sum.inr 3389, 1), (Sum.inr 3543, 1), (Sum.inr 3545, 2), (Sum.inr 4085, -1)]

theorem reindexCheck86 : Integer.Sparse.reindex keyMap MixedData.row86 = numericRow86 := by decide +kernel

theorem numericCheck86 (x : Master → ℝ) : Integer.Sparse.eval numericRow86 x =
    (1 : ℝ) * reducedSource86 x := by
  norm_num [numericRow86, reducedSource86, Integer.Sparse.eval, Sparse.eval, nodeValue2052, nodeValue3389, nodeValue3492, nodeValue3543, nodeValue3545, nodeValue4085]

noncomputable def reducedSource87 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2050 x + ((1 : ℝ) * Sparse.eval nodeValue2052 x + ((2 : ℝ) * Sparse.eval nodeValue2055 x + ((1 : ℝ) * Sparse.eval nodeValue2290 x + ((1 : ℝ) * Sparse.eval nodeValue3543 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0)))))

def numericRow87 : Integer.Sparse Master := [(Sum.inr 2050, 1), (Sum.inr 2052, 1), (Sum.inr 2055, 2), (Sum.inr 2290, 1), (Sum.inr 3543, 1), (Sum.inr 4085, -1)]

theorem reindexCheck87 : Integer.Sparse.reindex keyMap MixedData.row87 = numericRow87 := by decide +kernel

theorem numericCheck87 (x : Master → ℝ) : Integer.Sparse.eval numericRow87 x =
    (1 : ℝ) * reducedSource87 x := by
  norm_num [numericRow87, reducedSource87, Integer.Sparse.eval, Sparse.eval, nodeValue2050, nodeValue2052, nodeValue2055, nodeValue2290, nodeValue3543, nodeValue4085]

noncomputable def reducedSource88 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2290 x + ((2 : ℝ) * Sparse.eval nodeValue3543 x + ((2 : ℝ) * Sparse.eval nodeValue3634 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0)))

def numericRow88 : Integer.Sparse Master := [(Sum.inr 2290, 2), (Sum.inr 3543, 2), (Sum.inr 3634, 2), (Sum.inr 4085, -1)]

theorem reindexCheck88 : Integer.Sparse.reindex keyMap MixedData.row88 = numericRow88 := by decide +kernel

theorem numericCheck88 (x : Master → ℝ) : Integer.Sparse.eval numericRow88 x =
    (1 : ℝ) * reducedSource88 x := by
  norm_num [numericRow88, reducedSource88, Integer.Sparse.eval, Sparse.eval, nodeValue2290, nodeValue3543, nodeValue3634, nodeValue4085]

noncomputable def reducedSource89 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3387 x + ((2 : ℝ) * Sparse.eval nodeValue3389 x + ((2 : ℝ) * Sparse.eval nodeValue3393 x + ((1 : ℝ) * Sparse.eval nodeValue3543 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

def numericRow89 : Integer.Sparse Master := [(Sum.inr 3387, 1), (Sum.inr 3389, 2), (Sum.inr 3393, 2), (Sum.inr 3543, 1), (Sum.inr 4085, -1)]

theorem reindexCheck89 : Integer.Sparse.reindex keyMap MixedData.row89 = numericRow89 := by decide +kernel

theorem numericCheck89 (x : Master → ℝ) : Integer.Sparse.eval numericRow89 x =
    (1 : ℝ) * reducedSource89 x := by
  norm_num [numericRow89, reducedSource89, Integer.Sparse.eval, Sparse.eval, nodeValue3387, nodeValue3389, nodeValue3393, nodeValue3543, nodeValue4085]

noncomputable def reducedSource90 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2050 x + ((1 : ℝ) * Sparse.eval nodeValue3387 x + ((3 : ℝ) * Sparse.eval nodeValue3543 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0)))

def numericRow90 : Integer.Sparse Master := [(Sum.inr 2050, 2), (Sum.inr 3387, 1), (Sum.inr 3543, 3), (Sum.inr 4085, -1)]

theorem reindexCheck90 : Integer.Sparse.reindex keyMap MixedData.row90 = numericRow90 := by decide +kernel

theorem numericCheck90 (x : Master → ℝ) : Integer.Sparse.eval numericRow90 x =
    (1 : ℝ) * reducedSource90 x := by
  norm_num [numericRow90, reducedSource90, Integer.Sparse.eval, Sparse.eval, nodeValue2050, nodeValue3387, nodeValue3543, nodeValue4085]

noncomputable def reducedSource91 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4463 x + ((1 : ℝ) * Sparse.eval nodeValue4468 x + ((1 : ℝ) * Sparse.eval nodeValue4507 x + ((3 : ℝ) * Sparse.eval nodeValue4608 x + ((1 : ℝ) * Sparse.eval nodeValue4625 x + ((6 : ℝ) * Sparse.eval nodeValue5078 x + ((3 : ℝ) * Sparse.eval nodeValue5109 x + ((3 : ℝ) * Sparse.eval nodeValue5174 x + ((3 : ℝ) * Sparse.eval nodeValue5293 x + ((3 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5309 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + ((1 : ℝ) * Sparse.eval nodeValue5455 x + 0))))))))))))

def numericRow91 : Integer.Sparse Master := [(Sum.inl 0, 4), (Sum.inl 2, -5), (Sum.inl 1, -5), (Sum.inr 1046, -120), (Sum.inr 1051, -40), (Sum.inr 1091, -40), (Sum.inr 1242, -120), (Sum.inr 1750, -120), (Sum.inr 1752, -40), (Sum.inr 1756, -40), (Sum.inr 2485, -240), (Sum.inr 2519, -120), (Sum.inr 3300, -120), (Sum.inr 3310, -40), (Sum.inr 3481, -240), (Sum.inr 3486, -120), (Sum.inr 3615, -120), (Sum.inr 3627, -120), (Sum.inr 3632, -120), (Sum.inr 3633, -40)]

theorem reindexCheck91 : Integer.Sparse.reindex keyMap MixedData.row91 = numericRow91 := by decide +kernel

theorem numericCheck91 (x : Master → ℝ) : Integer.Sparse.eval numericRow91 x =
    (160 : ℝ) * reducedSource91 x := by
  norm_num [numericRow91, reducedSource91, Integer.Sparse.eval, Sparse.eval, nodeValue4463, nodeValue4468, nodeValue4507, nodeValue4608, nodeValue4625, nodeValue5078, nodeValue5109, nodeValue5174, nodeValue5293, nodeValue5294, nodeValue5309, nodeValue5310, nodeValue5455]
  ring

noncomputable def reducedSource92 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1046 x + ((1 : ℝ) * Sparse.eval nodeValue1051 x + ((1 : ℝ) * Sparse.eval nodeValue1091 x + ((3 : ℝ) * Sparse.eval nodeValue1242 x + ((1 : ℝ) * Sparse.eval nodeValue1304 x + ((6 : ℝ) * Sparse.eval nodeValue2485 x + ((3 : ℝ) * Sparse.eval nodeValue2519 x + ((3 : ℝ) * Sparse.eval nodeValue2601 x + ((3 : ℝ) * Sparse.eval nodeValue2768 x + ((1 : ℝ) * Sparse.eval nodeValue2788 x + ((3 : ℝ) * Sparse.eval nodeValue3102 x + ((1 : ℝ) * Sparse.eval nodeValue3123 x + ((1 : ℝ) * Sparse.eval nodeValue4019 x + 0))))))))))))

def numericRow92 : Integer.Sparse Master := [(Sum.inl 0, -4), (Sum.inl 2, 5), (Sum.inl 1, 5), (Sum.inr 1046, 120), (Sum.inr 1051, 40), (Sum.inr 1091, 40), (Sum.inr 1242, 120), (Sum.inr 2485, 240), (Sum.inr 2519, 120)]

theorem reindexCheck92 : Integer.Sparse.reindex keyMap MixedData.row92 = numericRow92 := by decide +kernel

theorem numericCheck92 (x : Master → ℝ) : Integer.Sparse.eval numericRow92 x =
    (40 : ℝ) * reducedSource92 x := by
  norm_num [numericRow92, reducedSource92, Integer.Sparse.eval, Sparse.eval, nodeValue1046, nodeValue1051, nodeValue1091, nodeValue1242, nodeValue1304, nodeValue2485, nodeValue2519, nodeValue2601, nodeValue2768, nodeValue2788, nodeValue3102, nodeValue3123, nodeValue4019]
  ring

noncomputable def reducedSource93 (x : Master → ℝ) : ℝ :=
  (6 : ℝ) * Sparse.eval nodeValue4890 x + ((2 : ℝ) * Sparse.eval nodeValue4897 x + ((2 : ℝ) * Sparse.eval nodeValue4899 x + ((6 : ℝ) * Sparse.eval nodeValue5252 x + ((6 : ℝ) * Sparse.eval nodeValue5261 x + ((3 : ℝ) * Sparse.eval nodeValue5268 x + ((3 : ℝ) * Sparse.eval nodeValue5296 x + ((2 : ℝ) * Sparse.eval nodeValue5312 x + 0)))))))

def numericRow93 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 2, 5), (Sum.inr 2247, -240), (Sum.inr 2281, -80), (Sum.inr 2290, -240), (Sum.inr 2294, -80), (Sum.inr 2726, -240), (Sum.inr 3545, -240), (Sum.inr 3634, -120), (Sum.inr 5252, 960), (Sum.inr 5268, 480)]

theorem reindexCheck93 : Integer.Sparse.reindex keyMap MixedData.row93 = numericRow93 := by decide +kernel

theorem numericCheck93 (x : Master → ℝ) : Integer.Sparse.eval numericRow93 x =
    (160 : ℝ) * reducedSource93 x := by
  norm_num [numericRow93, reducedSource93, Integer.Sparse.eval, Sparse.eval, nodeValue4890, nodeValue4897, nodeValue4899, nodeValue5252, nodeValue5261, nodeValue5268, nodeValue5296, nodeValue5312]
  ring

noncomputable def reducedSource94 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue2247 x + ((1 : ℝ) * Sparse.eval nodeValue2268 x + ((1 : ℝ) * Sparse.eval nodeValue2281 x + ((6 : ℝ) * Sparse.eval nodeValue2712 x + ((3 : ℝ) * Sparse.eval nodeValue2726 x + ((3 : ℝ) * Sparse.eval nodeValue2734 x + ((3 : ℝ) * Sparse.eval nodeValue2755 x + ((3 : ℝ) * Sparse.eval nodeValue2770 x + ((1 : ℝ) * Sparse.eval nodeValue2778 x + ((1 : ℝ) * Sparse.eval nodeValue2790 x + ((3 : ℝ) * Sparse.eval nodeValue3090 x + ((1 : ℝ) * Sparse.eval nodeValue3114 x + ((1 : ℝ) * Sparse.eval nodeValue3126 x + 0))))))))))))

def numericRow94 : Integer.Sparse Master := [(Sum.inl 0, -3), (Sum.inl 2, -15), (Sum.inr 2247, 120), (Sum.inr 2281, 40), (Sum.inr 2712, 240), (Sum.inr 2726, 120), (Sum.inr 2734, 120)]

theorem reindexCheck94 : Integer.Sparse.reindex keyMap MixedData.row94 = numericRow94 := by decide +kernel

theorem numericCheck94 (x : Master → ℝ) : Integer.Sparse.eval numericRow94 x =
    (40 : ℝ) * reducedSource94 x := by
  norm_num [numericRow94, reducedSource94, Integer.Sparse.eval, Sparse.eval, nodeValue2247, nodeValue2268, nodeValue2281, nodeValue2712, nodeValue2726, nodeValue2734, nodeValue2755, nodeValue2770, nodeValue2778, nodeValue2790, nodeValue3090, nodeValue3114, nodeValue3126]
  ring

noncomputable def reducedSource95 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2292 x + ((3 : ℝ) * Sparse.eval nodeValue3545 x + ((1 : ℝ) * Sparse.eval nodeValue3634 x + ((1 : ℝ) * Sparse.eval nodeValue3636 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

def numericRow95 : Integer.Sparse Master := [(Sum.inr 3545, 3), (Sum.inr 3634, 1), (Sum.inr 4085, -1)]

theorem reindexCheck95 : Integer.Sparse.reindex keyMap MixedData.row95 = numericRow95 := by decide +kernel

theorem numericCheck95 (x : Master → ℝ) : Integer.Sparse.eval numericRow95 x =
    (1 : ℝ) * reducedSource95 x := by
  norm_num [numericRow95, reducedSource95, Integer.Sparse.eval, Sparse.eval, nodeValue2292, nodeValue3545, nodeValue3634, nodeValue3636, nodeValue4085]

end MUB6.Certificate.MixedSourceBridge

end OAI
