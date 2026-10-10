import OAI.Analysis.MutuallyUnbiased.MixedData.Source0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource64 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1224 x + ((1 : ℝ) * Sparse.eval nodeValue2495 x + ((1 : ℝ) * Sparse.eval nodeValue2547 x + ((1 : ℝ) * Sparse.eval nodeValue2647 x + ((1 : ℝ) * Sparse.eval nodeValue2731 x + ((1 : ℝ) * Sparse.eval nodeValue2734 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow64 : Integer.Sparse Master := [(Sum.inr 1224, 1), (Sum.inr 2495, 1), (Sum.inr 2547, 1), (Sum.inr 2647, 1), (Sum.inr 2731, 1), (Sum.inr 2734, 1), (Sum.inr 4092, -1)]

theorem reindexCheck64 : Integer.Sparse.reindex keyMap MixedData.row64 = numericRow64 := by decide +kernel

theorem numericCheck64 (x : Master → ℝ) : Integer.Sparse.eval numericRow64 x =
    (1 : ℝ) * reducedSource64 x := by
  norm_num [numericRow64, reducedSource64, Integer.Sparse.eval, Sparse.eval, nodeValue1224, nodeValue2495, nodeValue2547, nodeValue2647, nodeValue2731, nodeValue2734, nodeValue4092]

noncomputable def reducedSource65 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1359 x + ((1 : ℝ) * Sparse.eval nodeValue2547 x + ((1 : ℝ) * Sparse.eval nodeValue2558 x + ((1 : ℝ) * Sparse.eval nodeValue2579 x + ((1 : ℝ) * Sparse.eval nodeValue2734 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow65 : Integer.Sparse Master := [(Sum.inr 1359, 1), (Sum.inr 2547, 1), (Sum.inr 2558, 1), (Sum.inr 2579, 1), (Sum.inr 2734, 1), (Sum.inr 3038, 1), (Sum.inr 4092, -1)]

theorem reindexCheck65 : Integer.Sparse.reindex keyMap MixedData.row65 = numericRow65 := by decide +kernel

theorem numericCheck65 (x : Master → ℝ) : Integer.Sparse.eval numericRow65 x =
    (1 : ℝ) * reducedSource65 x := by
  norm_num [numericRow65, reducedSource65, Integer.Sparse.eval, Sparse.eval, nodeValue1359, nodeValue2547, nodeValue2558, nodeValue2579, nodeValue2734, nodeValue3038, nodeValue4092]

noncomputable def reducedSource66 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1243 x + ((1 : ℝ) * Sparse.eval nodeValue2519 x + ((2 : ℝ) * Sparse.eval nodeValue2558 x + ((1 : ℝ) * Sparse.eval nodeValue2734 x + ((1 : ℝ) * Sparse.eval nodeValue2743 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow66 : Integer.Sparse Master := [(Sum.inr 1243, 1), (Sum.inr 2519, 1), (Sum.inr 2558, 2), (Sum.inr 2734, 1), (Sum.inr 2743, 1), (Sum.inr 4092, -1)]

theorem reindexCheck66 : Integer.Sparse.reindex keyMap MixedData.row66 = numericRow66 := by decide +kernel

theorem numericCheck66 (x : Master → ℝ) : Integer.Sparse.eval numericRow66 x =
    (1 : ℝ) * reducedSource66 x := by
  norm_num [numericRow66, reducedSource66, Integer.Sparse.eval, Sparse.eval, nodeValue1243, nodeValue2519, nodeValue2558, nodeValue2734, nodeValue2743, nodeValue4092]

noncomputable def reducedSource67 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1424 x + ((2 : ℝ) * Sparse.eval nodeValue2647 x + ((1 : ℝ) * Sparse.eval nodeValue2651 x + ((1 : ℝ) * Sparse.eval nodeValue2734 x + ((1 : ℝ) * Sparse.eval nodeValue2777 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow67 : Integer.Sparse Master := [(Sum.inr 1424, 1), (Sum.inr 2647, 2), (Sum.inr 2651, 1), (Sum.inr 2734, 1), (Sum.inr 2777, 1), (Sum.inr 4092, -1)]

theorem reindexCheck67 : Integer.Sparse.reindex keyMap MixedData.row67 = numericRow67 := by decide +kernel

theorem numericCheck67 (x : Master → ℝ) : Integer.Sparse.eval numericRow67 x =
    (1 : ℝ) * reducedSource67 x := by
  norm_num [numericRow67, reducedSource67, Integer.Sparse.eval, Sparse.eval, nodeValue1424, nodeValue2647, nodeValue2651, nodeValue2734, nodeValue2777, nodeValue4092]

noncomputable def reducedSource68 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1227 x + ((2 : ℝ) * Sparse.eval nodeValue1359 x + ((1 : ℝ) * Sparse.eval nodeValue1372 x + ((1 : ℝ) * Sparse.eval nodeValue1424 x + ((1 : ℝ) * Sparse.eval nodeValue2734 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow68 : Integer.Sparse Master := [(Sum.inr 1227, 1), (Sum.inr 1359, 2), (Sum.inr 1372, 1), (Sum.inr 1424, 1), (Sum.inr 2734, 1), (Sum.inr 4092, -1)]

theorem reindexCheck68 : Integer.Sparse.reindex keyMap MixedData.row68 = numericRow68 := by decide +kernel

theorem numericCheck68 (x : Master → ℝ) : Integer.Sparse.eval numericRow68 x =
    (1 : ℝ) * reducedSource68 x := by
  norm_num [numericRow68, reducedSource68, Integer.Sparse.eval, Sparse.eval, nodeValue1227, nodeValue1359, nodeValue1372, nodeValue1424, nodeValue2734, nodeValue4092]

noncomputable def reducedSource69 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2065 x + ((2 : ℝ) * Sparse.eval nodeValue3389 x + ((1 : ℝ) * Sparse.eval nodeValue3396 x + ((1 : ℝ) * Sparse.eval nodeValue3545 x + ((1 : ℝ) * Sparse.eval nodeValue3549 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0)))))

def numericRow69 : Integer.Sparse Master := [(Sum.inr 2065, 1), (Sum.inr 3389, 2), (Sum.inr 3396, 1), (Sum.inr 3545, 1), (Sum.inr 3549, 1), (Sum.inr 4085, -1)]

theorem reindexCheck69 : Integer.Sparse.reindex keyMap MixedData.row69 = numericRow69 := by decide +kernel

theorem numericCheck69 (x : Master → ℝ) : Integer.Sparse.eval numericRow69 x =
    (1 : ℝ) * reducedSource69 x := by
  norm_num [numericRow69, reducedSource69, Integer.Sparse.eval, Sparse.eval, nodeValue2065, nodeValue3389, nodeValue3396, nodeValue3545, nodeValue3549, nodeValue4085]

noncomputable def reducedSource70 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2055 x + ((1 : ℝ) * Sparse.eval nodeValue2063 x + ((1 : ℝ) * Sparse.eval nodeValue2065 x + ((1 : ℝ) * Sparse.eval nodeValue2294 x + ((1 : ℝ) * Sparse.eval nodeValue3549 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0)))))

def numericRow70 : Integer.Sparse Master := [(Sum.inr 2055, 2), (Sum.inr 2063, 1), (Sum.inr 2065, 1), (Sum.inr 2294, 1), (Sum.inr 3549, 1), (Sum.inr 4085, -1)]

theorem reindexCheck70 : Integer.Sparse.reindex keyMap MixedData.row70 = numericRow70 := by decide +kernel

theorem numericCheck70 (x : Master → ℝ) : Integer.Sparse.eval numericRow70 x =
    (1 : ℝ) * reducedSource70 x := by
  norm_num [numericRow70, reducedSource70, Integer.Sparse.eval, Sparse.eval, nodeValue2055, nodeValue2063, nodeValue2065, nodeValue2294, nodeValue3549, nodeValue4085]

noncomputable def reducedSource71 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2294 x + ((3 : ℝ) * Sparse.eval nodeValue3549 x + ((1 : ℝ) * Sparse.eval nodeValue3634 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0)))

def numericRow71 : Integer.Sparse Master := [(Sum.inr 2294, 2), (Sum.inr 3549, 3), (Sum.inr 3634, 1), (Sum.inr 4085, -1)]

theorem reindexCheck71 : Integer.Sparse.reindex keyMap MixedData.row71 = numericRow71 := by decide +kernel

theorem numericCheck71 (x : Master → ℝ) : Integer.Sparse.eval numericRow71 x =
    (1 : ℝ) * reducedSource71 x := by
  norm_num [numericRow71, reducedSource71, Integer.Sparse.eval, Sparse.eval, nodeValue2294, nodeValue3549, nodeValue3634, nodeValue4085]

noncomputable def reducedSource72 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3160 x + ((2 : ℝ) * Sparse.eval nodeValue3393 x + ((2 : ℝ) * Sparse.eval nodeValue3396 x + ((1 : ℝ) * Sparse.eval nodeValue3549 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

def numericRow72 : Integer.Sparse Master := [(Sum.inr 3160, 1), (Sum.inr 3393, 2), (Sum.inr 3396, 2), (Sum.inr 3549, 1), (Sum.inr 4085, -1)]

theorem reindexCheck72 : Integer.Sparse.reindex keyMap MixedData.row72 = numericRow72 := by decide +kernel

theorem numericCheck72 (x : Master → ℝ) : Integer.Sparse.eval numericRow72 x =
    (1 : ℝ) * reducedSource72 x := by
  norm_num [numericRow72, reducedSource72, Integer.Sparse.eval, Sparse.eval, nodeValue3160, nodeValue3393, nodeValue3396, nodeValue3549, nodeValue4085]

noncomputable def reducedSource73 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2055 x + ((1 : ℝ) * Sparse.eval nodeValue3393 x + ((1 : ℝ) * Sparse.eval nodeValue3495 x + ((1 : ℝ) * Sparse.eval nodeValue3543 x + ((1 : ℝ) * Sparse.eval nodeValue3549 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0)))))

def numericRow73 : Integer.Sparse Master := [(Sum.inr 2055, 2), (Sum.inr 3393, 1), (Sum.inr 3495, 1), (Sum.inr 3543, 1), (Sum.inr 3549, 1), (Sum.inr 4085, -1)]

theorem reindexCheck73 : Integer.Sparse.reindex keyMap MixedData.row73 = numericRow73 := by decide +kernel

theorem numericCheck73 (x : Master → ℝ) : Integer.Sparse.eval numericRow73 x =
    (1 : ℝ) * reducedSource73 x := by
  norm_num [numericRow73, reducedSource73, Integer.Sparse.eval, Sparse.eval, nodeValue2055, nodeValue3393, nodeValue3495, nodeValue3543, nodeValue3549, nodeValue4085]

noncomputable def reducedSource74 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3154 x + ((2 : ℝ) * Sparse.eval nodeValue3389 x + ((1 : ℝ) * Sparse.eval nodeValue3495 x + ((2 : ℝ) * Sparse.eval nodeValue3549 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

def numericRow74 : Integer.Sparse Master := [(Sum.inr 3154, 1), (Sum.inr 3389, 2), (Sum.inr 3495, 1), (Sum.inr 3549, 2), (Sum.inr 4085, -1)]

theorem reindexCheck74 : Integer.Sparse.reindex keyMap MixedData.row74 = numericRow74 := by decide +kernel

theorem numericCheck74 (x : Master → ℝ) : Integer.Sparse.eval numericRow74 x =
    (1 : ℝ) * reducedSource74 x := by
  norm_num [numericRow74, reducedSource74, Integer.Sparse.eval, Sparse.eval, nodeValue3154, nodeValue3389, nodeValue3495, nodeValue3549, nodeValue4085]

noncomputable def reducedSource75 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2063 x + ((2 : ℝ) * Sparse.eval nodeValue3154 x + ((1 : ℝ) * Sparse.eval nodeValue3160 x + ((1 : ℝ) * Sparse.eval nodeValue3549 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

def numericRow75 : Integer.Sparse Master := [(Sum.inr 2063, 2), (Sum.inr 3154, 2), (Sum.inr 3160, 1), (Sum.inr 3549, 1), (Sum.inr 4085, -1)]

theorem reindexCheck75 : Integer.Sparse.reindex keyMap MixedData.row75 = numericRow75 := by decide +kernel

theorem numericCheck75 (x : Master → ℝ) : Integer.Sparse.eval numericRow75 x =
    (1 : ℝ) * reducedSource75 x := by
  norm_num [numericRow75, reducedSource75, Integer.Sparse.eval, Sparse.eval, nodeValue2063, nodeValue3154, nodeValue3160, nodeValue3549, nodeValue4085]

noncomputable def reducedSource76 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1613 x + ((1 : ℝ) * Sparse.eval nodeValue1615 x + ((2 : ℝ) * Sparse.eval nodeValue1619 x + ((1 : ℝ) * Sparse.eval nodeValue1723 x + ((1 : ℝ) * Sparse.eval nodeValue3279 x + ((1 : ℝ) * Sparse.eval nodeValue3283 x + ((2 : ℝ) * Sparse.eval nodeValue3291 x + ((1 : ℝ) * Sparse.eval nodeValue3350 x + ((2 : ℝ) * Sparse.eval nodeValue3355 x + ((2 : ℝ) * Sparse.eval nodeValue3434 x + ((1 : ℝ) * Sparse.eval nodeValue3466 x + ((2 : ℝ) * Sparse.eval nodeValue3481 x + ((2 : ℝ) * Sparse.eval nodeValue3519 x + ((2 : ℝ) * Sparse.eval nodeValue3523 x + ((1 : ℝ) * Sparse.eval nodeValue3531 x + ((1 : ℝ) * Sparse.eval nodeValue3539 x + ((2 : ℝ) * Sparse.eval nodeValue3540 x + ((2 : ℝ) * Sparse.eval nodeValue3544 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((1 : ℝ) * Sparse.eval nodeValue3625 x + ((1 : ℝ) * Sparse.eval nodeValue3858 x + 0))))))))))))))))))))

def numericRow76 : Integer.Sparse Master := [(Sum.inl 0, -33), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 12, -80), (Sum.inl 1, -190), (Sum.inr 1613, 4320), (Sum.inr 1615, 4320), (Sum.inr 1619, 8640), (Sum.inr 1723, 4320), (Sum.inr 3279, 4320), (Sum.inr 3283, 4320), (Sum.inr 3291, 8640), (Sum.inr 3350, 4320), (Sum.inr 3355, 8640), (Sum.inr 3434, 8640), (Sum.inr 3466, 4320), (Sum.inr 3481, 8640), (Sum.inr 3519, 8640), (Sum.inr 3523, 8640), (Sum.inr 3539, 4320), (Sum.inr 3540, 8640), (Sum.inr 3544, 8640), (Sum.inr 3580, 4320), (Sum.inr 3625, 4320)]

theorem reindexCheck76 : Integer.Sparse.reindex keyMap MixedData.row76 = numericRow76 := by decide +kernel

theorem numericCheck76 (x : Master → ℝ) : Integer.Sparse.eval numericRow76 x =
    (4320 : ℝ) * reducedSource76 x := by
  norm_num [numericRow76, reducedSource76, Integer.Sparse.eval, Sparse.eval, nodeValue1613, nodeValue1615, nodeValue1619, nodeValue1723, nodeValue3279, nodeValue3283, nodeValue3291, nodeValue3350, nodeValue3355, nodeValue3434, nodeValue3466, nodeValue3481, nodeValue3519, nodeValue3523, nodeValue3531, nodeValue3539, nodeValue3540, nodeValue3544, nodeValue3580, nodeValue3625, nodeValue3858]
  ring

noncomputable def reducedSource77 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2712 x + ((1 : ℝ) * Sparse.eval nodeValue3064 x + ((1 : ℝ) * Sparse.eval nodeValue3077 x + ((2 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3902 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow77 : Integer.Sparse Master := [(Sum.inr 2712, 1), (Sum.inr 3064, 1), (Sum.inr 3077, 1), (Sum.inr 3086, 2), (Sum.inr 3902, 1), (Sum.inr 4091, -1)]

theorem reindexCheck77 : Integer.Sparse.reindex keyMap MixedData.row77 = numericRow77 := by decide +kernel

theorem numericCheck77 (x : Master → ℝ) : Integer.Sparse.eval numericRow77 x =
    (1 : ℝ) * reducedSource77 x := by
  norm_num [numericRow77, reducedSource77, Integer.Sparse.eval, Sparse.eval, nodeValue2712, nodeValue3064, nodeValue3077, nodeValue3086, nodeValue3902, nodeValue4091]

noncomputable def reducedSource78 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1206 x + ((1 : ℝ) * Sparse.eval nodeValue1209 x + ((2 : ℝ) * Sparse.eval nodeValue1217 x + ((1 : ℝ) * Sparse.eval nodeValue1249 x + ((1 : ℝ) * Sparse.eval nodeValue2712 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow78 : Integer.Sparse Master := [(Sum.inr 1206, 1), (Sum.inr 1209, 1), (Sum.inr 1217, 2), (Sum.inr 1249, 1), (Sum.inr 2712, 1), (Sum.inr 4091, -1)]

theorem reindexCheck78 : Integer.Sparse.reindex keyMap MixedData.row78 = numericRow78 := by decide +kernel

theorem numericCheck78 (x : Master → ℝ) : Integer.Sparse.eval numericRow78 x =
    (1 : ℝ) * reducedSource78 x := by
  norm_num [numericRow78, reducedSource78, Integer.Sparse.eval, Sparse.eval, nodeValue1206, nodeValue1209, nodeValue1217, nodeValue1249, nodeValue2712, nodeValue4091]

noncomputable def reducedSource79 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1249 x + ((1 : ℝ) * Sparse.eval nodeValue2562 x + ((2 : ℝ) * Sparse.eval nodeValue2624 x + ((1 : ℝ) * Sparse.eval nodeValue2712 x + ((1 : ℝ) * Sparse.eval nodeValue2751 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow79 : Integer.Sparse Master := [(Sum.inr 1249, 1), (Sum.inr 2562, 1), (Sum.inr 2624, 2), (Sum.inr 2712, 1), (Sum.inr 2751, 1), (Sum.inr 4091, -1)]

theorem reindexCheck79 : Integer.Sparse.reindex keyMap MixedData.row79 = numericRow79 := by decide +kernel

theorem numericCheck79 (x : Master → ℝ) : Integer.Sparse.eval numericRow79 x =
    (1 : ℝ) * reducedSource79 x := by
  norm_num [numericRow79, reducedSource79, Integer.Sparse.eval, Sparse.eval, nodeValue1249, nodeValue2562, nodeValue2624, nodeValue2712, nodeValue2751, nodeValue4091]

end MUB6.Certificate.MixedSourceBridge

end OAI
