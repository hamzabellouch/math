import OAI.Analysis.MutuallyUnbiased.MixedData.Source1
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource192 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2513 x + ((1 : ℝ) * Sparse.eval nodeValue2520 x + ((1 : ℝ) * Sparse.eval nodeValue2522 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + ((1 : ℝ) * Sparse.eval nodeValue3626 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow192 : Integer.Sparse Master := [(Sum.inr 2513, 2), (Sum.inr 2520, 1), (Sum.inr 2522, 1), (Sum.inr 2744, 1), (Sum.inr 3626, 1), (Sum.inr 4084, -1)]

theorem reindexCheck192 : Integer.Sparse.reindex keyMap MixedData.row192 = numericRow192 := by decide +kernel

theorem numericCheck192 (x : Master → ℝ) : Integer.Sparse.eval numericRow192 x =
    (1 : ℝ) * reducedSource192 x := by
  norm_num [numericRow192, reducedSource192, Integer.Sparse.eval, Sparse.eval, nodeValue2513, nodeValue2520, nodeValue2522, nodeValue2744, nodeValue3626, nodeValue4084]

noncomputable def reducedSource193 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1238 x + ((1 : ℝ) * Sparse.eval nodeValue2133 x + ((1 : ℝ) * Sparse.eval nodeValue2513 x + ((1 : ℝ) * Sparse.eval nodeValue2555 x + ((1 : ℝ) * Sparse.eval nodeValue2738 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow193 : Integer.Sparse Master := [(Sum.inr 1238, 1), (Sum.inr 2133, 1), (Sum.inr 2513, 1), (Sum.inr 2555, 1), (Sum.inr 2738, 1), (Sum.inr 2744, 1), (Sum.inr 4084, -1)]

theorem reindexCheck193 : Integer.Sparse.reindex keyMap MixedData.row193 = numericRow193 := by decide +kernel

theorem numericCheck193 (x : Master → ℝ) : Integer.Sparse.eval numericRow193 x =
    (1 : ℝ) * reducedSource193 x := by
  norm_num [numericRow193, reducedSource193, Integer.Sparse.eval, Sparse.eval, nodeValue1238, nodeValue2133, nodeValue2513, nodeValue2555, nodeValue2738, nodeValue2744, nodeValue4084]

noncomputable def reducedSource194 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2555 x + ((1 : ℝ) * Sparse.eval nodeValue2559 x + ((1 : ℝ) * Sparse.eval nodeValue2560 x + ((1 : ℝ) * Sparse.eval nodeValue2592 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow194 : Integer.Sparse Master := [(Sum.inr 2555, 1), (Sum.inr 2559, 1), (Sum.inr 2560, 1), (Sum.inr 2592, 1), (Sum.inr 2744, 1), (Sum.inr 3541, 1), (Sum.inr 4084, -1)]

theorem reindexCheck194 : Integer.Sparse.reindex keyMap MixedData.row194 = numericRow194 := by decide +kernel

theorem numericCheck194 (x : Master → ℝ) : Integer.Sparse.eval numericRow194 x =
    (1 : ℝ) * reducedSource194 x := by
  norm_num [numericRow194, reducedSource194, Integer.Sparse.eval, Sparse.eval, nodeValue2555, nodeValue2559, nodeValue2560, nodeValue2592, nodeValue2744, nodeValue3541, nodeValue4084]

noncomputable def reducedSource195 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1245 x + ((1 : ℝ) * Sparse.eval nodeValue2522 x + ((2 : ℝ) * Sparse.eval nodeValue2560 x + ((1 : ℝ) * Sparse.eval nodeValue2740 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow195 : Integer.Sparse Master := [(Sum.inr 1245, 1), (Sum.inr 2522, 1), (Sum.inr 2560, 2), (Sum.inr 2740, 1), (Sum.inr 2744, 1), (Sum.inr 4084, -1)]

theorem reindexCheck195 : Integer.Sparse.reindex keyMap MixedData.row195 = numericRow195 := by decide +kernel

theorem numericCheck195 (x : Master → ℝ) : Integer.Sparse.eval numericRow195 x =
    (1 : ℝ) * reducedSource195 x := by
  norm_num [numericRow195, reducedSource195, Integer.Sparse.eval, Sparse.eval, nodeValue1245, nodeValue2522, nodeValue2560, nodeValue2740, nodeValue2744, nodeValue4084]

noncomputable def reducedSource196 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2133 x + ((1 : ℝ) * Sparse.eval nodeValue2136 x + ((1 : ℝ) * Sparse.eval nodeValue2138 x + ((1 : ℝ) * Sparse.eval nodeValue2279 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow196 : Integer.Sparse Master := [(Sum.inr 2133, 2), (Sum.inr 2136, 1), (Sum.inr 2138, 1), (Sum.inr 2279, 1), (Sum.inr 2744, 1), (Sum.inr 4084, -1)]

theorem reindexCheck196 : Integer.Sparse.reindex keyMap MixedData.row196 = numericRow196 := by decide +kernel

theorem numericCheck196 (x : Master → ℝ) : Integer.Sparse.eval numericRow196 x =
    (1 : ℝ) * reducedSource196 x := by
  norm_num [numericRow196, reducedSource196, Integer.Sparse.eval, Sparse.eval, nodeValue2133, nodeValue2136, nodeValue2138, nodeValue2279, nodeValue2744, nodeValue4084]

noncomputable def reducedSource197 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1244 x + ((1 : ℝ) * Sparse.eval nodeValue2136 x + ((1 : ℝ) * Sparse.eval nodeValue2520 x + ((2 : ℝ) * Sparse.eval nodeValue2559 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow197 : Integer.Sparse Master := [(Sum.inr 1244, 1), (Sum.inr 2136, 1), (Sum.inr 2520, 1), (Sum.inr 2559, 2), (Sum.inr 2744, 1), (Sum.inr 4084, -1)]

theorem reindexCheck197 : Integer.Sparse.reindex keyMap MixedData.row197 = numericRow197 := by decide +kernel

theorem numericCheck197 (x : Master → ℝ) : Integer.Sparse.eval numericRow197 x =
    (1 : ℝ) * reducedSource197 x := by
  norm_num [numericRow197, reducedSource197, Integer.Sparse.eval, Sparse.eval, nodeValue1244, nodeValue2136, nodeValue2520, nodeValue2559, nodeValue2744, nodeValue4084]

noncomputable def reducedSource198 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1006 x + ((1 : ℝ) * Sparse.eval nodeValue1010 x + ((1 : ℝ) * Sparse.eval nodeValue1011 x + ((1 : ℝ) * Sparse.eval nodeValue1084 x + ((2 : ℝ) * Sparse.eval nodeValue2405 x + ((1 : ℝ) * Sparse.eval nodeValue2408 x + ((1 : ℝ) * Sparse.eval nodeValue2409 x + ((2 : ℝ) * Sparse.eval nodeValue2463 x + ((2 : ℝ) * Sparse.eval nodeValue2465 x + ((2 : ℝ) * Sparse.eval nodeValue2466 x + ((2 : ℝ) * Sparse.eval nodeValue2513 x + ((2 : ℝ) * Sparse.eval nodeValue2732 x + ((1 : ℝ) * Sparse.eval nodeValue2734 x + ((2 : ℝ) * Sparse.eval nodeValue2735 x + ((1 : ℝ) * Sparse.eval nodeValue2737 x + ((1 : ℝ) * Sparse.eval nodeValue2776 x + ((1 : ℝ) * Sparse.eval nodeValue2781 x + ((2 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3583 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((1 : ℝ) * Sparse.eval nodeValue3889 x + 0))))))))))))))))))))

def numericRow198 : Integer.Sparse Master := [(Sum.inl 0, -26), (Sum.inl 2, 5), (Sum.inl 3, 160), (Sum.inl 13, 80), (Sum.inl 12, 160), (Sum.inl 1, -85), (Sum.inr 1006, 4320), (Sum.inr 1010, 2160), (Sum.inr 1011, 2160), (Sum.inr 1084, 2160), (Sum.inr 2405, 4320), (Sum.inr 2408, 2160), (Sum.inr 2409, 2160), (Sum.inr 2463, 4320), (Sum.inr 2465, 4320), (Sum.inr 2466, 4320), (Sum.inr 2513, 4320), (Sum.inr 2732, 4320), (Sum.inr 2734, 2160), (Sum.inr 2735, 4320), (Sum.inr 2737, 2160), (Sum.inr 2781, 2160), (Sum.inr 3573, 4320), (Sum.inr 3583, 2160), (Sum.inr 3584, 2160)]

theorem reindexCheck198 : Integer.Sparse.reindex keyMap MixedData.row198 = numericRow198 := by decide +kernel

theorem numericCheck198 (x : Master → ℝ) : Integer.Sparse.eval numericRow198 x =
    (2160 : ℝ) * reducedSource198 x := by
  norm_num [numericRow198, reducedSource198, Integer.Sparse.eval, Sparse.eval, nodeValue1006, nodeValue1010, nodeValue1011, nodeValue1084, nodeValue2405, nodeValue2408, nodeValue2409, nodeValue2463, nodeValue2465, nodeValue2466, nodeValue2513, nodeValue2732, nodeValue2734, nodeValue2735, nodeValue2737, nodeValue2776, nodeValue2781, nodeValue3573, nodeValue3583, nodeValue3584, nodeValue3889]
  ring

noncomputable def reducedSource199 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1184 x + ((1 : ℝ) * Sparse.eval nodeValue1186 x + ((1 : ℝ) * Sparse.eval nodeValue1192 x + ((1 : ℝ) * Sparse.eval nodeValue1292 x + ((2 : ℝ) * Sparse.eval nodeValue1610 x + ((1 : ℝ) * Sparse.eval nodeValue1628 x + ((1 : ℝ) * Sparse.eval nodeValue1716 x + ((2 : ℝ) * Sparse.eval nodeValue2837 x + ((1 : ℝ) * Sparse.eval nodeValue2842 x + ((2 : ℝ) * Sparse.eval nodeValue2906 x + ((2 : ℝ) * Sparse.eval nodeValue2910 x + ((2 : ℝ) * Sparse.eval nodeValue2952 x + ((2 : ℝ) * Sparse.eval nodeValue3024 x + ((2 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((1 : ℝ) * Sparse.eval nodeValue3098 x + ((1 : ℝ) * Sparse.eval nodeValue3119 x + ((2 : ℝ) * Sparse.eval nodeValue3541 x + ((1 : ℝ) * Sparse.eval nodeValue3549 x + ((1 : ℝ) * Sparse.eval nodeValue3626 x + ((1 : ℝ) * Sparse.eval nodeValue3862 x + 0))))))))))))))))))))

def numericRow199 : Integer.Sparse Master := [(Sum.inl 0, -56), (Sum.inl 2, -40), (Sum.inl 3, 320), (Sum.inl 12, 160), (Sum.inl 26, 160), (Sum.inl 4, 160), (Sum.inl 1, -80), (Sum.inr 1184, 8640), (Sum.inr 1186, 4320), (Sum.inr 1192, 4320), (Sum.inr 1292, 4320), (Sum.inr 1610, 8640), (Sum.inr 1628, 4320), (Sum.inr 1716, 4320), (Sum.inr 2837, 8640), (Sum.inr 2842, 4320), (Sum.inr 2906, 8640), (Sum.inr 2910, 8640), (Sum.inr 2952, 8640), (Sum.inr 3024, 8640), (Sum.inr 3051, 8640), (Sum.inr 3055, 4320), (Sum.inr 3098, 4320), (Sum.inr 3541, 8640), (Sum.inr 3549, 4320), (Sum.inr 3626, 4320)]

theorem reindexCheck199 : Integer.Sparse.reindex keyMap MixedData.row199 = numericRow199 := by decide +kernel

theorem numericCheck199 (x : Master → ℝ) : Integer.Sparse.eval numericRow199 x =
    (4320 : ℝ) * reducedSource199 x := by
  norm_num [numericRow199, reducedSource199, Integer.Sparse.eval, Sparse.eval, nodeValue1184, nodeValue1186, nodeValue1192, nodeValue1292, nodeValue1610, nodeValue1628, nodeValue1716, nodeValue2837, nodeValue2842, nodeValue2906, nodeValue2910, nodeValue2952, nodeValue3024, nodeValue3051, nodeValue3055, nodeValue3098, nodeValue3119, nodeValue3541, nodeValue3549, nodeValue3626, nodeValue3862]
  ring

noncomputable def reducedSource200 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2773 x + ((1 : ℝ) * Sparse.eval nodeValue2774 x + ((1 : ℝ) * Sparse.eval nodeValue2777 x + ((1 : ℝ) * Sparse.eval nodeValue2782 x + ((1 : ℝ) * Sparse.eval nodeValue3907 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow200 : Integer.Sparse Master := [(Sum.inr 2773, 2), (Sum.inr 2774, 1), (Sum.inr 2777, 1), (Sum.inr 2782, 1), (Sum.inr 3907, 1), (Sum.inr 4092, -1)]

theorem reindexCheck200 : Integer.Sparse.reindex keyMap MixedData.row200 = numericRow200 := by decide +kernel

theorem numericCheck200 (x : Master → ℝ) : Integer.Sparse.eval numericRow200 x =
    (1 : ℝ) * reducedSource200 x := by
  norm_num [numericRow200, reducedSource200, Integer.Sparse.eval, Sparse.eval, nodeValue2773, nodeValue2774, nodeValue2777, nodeValue2782, nodeValue3907, nodeValue4092]

noncomputable def reducedSource201 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1282 x + ((2 : ℝ) * Sparse.eval nodeValue1422 x + ((1 : ℝ) * Sparse.eval nodeValue1424 x + ((1 : ℝ) * Sparse.eval nodeValue1436 x + ((1 : ℝ) * Sparse.eval nodeValue2777 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow201 : Integer.Sparse Master := [(Sum.inr 1282, 1), (Sum.inr 1422, 2), (Sum.inr 1424, 1), (Sum.inr 1436, 1), (Sum.inr 2777, 1), (Sum.inr 4092, -1)]

theorem reindexCheck201 : Integer.Sparse.reindex keyMap MixedData.row201 = numericRow201 := by decide +kernel

theorem numericCheck201 (x : Master → ℝ) : Integer.Sparse.eval numericRow201 x =
    (1 : ℝ) * reducedSource201 x := by
  norm_num [numericRow201, reducedSource201, Integer.Sparse.eval, Sparse.eval, nodeValue1282, nodeValue1422, nodeValue1424, nodeValue1436, nodeValue2777, nodeValue4092]

noncomputable def reducedSource202 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1436 x + ((2 : ℝ) * Sparse.eval nodeValue2759 x + ((1 : ℝ) * Sparse.eval nodeValue2769 x + ((1 : ℝ) * Sparse.eval nodeValue2777 x + ((1 : ℝ) * Sparse.eval nodeValue3054 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow202 : Integer.Sparse Master := [(Sum.inr 1436, 1), (Sum.inr 2759, 2), (Sum.inr 2769, 1), (Sum.inr 2777, 1), (Sum.inr 3054, 1), (Sum.inr 4092, -1)]

theorem reindexCheck202 : Integer.Sparse.reindex keyMap MixedData.row202 = numericRow202 := by decide +kernel

theorem numericCheck202 (x : Master → ℝ) : Integer.Sparse.eval numericRow202 x =
    (1 : ℝ) * reducedSource202 x := by
  norm_num [numericRow202, reducedSource202, Integer.Sparse.eval, Sparse.eval, nodeValue1436, nodeValue2759, nodeValue2769, nodeValue2777, nodeValue3054, nodeValue4092]

noncomputable def reducedSource203 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1283 x + ((2 : ℝ) * Sparse.eval nodeValue2582 x + ((1 : ℝ) * Sparse.eval nodeValue2651 x + ((1 : ℝ) * Sparse.eval nodeValue2774 x + ((1 : ℝ) * Sparse.eval nodeValue2777 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow203 : Integer.Sparse Master := [(Sum.inr 1283, 1), (Sum.inr 2582, 2), (Sum.inr 2651, 1), (Sum.inr 2774, 1), (Sum.inr 2777, 1), (Sum.inr 4092, -1)]

theorem reindexCheck203 : Integer.Sparse.reindex keyMap MixedData.row203 = numericRow203 := by decide +kernel

theorem numericCheck203 (x : Master → ℝ) : Integer.Sparse.eval numericRow203 x =
    (1 : ℝ) * reducedSource203 x := by
  norm_num [numericRow203, reducedSource203, Integer.Sparse.eval, Sparse.eval, nodeValue1283, nodeValue2582, nodeValue2651, nodeValue2774, nodeValue2777, nodeValue4092]

noncomputable def reducedSource204 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1422 x + ((1 : ℝ) * Sparse.eval nodeValue2580 x + ((1 : ℝ) * Sparse.eval nodeValue2582 x + ((1 : ℝ) * Sparse.eval nodeValue2600 x + ((1 : ℝ) * Sparse.eval nodeValue2777 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow204 : Integer.Sparse Master := [(Sum.inr 1422, 1), (Sum.inr 2580, 1), (Sum.inr 2582, 1), (Sum.inr 2600, 1), (Sum.inr 2777, 1), (Sum.inr 3038, 1), (Sum.inr 4092, -1)]

theorem reindexCheck204 : Integer.Sparse.reindex keyMap MixedData.row204 = numericRow204 := by decide +kernel

theorem numericCheck204 (x : Master → ℝ) : Integer.Sparse.eval numericRow204 x =
    (1 : ℝ) * reducedSource204 x := by
  norm_num [numericRow204, reducedSource204, Integer.Sparse.eval, Sparse.eval, nodeValue1422, nodeValue2580, nodeValue2582, nodeValue2600, nodeValue2777, nodeValue3038, nodeValue4092]

noncomputable def reducedSource205 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1280 x + ((1 : ℝ) * Sparse.eval nodeValue2580 x + ((1 : ℝ) * Sparse.eval nodeValue2647 x + ((1 : ℝ) * Sparse.eval nodeValue2759 x + ((1 : ℝ) * Sparse.eval nodeValue2773 x + ((1 : ℝ) * Sparse.eval nodeValue2777 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow205 : Integer.Sparse Master := [(Sum.inr 1280, 1), (Sum.inr 2580, 1), (Sum.inr 2647, 1), (Sum.inr 2759, 1), (Sum.inr 2773, 1), (Sum.inr 2777, 1), (Sum.inr 4092, -1)]

theorem reindexCheck205 : Integer.Sparse.reindex keyMap MixedData.row205 = numericRow205 := by decide +kernel

theorem numericCheck205 (x : Master → ℝ) : Integer.Sparse.eval numericRow205 x =
    (1 : ℝ) * reducedSource205 x := by
  norm_num [numericRow205, reducedSource205, Integer.Sparse.eval, Sparse.eval, nodeValue1280, nodeValue2580, nodeValue2647, nodeValue2759, nodeValue2773, nodeValue2777, nodeValue4092]

noncomputable def reducedSource206 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1280 x + ((1 : ℝ) * Sparse.eval nodeValue1282 x + ((1 : ℝ) * Sparse.eval nodeValue1283 x + ((1 : ℝ) * Sparse.eval nodeValue1306 x + ((1 : ℝ) * Sparse.eval nodeValue2777 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow206 : Integer.Sparse Master := [(Sum.inr 1280, 2), (Sum.inr 1282, 1), (Sum.inr 1283, 1), (Sum.inr 1306, 1), (Sum.inr 2777, 1), (Sum.inr 4092, -1)]

theorem reindexCheck206 : Integer.Sparse.reindex keyMap MixedData.row206 = numericRow206 := by decide +kernel

theorem numericCheck206 (x : Master → ℝ) : Integer.Sparse.eval numericRow206 x =
    (1 : ℝ) * reducedSource206 x := by
  norm_num [numericRow206, reducedSource206, Integer.Sparse.eval, Sparse.eval, nodeValue1280, nodeValue1282, nodeValue1283, nodeValue1306, nodeValue2777, nodeValue4092]

noncomputable def reducedSource207 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1060 x + ((1 : ℝ) * Sparse.eval nodeValue1061 x + ((1 : ℝ) * Sparse.eval nodeValue1062 x + ((1 : ℝ) * Sparse.eval nodeValue1088 x + ((2 : ℝ) * Sparse.eval nodeValue2496 x + ((2 : ℝ) * Sparse.eval nodeValue2497 x + ((2 : ℝ) * Sparse.eval nodeValue2498 x + ((2 : ℝ) * Sparse.eval nodeValue2516 x + ((2 : ℝ) * Sparse.eval nodeValue2641 x + ((1 : ℝ) * Sparse.eval nodeValue2642 x + ((1 : ℝ) * Sparse.eval nodeValue2643 x + ((2 : ℝ) * Sparse.eval nodeValue2748 x + ((1 : ℝ) * Sparse.eval nodeValue2761 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((1 : ℝ) * Sparse.eval nodeValue2771 x + ((2 : ℝ) * Sparse.eval nodeValue2777 x + ((1 : ℝ) * Sparse.eval nodeValue2778 x + ((1 : ℝ) * Sparse.eval nodeValue2789 x + ((2 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3110 x + ((1 : ℝ) * Sparse.eval nodeValue3121 x + 0))))))))))))))))))))

def numericRow207 : Integer.Sparse Master := [(Sum.inl 0, -244), (Sum.inl 6, -20), (Sum.inl 2, 120), (Sum.inl 3, -640), (Sum.inl 13, -640), (Sum.inl 52, 320), (Sum.inr 1060, 17280), (Sum.inr 1061, 8640), (Sum.inr 1062, 8640), (Sum.inr 1088, 8640), (Sum.inr 2496, 17280), (Sum.inr 2497, 17280), (Sum.inr 2498, 17280), (Sum.inr 2516, 17280), (Sum.inr 2641, 17280), (Sum.inr 2643, 8640), (Sum.inr 2748, 17280), (Sum.inr 2761, 8640), (Sum.inr 2765, 8640), (Sum.inr 2771, 8640), (Sum.inr 2777, 17280), (Sum.inr 2789, 8640), (Sum.inr 3086, 17280)]

theorem reindexCheck207 : Integer.Sparse.reindex keyMap MixedData.row207 = numericRow207 := by decide +kernel

theorem numericCheck207 (x : Master → ℝ) : Integer.Sparse.eval numericRow207 x =
    (8640 : ℝ) * reducedSource207 x := by
  norm_num [numericRow207, reducedSource207, Integer.Sparse.eval, Sparse.eval, nodeValue1060, nodeValue1061, nodeValue1062, nodeValue1088, nodeValue2496, nodeValue2497, nodeValue2498, nodeValue2516, nodeValue2641, nodeValue2642, nodeValue2643, nodeValue2748, nodeValue2761, nodeValue2765, nodeValue2771, nodeValue2777, nodeValue2778, nodeValue2789, nodeValue3086, nodeValue3110, nodeValue3121]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
