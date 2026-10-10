import OAI.Analysis.MutuallyUnbiased.MixedData.Source13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1760 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3476 x + ((1 : ℝ) * Sparse.eval nodeValue3478 x + ((1 : ℝ) * Sparse.eval nodeValue3480 x + ((1 : ℝ) * Sparse.eval nodeValue3482 x + ((1 : ℝ) * Sparse.eval nodeValue3522 x + ((1 : ℝ) * Sparse.eval nodeValue3612 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

def numericRow1760 : Integer.Sparse Master := [(Sum.inr 3476, 1), (Sum.inr 3478, 1), (Sum.inr 3480, 1), (Sum.inr 3482, 1), (Sum.inr 3522, 1), (Sum.inr 3612, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1760 : Integer.Sparse.reindex keyMap MixedData.row1760 = numericRow1760 := by decide +kernel

theorem numericCheck1760 (x : Master → ℝ) : Integer.Sparse.eval numericRow1760 x =
    (1 : ℝ) * reducedSource1760 x := by
  norm_num [numericRow1760, reducedSource1760, Integer.Sparse.eval, Sparse.eval, nodeValue3476, nodeValue3478, nodeValue3480, nodeValue3482, nodeValue3522, nodeValue3612, nodeValue4082]

noncomputable def reducedSource1761 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1928 x + ((1 : ℝ) * Sparse.eval nodeValue2674 x + ((1 : ℝ) * Sparse.eval nodeValue3348 x + ((1 : ℝ) * Sparse.eval nodeValue3430 x + ((1 : ℝ) * Sparse.eval nodeValue3478 x + ((1 : ℝ) * Sparse.eval nodeValue3480 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

def numericRow1761 : Integer.Sparse Master := [(Sum.inr 1928, 1), (Sum.inr 2674, 1), (Sum.inr 3348, 1), (Sum.inr 3430, 1), (Sum.inr 3478, 1), (Sum.inr 3480, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1761 : Integer.Sparse.reindex keyMap MixedData.row1761 = numericRow1761 := by decide +kernel

theorem numericCheck1761 (x : Master → ℝ) : Integer.Sparse.eval numericRow1761 x =
    (1 : ℝ) * reducedSource1761 x := by
  norm_num [numericRow1761, reducedSource1761, Integer.Sparse.eval, Sparse.eval, nodeValue1928, nodeValue2674, nodeValue3348, nodeValue3430, nodeValue3478, nodeValue3480, nodeValue4082]

noncomputable def reducedSource1762 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1117 x + ((1 : ℝ) * Sparse.eval nodeValue2324 x + ((1 : ℝ) * Sparse.eval nodeValue2441 x + ((1 : ℝ) * Sparse.eval nodeValue2473 x + ((1 : ℝ) * Sparse.eval nodeValue2480 x + ((1 : ℝ) * Sparse.eval nodeValue2483 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow1762 : Integer.Sparse Master := [(Sum.inr 1117, 1), (Sum.inr 2324, 1), (Sum.inr 2441, 1), (Sum.inr 2473, 1), (Sum.inr 2480, 1), (Sum.inr 2483, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1762 : Integer.Sparse.reindex keyMap MixedData.row1762 = numericRow1762 := by decide +kernel

theorem numericCheck1762 (x : Master → ℝ) : Integer.Sparse.eval numericRow1762 x =
    (1 : ℝ) * reducedSource1762 x := by
  norm_num [numericRow1762, reducedSource1762, Integer.Sparse.eval, Sparse.eval, nodeValue1117, nodeValue2324, nodeValue2441, nodeValue2473, nodeValue2480, nodeValue2483, nodeValue4091]

noncomputable def reducedSource1763 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2320 x + ((1 : ℝ) * Sparse.eval nodeValue2797 x + ((1 : ℝ) * Sparse.eval nodeValue2900 x + ((1 : ℝ) * Sparse.eval nodeValue2931 x + ((1 : ℝ) * Sparse.eval nodeValue2981 x + ((1 : ℝ) * Sparse.eval nodeValue3690 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow1763 : Integer.Sparse Master := [(Sum.inr 2320, 1), (Sum.inr 2797, 1), (Sum.inr 2900, 1), (Sum.inr 2931, 1), (Sum.inr 2981, 1), (Sum.inr 3690, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1763 : Integer.Sparse.reindex keyMap MixedData.row1763 = numericRow1763 := by decide +kernel

theorem numericCheck1763 (x : Master → ℝ) : Integer.Sparse.eval numericRow1763 x =
    (1 : ℝ) * reducedSource1763 x := by
  norm_num [numericRow1763, reducedSource1763, Integer.Sparse.eval, Sparse.eval, nodeValue2320, nodeValue2797, nodeValue2900, nodeValue2931, nodeValue2981, nodeValue3690, nodeValue4091]

noncomputable def reducedSource1764 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1941 x + ((1 : ℝ) * Sparse.eval nodeValue3351 x + ((2 : ℝ) * Sparse.eval nodeValue3476 x + ((2 : ℝ) * Sparse.eval nodeValue3482 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))

def numericRow1764 : Integer.Sparse Master := [(Sum.inr 1941, 1), (Sum.inr 3476, 2), (Sum.inr 3482, 2), (Sum.inr 4082, -1)]

theorem reindexCheck1764 : Integer.Sparse.reindex keyMap MixedData.row1764 = numericRow1764 := by decide +kernel

theorem numericCheck1764 (x : Master → ℝ) : Integer.Sparse.eval numericRow1764 x =
    (1 : ℝ) * reducedSource1764 x := by
  norm_num [numericRow1764, reducedSource1764, Integer.Sparse.eval, Sparse.eval, nodeValue1941, nodeValue3351, nodeValue3476, nodeValue3482, nodeValue4082]

noncomputable def reducedSource1765 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1921 x + ((1 : ℝ) * Sparse.eval nodeValue2668 x + ((1 : ℝ) * Sparse.eval nodeValue3345 x + ((1 : ℝ) * Sparse.eval nodeValue3476 x + ((2 : ℝ) * Sparse.eval nodeValue3478 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

def numericRow1765 : Integer.Sparse Master := [(Sum.inr 1921, 1), (Sum.inr 2668, 1), (Sum.inr 3345, 1), (Sum.inr 3476, 1), (Sum.inr 3478, 2), (Sum.inr 4082, -1)]

theorem reindexCheck1765 : Integer.Sparse.reindex keyMap MixedData.row1765 = numericRow1765 := by decide +kernel

theorem numericCheck1765 (x : Master → ℝ) : Integer.Sparse.eval numericRow1765 x =
    (1 : ℝ) * reducedSource1765 x := by
  norm_num [numericRow1765, reducedSource1765, Integer.Sparse.eval, Sparse.eval, nodeValue1921, nodeValue2668, nodeValue3345, nodeValue3476, nodeValue3478, nodeValue4082]

noncomputable def reducedSource1766 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1807 x + ((1 : ℝ) * Sparse.eval nodeValue2427 x + ((1 : ℝ) * Sparse.eval nodeValue2435 x + ((1 : ℝ) * Sparse.eval nodeValue2522 x + ((1 : ℝ) * Sparse.eval nodeValue2560 x + ((1 : ℝ) * Sparse.eval nodeValue3391 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow1766 : Integer.Sparse Master := [(Sum.inr 1807, 1), (Sum.inr 2427, 1), (Sum.inr 2435, 1), (Sum.inr 2522, 1), (Sum.inr 2560, 1), (Sum.inr 3391, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1766 : Integer.Sparse.reindex keyMap MixedData.row1766 = numericRow1766 := by decide +kernel

theorem numericCheck1766 (x : Master → ℝ) : Integer.Sparse.eval numericRow1766 x =
    (1 : ℝ) * reducedSource1766 x := by
  norm_num [numericRow1766, reducedSource1766, Integer.Sparse.eval, Sparse.eval, nodeValue1807, nodeValue2427, nodeValue2435, nodeValue2522, nodeValue2560, nodeValue3391, nodeValue4084]

noncomputable def reducedSource1767 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1347 x + ((1 : ℝ) * Sparse.eval nodeValue2831 x + ((1 : ℝ) * Sparse.eval nodeValue2902 x + ((1 : ℝ) * Sparse.eval nodeValue2942 x + ((1 : ℝ) * Sparse.eval nodeValue2954 x + ((1 : ℝ) * Sparse.eval nodeValue2964 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow1767 : Integer.Sparse Master := [(Sum.inr 1347, 1), (Sum.inr 2831, 1), (Sum.inr 2902, 1), (Sum.inr 2942, 1), (Sum.inr 2954, 1), (Sum.inr 2964, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1767 : Integer.Sparse.reindex keyMap MixedData.row1767 = numericRow1767 := by decide +kernel

theorem numericCheck1767 (x : Master → ℝ) : Integer.Sparse.eval numericRow1767 x =
    (1 : ℝ) * reducedSource1767 x := by
  norm_num [numericRow1767, reducedSource1767, Integer.Sparse.eval, Sparse.eval, nodeValue1347, nodeValue2831, nodeValue2902, nodeValue2942, nodeValue2954, nodeValue2964, nodeValue4091]

noncomputable def reducedSource1768 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2584 x + ((1 : ℝ) * Sparse.eval nodeValue2668 x + ((1 : ℝ) * Sparse.eval nodeValue2670 x + ((1 : ℝ) * Sparse.eval nodeValue2674 x + ((1 : ℝ) * Sparse.eval nodeValue2681 x + ((1 : ℝ) * Sparse.eval nodeValue3478 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

def numericRow1768 : Integer.Sparse Master := [(Sum.inr 2584, 1), (Sum.inr 2668, 1), (Sum.inr 2670, 1), (Sum.inr 2674, 1), (Sum.inr 2681, 1), (Sum.inr 3478, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1768 : Integer.Sparse.reindex keyMap MixedData.row1768 = numericRow1768 := by decide +kernel

theorem numericCheck1768 (x : Master → ℝ) : Integer.Sparse.eval numericRow1768 x =
    (1 : ℝ) * reducedSource1768 x := by
  norm_num [numericRow1768, reducedSource1768, Integer.Sparse.eval, Sparse.eval, nodeValue2584, nodeValue2668, nodeValue2670, nodeValue2674, nodeValue2681, nodeValue3478, nodeValue4082]

noncomputable def reducedSource1769 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2670 x + ((1 : ℝ) * Sparse.eval nodeValue3478 x + ((1 : ℝ) * Sparse.eval nodeValue3516 x + ((1 : ℝ) * Sparse.eval nodeValue3522 x + ((1 : ℝ) * Sparse.eval nodeValue3538 x + ((1 : ℝ) * Sparse.eval nodeValue3614 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

def numericRow1769 : Integer.Sparse Master := [(Sum.inr 2670, 1), (Sum.inr 3478, 1), (Sum.inr 3516, 1), (Sum.inr 3522, 1), (Sum.inr 3538, 1), (Sum.inr 3614, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1769 : Integer.Sparse.reindex keyMap MixedData.row1769 = numericRow1769 := by decide +kernel

theorem numericCheck1769 (x : Master → ℝ) : Integer.Sparse.eval numericRow1769 x =
    (1 : ℝ) * reducedSource1769 x := by
  norm_num [numericRow1769, reducedSource1769, Integer.Sparse.eval, Sparse.eval, nodeValue2670, nodeValue3478, nodeValue3516, nodeValue3522, nodeValue3538, nodeValue3614, nodeValue4082]

noncomputable def reducedSource1770 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2347 x + ((1 : ℝ) * Sparse.eval nodeValue2423 x + ((1 : ℝ) * Sparse.eval nodeValue2431 x + ((1 : ℝ) * Sparse.eval nodeValue2488 x + ((1 : ℝ) * Sparse.eval nodeValue2545 x + ((1 : ℝ) * Sparse.eval nodeValue3719 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1770 : Integer.Sparse Master := [(Sum.inr 2347, 1), (Sum.inr 2423, 1), (Sum.inr 2431, 1), (Sum.inr 2488, 1), (Sum.inr 2545, 1), (Sum.inr 3719, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1770 : Integer.Sparse.reindex keyMap MixedData.row1770 = numericRow1770 := by decide +kernel

theorem numericCheck1770 (x : Master → ℝ) : Integer.Sparse.eval numericRow1770 x =
    (1 : ℝ) * reducedSource1770 x := by
  norm_num [numericRow1770, reducedSource1770, Integer.Sparse.eval, Sparse.eval, nodeValue2347, nodeValue2423, nodeValue2431, nodeValue2488, nodeValue2545, nodeValue3719, nodeValue4092]

noncomputable def reducedSource1771 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1151 x + ((1 : ℝ) * Sparse.eval nodeValue2350 x + ((1 : ℝ) * Sparse.eval nodeValue2431 x + ((1 : ℝ) * Sparse.eval nodeValue2545 x + ((1 : ℝ) * Sparse.eval nodeValue2553 x + ((1 : ℝ) * Sparse.eval nodeValue2557 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1771 : Integer.Sparse Master := [(Sum.inr 1151, 1), (Sum.inr 2350, 1), (Sum.inr 2431, 1), (Sum.inr 2545, 1), (Sum.inr 2553, 1), (Sum.inr 2557, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1771 : Integer.Sparse.reindex keyMap MixedData.row1771 = numericRow1771 := by decide +kernel

theorem numericCheck1771 (x : Master → ℝ) : Integer.Sparse.eval numericRow1771 x =
    (1 : ℝ) * reducedSource1771 x := by
  norm_num [numericRow1771, reducedSource1771, Integer.Sparse.eval, Sparse.eval, nodeValue1151, nodeValue2350, nodeValue2431, nodeValue2545, nodeValue2553, nodeValue2557, nodeValue4092]

noncomputable def reducedSource1772 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1330 x + ((1 : ℝ) * Sparse.eval nodeValue2824 x + ((1 : ℝ) * Sparse.eval nodeValue2896 x + ((1 : ℝ) * Sparse.eval nodeValue2916 x + ((1 : ℝ) * Sparse.eval nodeValue2924 x + ((1 : ℝ) * Sparse.eval nodeValue2928 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow1772 : Integer.Sparse Master := [(Sum.inr 1330, 1), (Sum.inr 2824, 1), (Sum.inr 2896, 1), (Sum.inr 2916, 1), (Sum.inr 2924, 1), (Sum.inr 2928, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1772 : Integer.Sparse.reindex keyMap MixedData.row1772 = numericRow1772 := by decide +kernel

theorem numericCheck1772 (x : Master → ℝ) : Integer.Sparse.eval numericRow1772 x =
    (1 : ℝ) * reducedSource1772 x := by
  norm_num [numericRow1772, reducedSource1772, Integer.Sparse.eval, Sparse.eval, nodeValue1330, nodeValue2824, nodeValue2896, nodeValue2916, nodeValue2924, nodeValue2928, nodeValue4091]

noncomputable def reducedSource1773 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2349 x + ((1 : ℝ) * Sparse.eval nodeValue2890 x + ((1 : ℝ) * Sparse.eval nodeValue2896 x + ((2 : ℝ) * Sparse.eval nodeValue2916 x + ((1 : ℝ) * Sparse.eval nodeValue3721 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow1773 : Integer.Sparse Master := [(Sum.inr 2349, 1), (Sum.inr 2890, 1), (Sum.inr 2896, 1), (Sum.inr 2916, 2), (Sum.inr 3721, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1773 : Integer.Sparse.reindex keyMap MixedData.row1773 = numericRow1773 := by decide +kernel

theorem numericCheck1773 (x : Master → ℝ) : Integer.Sparse.eval numericRow1773 x =
    (1 : ℝ) * reducedSource1773 x := by
  norm_num [numericRow1773, reducedSource1773, Integer.Sparse.eval, Sparse.eval, nodeValue2349, nodeValue2890, nodeValue2896, nodeValue2916, nodeValue3721, nodeValue4091]

noncomputable def reducedSource1774 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2534 x + ((1 : ℝ) * Sparse.eval nodeValue3430 x + ((1 : ℝ) * Sparse.eval nodeValue3433 x + ((1 : ℝ) * Sparse.eval nodeValue3478 x + ((2 : ℝ) * Sparse.eval nodeValue3516 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

def numericRow1774 : Integer.Sparse Master := [(Sum.inr 2534, 1), (Sum.inr 3430, 1), (Sum.inr 3433, 1), (Sum.inr 3478, 1), (Sum.inr 3516, 2), (Sum.inr 4082, -1)]

theorem reindexCheck1774 : Integer.Sparse.reindex keyMap MixedData.row1774 = numericRow1774 := by decide +kernel

theorem numericCheck1774 (x : Master → ℝ) : Integer.Sparse.eval numericRow1774 x =
    (1 : ℝ) * reducedSource1774 x := by
  norm_num [numericRow1774, reducedSource1774, Integer.Sparse.eval, Sparse.eval, nodeValue2534, nodeValue3430, nodeValue3433, nodeValue3478, nodeValue3516, nodeValue4082]

noncomputable def reducedSource1775 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2422 x + ((1 : ℝ) * Sparse.eval nodeValue2432 x + ((1 : ℝ) * Sparse.eval nodeValue2489 x + ((1 : ℝ) * Sparse.eval nodeValue2546 x + ((1 : ℝ) * Sparse.eval nodeValue3779 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow1775 : Integer.Sparse Master := [(Sum.inr 2422, 2), (Sum.inr 2432, 1), (Sum.inr 2489, 1), (Sum.inr 3779, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1775 : Integer.Sparse.reindex keyMap MixedData.row1775 = numericRow1775 := by decide +kernel

theorem numericCheck1775 (x : Master → ℝ) : Integer.Sparse.eval numericRow1775 x =
    (1 : ℝ) * reducedSource1775 x := by
  norm_num [numericRow1775, reducedSource1775, Integer.Sparse.eval, Sparse.eval, nodeValue2422, nodeValue2432, nodeValue2489, nodeValue2546, nodeValue3779, nodeValue4091]

end MUB6.Certificate.MixedSourceBridge

end OAI
