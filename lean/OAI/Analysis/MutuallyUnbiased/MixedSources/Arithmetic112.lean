import OAI.Analysis.MutuallyUnbiased.MixedData.Source14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values36
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values85
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1792 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1171 x + ((1 : ℝ) * Sparse.eval nodeValue2362 x + ((1 : ℝ) * Sparse.eval nodeValue2529 x + ((1 : ℝ) * Sparse.eval nodeValue2575 x + ((1 : ℝ) * Sparse.eval nodeValue2590 x + ((1 : ℝ) * Sparse.eval nodeValue2600 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1792 : Integer.Sparse Master := [(Sum.inr 1171, 1), (Sum.inr 2362, 1), (Sum.inr 2529, 1), (Sum.inr 2575, 1), (Sum.inr 2590, 1), (Sum.inr 2600, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1792 : Integer.Sparse.reindex keyMap MixedData.row1792 = numericRow1792 := by decide +kernel

theorem numericCheck1792 (x : Master → ℝ) : Integer.Sparse.eval numericRow1792 x =
    (1 : ℝ) * reducedSource1792 x := by
  norm_num [numericRow1792, reducedSource1792, Integer.Sparse.eval, Sparse.eval, nodeValue1171, nodeValue2362, nodeValue2529, nodeValue2575, nodeValue2590, nodeValue2600, nodeValue4092]

noncomputable def reducedSource1793 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1812 x + ((1 : ℝ) * Sparse.eval nodeValue2892 x + ((1 : ℝ) * Sparse.eval nodeValue2899 x + ((2 : ℝ) * Sparse.eval nodeValue2930 x + ((1 : ℝ) * Sparse.eval nodeValue3394 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow1793 : Integer.Sparse Master := [(Sum.inr 1812, 1), (Sum.inr 2892, 1), (Sum.inr 2899, 1), (Sum.inr 2930, 2), (Sum.inr 3394, 1), (Sum.inr 4083, -1)]

theorem reindexCheck1793 : Integer.Sparse.reindex keyMap MixedData.row1793 = numericRow1793 := by decide +kernel

theorem numericCheck1793 (x : Master → ℝ) : Integer.Sparse.eval numericRow1793 x =
    (1 : ℝ) * reducedSource1793 x := by
  norm_num [numericRow1793, reducedSource1793, Integer.Sparse.eval, Sparse.eval, nodeValue1812, nodeValue2892, nodeValue2899, nodeValue2930, nodeValue3394, nodeValue4083]

noncomputable def reducedSource1794 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2396 x + ((1 : ℝ) * Sparse.eval nodeValue2399 x + ((1 : ℝ) * Sparse.eval nodeValue2401 x + ((1 : ℝ) * Sparse.eval nodeValue2405 x + ((1 : ℝ) * Sparse.eval nodeValue2681 x + ((1 : ℝ) * Sparse.eval nodeValue3612 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

def numericRow1794 : Integer.Sparse Master := [(Sum.inr 2396, 1), (Sum.inr 2399, 1), (Sum.inr 2401, 1), (Sum.inr 2405, 1), (Sum.inr 2681, 1), (Sum.inr 3612, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1794 : Integer.Sparse.reindex keyMap MixedData.row1794 = numericRow1794 := by decide +kernel

theorem numericCheck1794 (x : Master → ℝ) : Integer.Sparse.eval numericRow1794 x =
    (1 : ℝ) * reducedSource1794 x := by
  norm_num [numericRow1794, reducedSource1794, Integer.Sparse.eval, Sparse.eval, nodeValue2396, nodeValue2399, nodeValue2401, nodeValue2405, nodeValue2681, nodeValue3612, nodeValue4082]

noncomputable def reducedSource1795 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4332 x + ((1 : ℝ) * Sparse.eval nodeValue4334 x + ((1 : ℝ) * Sparse.eval nodeValue4335 x + ((1 : ℝ) * Sparse.eval nodeValue4357 x + ((1 : ℝ) * Sparse.eval nodeValue4444 x + ((1 : ℝ) * Sparse.eval nodeValue4930 x + ((1 : ℝ) * Sparse.eval nodeValue4933 x + ((1 : ℝ) * Sparse.eval nodeValue4934 x + ((1 : ℝ) * Sparse.eval nodeValue4935 x + ((1 : ℝ) * Sparse.eval nodeValue4948 x + ((1 : ℝ) * Sparse.eval nodeValue4951 x + ((1 : ℝ) * Sparse.eval nodeValue4954 x + ((1 : ℝ) * Sparse.eval nodeValue4970 x + ((1 : ℝ) * Sparse.eval nodeValue5040 x + ((1 : ℝ) * Sparse.eval nodeValue5067 x + ((1 : ℝ) * Sparse.eval nodeValue5078 x + ((1 : ℝ) * Sparse.eval nodeValue5117 x + ((1 : ℝ) * Sparse.eval nodeValue5145 x + ((1 : ℝ) * Sparse.eval nodeValue5147 x + ((1 : ℝ) * Sparse.eval nodeValue5149 x + ((1 : ℝ) * Sparse.eval nodeValue5152 x + ((1 : ℝ) * Sparse.eval nodeValue5164 x + ((1 : ℝ) * Sparse.eval nodeValue5170 x + ((1 : ℝ) * Sparse.eval nodeValue5282 x + ((1 : ℝ) * Sparse.eval nodeValue5284 x + ((1 : ℝ) * Sparse.eval nodeValue5352 x + ((1 : ℝ) * Sparse.eval nodeValue5356 x + ((1 : ℝ) * Sparse.eval nodeValue5369 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + 0)))))))))))))))))))))))))))))

def numericRow1795 : Integer.Sparse Master := [(Sum.inr 2339, -1), (Sum.inr 2485, -1), (Sum.inr 2815, -1), (Sum.inr 2893, -1), (Sum.inr 2924, -1), (Sum.inr 2931, -1), (Sum.inr 2954, -1), (Sum.inr 3077, -1), (Sum.inr 3420, -1), (Sum.inr 3481, -1), (Sum.inr 3588, -1), (Sum.inr 3599, -1), (Sum.inr 3605, -1), (Sum.inr 3606, -1), (Sum.inr 3612, -1), (Sum.inr 3625, -1), (Sum.inr 3690, -1), (Sum.inr 3694, -1), (Sum.inr 3764, -1), (Sum.inr 3773, -1), (Sum.inr 3958, -1), (Sum.inr 3961, -1), (Sum.inr 4332, 4), (Sum.inr 4334, 4), (Sum.inr 4335, 4), (Sum.inr 4357, 4), (Sum.inr 4444, 4), (Sum.inr 4930, 4), (Sum.inr 4933, 4), (Sum.inr 4934, 4), (Sum.inr 4935, 4), (Sum.inr 4951, 4), (Sum.inr 4954, 4), (Sum.inr 5040, 4), (Sum.inr 5067, 4), (Sum.inr 5145, 4), (Sum.inr 5147, 4), (Sum.inr 5164, 4), (Sum.inr 5282, 4)]

theorem reindexCheck1795 : Integer.Sparse.reindex keyMap MixedData.row1795 = numericRow1795 := by decide +kernel

theorem numericCheck1795 (x : Master → ℝ) : Integer.Sparse.eval numericRow1795 x =
    (4 : ℝ) * reducedSource1795 x := by
  norm_num [numericRow1795, reducedSource1795, Integer.Sparse.eval, Sparse.eval, nodeValue4332, nodeValue4334, nodeValue4335, nodeValue4357, nodeValue4444, nodeValue4930, nodeValue4933, nodeValue4934, nodeValue4935, nodeValue4948, nodeValue4951, nodeValue4954, nodeValue4970, nodeValue5040, nodeValue5067, nodeValue5078, nodeValue5117, nodeValue5145, nodeValue5147, nodeValue5149, nodeValue5152, nodeValue5164, nodeValue5170, nodeValue5282, nodeValue5284, nodeValue5352, nodeValue5356, nodeValue5369, nodeValue5410, nodeValue5473]
  ring

noncomputable def reducedSource1796 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue910 x + ((1 : ℝ) * Sparse.eval nodeValue912 x + ((1 : ℝ) * Sparse.eval nodeValue913 x + ((1 : ℝ) * Sparse.eval nodeValue935 x + ((1 : ℝ) * Sparse.eval nodeValue1026 x + ((1 : ℝ) * Sparse.eval nodeValue2324 x + ((1 : ℝ) * Sparse.eval nodeValue2325 x + ((1 : ℝ) * Sparse.eval nodeValue2326 x + ((1 : ℝ) * Sparse.eval nodeValue2343 x + ((1 : ℝ) * Sparse.eval nodeValue2347 x + ((1 : ℝ) * Sparse.eval nodeValue2357 x + ((1 : ℝ) * Sparse.eval nodeValue2422 x + ((1 : ℝ) * Sparse.eval nodeValue2433 x + ((1 : ℝ) * Sparse.eval nodeValue2473 x + ((1 : ℝ) * Sparse.eval nodeValue2530 x + ((1 : ℝ) * Sparse.eval nodeValue2531 x + ((1 : ℝ) * Sparse.eval nodeValue2567 x + ((1 : ℝ) * Sparse.eval nodeValue2569 x + ((1 : ℝ) * Sparse.eval nodeValue2570 x + ((1 : ℝ) * Sparse.eval nodeValue2572 x + ((1 : ℝ) * Sparse.eval nodeValue2576 x + ((1 : ℝ) * Sparse.eval nodeValue2591 x + ((1 : ℝ) * Sparse.eval nodeValue2596 x + ((1 : ℝ) * Sparse.eval nodeValue2751 x + ((1 : ℝ) * Sparse.eval nodeValue2753 x + ((1 : ℝ) * Sparse.eval nodeValue3926 x + ((1 : ℝ) * Sparse.eval nodeValue3936 x + ((1 : ℝ) * Sparse.eval nodeValue3940 x + ((1 : ℝ) * Sparse.eval nodeValue3995 x + ((1 : ℝ) * Sparse.eval nodeValue3996 x + 0)))))))))))))))))))))))))))))

def numericRow1796 : Integer.Sparse Master := [(Sum.inl 0, -308), (Sum.inl 5, -240), (Sum.inl 2, 400), (Sum.inl 7, 320), (Sum.inl 8, 320), (Sum.inl 51, -960), (Sum.inl 3, 320), (Sum.inl 1, -620), (Sum.inr 910, 5760), (Sum.inr 912, 5760), (Sum.inr 913, 5760), (Sum.inr 935, 5760), (Sum.inr 1026, 5760), (Sum.inr 2324, 5760), (Sum.inr 2325, 5760), (Sum.inr 2326, 5760), (Sum.inr 2343, 5760), (Sum.inr 2347, 5760), (Sum.inr 2422, 5760), (Sum.inr 2433, 5760), (Sum.inr 2473, 5760), (Sum.inr 2567, 5760), (Sum.inr 2569, 5760), (Sum.inr 2591, 5760), (Sum.inr 2751, 5760)]

theorem reindexCheck1796 : Integer.Sparse.reindex keyMap MixedData.row1796 = numericRow1796 := by decide +kernel

theorem numericCheck1796 (x : Master → ℝ) : Integer.Sparse.eval numericRow1796 x =
    (5760 : ℝ) * reducedSource1796 x := by
  norm_num [numericRow1796, reducedSource1796, Integer.Sparse.eval, Sparse.eval, nodeValue910, nodeValue912, nodeValue913, nodeValue935, nodeValue1026, nodeValue2324, nodeValue2325, nodeValue2326, nodeValue2343, nodeValue2347, nodeValue2357, nodeValue2422, nodeValue2433, nodeValue2473, nodeValue2530, nodeValue2531, nodeValue2567, nodeValue2569, nodeValue2570, nodeValue2572, nodeValue2576, nodeValue2591, nodeValue2596, nodeValue2751, nodeValue2753, nodeValue3926, nodeValue3936, nodeValue3940, nodeValue3995, nodeValue3996]
  ring

noncomputable def reducedSource1797 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1678 x + ((1 : ℝ) * Sparse.eval nodeValue1679 x + ((1 : ℝ) * Sparse.eval nodeValue1682 x + ((1 : ℝ) * Sparse.eval nodeValue1689 x + ((1 : ℝ) * Sparse.eval nodeValue1736 x + ((1 : ℝ) * Sparse.eval nodeValue3408 x + ((1 : ℝ) * Sparse.eval nodeValue3414 x + ((1 : ℝ) * Sparse.eval nodeValue3415 x + ((1 : ℝ) * Sparse.eval nodeValue3418 x + ((1 : ℝ) * Sparse.eval nodeValue3419 x + ((1 : ℝ) * Sparse.eval nodeValue3420 x + ((1 : ℝ) * Sparse.eval nodeValue3452 x + ((1 : ℝ) * Sparse.eval nodeValue3454 x + ((1 : ℝ) * Sparse.eval nodeValue3476 x + ((1 : ℝ) * Sparse.eval nodeValue3481 x + ((1 : ℝ) * Sparse.eval nodeValue3530 x + ((1 : ℝ) * Sparse.eval nodeValue3562 x + ((1 : ℝ) * Sparse.eval nodeValue3565 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((1 : ℝ) * Sparse.eval nodeValue3588 x + ((1 : ℝ) * Sparse.eval nodeValue3599 x + ((1 : ℝ) * Sparse.eval nodeValue3605 x + ((1 : ℝ) * Sparse.eval nodeValue3606 x + ((1 : ℝ) * Sparse.eval nodeValue3612 x + ((1 : ℝ) * Sparse.eval nodeValue3625 x + ((1 : ℝ) * Sparse.eval nodeValue3764 x + ((1 : ℝ) * Sparse.eval nodeValue3773 x + ((1 : ℝ) * Sparse.eval nodeValue3774 x + ((1 : ℝ) * Sparse.eval nodeValue3816 x + ((1 : ℝ) * Sparse.eval nodeValue3961 x + 0)))))))))))))))))))))))))))))

def numericRow1797 : Integer.Sparse Master := [(Sum.inr 1678, 1), (Sum.inr 1679, 1), (Sum.inr 1682, 1), (Sum.inr 1689, 1), (Sum.inr 1736, 1), (Sum.inr 3408, 1), (Sum.inr 3414, 1), (Sum.inr 3415, 1), (Sum.inr 3418, 1), (Sum.inr 3419, 1), (Sum.inr 3420, 1), (Sum.inr 3452, 1), (Sum.inr 3454, 1), (Sum.inr 3476, 1), (Sum.inr 3481, 1), (Sum.inr 3530, 1), (Sum.inr 3562, 1), (Sum.inr 3565, 1), (Sum.inr 3580, 1), (Sum.inr 3588, 1), (Sum.inr 3599, 1), (Sum.inr 3605, 1), (Sum.inr 3606, 1), (Sum.inr 3612, 1), (Sum.inr 3625, 1), (Sum.inr 3764, 1), (Sum.inr 3773, 1), (Sum.inr 3961, 1)]

theorem reindexCheck1797 : Integer.Sparse.reindex keyMap MixedData.row1797 = numericRow1797 := by decide +kernel

theorem numericCheck1797 (x : Master → ℝ) : Integer.Sparse.eval numericRow1797 x =
    (1 : ℝ) * reducedSource1797 x := by
  norm_num [numericRow1797, reducedSource1797, Integer.Sparse.eval, Sparse.eval, nodeValue1678, nodeValue1679, nodeValue1682, nodeValue1689, nodeValue1736, nodeValue3408, nodeValue3414, nodeValue3415, nodeValue3418, nodeValue3419, nodeValue3420, nodeValue3452, nodeValue3454, nodeValue3476, nodeValue3481, nodeValue3530, nodeValue3562, nodeValue3565, nodeValue3580, nodeValue3588, nodeValue3599, nodeValue3605, nodeValue3606, nodeValue3612, nodeValue3625, nodeValue3764, nodeValue3773, nodeValue3774, nodeValue3816, nodeValue3961]

noncomputable def reducedSource1798 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2326 x + ((1 : ℝ) * Sparse.eval nodeValue2802 x + ((1 : ℝ) * Sparse.eval nodeValue2822 x + ((1 : ℝ) * Sparse.eval nodeValue2827 x + ((1 : ℝ) * Sparse.eval nodeValue2931 x + ((1 : ℝ) * Sparse.eval nodeValue3694 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow1798 : Integer.Sparse Master := [(Sum.inr 2326, 1), (Sum.inr 2802, 1), (Sum.inr 2822, 1), (Sum.inr 2827, 1), (Sum.inr 2931, 1), (Sum.inr 3694, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1798 : Integer.Sparse.reindex keyMap MixedData.row1798 = numericRow1798 := by decide +kernel

theorem numericCheck1798 (x : Master → ℝ) : Integer.Sparse.eval numericRow1798 x =
    (1 : ℝ) * reducedSource1798 x := by
  norm_num [numericRow1798, reducedSource1798, Integer.Sparse.eval, Sparse.eval, nodeValue2326, nodeValue2802, nodeValue2822, nodeValue2827, nodeValue2931, nodeValue3694, nodeValue4091]

noncomputable def reducedSource1799 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1328 x + ((1 : ℝ) * Sparse.eval nodeValue2822 x + ((1 : ℝ) * Sparse.eval nodeValue2893 x + ((1 : ℝ) * Sparse.eval nodeValue2924 x + ((1 : ℝ) * Sparse.eval nodeValue2925 x + ((1 : ℝ) * Sparse.eval nodeValue2931 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow1799 : Integer.Sparse Master := [(Sum.inr 1328, 1), (Sum.inr 2822, 1), (Sum.inr 2893, 1), (Sum.inr 2924, 1), (Sum.inr 2925, 1), (Sum.inr 2931, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1799 : Integer.Sparse.reindex keyMap MixedData.row1799 = numericRow1799 := by decide +kernel

theorem numericCheck1799 (x : Master → ℝ) : Integer.Sparse.eval numericRow1799 x =
    (1 : ℝ) * reducedSource1799 x := by
  norm_num [numericRow1799, reducedSource1799, Integer.Sparse.eval, Sparse.eval, nodeValue1328, nodeValue2822, nodeValue2893, nodeValue2924, nodeValue2925, nodeValue2931, nodeValue4091]

noncomputable def reducedSource1800 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1338 x + ((1 : ℝ) * Sparse.eval nodeValue2827 x + ((1 : ℝ) * Sparse.eval nodeValue2900 x + ((1 : ℝ) * Sparse.eval nodeValue2931 x + ((1 : ℝ) * Sparse.eval nodeValue2954 x + ((1 : ℝ) * Sparse.eval nodeValue2955 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow1800 : Integer.Sparse Master := [(Sum.inr 1338, 1), (Sum.inr 2827, 1), (Sum.inr 2900, 1), (Sum.inr 2931, 1), (Sum.inr 2954, 1), (Sum.inr 2955, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1800 : Integer.Sparse.reindex keyMap MixedData.row1800 = numericRow1800 := by decide +kernel

theorem numericCheck1800 (x : Master → ℝ) : Integer.Sparse.eval numericRow1800 x =
    (1 : ℝ) * reducedSource1800 x := by
  norm_num [numericRow1800, reducedSource1800, Integer.Sparse.eval, Sparse.eval, nodeValue1338, nodeValue2827, nodeValue2900, nodeValue2931, nodeValue2954, nodeValue2955, nodeValue4091]

noncomputable def reducedSource1801 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2399 x + ((1 : ℝ) * Sparse.eval nodeValue3433 x + ((1 : ℝ) * Sparse.eval nodeValue3439 x + ((1 : ℝ) * Sparse.eval nodeValue3485 x + ((1 : ℝ) * Sparse.eval nodeValue3522 x + ((1 : ℝ) * Sparse.eval nodeValue3612 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

def numericRow1801 : Integer.Sparse Master := [(Sum.inr 2399, 1), (Sum.inr 3433, 1), (Sum.inr 3522, 1), (Sum.inr 3612, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1801 : Integer.Sparse.reindex keyMap MixedData.row1801 = numericRow1801 := by decide +kernel

theorem numericCheck1801 (x : Master → ℝ) : Integer.Sparse.eval numericRow1801 x =
    (1 : ℝ) * reducedSource1801 x := by
  norm_num [numericRow1801, reducedSource1801, Integer.Sparse.eval, Sparse.eval, nodeValue2399, nodeValue3433, nodeValue3439, nodeValue3485, nodeValue3522, nodeValue3612, nodeValue4082]

noncomputable def reducedSource1802 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2910 x + ((1 : ℝ) * Sparse.eval nodeValue3346 x + ((1 : ℝ) * Sparse.eval nodeValue3349 x + ((1 : ℝ) * Sparse.eval nodeValue3357 x + ((1 : ℝ) * Sparse.eval nodeValue3479 x + ((1 : ℝ) * Sparse.eval nodeValue3570 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0))))))

def numericRow1802 : Integer.Sparse Master := [(Sum.inr 2910, 1), (Sum.inr 3346, 1), (Sum.inr 3349, 1), (Sum.inr 3357, 1), (Sum.inr 3479, 1), (Sum.inr 3570, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1802 : Integer.Sparse.reindex keyMap MixedData.row1802 = numericRow1802 := by decide +kernel

theorem numericCheck1802 (x : Master → ℝ) : Integer.Sparse.eval numericRow1802 x =
    (1 : ℝ) * reducedSource1802 x := by
  norm_num [numericRow1802, reducedSource1802, Integer.Sparse.eval, Sparse.eval, nodeValue2910, nodeValue3346, nodeValue3349, nodeValue3357, nodeValue3479, nodeValue3570, nodeValue4080]

noncomputable def reducedSource1803 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2355 x + ((1 : ℝ) * Sparse.eval nodeValue2438 x + ((1 : ℝ) * Sparse.eval nodeValue2443 x + ((1 : ℝ) * Sparse.eval nodeValue2488 x + ((1 : ℝ) * Sparse.eval nodeValue2620 x + ((1 : ℝ) * Sparse.eval nodeValue3732 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1803 : Integer.Sparse Master := [(Sum.inr 2355, 1), (Sum.inr 2438, 1), (Sum.inr 2443, 1), (Sum.inr 2488, 1), (Sum.inr 2620, 1), (Sum.inr 3732, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1803 : Integer.Sparse.reindex keyMap MixedData.row1803 = numericRow1803 := by decide +kernel

theorem numericCheck1803 (x : Master → ℝ) : Integer.Sparse.eval numericRow1803 x =
    (1 : ℝ) * reducedSource1803 x := by
  norm_num [numericRow1803, reducedSource1803, Integer.Sparse.eval, Sparse.eval, nodeValue2355, nodeValue2438, nodeValue2443, nodeValue2488, nodeValue2620, nodeValue3732, nodeValue4092]

noncomputable def reducedSource1804 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2352 x + ((1 : ℝ) * Sparse.eval nodeValue2798 x + ((1 : ℝ) * Sparse.eval nodeValue2803 x + ((1 : ℝ) * Sparse.eval nodeValue2817 x + ((1 : ℝ) * Sparse.eval nodeValue2867 x + ((1 : ℝ) * Sparse.eval nodeValue3693 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1804 : Integer.Sparse Master := [(Sum.inr 2352, 1), (Sum.inr 2798, 1), (Sum.inr 2803, 1), (Sum.inr 2817, 1), (Sum.inr 2867, 1), (Sum.inr 3693, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1804 : Integer.Sparse.reindex keyMap MixedData.row1804 = numericRow1804 := by decide +kernel

theorem numericCheck1804 (x : Master → ℝ) : Integer.Sparse.eval numericRow1804 x =
    (1 : ℝ) * reducedSource1804 x := by
  norm_num [numericRow1804, reducedSource1804, Integer.Sparse.eval, Sparse.eval, nodeValue2352, nodeValue2798, nodeValue2803, nodeValue2817, nodeValue2867, nodeValue3693, nodeValue4092]

noncomputable def reducedSource1805 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1321 x + ((1 : ℝ) * Sparse.eval nodeValue2817 x + ((1 : ℝ) * Sparse.eval nodeValue2848 x + ((1 : ℝ) * Sparse.eval nodeValue2867 x + ((1 : ℝ) * Sparse.eval nodeValue2881 x + ((1 : ℝ) * Sparse.eval nodeValue2885 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1805 : Integer.Sparse Master := [(Sum.inr 1321, 1), (Sum.inr 2817, 1), (Sum.inr 2848, 1), (Sum.inr 2867, 1), (Sum.inr 2881, 1), (Sum.inr 2885, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1805 : Integer.Sparse.reindex keyMap MixedData.row1805 = numericRow1805 := by decide +kernel

theorem numericCheck1805 (x : Master → ℝ) : Integer.Sparse.eval numericRow1805 x =
    (1 : ℝ) * reducedSource1805 x := by
  norm_num [numericRow1805, reducedSource1805, Integer.Sparse.eval, Sparse.eval, nodeValue1321, nodeValue2817, nodeValue2848, nodeValue2867, nodeValue2881, nodeValue2885, nodeValue4092]

noncomputable def reducedSource1806 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2538 x + ((1 : ℝ) * Sparse.eval nodeValue3345 x + ((1 : ℝ) * Sparse.eval nodeValue3348 x + ((1 : ℝ) * Sparse.eval nodeValue3354 x + ((1 : ℝ) * Sparse.eval nodeValue3478 x + ((1 : ℝ) * Sparse.eval nodeValue3538 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

def numericRow1806 : Integer.Sparse Master := [(Sum.inr 2538, 1), (Sum.inr 3345, 1), (Sum.inr 3348, 1), (Sum.inr 3354, 1), (Sum.inr 3478, 1), (Sum.inr 3538, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1806 : Integer.Sparse.reindex keyMap MixedData.row1806 = numericRow1806 := by decide +kernel

theorem numericCheck1806 (x : Master → ℝ) : Integer.Sparse.eval numericRow1806 x =
    (1 : ℝ) * reducedSource1806 x := by
  norm_num [numericRow1806, reducedSource1806, Integer.Sparse.eval, Sparse.eval, nodeValue2538, nodeValue3345, nodeValue3348, nodeValue3354, nodeValue3478, nodeValue3538, nodeValue4082]

noncomputable def reducedSource1807 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2048 x + ((1 : ℝ) * Sparse.eval nodeValue3386 x + ((1 : ℝ) * Sparse.eval nodeValue3491 x + ((1 : ℝ) * Sparse.eval nodeValue3522 x + ((1 : ℝ) * Sparse.eval nodeValue3538 x + ((1 : ℝ) * Sparse.eval nodeValue3542 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

def numericRow1807 : Integer.Sparse Master := [(Sum.inr 2048, 1), (Sum.inr 3386, 1), (Sum.inr 3491, 1), (Sum.inr 3522, 1), (Sum.inr 3538, 1), (Sum.inr 3542, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1807 : Integer.Sparse.reindex keyMap MixedData.row1807 = numericRow1807 := by decide +kernel

theorem numericCheck1807 (x : Master → ℝ) : Integer.Sparse.eval numericRow1807 x =
    (1 : ℝ) * reducedSource1807 x := by
  norm_num [numericRow1807, reducedSource1807, Integer.Sparse.eval, Sparse.eval, nodeValue2048, nodeValue3386, nodeValue3491, nodeValue3522, nodeValue3538, nodeValue3542, nodeValue4082]

end MUB6.Certificate.MixedSourceBridge

end OAI
