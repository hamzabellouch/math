import OAI.Analysis.MutuallyUnbiased.MixedData.Source13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1744 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue4064 x + ((1 : ℝ) * Sparse.eval nodeValue4066 x + ((2 : ℝ) * Sparse.eval nodeValue4067 x + ((2 : ℝ) * Sparse.eval nodeValue4070 x + ((4 : ℝ) * Sparse.eval nodeValue4074 x + ((1 : ℝ) * Sparse.eval nodeValue4076 x + ((2 : ℝ) * Sparse.eval nodeValue4077 x + ((4 : ℝ) * Sparse.eval nodeValue4080 x + ((4 : ℝ) * Sparse.eval nodeValue4081 x + ((2 : ℝ) * Sparse.eval nodeValue4082 x + ((2 : ℝ) * Sparse.eval nodeValue4084 x + ((1 : ℝ) * Sparse.eval nodeValue4085 x + ((1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))))))))

def numericRow1744 : Integer.Sparse Master := [(Sum.inr 4064, 4), (Sum.inr 4066, 1), (Sum.inr 4067, 2), (Sum.inr 4070, 2), (Sum.inr 4074, 4), (Sum.inr 4076, 1), (Sum.inr 4077, 2), (Sum.inr 4080, 4), (Sum.inr 4081, 4), (Sum.inr 4082, 2), (Sum.inr 4084, 2), (Sum.inr 4085, 1), (Sum.inr 4092, 1)]

theorem reindexCheck1744 : Integer.Sparse.reindex keyMap MixedData.row1744 = numericRow1744 := by decide +kernel

theorem numericCheck1744 (x : Master → ℝ) : Integer.Sparse.eval numericRow1744 x =
    (1 : ℝ) * reducedSource1744 x := by
  norm_num [numericRow1744, reducedSource1744, Integer.Sparse.eval, Sparse.eval, nodeValue4064, nodeValue4066, nodeValue4067, nodeValue4070, nodeValue4074, nodeValue4076, nodeValue4077, nodeValue4080, nodeValue4081, nodeValue4082, nodeValue4084, nodeValue4085, nodeValue4092]

noncomputable def reducedSource1745 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2340 x + ((1 : ℝ) * Sparse.eval nodeValue2816 x + ((1 : ℝ) * Sparse.eval nodeValue3162 x + ((1 : ℝ) * Sparse.eval nodeValue3174 x + ((1 : ℝ) * Sparse.eval nodeValue3198 x + ((1 : ℝ) * Sparse.eval nodeValue3706 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1745 : Integer.Sparse Master := [(Sum.inr 2340, 1), (Sum.inr 2816, 1), (Sum.inr 3162, 1), (Sum.inr 3174, 1), (Sum.inr 3198, 1), (Sum.inr 3706, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1745 : Integer.Sparse.reindex keyMap MixedData.row1745 = numericRow1745 := by decide +kernel

theorem numericCheck1745 (x : Master → ℝ) : Integer.Sparse.eval numericRow1745 x =
    (1 : ℝ) * reducedSource1745 x := by
  norm_num [numericRow1745, reducedSource1745, Integer.Sparse.eval, Sparse.eval, nodeValue2340, nodeValue2816, nodeValue3162, nodeValue3174, nodeValue3198, nodeValue3706, nodeValue4092]

noncomputable def reducedSource1746 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2213 x + ((1 : ℝ) * Sparse.eval nodeValue2215 x + ((1 : ℝ) * Sparse.eval nodeValue2217 x + ((1 : ℝ) * Sparse.eval nodeValue2225 x + ((1 : ℝ) * Sparse.eval nodeValue2274 x + ((1 : ℝ) * Sparse.eval nodeValue3612 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

def numericRow1746 : Integer.Sparse Master := [(Sum.inr 2213, 1), (Sum.inr 2215, 1), (Sum.inr 2217, 1), (Sum.inr 2225, 1), (Sum.inr 2274, 1), (Sum.inr 3612, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1746 : Integer.Sparse.reindex keyMap MixedData.row1746 = numericRow1746 := by decide +kernel

theorem numericCheck1746 (x : Master → ℝ) : Integer.Sparse.eval numericRow1746 x =
    (1 : ℝ) * reducedSource1746 x := by
  norm_num [numericRow1746, reducedSource1746, Integer.Sparse.eval, Sparse.eval, nodeValue2213, nodeValue2215, nodeValue2217, nodeValue2225, nodeValue2274, nodeValue3612, nodeValue4082]

noncomputable def reducedSource1747 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue910 x + ((1 : ℝ) * Sparse.eval nodeValue1794 x + ((1 : ℝ) * Sparse.eval nodeValue1977 x + ((1 : ℝ) * Sparse.eval nodeValue2012 x + ((1 : ℝ) * Sparse.eval nodeValue2020 x + ((1 : ℝ) * Sparse.eval nodeValue2023 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

def numericRow1747 : Integer.Sparse Master := [(Sum.inr 910, 1), (Sum.inr 1794, 1), (Sum.inr 1977, 1), (Sum.inr 2012, 1), (Sum.inr 2020, 1), (Sum.inr 2023, 1), (Sum.inr 4083, -1)]

theorem reindexCheck1747 : Integer.Sparse.reindex keyMap MixedData.row1747 = numericRow1747 := by decide +kernel

theorem numericCheck1747 (x : Master → ℝ) : Integer.Sparse.eval numericRow1747 x =
    (1 : ℝ) * reducedSource1747 x := by
  norm_num [numericRow1747, reducedSource1747, Integer.Sparse.eval, Sparse.eval, nodeValue910, nodeValue1794, nodeValue1977, nodeValue2012, nodeValue2020, nodeValue2023, nodeValue4083]

noncomputable def reducedSource1748 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2323 x + ((1 : ℝ) * Sparse.eval nodeValue2800 x + ((1 : ℝ) * Sparse.eval nodeValue3189 x + ((2 : ℝ) * Sparse.eval nodeValue3199 x + ((1 : ℝ) * Sparse.eval nodeValue3692 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow1748 : Integer.Sparse Master := [(Sum.inr 2323, 1), (Sum.inr 2800, 1), (Sum.inr 3189, 1), (Sum.inr 3199, 2), (Sum.inr 3692, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1748 : Integer.Sparse.reindex keyMap MixedData.row1748 = numericRow1748 := by decide +kernel

theorem numericCheck1748 (x : Master → ℝ) : Integer.Sparse.eval numericRow1748 x =
    (1 : ℝ) * reducedSource1748 x := by
  norm_num [numericRow1748, reducedSource1748, Integer.Sparse.eval, Sparse.eval, nodeValue2323, nodeValue2800, nodeValue3189, nodeValue3199, nodeValue3692, nodeValue4091]

noncomputable def reducedSource1749 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2213 x + ((1 : ℝ) * Sparse.eval nodeValue2396 x + ((1 : ℝ) * Sparse.eval nodeValue3476 x + ((1 : ℝ) * Sparse.eval nodeValue3610 x + ((2 : ℝ) * Sparse.eval nodeValue3612 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

def numericRow1749 : Integer.Sparse Master := [(Sum.inr 2213, 1), (Sum.inr 2396, 1), (Sum.inr 3476, 1), (Sum.inr 3610, 1), (Sum.inr 3612, 2), (Sum.inr 4082, -1)]

theorem reindexCheck1749 : Integer.Sparse.reindex keyMap MixedData.row1749 = numericRow1749 := by decide +kernel

theorem numericCheck1749 (x : Master → ℝ) : Integer.Sparse.eval numericRow1749 x =
    (1 : ℝ) * reducedSource1749 x := by
  norm_num [numericRow1749, reducedSource1749, Integer.Sparse.eval, Sparse.eval, nodeValue2213, nodeValue2396, nodeValue3476, nodeValue3610, nodeValue3612, nodeValue4082]

noncomputable def reducedSource1750 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3193 x + ((1 : ℝ) * Sparse.eval nodeValue3648 x + ((1 : ℝ) * Sparse.eval nodeValue3653 x + ((1 : ℝ) * Sparse.eval nodeValue3659 x + ((2 : ℝ) * Sparse.eval nodeValue3762 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0)))))

def numericRow1750 : Integer.Sparse Master := [(Sum.inr 3193, 1), (Sum.inr 3648, 1), (Sum.inr 3653, 1), (Sum.inr 3659, 1), (Sum.inr 3762, 2), (Sum.inr 4088, -1)]

theorem reindexCheck1750 : Integer.Sparse.reindex keyMap MixedData.row1750 = numericRow1750 := by decide +kernel

theorem numericCheck1750 (x : Master → ℝ) : Integer.Sparse.eval numericRow1750 x =
    (1 : ℝ) * reducedSource1750 x := by
  norm_num [numericRow1750, reducedSource1750, Integer.Sparse.eval, Sparse.eval, nodeValue3193, nodeValue3648, nodeValue3653, nodeValue3659, nodeValue3762, nodeValue4088]

noncomputable def reducedSource1751 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue950 x + ((1 : ℝ) * Sparse.eval nodeValue1829 x + ((1 : ℝ) * Sparse.eval nodeValue1977 x + ((1 : ℝ) * Sparse.eval nodeValue2094 x + ((1 : ℝ) * Sparse.eval nodeValue2107 x + ((1 : ℝ) * Sparse.eval nodeValue2110 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

def numericRow1751 : Integer.Sparse Master := [(Sum.inr 950, 1), (Sum.inr 1829, 1), (Sum.inr 1977, 1), (Sum.inr 2094, 1), (Sum.inr 2107, 1), (Sum.inr 2110, 1), (Sum.inr 4083, -1)]

theorem reindexCheck1751 : Integer.Sparse.reindex keyMap MixedData.row1751 = numericRow1751 := by decide +kernel

theorem numericCheck1751 (x : Master → ℝ) : Integer.Sparse.eval numericRow1751 x =
    (1 : ℝ) * reducedSource1751 x := by
  norm_num [numericRow1751, reducedSource1751, Integer.Sparse.eval, Sparse.eval, nodeValue950, nodeValue1829, nodeValue1977, nodeValue2094, nodeValue2107, nodeValue2110, nodeValue4083]

noncomputable def reducedSource1752 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2327 x + ((1 : ℝ) * Sparse.eval nodeValue2803 x + ((1 : ℝ) * Sparse.eval nodeValue3133 x + ((1 : ℝ) * Sparse.eval nodeValue3138 x + ((1 : ℝ) * Sparse.eval nodeValue3174 x + ((1 : ℝ) * Sparse.eval nodeValue3693 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1752 : Integer.Sparse Master := [(Sum.inr 2327, 1), (Sum.inr 2803, 1), (Sum.inr 3133, 1), (Sum.inr 3138, 1), (Sum.inr 3174, 1), (Sum.inr 3693, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1752 : Integer.Sparse.reindex keyMap MixedData.row1752 = numericRow1752 := by decide +kernel

theorem numericCheck1752 (x : Master → ℝ) : Integer.Sparse.eval numericRow1752 x =
    (1 : ℝ) * reducedSource1752 x := by
  norm_num [numericRow1752, reducedSource1752, Integer.Sparse.eval, Sparse.eval, nodeValue2327, nodeValue2803, nodeValue3133, nodeValue3138, nodeValue3174, nodeValue3693, nodeValue4092]

noncomputable def reducedSource1753 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2274 x + ((1 : ℝ) * Sparse.eval nodeValue2401 x + ((1 : ℝ) * Sparse.eval nodeValue3536 x + ((1 : ℝ) * Sparse.eval nodeValue3612 x + ((1 : ℝ) * Sparse.eval nodeValue3630 x + ((1 : ℝ) * Sparse.eval nodeValue3631 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

def numericRow1753 : Integer.Sparse Master := [(Sum.inr 2274, 1), (Sum.inr 2401, 1), (Sum.inr 3536, 1), (Sum.inr 3612, 1), (Sum.inr 3630, 1), (Sum.inr 3631, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1753 : Integer.Sparse.reindex keyMap MixedData.row1753 = numericRow1753 := by decide +kernel

theorem numericCheck1753 (x : Master → ℝ) : Integer.Sparse.eval numericRow1753 x =
    (1 : ℝ) * reducedSource1753 x := by
  norm_num [numericRow1753, reducedSource1753, Integer.Sparse.eval, Sparse.eval, nodeValue2274, nodeValue2401, nodeValue3536, nodeValue3612, nodeValue3630, nodeValue3631, nodeValue4082]

noncomputable def reducedSource1754 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2274 x + ((1 : ℝ) * Sparse.eval nodeValue2276 x + ((1 : ℝ) * Sparse.eval nodeValue2280 x + ((1 : ℝ) * Sparse.eval nodeValue2288 x + ((1 : ℝ) * Sparse.eval nodeValue3631 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

def numericRow1754 : Integer.Sparse Master := [(Sum.inr 2274, 2), (Sum.inr 2276, 1), (Sum.inr 2280, 1), (Sum.inr 2288, 1), (Sum.inr 3631, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1754 : Integer.Sparse.reindex keyMap MixedData.row1754 = numericRow1754 := by decide +kernel

theorem numericCheck1754 (x : Master → ℝ) : Integer.Sparse.eval numericRow1754 x =
    (1 : ℝ) * reducedSource1754 x := by
  norm_num [numericRow1754, reducedSource1754, Integer.Sparse.eval, Sparse.eval, nodeValue2274, nodeValue2276, nodeValue2280, nodeValue2288, nodeValue3631, nodeValue4082]

noncomputable def reducedSource1755 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3166 x + ((1 : ℝ) * Sparse.eval nodeValue3658 x + ((1 : ℝ) * Sparse.eval nodeValue3660 x + ((1 : ℝ) * Sparse.eval nodeValue3666 x + ((2 : ℝ) * Sparse.eval nodeValue3772 x + ((-1 : ℝ) * Sparse.eval nodeValue4089 x + 0)))))

def numericRow1755 : Integer.Sparse Master := [(Sum.inr 3166, 1), (Sum.inr 3658, 1), (Sum.inr 3660, 1), (Sum.inr 3666, 1), (Sum.inr 3772, 2), (Sum.inr 4089, -1)]

theorem reindexCheck1755 : Integer.Sparse.reindex keyMap MixedData.row1755 = numericRow1755 := by decide +kernel

theorem numericCheck1755 (x : Master → ℝ) : Integer.Sparse.eval numericRow1755 x =
    (1 : ℝ) * reducedSource1755 x := by
  norm_num [numericRow1755, reducedSource1755, Integer.Sparse.eval, Sparse.eval, nodeValue3166, nodeValue3658, nodeValue3660, nodeValue3666, nodeValue3772, nodeValue4089]

noncomputable def reducedSource1756 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2346 x + ((1 : ℝ) * Sparse.eval nodeValue2821 x + ((2 : ℝ) * Sparse.eval nodeValue3129 x + ((1 : ℝ) * Sparse.eval nodeValue3161 x + ((1 : ℝ) * Sparse.eval nodeValue3397 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1756 : Integer.Sparse Master := [(Sum.inr 2346, 1), (Sum.inr 2821, 1), (Sum.inr 3129, 2), (Sum.inr 3161, 1), (Sum.inr 3397, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1756 : Integer.Sparse.reindex keyMap MixedData.row1756 = numericRow1756 := by decide +kernel

theorem numericCheck1756 (x : Master → ℝ) : Integer.Sparse.eval numericRow1756 x =
    (1 : ℝ) * reducedSource1756 x := by
  norm_num [numericRow1756, reducedSource1756, Integer.Sparse.eval, Sparse.eval, nodeValue2346, nodeValue2821, nodeValue3129, nodeValue3161, nodeValue3397, nodeValue4084]

noncomputable def reducedSource1757 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3147 x + ((1 : ℝ) * Sparse.eval nodeValue3372 x + ((1 : ℝ) * Sparse.eval nodeValue3473 x + ((2 : ℝ) * Sparse.eval nodeValue3480 x + ((1 : ℝ) * Sparse.eval nodeValue3611 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

def numericRow1757 : Integer.Sparse Master := [(Sum.inr 3147, 1), (Sum.inr 3372, 1), (Sum.inr 3473, 1), (Sum.inr 3480, 2), (Sum.inr 3611, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1757 : Integer.Sparse.reindex keyMap MixedData.row1757 = numericRow1757 := by decide +kernel

theorem numericCheck1757 (x : Master → ℝ) : Integer.Sparse.eval numericRow1757 x =
    (1 : ℝ) * reducedSource1757 x := by
  norm_num [numericRow1757, reducedSource1757, Integer.Sparse.eval, Sparse.eval, nodeValue3147, nodeValue3372, nodeValue3473, nodeValue3480, nodeValue3611, nodeValue4082]

noncomputable def reducedSource1758 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1141 x + ((1 : ℝ) * Sparse.eval nodeValue2343 x + ((1 : ℝ) * Sparse.eval nodeValue2433 x + ((1 : ℝ) * Sparse.eval nodeValue2499 x + ((1 : ℝ) * Sparse.eval nodeValue2512 x + ((1 : ℝ) * Sparse.eval nodeValue2515 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1758 : Integer.Sparse Master := [(Sum.inr 1141, 1), (Sum.inr 2343, 1), (Sum.inr 2433, 1), (Sum.inr 2499, 1), (Sum.inr 2512, 1), (Sum.inr 2515, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1758 : Integer.Sparse.reindex keyMap MixedData.row1758 = numericRow1758 := by decide +kernel

theorem numericCheck1758 (x : Master → ℝ) : Integer.Sparse.eval numericRow1758 x =
    (1 : ℝ) * reducedSource1758 x := by
  norm_num [numericRow1758, reducedSource1758, Integer.Sparse.eval, Sparse.eval, nodeValue1141, nodeValue2343, nodeValue2433, nodeValue2499, nodeValue2512, nodeValue2515, nodeValue4092]

noncomputable def reducedSource1759 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2335 x + ((1 : ℝ) * Sparse.eval nodeValue2811 x + ((1 : ℝ) * Sparse.eval nodeValue2846 x + ((1 : ℝ) * Sparse.eval nodeValue2889 x + ((1 : ℝ) * Sparse.eval nodeValue2979 x + ((1 : ℝ) * Sparse.eval nodeValue3705 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1759 : Integer.Sparse Master := [(Sum.inr 2335, 1), (Sum.inr 2811, 1), (Sum.inr 2846, 1), (Sum.inr 2889, 1), (Sum.inr 2979, 1), (Sum.inr 3705, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1759 : Integer.Sparse.reindex keyMap MixedData.row1759 = numericRow1759 := by decide +kernel

theorem numericCheck1759 (x : Master → ℝ) : Integer.Sparse.eval numericRow1759 x =
    (1 : ℝ) * reducedSource1759 x := by
  norm_num [numericRow1759, reducedSource1759, Integer.Sparse.eval, Sparse.eval, nodeValue2335, nodeValue2811, nodeValue2846, nodeValue2889, nodeValue2979, nodeValue3705, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
