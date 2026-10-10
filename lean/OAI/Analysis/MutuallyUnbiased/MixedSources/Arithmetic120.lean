import OAI.Analysis.MutuallyUnbiased.MixedData.Source15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values85
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1920 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2895 x + ((1 : ℝ) * Sparse.eval nodeValue2896 x + ((1 : ℝ) * Sparse.eval nodeValue2898 x + ((2 : ℝ) * Sparse.eval nodeValue2928 x + ((1 : ℝ) * Sparse.eval nodeValue3964 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow1920 : Integer.Sparse Master := [(Sum.inr 2895, 1), (Sum.inr 2896, 1), (Sum.inr 2898, 1), (Sum.inr 2928, 2), (Sum.inr 3964, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1920 : Integer.Sparse.reindex keyMap MixedData.row1920 = numericRow1920 := by decide +kernel

theorem numericCheck1920 (x : Master → ℝ) : Integer.Sparse.eval numericRow1920 x =
    (1 : ℝ) * reducedSource1920 x := by
  norm_num [numericRow1920, reducedSource1920, Integer.Sparse.eval, Sparse.eval, nodeValue2895, nodeValue2896, nodeValue2898, nodeValue2928, nodeValue3964, nodeValue4091]

noncomputable def reducedSource1921 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1158 x + ((1 : ℝ) * Sparse.eval nodeValue2354 x + ((1 : ℝ) * Sparse.eval nodeValue2556 x + ((2 : ℝ) * Sparse.eval nodeValue2567 x + ((1 : ℝ) * Sparse.eval nodeValue2589 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow1921 : Integer.Sparse Master := [(Sum.inr 1158, 1), (Sum.inr 2354, 1), (Sum.inr 2556, 1), (Sum.inr 2567, 2), (Sum.inr 2589, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1921 : Integer.Sparse.reindex keyMap MixedData.row1921 = numericRow1921 := by decide +kernel

theorem numericCheck1921 (x : Master → ℝ) : Integer.Sparse.eval numericRow1921 x =
    (1 : ℝ) * reducedSource1921 x := by
  norm_num [numericRow1921, reducedSource1921, Integer.Sparse.eval, Sparse.eval, nodeValue1158, nodeValue2354, nodeValue2556, nodeValue2567, nodeValue2589, nodeValue4091]

noncomputable def reducedSource1922 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2847 x + ((1 : ℝ) * Sparse.eval nodeValue2893 x + ((1 : ℝ) * Sparse.eval nodeValue2898 x + ((2 : ℝ) * Sparse.eval nodeValue2925 x + ((1 : ℝ) * Sparse.eval nodeValue3945 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow1922 : Integer.Sparse Master := [(Sum.inr 2847, 1), (Sum.inr 2893, 1), (Sum.inr 2898, 1), (Sum.inr 2925, 2), (Sum.inr 3945, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1922 : Integer.Sparse.reindex keyMap MixedData.row1922 = numericRow1922 := by decide +kernel

theorem numericCheck1922 (x : Master → ℝ) : Integer.Sparse.eval numericRow1922 x =
    (1 : ℝ) * reducedSource1922 x := by
  norm_num [numericRow1922, reducedSource1922, Integer.Sparse.eval, Sparse.eval, nodeValue2847, nodeValue2893, nodeValue2898, nodeValue2925, nodeValue3945, nodeValue4091]

noncomputable def reducedSource1923 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2922 x + ((1 : ℝ) * Sparse.eval nodeValue3748 x + ((1 : ℝ) * Sparse.eval nodeValue3751 x + ((1 : ℝ) * Sparse.eval nodeValue3758 x + ((1 : ℝ) * Sparse.eval nodeValue3866 x + ((1 : ℝ) * Sparse.eval nodeValue3973 x + ((-1 : ℝ) * Sparse.eval nodeValue4087 x + 0))))))

def numericRow1923 : Integer.Sparse Master := [(Sum.inr 2922, 1), (Sum.inr 3748, 1), (Sum.inr 3751, 1), (Sum.inr 3758, 1), (Sum.inr 3866, 1), (Sum.inr 3973, 1), (Sum.inr 4087, -1)]

theorem reindexCheck1923 : Integer.Sparse.reindex keyMap MixedData.row1923 = numericRow1923 := by decide +kernel

theorem numericCheck1923 (x : Master → ℝ) : Integer.Sparse.eval numericRow1923 x =
    (1 : ℝ) * reducedSource1923 x := by
  norm_num [numericRow1923, reducedSource1923, Integer.Sparse.eval, Sparse.eval, nodeValue2922, nodeValue3748, nodeValue3751, nodeValue3758, nodeValue3866, nodeValue3973, nodeValue4087]

noncomputable def reducedSource1924 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4327 x + ((1 : ℝ) * Sparse.eval nodeValue4328 x + ((1 : ℝ) * Sparse.eval nodeValue4332 x + ((1 : ℝ) * Sparse.eval nodeValue4345 x + ((1 : ℝ) * Sparse.eval nodeValue4439 x + ((1 : ℝ) * Sparse.eval nodeValue4930 x + ((1 : ℝ) * Sparse.eval nodeValue4931 x + ((1 : ℝ) * Sparse.eval nodeValue4933 x + ((1 : ℝ) * Sparse.eval nodeValue4942 x + ((1 : ℝ) * Sparse.eval nodeValue5037 x + ((1 : ℝ) * Sparse.eval nodeValue5078 x + ((1 : ℝ) * Sparse.eval nodeValue5114 x + ((1 : ℝ) * Sparse.eval nodeValue5117 x + ((1 : ℝ) * Sparse.eval nodeValue5128 x + ((1 : ℝ) * Sparse.eval nodeValue5129 x + ((1 : ℝ) * Sparse.eval nodeValue5138 x + ((1 : ℝ) * Sparse.eval nodeValue5144 x + ((1 : ℝ) * Sparse.eval nodeValue5145 x + ((1 : ℝ) * Sparse.eval nodeValue5149 x + ((1 : ℝ) * Sparse.eval nodeValue5152 x + ((1 : ℝ) * Sparse.eval nodeValue5160 x + ((1 : ℝ) * Sparse.eval nodeValue5170 x + ((1 : ℝ) * Sparse.eval nodeValue5251 x + ((1 : ℝ) * Sparse.eval nodeValue5281 x + ((1 : ℝ) * Sparse.eval nodeValue5284 x + ((1 : ℝ) * Sparse.eval nodeValue5393 x + ((1 : ℝ) * Sparse.eval nodeValue5396 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5478 x + 0)))))))))))))))))))))))))))))

def numericRow1924 : Integer.Sparse Master := [(Sum.inr 2429, -1), (Sum.inr 2485, -1), (Sum.inr 2893, -1), (Sum.inr 2896, -1), (Sum.inr 2924, -1), (Sum.inr 2931, -1), (Sum.inr 2954, -1), (Sum.inr 3077, -1), (Sum.inr 3455, -1), (Sum.inr 3481, -1), (Sum.inr 3597, -1), (Sum.inr 3599, -1), (Sum.inr 3605, -1), (Sum.inr 3606, -1), (Sum.inr 3612, -1), (Sum.inr 3625, -1), (Sum.inr 3779, -1), (Sum.inr 3797, -1), (Sum.inr 3838, -1), (Sum.inr 3843, -1), (Sum.inr 3974, -2), (Sum.inr 4327, 4), (Sum.inr 4328, 4), (Sum.inr 4332, 4), (Sum.inr 4345, 4), (Sum.inr 4439, 4), (Sum.inr 4930, 4), (Sum.inr 4931, 4), (Sum.inr 4933, 4), (Sum.inr 4942, 4), (Sum.inr 5128, 4), (Sum.inr 5129, 4), (Sum.inr 5138, 4), (Sum.inr 5144, 4), (Sum.inr 5145, 4), (Sum.inr 5160, 4), (Sum.inr 5251, 4), (Sum.inr 5281, 4)]

theorem reindexCheck1924 : Integer.Sparse.reindex keyMap MixedData.row1924 = numericRow1924 := by decide +kernel

theorem numericCheck1924 (x : Master → ℝ) : Integer.Sparse.eval numericRow1924 x =
    (4 : ℝ) * reducedSource1924 x := by
  norm_num [numericRow1924, reducedSource1924, Integer.Sparse.eval, Sparse.eval, nodeValue4327, nodeValue4328, nodeValue4332, nodeValue4345, nodeValue4439, nodeValue4930, nodeValue4931, nodeValue4933, nodeValue4942, nodeValue5037, nodeValue5078, nodeValue5114, nodeValue5117, nodeValue5128, nodeValue5129, nodeValue5138, nodeValue5144, nodeValue5145, nodeValue5149, nodeValue5152, nodeValue5160, nodeValue5170, nodeValue5251, nodeValue5281, nodeValue5284, nodeValue5393, nodeValue5396, nodeValue5410, nodeValue5424, nodeValue5478]
  ring

noncomputable def reducedSource1925 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue905 x + ((1 : ℝ) * Sparse.eval nodeValue906 x + ((1 : ℝ) * Sparse.eval nodeValue910 x + ((1 : ℝ) * Sparse.eval nodeValue923 x + ((1 : ℝ) * Sparse.eval nodeValue1021 x + ((1 : ℝ) * Sparse.eval nodeValue2320 x + ((1 : ℝ) * Sparse.eval nodeValue2321 x + ((1 : ℝ) * Sparse.eval nodeValue2324 x + ((1 : ℝ) * Sparse.eval nodeValue2333 x + ((1 : ℝ) * Sparse.eval nodeValue2526 x + ((1 : ℝ) * Sparse.eval nodeValue2527 x + ((1 : ℝ) * Sparse.eval nodeValue2530 x + ((1 : ℝ) * Sparse.eval nodeValue2543 x + ((1 : ℝ) * Sparse.eval nodeValue2545 x + ((1 : ℝ) * Sparse.eval nodeValue2557 x + ((1 : ℝ) * Sparse.eval nodeValue2566 x + ((1 : ℝ) * Sparse.eval nodeValue2567 x + ((1 : ℝ) * Sparse.eval nodeValue2570 x + ((1 : ℝ) * Sparse.eval nodeValue2572 x + ((1 : ℝ) * Sparse.eval nodeValue2576 x + ((1 : ℝ) * Sparse.eval nodeValue2587 x + ((1 : ℝ) * Sparse.eval nodeValue2596 x + ((1 : ℝ) * Sparse.eval nodeValue2710 x + ((1 : ℝ) * Sparse.eval nodeValue2750 x + ((1 : ℝ) * Sparse.eval nodeValue2753 x + ((1 : ℝ) * Sparse.eval nodeValue3925 x + ((1 : ℝ) * Sparse.eval nodeValue3988 x + ((1 : ℝ) * Sparse.eval nodeValue3990 x + ((1 : ℝ) * Sparse.eval nodeValue3994 x + ((1 : ℝ) * Sparse.eval nodeValue3996 x + 0)))))))))))))))))))))))))))))

def numericRow1925 : Integer.Sparse Master := [(Sum.inl 0, -386), (Sum.inl 9, 200), (Sum.inl 58, -10), (Sum.inl 5, -400), (Sum.inl 6, -10), (Sum.inl 68, -600), (Sum.inl 2, 850), (Sum.inl 69, 480), (Sum.inl 70, 160), (Sum.inl 71, 320), (Sum.inl 7, 960), (Sum.inl 35, 320), (Sum.inl 8, 1280), (Sum.inl 124, -960), (Sum.inl 125, -480), (Sum.inl 126, -960), (Sum.inl 51, -960), (Sum.inl 3, 2720), (Sum.inl 13, 160), (Sum.inl 52, 320), (Sum.inl 23, -480), (Sum.inl 24, -960), (Sum.inl 12, 480), (Sum.inl 56, -480), (Sum.inl 26, 320), (Sum.inl 4, 1120), (Sum.inl 27, 240), (Sum.inl 1, -1420), (Sum.inl 30, -480), (Sum.inl 31, -480), (Sum.inr 905, 8640), (Sum.inr 906, 8640), (Sum.inr 910, 8640), (Sum.inr 923, 8640), (Sum.inr 1021, 8640), (Sum.inr 2320, 8640), (Sum.inr 2321, 8640), (Sum.inr 2324, 8640), (Sum.inr 2333, 8640), (Sum.inr 2543, 8640), (Sum.inr 2545, 8640), (Sum.inr 2557, 8640), (Sum.inr 2566, 8640), (Sum.inr 2567, 8640), (Sum.inr 2587, 8640), (Sum.inr 2710, 8640), (Sum.inr 2750, 8640)]

theorem reindexCheck1925 : Integer.Sparse.reindex keyMap MixedData.row1925 = numericRow1925 := by decide +kernel

theorem numericCheck1925 (x : Master → ℝ) : Integer.Sparse.eval numericRow1925 x =
    (8640 : ℝ) * reducedSource1925 x := by
  norm_num [numericRow1925, reducedSource1925, Integer.Sparse.eval, Sparse.eval, nodeValue905, nodeValue906, nodeValue910, nodeValue923, nodeValue1021, nodeValue2320, nodeValue2321, nodeValue2324, nodeValue2333, nodeValue2526, nodeValue2527, nodeValue2530, nodeValue2543, nodeValue2545, nodeValue2557, nodeValue2566, nodeValue2567, nodeValue2570, nodeValue2572, nodeValue2576, nodeValue2587, nodeValue2596, nodeValue2710, nodeValue2750, nodeValue2753, nodeValue3925, nodeValue3988, nodeValue3990, nodeValue3994, nodeValue3996]
  ring

noncomputable def reducedSource1926 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1667 x + ((1 : ℝ) * Sparse.eval nodeValue1668 x + ((1 : ℝ) * Sparse.eval nodeValue1670 x + ((1 : ℝ) * Sparse.eval nodeValue1678 x + ((1 : ℝ) * Sparse.eval nodeValue1713 x + ((1 : ℝ) * Sparse.eval nodeValue3406 x + ((1 : ℝ) * Sparse.eval nodeValue3407 x + ((1 : ℝ) * Sparse.eval nodeValue3408 x + ((1 : ℝ) * Sparse.eval nodeValue3414 x + ((1 : ℝ) * Sparse.eval nodeValue3455 x + ((1 : ℝ) * Sparse.eval nodeValue3481 x + ((1 : ℝ) * Sparse.eval nodeValue3516 x + ((1 : ℝ) * Sparse.eval nodeValue3517 x + ((1 : ℝ) * Sparse.eval nodeValue3519 x + ((1 : ℝ) * Sparse.eval nodeValue3539 x + ((1 : ℝ) * Sparse.eval nodeValue3557 x + ((1 : ℝ) * Sparse.eval nodeValue3558 x + ((1 : ℝ) * Sparse.eval nodeValue3562 x + ((1 : ℝ) * Sparse.eval nodeValue3571 x + ((1 : ℝ) * Sparse.eval nodeValue3597 x + ((1 : ℝ) * Sparse.eval nodeValue3599 x + ((1 : ℝ) * Sparse.eval nodeValue3605 x + ((1 : ℝ) * Sparse.eval nodeValue3606 x + ((1 : ℝ) * Sparse.eval nodeValue3612 x + ((1 : ℝ) * Sparse.eval nodeValue3625 x + ((1 : ℝ) * Sparse.eval nodeValue3797 x + ((1 : ℝ) * Sparse.eval nodeValue3798 x + ((1 : ℝ) * Sparse.eval nodeValue3816 x + ((1 : ℝ) * Sparse.eval nodeValue3843 x + ((1 : ℝ) * Sparse.eval nodeValue3974 x + 0)))))))))))))))))))))))))))))

def numericRow1926 : Integer.Sparse Master := [(Sum.inr 1667, 1), (Sum.inr 1668, 1), (Sum.inr 1670, 1), (Sum.inr 1678, 1), (Sum.inr 1713, 1), (Sum.inr 3406, 1), (Sum.inr 3407, 1), (Sum.inr 3408, 1), (Sum.inr 3414, 1), (Sum.inr 3455, 1), (Sum.inr 3481, 1), (Sum.inr 3516, 1), (Sum.inr 3517, 1), (Sum.inr 3519, 1), (Sum.inr 3539, 1), (Sum.inr 3557, 1), (Sum.inr 3558, 1), (Sum.inr 3562, 1), (Sum.inr 3571, 1), (Sum.inr 3597, 1), (Sum.inr 3599, 1), (Sum.inr 3605, 1), (Sum.inr 3606, 1), (Sum.inr 3612, 1), (Sum.inr 3625, 1), (Sum.inr 3797, 1), (Sum.inr 3843, 1), (Sum.inr 3974, 1)]

theorem reindexCheck1926 : Integer.Sparse.reindex keyMap MixedData.row1926 = numericRow1926 := by decide +kernel

theorem numericCheck1926 (x : Master → ℝ) : Integer.Sparse.eval numericRow1926 x =
    (1 : ℝ) * reducedSource1926 x := by
  norm_num [numericRow1926, reducedSource1926, Integer.Sparse.eval, Sparse.eval, nodeValue1667, nodeValue1668, nodeValue1670, nodeValue1678, nodeValue1713, nodeValue3406, nodeValue3407, nodeValue3408, nodeValue3414, nodeValue3455, nodeValue3481, nodeValue3516, nodeValue3517, nodeValue3519, nodeValue3539, nodeValue3557, nodeValue3558, nodeValue3562, nodeValue3571, nodeValue3597, nodeValue3599, nodeValue3605, nodeValue3606, nodeValue3612, nodeValue3625, nodeValue3797, nodeValue3798, nodeValue3816, nodeValue3843, nodeValue3974]

noncomputable def reducedSource1927 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2422 x + ((1 : ℝ) * Sparse.eval nodeValue2822 x + ((1 : ℝ) * Sparse.eval nodeValue2824 x + ((1 : ℝ) * Sparse.eval nodeValue2826 x + ((1 : ℝ) * Sparse.eval nodeValue2924 x + ((1 : ℝ) * Sparse.eval nodeValue3779 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow1927 : Integer.Sparse Master := [(Sum.inr 2422, 1), (Sum.inr 2822, 1), (Sum.inr 2824, 1), (Sum.inr 2826, 1), (Sum.inr 2924, 1), (Sum.inr 3779, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1927 : Integer.Sparse.reindex keyMap MixedData.row1927 = numericRow1927 := by decide +kernel

theorem numericCheck1927 (x : Master → ℝ) : Integer.Sparse.eval numericRow1927 x =
    (1 : ℝ) * reducedSource1927 x := by
  norm_num [numericRow1927, reducedSource1927, Integer.Sparse.eval, Sparse.eval, nodeValue2422, nodeValue2822, nodeValue2824, nodeValue2826, nodeValue2924, nodeValue3779, nodeValue4091]

noncomputable def reducedSource1928 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1169 x + ((1 : ℝ) * Sparse.eval nodeValue2361 x + ((3 : ℝ) * Sparse.eval nodeValue2573 x + ((1 : ℝ) * Sparse.eval nodeValue2589 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))

def numericRow1928 : Integer.Sparse Master := [(Sum.inr 1169, 1), (Sum.inr 2361, 1), (Sum.inr 2573, 3), (Sum.inr 2589, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1928 : Integer.Sparse.reindex keyMap MixedData.row1928 = numericRow1928 := by decide +kernel

theorem numericCheck1928 (x : Master → ℝ) : Integer.Sparse.eval numericRow1928 x =
    (1 : ℝ) * reducedSource1928 x := by
  norm_num [numericRow1928, reducedSource1928, Integer.Sparse.eval, Sparse.eval, nodeValue1169, nodeValue2361, nodeValue2573, nodeValue2589, nodeValue4091]

noncomputable def reducedSource1929 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1964 x + ((2 : ℝ) * Sparse.eval nodeValue2892 x + ((2 : ℝ) * Sparse.eval nodeValue2923 x + ((1 : ℝ) * Sparse.eval nodeValue3496 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

def numericRow1929 : Integer.Sparse Master := [(Sum.inr 1964, 1), (Sum.inr 2892, 2), (Sum.inr 2923, 2), (Sum.inr 3496, 1), (Sum.inr 4083, -1)]

theorem reindexCheck1929 : Integer.Sparse.reindex keyMap MixedData.row1929 = numericRow1929 := by decide +kernel

theorem numericCheck1929 (x : Master → ℝ) : Integer.Sparse.eval numericRow1929 x =
    (1 : ℝ) * reducedSource1929 x := by
  norm_num [numericRow1929, reducedSource1929, Integer.Sparse.eval, Sparse.eval, nodeValue1964, nodeValue2892, nodeValue2923, nodeValue3496, nodeValue4083]

noncomputable def reducedSource1930 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2800 x + ((2 : ℝ) * Sparse.eval nodeValue2801 x + ((1 : ℝ) * Sparse.eval nodeValue2814 x + ((1 : ℝ) * Sparse.eval nodeValue2864 x + ((1 : ℝ) * Sparse.eval nodeValue3692 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow1930 : Integer.Sparse Master := [(Sum.inr 2800, 1), (Sum.inr 2801, 2), (Sum.inr 2814, 1), (Sum.inr 2864, 1), (Sum.inr 3692, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1930 : Integer.Sparse.reindex keyMap MixedData.row1930 = numericRow1930 := by decide +kernel

theorem numericCheck1930 (x : Master → ℝ) : Integer.Sparse.eval numericRow1930 x =
    (1 : ℝ) * reducedSource1930 x := by
  norm_num [numericRow1930, reducedSource1930, Integer.Sparse.eval, Sparse.eval, nodeValue2800, nodeValue2801, nodeValue2814, nodeValue2864, nodeValue3692, nodeValue4091]

noncomputable def reducedSource1931 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2797 x + ((1 : ℝ) * Sparse.eval nodeValue2799 x + ((1 : ℝ) * Sparse.eval nodeValue2801 x + ((1 : ℝ) * Sparse.eval nodeValue2809 x + ((1 : ℝ) * Sparse.eval nodeValue2862 x + ((1 : ℝ) * Sparse.eval nodeValue3690 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow1931 : Integer.Sparse Master := [(Sum.inr 2797, 1), (Sum.inr 2799, 1), (Sum.inr 2801, 1), (Sum.inr 2809, 1), (Sum.inr 2862, 1), (Sum.inr 3690, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1931 : Integer.Sparse.reindex keyMap MixedData.row1931 = numericRow1931 := by decide +kernel

theorem numericCheck1931 (x : Master → ℝ) : Integer.Sparse.eval numericRow1931 x =
    (1 : ℝ) * reducedSource1931 x := by
  norm_num [numericRow1931, reducedSource1931, Integer.Sparse.eval, Sparse.eval, nodeValue2797, nodeValue2799, nodeValue2801, nodeValue2809, nodeValue2862, nodeValue3690, nodeValue4091]

noncomputable def reducedSource1932 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2524 x + ((2 : ℝ) * Sparse.eval nodeValue2798 x + ((1 : ℝ) * Sparse.eval nodeValue2807 x + ((1 : ℝ) * Sparse.eval nodeValue2861 x + ((1 : ℝ) * Sparse.eval nodeValue3689 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow1932 : Integer.Sparse Master := [(Sum.inr 2524, 1), (Sum.inr 2798, 2), (Sum.inr 2807, 1), (Sum.inr 2861, 1), (Sum.inr 3689, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1932 : Integer.Sparse.reindex keyMap MixedData.row1932 = numericRow1932 := by decide +kernel

theorem numericCheck1932 (x : Master → ℝ) : Integer.Sparse.eval numericRow1932 x =
    (1 : ℝ) * reducedSource1932 x := by
  norm_num [numericRow1932, reducedSource1932, Integer.Sparse.eval, Sparse.eval, nodeValue2524, nodeValue2798, nodeValue2807, nodeValue2861, nodeValue3689, nodeValue4092]

noncomputable def reducedSource1933 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2031 x + ((1 : ℝ) * Sparse.eval nodeValue2036 x + ((1 : ℝ) * Sparse.eval nodeValue2046 x + ((1 : ℝ) * Sparse.eval nodeValue2275 x + ((1 : ℝ) * Sparse.eval nodeValue3537 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

def numericRow1933 : Integer.Sparse Master := [(Sum.inr 2031, 2), (Sum.inr 2036, 1), (Sum.inr 2046, 1), (Sum.inr 2275, 1), (Sum.inr 3537, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1933 : Integer.Sparse.reindex keyMap MixedData.row1933 = numericRow1933 := by decide +kernel

theorem numericCheck1933 (x : Master → ℝ) : Integer.Sparse.eval numericRow1933 x =
    (1 : ℝ) * reducedSource1933 x := by
  norm_num [numericRow1933, reducedSource1933, Integer.Sparse.eval, Sparse.eval, nodeValue2031, nodeValue2036, nodeValue2046, nodeValue2275, nodeValue3537, nodeValue4080]

noncomputable def reducedSource1934 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2810 x + ((1 : ℝ) * Sparse.eval nodeValue2816 x + ((1 : ℝ) * Sparse.eval nodeValue2817 x + ((1 : ℝ) * Sparse.eval nodeValue2819 x + ((1 : ℝ) * Sparse.eval nodeValue2885 x + ((1 : ℝ) * Sparse.eval nodeValue3706 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1934 : Integer.Sparse Master := [(Sum.inr 2810, 1), (Sum.inr 2816, 1), (Sum.inr 2817, 1), (Sum.inr 2819, 1), (Sum.inr 2885, 1), (Sum.inr 3706, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1934 : Integer.Sparse.reindex keyMap MixedData.row1934 = numericRow1934 := by decide +kernel

theorem numericCheck1934 (x : Master → ℝ) : Integer.Sparse.eval numericRow1934 x =
    (1 : ℝ) * reducedSource1934 x := by
  norm_num [numericRow1934, reducedSource1934, Integer.Sparse.eval, Sparse.eval, nodeValue2810, nodeValue2816, nodeValue2817, nodeValue2819, nodeValue2885, nodeValue3706, nodeValue4092]

noncomputable def reducedSource1935 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4364 x + ((1 : ℝ) * Sparse.eval nodeValue4365 x + ((2 : ℝ) * Sparse.eval nodeValue4369 x + ((1 : ℝ) * Sparse.eval nodeValue4474 x + ((1 : ℝ) * Sparse.eval nodeValue4968 x + ((1 : ℝ) * Sparse.eval nodeValue4970 x + ((2 : ℝ) * Sparse.eval nodeValue4974 x + ((1 : ℝ) * Sparse.eval nodeValue5041 x + ((2 : ℝ) * Sparse.eval nodeValue5043 x + ((1 : ℝ) * Sparse.eval nodeValue5085 x + ((2 : ℝ) * Sparse.eval nodeValue5147 x + ((2 : ℝ) * Sparse.eval nodeValue5185 x + ((2 : ℝ) * Sparse.eval nodeValue5189 x + ((1 : ℝ) * Sparse.eval nodeValue5202 x + ((2 : ℝ) * Sparse.eval nodeValue5203 x + ((2 : ℝ) * Sparse.eval nodeValue5266 x + ((1 : ℝ) * Sparse.eval nodeValue5301 x + ((1 : ℝ) * Sparse.eval nodeValue5369 x + ((1 : ℝ) * Sparse.eval nodeValue5469 x + ((2 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5474 x + 0))))))))))))))))))))

def numericRow1935 : Integer.Sparse Master := [(Sum.inr 2809, -1), (Sum.inr 2815, -1), (Sum.inr 2818, -2), (Sum.inr 2880, -1), (Sum.inr 2884, -2), (Sum.inr 3053, -1), (Sum.inr 3587, -1), (Sum.inr 3588, -1), (Sum.inr 3592, -2), (Sum.inr 3617, -1), (Sum.inr 3619, -1), (Sum.inr 3621, -2), (Sum.inr 3945, -1), (Sum.inr 3952, -1), (Sum.inr 3958, -2), (Sum.inr 3961, -2), (Sum.inr 4364, 4), (Sum.inr 4365, 4), (Sum.inr 4369, 8), (Sum.inr 4474, 4), (Sum.inr 5041, 4), (Sum.inr 5043, 8), (Sum.inr 5085, 4), (Sum.inr 5147, 8), (Sum.inr 5185, 8), (Sum.inr 5189, 8), (Sum.inr 5266, 8)]

theorem reindexCheck1935 : Integer.Sparse.reindex keyMap MixedData.row1935 = numericRow1935 := by decide +kernel

theorem numericCheck1935 (x : Master → ℝ) : Integer.Sparse.eval numericRow1935 x =
    (4 : ℝ) * reducedSource1935 x := by
  norm_num [numericRow1935, reducedSource1935, Integer.Sparse.eval, Sparse.eval, nodeValue4364, nodeValue4365, nodeValue4369, nodeValue4474, nodeValue4968, nodeValue4970, nodeValue4974, nodeValue5041, nodeValue5043, nodeValue5085, nodeValue5147, nodeValue5185, nodeValue5189, nodeValue5202, nodeValue5203, nodeValue5266, nodeValue5301, nodeValue5369, nodeValue5469, nodeValue5473, nodeValue5474]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
