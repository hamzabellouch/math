import OAI.Analysis.MutuallyUnbiased.MixedData.Source14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values85
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1904 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4550 x + ((1 : ℝ) * Sparse.eval nodeValue4551 x + ((2 : ℝ) * Sparse.eval nodeValue4553 x + ((1 : ℝ) * Sparse.eval nodeValue4623 x + ((1 : ℝ) * Sparse.eval nodeValue4967 x + ((1 : ℝ) * Sparse.eval nodeValue4970 x + ((2 : ℝ) * Sparse.eval nodeValue4973 x + ((1 : ℝ) * Sparse.eval nodeValue5113 x + ((2 : ℝ) * Sparse.eval nodeValue5114 x + ((1 : ℝ) * Sparse.eval nodeValue5166 x + ((3 : ℝ) * Sparse.eval nodeValue5168 x + ((2 : ℝ) * Sparse.eval nodeValue5170 x + ((2 : ℝ) * Sparse.eval nodeValue5171 x + ((2 : ℝ) * Sparse.eval nodeValue5176 x + ((1 : ℝ) * Sparse.eval nodeValue5306 x + ((2 : ℝ) * Sparse.eval nodeValue5308 x + ((1 : ℝ) * Sparse.eval nodeValue5387 x + ((1 : ℝ) * Sparse.eval nodeValue5415 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((2 : ℝ) * Sparse.eval nodeValue5441 x + 0)))))))))))))))))))

def numericRow1904 : Integer.Sparse Master := [(Sum.inl 0, 106), (Sum.inl 6, 5), (Sum.inl 2, 5), (Sum.inl 7, -80), (Sum.inl 3, -80), (Sum.inl 1, 530), (Sum.inr 1135, -1080), (Sum.inr 1136, -1080), (Sum.inr 1138, -2160), (Sum.inr 2814, -1080), (Sum.inr 2815, -1080), (Sum.inr 2817, -2160), (Sum.inr 2896, -2160), (Sum.inr 2954, -2160), (Sum.inr 3269, -1080), (Sum.inr 3270, -2160), (Sum.inr 3273, -1080), (Sum.inr 3308, -1080), (Sum.inr 3585, -1080), (Sum.inr 3588, -1080), (Sum.inr 3591, -2160), (Sum.inr 3597, -2160), (Sum.inr 3603, -3240), (Sum.inr 3606, -2160), (Sum.inr 3608, -2160), (Sum.inr 3614, -2160), (Sum.inr 3623, -1080), (Sum.inr 3891, -1080), (Sum.inr 3895, -1080), (Sum.inr 3902, -1080)]

theorem reindexCheck1904 : Integer.Sparse.reindex keyMap MixedData.row1904 = numericRow1904 := by decide +kernel

theorem numericCheck1904 (x : Master → ℝ) : Integer.Sparse.eval numericRow1904 x =
    (4320 : ℝ) * reducedSource1904 x := by
  norm_num [numericRow1904, reducedSource1904, Integer.Sparse.eval, Sparse.eval, nodeValue4550, nodeValue4551, nodeValue4553, nodeValue4623, nodeValue4967, nodeValue4970, nodeValue4973, nodeValue5113, nodeValue5114, nodeValue5166, nodeValue5168, nodeValue5170, nodeValue5171, nodeValue5176, nodeValue5306, nodeValue5308, nodeValue5387, nodeValue5415, nodeValue5439, nodeValue5441]
  ring

noncomputable def reducedSource1905 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1135 x + ((1 : ℝ) * Sparse.eval nodeValue1136 x + ((2 : ℝ) * Sparse.eval nodeValue1138 x + ((1 : ℝ) * Sparse.eval nodeValue1305 x + ((1 : ℝ) * Sparse.eval nodeValue2814 x + ((1 : ℝ) * Sparse.eval nodeValue2815 x + ((2 : ℝ) * Sparse.eval nodeValue2817 x + ((1 : ℝ) * Sparse.eval nodeValue2894 x + ((2 : ℝ) * Sparse.eval nodeValue2896 x + ((1 : ℝ) * Sparse.eval nodeValue2953 x + ((2 : ℝ) * Sparse.eval nodeValue2954 x + ((3 : ℝ) * Sparse.eval nodeValue2963 x + ((2 : ℝ) * Sparse.eval nodeValue2965 x + ((2 : ℝ) * Sparse.eval nodeValue2968 x + ((1 : ℝ) * Sparse.eval nodeValue3120 x + ((2 : ℝ) * Sparse.eval nodeValue3124 x + ((1 : ℝ) * Sparse.eval nodeValue3739 x + ((1 : ℝ) * Sparse.eval nodeValue4012 x + ((1 : ℝ) * Sparse.eval nodeValue4031 x + ((2 : ℝ) * Sparse.eval nodeValue4037 x + 0)))))))))))))))))))

def numericRow1905 : Integer.Sparse Master := [(Sum.inl 0, -106), (Sum.inl 6, -5), (Sum.inl 2, -5), (Sum.inl 7, 80), (Sum.inl 3, 80), (Sum.inl 1, -530), (Sum.inr 1135, 1080), (Sum.inr 1136, 1080), (Sum.inr 1138, 2160), (Sum.inr 2814, 1080), (Sum.inr 2815, 1080), (Sum.inr 2817, 2160), (Sum.inr 2896, 2160), (Sum.inr 2954, 2160)]

theorem reindexCheck1905 : Integer.Sparse.reindex keyMap MixedData.row1905 = numericRow1905 := by decide +kernel

theorem numericCheck1905 (x : Master → ℝ) : Integer.Sparse.eval numericRow1905 x =
    (1080 : ℝ) * reducedSource1905 x := by
  norm_num [numericRow1905, reducedSource1905, Integer.Sparse.eval, Sparse.eval, nodeValue1135, nodeValue1136, nodeValue1138, nodeValue1305, nodeValue2814, nodeValue2815, nodeValue2817, nodeValue2894, nodeValue2896, nodeValue2953, nodeValue2954, nodeValue2963, nodeValue2965, nodeValue2968, nodeValue3120, nodeValue3124, nodeValue3739, nodeValue4012, nodeValue4031, nodeValue4037]
  ring

noncomputable def reducedSource1906 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4341 x + ((1 : ℝ) * Sparse.eval nodeValue4343 x + ((2 : ℝ) * Sparse.eval nodeValue4349 x + ((1 : ℝ) * Sparse.eval nodeValue4457 x + ((1 : ℝ) * Sparse.eval nodeValue4760 x + ((1 : ℝ) * Sparse.eval nodeValue4769 x + ((2 : ℝ) * Sparse.eval nodeValue4804 x + ((1 : ℝ) * Sparse.eval nodeValue4939 x + ((2 : ℝ) * Sparse.eval nodeValue4946 x + ((2 : ℝ) * Sparse.eval nodeValue5036 x + ((1 : ℝ) * Sparse.eval nodeValue5072 x + ((2 : ℝ) * Sparse.eval nodeValue5134 x + ((2 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5167 x + ((2 : ℝ) * Sparse.eval nodeValue5169 x + ((2 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5416 x + ((1 : ℝ) * Sparse.eval nodeValue5418 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5486 x + 0))))))))))))))))))))

def numericRow1906 : Integer.Sparse Master := [(Sum.inl 0, 38), (Sum.inl 6, 1), (Sum.inl 2, 1), (Sum.inl 7, -16), (Sum.inl 3, -16), (Sum.inl 1, -26), (Sum.inr 919, -432), (Sum.inr 921, -432), (Sum.inr 927, -864), (Sum.inr 1040, -432), (Sum.inr 1664, -432), (Sum.inr 1666, -432), (Sum.inr 1675, -864), (Sum.inr 1707, -432), (Sum.inr 1960, -432), (Sum.inr 1969, -432), (Sum.inr 2022, -864), (Sum.inr 2173, -432), (Sum.inr 2185, -432), (Sum.inr 2203, -864), (Sum.inr 2330, -432), (Sum.inr 2337, -864), (Sum.inr 2428, -864), (Sum.inr 2479, -432), (Sum.inr 2553, -864), (Sum.inr 2561, -864), (Sum.inr 2722, -864), (Sum.inr 3404, -432), (Sum.inr 3412, -864), (Sum.inr 3450, -864), (Sum.inr 3459, -432), (Sum.inr 3514, -864), (Sum.inr 3522, -864), (Sum.inr 3533, -864), (Sum.inr 3602, -432), (Sum.inr 3607, -864), (Sum.inr 3622, -432), (Sum.inr 3896, -432), (Sum.inr 3898, -432), (Sum.inr 3903, -864)]

theorem reindexCheck1906 : Integer.Sparse.reindex keyMap MixedData.row1906 = numericRow1906 := by decide +kernel

theorem numericCheck1906 (x : Master → ℝ) : Integer.Sparse.eval numericRow1906 x =
    (1728 : ℝ) * reducedSource1906 x := by
  norm_num [numericRow1906, reducedSource1906, Integer.Sparse.eval, Sparse.eval, nodeValue4341, nodeValue4343, nodeValue4349, nodeValue4457, nodeValue4760, nodeValue4769, nodeValue4804, nodeValue4939, nodeValue4946, nodeValue5036, nodeValue5072, nodeValue5134, nodeValue5141, nodeValue5167, nodeValue5169, nodeValue5258, nodeValue5292, nodeValue5416, nodeValue5418, nodeValue5434, nodeValue5486]
  ring

noncomputable def reducedSource1907 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue919 x + ((1 : ℝ) * Sparse.eval nodeValue921 x + ((2 : ℝ) * Sparse.eval nodeValue927 x + ((1 : ℝ) * Sparse.eval nodeValue1040 x + ((1 : ℝ) * Sparse.eval nodeValue1960 x + ((1 : ℝ) * Sparse.eval nodeValue1969 x + ((2 : ℝ) * Sparse.eval nodeValue2022 x + ((1 : ℝ) * Sparse.eval nodeValue2330 x + ((2 : ℝ) * Sparse.eval nodeValue2337 x + ((2 : ℝ) * Sparse.eval nodeValue2428 x + ((1 : ℝ) * Sparse.eval nodeValue2479 x + ((2 : ℝ) * Sparse.eval nodeValue2553 x + ((2 : ℝ) * Sparse.eval nodeValue2561 x + ((1 : ℝ) * Sparse.eval nodeValue2593 x + ((2 : ℝ) * Sparse.eval nodeValue2595 x + ((2 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue2766 x + ((1 : ℝ) * Sparse.eval nodeValue3821 x + ((1 : ℝ) * Sparse.eval nodeValue3824 x + ((2 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3999 x + 0))))))))))))))))))))

def numericRow1907 : Integer.Sparse Master := [(Sum.inl 0, -38), (Sum.inl 6, -1), (Sum.inl 2, -1), (Sum.inl 7, 16), (Sum.inl 3, 16), (Sum.inl 1, 26), (Sum.inr 919, 432), (Sum.inr 921, 432), (Sum.inr 927, 864), (Sum.inr 1040, 432), (Sum.inr 1960, 432), (Sum.inr 1969, 432), (Sum.inr 2022, 864), (Sum.inr 2330, 432), (Sum.inr 2337, 864), (Sum.inr 2428, 864), (Sum.inr 2479, 432), (Sum.inr 2553, 864), (Sum.inr 2561, 864), (Sum.inr 2722, 864)]

theorem reindexCheck1907 : Integer.Sparse.reindex keyMap MixedData.row1907 = numericRow1907 := by decide +kernel

theorem numericCheck1907 (x : Master → ℝ) : Integer.Sparse.eval numericRow1907 x =
    (432 : ℝ) * reducedSource1907 x := by
  norm_num [numericRow1907, reducedSource1907, Integer.Sparse.eval, Sparse.eval, nodeValue919, nodeValue921, nodeValue927, nodeValue1040, nodeValue1960, nodeValue1969, nodeValue2022, nodeValue2330, nodeValue2337, nodeValue2428, nodeValue2479, nodeValue2553, nodeValue2561, nodeValue2593, nodeValue2595, nodeValue2722, nodeValue2766, nodeValue3821, nodeValue3824, nodeValue3852, nodeValue3999]
  ring

noncomputable def reducedSource1908 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4544 x + ((1 : ℝ) * Sparse.eval nodeValue4546 x + ((1 : ℝ) * Sparse.eval nodeValue4549 x + ((1 : ℝ) * Sparse.eval nodeValue4554 x + ((1 : ℝ) * Sparse.eval nodeValue4624 x + ((1 : ℝ) * Sparse.eval nodeValue4968 x + ((1 : ℝ) * Sparse.eval nodeValue4972 x + ((1 : ℝ) * Sparse.eval nodeValue4974 x + ((1 : ℝ) * Sparse.eval nodeValue4977 x + ((1 : ℝ) * Sparse.eval nodeValue5037 x + ((1 : ℝ) * Sparse.eval nodeValue5078 x + ((1 : ℝ) * Sparse.eval nodeValue5115 x + ((1 : ℝ) * Sparse.eval nodeValue5117 x + ((1 : ℝ) * Sparse.eval nodeValue5148 x + ((1 : ℝ) * Sparse.eval nodeValue5152 x + ((1 : ℝ) * Sparse.eval nodeValue5167 x + ((3 : ℝ) * Sparse.eval nodeValue5169 x + ((1 : ℝ) * Sparse.eval nodeValue5172 x + ((1 : ℝ) * Sparse.eval nodeValue5174 x + ((1 : ℝ) * Sparse.eval nodeValue5177 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5307 x + ((1 : ℝ) * Sparse.eval nodeValue5309 x + ((1 : ℝ) * Sparse.eval nodeValue5388 x + ((1 : ℝ) * Sparse.eval nodeValue5416 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5440 x + ((1 : ℝ) * Sparse.eval nodeValue5442 x + 0)))))))))))))))))))))))))))

def numericRow1908 : Integer.Sparse Master := [(Sum.inl 0, 133), (Sum.inl 6, 5), (Sum.inl 2, -30), (Sum.inl 8, -80), (Sum.inl 1, -160), (Sum.inr 1129, -1080), (Sum.inr 1131, -1080), (Sum.inr 1134, -1080), (Sum.inr 1139, -1080), (Sum.inr 2429, -1080), (Sum.inr 2434, -1080), (Sum.inr 2485, -1080), (Sum.inr 2809, -1080), (Sum.inr 2813, -1080), (Sum.inr 2818, -1080), (Sum.inr 2893, -1080), (Sum.inr 2931, -1080), (Sum.inr 3263, -1080), (Sum.inr 3264, -1080), (Sum.inr 3265, -1080), (Sum.inr 3274, -1080), (Sum.inr 3309, -1080), (Sum.inr 3455, -1080), (Sum.inr 3457, -1080), (Sum.inr 3481, -1080), (Sum.inr 3587, -1080), (Sum.inr 3592, -1080), (Sum.inr 3595, -1080), (Sum.inr 3599, -1080), (Sum.inr 3602, -1080), (Sum.inr 3607, -3240), (Sum.inr 3612, -1080), (Sum.inr 3613, -1080), (Sum.inr 3615, -1080), (Sum.inr 3616, -1080), (Sum.inr 3627, -1080), (Sum.inr 3892, -1080), (Sum.inr 3896, -1080), (Sum.inr 3903, -1080)]

theorem reindexCheck1908 : Integer.Sparse.reindex keyMap MixedData.row1908 = numericRow1908 := by decide +kernel

theorem numericCheck1908 (x : Master → ℝ) : Integer.Sparse.eval numericRow1908 x =
    (4320 : ℝ) * reducedSource1908 x := by
  norm_num [numericRow1908, reducedSource1908, Integer.Sparse.eval, Sparse.eval, nodeValue4544, nodeValue4546, nodeValue4549, nodeValue4554, nodeValue4624, nodeValue4968, nodeValue4972, nodeValue4974, nodeValue4977, nodeValue5037, nodeValue5078, nodeValue5115, nodeValue5117, nodeValue5148, nodeValue5152, nodeValue5167, nodeValue5169, nodeValue5172, nodeValue5174, nodeValue5177, nodeValue5293, nodeValue5307, nodeValue5309, nodeValue5388, nodeValue5416, nodeValue5434, nodeValue5440, nodeValue5442]
  ring

noncomputable def reducedSource1909 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1129 x + ((1 : ℝ) * Sparse.eval nodeValue1131 x + ((1 : ℝ) * Sparse.eval nodeValue1134 x + ((1 : ℝ) * Sparse.eval nodeValue1139 x + ((1 : ℝ) * Sparse.eval nodeValue1301 x + ((1 : ℝ) * Sparse.eval nodeValue2429 x + ((1 : ℝ) * Sparse.eval nodeValue2434 x + ((1 : ℝ) * Sparse.eval nodeValue2485 x + ((1 : ℝ) * Sparse.eval nodeValue2601 x + ((1 : ℝ) * Sparse.eval nodeValue2809 x + ((1 : ℝ) * Sparse.eval nodeValue2813 x + ((1 : ℝ) * Sparse.eval nodeValue2818 x + ((1 : ℝ) * Sparse.eval nodeValue2893 x + ((1 : ℝ) * Sparse.eval nodeValue2897 x + ((1 : ℝ) * Sparse.eval nodeValue2927 x + ((1 : ℝ) * Sparse.eval nodeValue2931 x + ((1 : ℝ) * Sparse.eval nodeValue2958 x + ((1 : ℝ) * Sparse.eval nodeValue2959 x + ((3 : ℝ) * Sparse.eval nodeValue2960 x + ((1 : ℝ) * Sparse.eval nodeValue2969 x + ((1 : ℝ) * Sparse.eval nodeValue3102 x + ((1 : ℝ) * Sparse.eval nodeValue3122 x + ((1 : ℝ) * Sparse.eval nodeValue3123 x + ((1 : ℝ) * Sparse.eval nodeValue3737 x + ((1 : ℝ) * Sparse.eval nodeValue3967 x + ((1 : ℝ) * Sparse.eval nodeValue3982 x + ((1 : ℝ) * Sparse.eval nodeValue4001 x + ((1 : ℝ) * Sparse.eval nodeValue4036 x + 0)))))))))))))))))))))))))))

def numericRow1909 : Integer.Sparse Master := [(Sum.inl 0, -133), (Sum.inl 6, -5), (Sum.inl 2, 30), (Sum.inl 8, 80), (Sum.inl 1, 160), (Sum.inr 1129, 1080), (Sum.inr 1131, 1080), (Sum.inr 1134, 1080), (Sum.inr 1139, 1080), (Sum.inr 2429, 1080), (Sum.inr 2434, 1080), (Sum.inr 2485, 1080), (Sum.inr 2809, 1080), (Sum.inr 2813, 1080), (Sum.inr 2818, 1080), (Sum.inr 2893, 1080), (Sum.inr 2931, 1080)]

theorem reindexCheck1909 : Integer.Sparse.reindex keyMap MixedData.row1909 = numericRow1909 := by decide +kernel

theorem numericCheck1909 (x : Master → ℝ) : Integer.Sparse.eval numericRow1909 x =
    (1080 : ℝ) * reducedSource1909 x := by
  norm_num [numericRow1909, reducedSource1909, Integer.Sparse.eval, Sparse.eval, nodeValue1129, nodeValue1131, nodeValue1134, nodeValue1139, nodeValue1301, nodeValue2429, nodeValue2434, nodeValue2485, nodeValue2601, nodeValue2809, nodeValue2813, nodeValue2818, nodeValue2893, nodeValue2897, nodeValue2927, nodeValue2931, nodeValue2958, nodeValue2959, nodeValue2960, nodeValue2969, nodeValue3102, nodeValue3122, nodeValue3123, nodeValue3737, nodeValue3967, nodeValue3982, nodeValue4001, nodeValue4036]
  ring

noncomputable def reducedSource1910 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4344 x + ((1 : ℝ) * Sparse.eval nodeValue4346 x + ((1 : ℝ) * Sparse.eval nodeValue4349 x + ((1 : ℝ) * Sparse.eval nodeValue4355 x + ((1 : ℝ) * Sparse.eval nodeValue4458 x + ((1 : ℝ) * Sparse.eval nodeValue4941 x + ((1 : ℝ) * Sparse.eval nodeValue4943 x + ((1 : ℝ) * Sparse.eval nodeValue4946 x + ((1 : ℝ) * Sparse.eval nodeValue4950 x + ((1 : ℝ) * Sparse.eval nodeValue5033 x + ((1 : ℝ) * Sparse.eval nodeValue5036 x + ((1 : ℝ) * Sparse.eval nodeValue5039 x + ((1 : ℝ) * Sparse.eval nodeValue5073 x + ((1 : ℝ) * Sparse.eval nodeValue5075 x + ((1 : ℝ) * Sparse.eval nodeValue5137 x + ((1 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5167 x + ((1 : ℝ) * Sparse.eval nodeValue5168 x + ((2 : ℝ) * Sparse.eval nodeValue5169 x + ((1 : ℝ) * Sparse.eval nodeValue5171 x + ((1 : ℝ) * Sparse.eval nodeValue5177 x + ((1 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5465 x + ((1 : ℝ) * Sparse.eval nodeValue5476 x + ((1 : ℝ) * Sparse.eval nodeValue5483 x + ((1 : ℝ) * Sparse.eval nodeValue5486 x + ((1 : ℝ) * Sparse.eval nodeValue5487 x + 0))))))))))))))))))))))))))))

def numericRow1910 : Integer.Sparse Master := [(Sum.inl 0, 181), (Sum.inl 6, 5), (Sum.inl 2, -30), (Sum.inl 8, -80), (Sum.inl 1, 80), (Sum.inr 922, -1440), (Sum.inr 924, -1440), (Sum.inr 927, -1440), (Sum.inr 933, -1440), (Sum.inr 1041, -1440), (Sum.inr 1673, -1440), (Sum.inr 1674, -1440), (Sum.inr 1675, -1440), (Sum.inr 1691, -1440), (Sum.inr 1724, -1440), (Sum.inr 2332, -1440), (Sum.inr 2334, -1440), (Sum.inr 2337, -1440), (Sum.inr 2342, -1440), (Sum.inr 2425, -1440), (Sum.inr 2428, -1440), (Sum.inr 2432, -1440), (Sum.inr 2480, -1440), (Sum.inr 2482, -1440), (Sum.inr 2556, -1440), (Sum.inr 2561, -1440), (Sum.inr 2723, -1440), (Sum.inr 3410, -1440), (Sum.inr 3411, -1440), (Sum.inr 3412, -1440), (Sum.inr 3421, -1440), (Sum.inr 3449, -1440), (Sum.inr 3450, -1440), (Sum.inr 3456, -1440), (Sum.inr 3467, -1440), (Sum.inr 3468, -1440), (Sum.inr 3521, -1440), (Sum.inr 3522, -1440), (Sum.inr 3544, -1440), (Sum.inr 3602, -1440), (Sum.inr 3603, -1440), (Sum.inr 3607, -2880), (Sum.inr 3608, -1440), (Sum.inr 3616, -1440), (Sum.inr 3622, -1440), (Sum.inr 3627, -1440), (Sum.inr 4042, -1440), (Sum.inr 4045, -1440), (Sum.inr 4047, -1440)]

theorem reindexCheck1910 : Integer.Sparse.reindex keyMap MixedData.row1910 = numericRow1910 := by decide +kernel

theorem numericCheck1910 (x : Master → ℝ) : Integer.Sparse.eval numericRow1910 x =
    (5760 : ℝ) * reducedSource1910 x := by
  norm_num [numericRow1910, reducedSource1910, Integer.Sparse.eval, Sparse.eval, nodeValue4344, nodeValue4346, nodeValue4349, nodeValue4355, nodeValue4458, nodeValue4941, nodeValue4943, nodeValue4946, nodeValue4950, nodeValue5033, nodeValue5036, nodeValue5039, nodeValue5073, nodeValue5075, nodeValue5137, nodeValue5141, nodeValue5167, nodeValue5168, nodeValue5169, nodeValue5171, nodeValue5177, nodeValue5259, nodeValue5292, nodeValue5293, nodeValue5465, nodeValue5476, nodeValue5483, nodeValue5486, nodeValue5487]
  ring

noncomputable def reducedSource1911 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue922 x + ((1 : ℝ) * Sparse.eval nodeValue924 x + ((1 : ℝ) * Sparse.eval nodeValue927 x + ((1 : ℝ) * Sparse.eval nodeValue933 x + ((1 : ℝ) * Sparse.eval nodeValue1041 x + ((1 : ℝ) * Sparse.eval nodeValue2332 x + ((1 : ℝ) * Sparse.eval nodeValue2334 x + ((1 : ℝ) * Sparse.eval nodeValue2337 x + ((1 : ℝ) * Sparse.eval nodeValue2342 x + ((1 : ℝ) * Sparse.eval nodeValue2425 x + ((1 : ℝ) * Sparse.eval nodeValue2428 x + ((1 : ℝ) * Sparse.eval nodeValue2432 x + ((1 : ℝ) * Sparse.eval nodeValue2480 x + ((1 : ℝ) * Sparse.eval nodeValue2482 x + ((1 : ℝ) * Sparse.eval nodeValue2556 x + ((1 : ℝ) * Sparse.eval nodeValue2561 x + ((1 : ℝ) * Sparse.eval nodeValue2593 x + ((1 : ℝ) * Sparse.eval nodeValue2594 x + ((2 : ℝ) * Sparse.eval nodeValue2595 x + ((1 : ℝ) * Sparse.eval nodeValue2598 x + ((1 : ℝ) * Sparse.eval nodeValue2605 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2766 x + ((1 : ℝ) * Sparse.eval nodeValue2767 x + ((1 : ℝ) * Sparse.eval nodeValue3931 x + ((1 : ℝ) * Sparse.eval nodeValue3965 x + ((1 : ℝ) * Sparse.eval nodeValue3981 x + ((1 : ℝ) * Sparse.eval nodeValue3999 x + ((1 : ℝ) * Sparse.eval nodeValue4000 x + 0))))))))))))))))))))))))))))

def numericRow1911 : Integer.Sparse Master := [(Sum.inl 0, -181), (Sum.inl 6, -5), (Sum.inl 2, 30), (Sum.inl 8, 80), (Sum.inl 1, -80), (Sum.inr 922, 1440), (Sum.inr 924, 1440), (Sum.inr 927, 1440), (Sum.inr 933, 1440), (Sum.inr 1041, 1440), (Sum.inr 2332, 1440), (Sum.inr 2334, 1440), (Sum.inr 2337, 1440), (Sum.inr 2342, 1440), (Sum.inr 2425, 1440), (Sum.inr 2428, 1440), (Sum.inr 2432, 1440), (Sum.inr 2480, 1440), (Sum.inr 2482, 1440), (Sum.inr 2556, 1440), (Sum.inr 2561, 1440), (Sum.inr 2723, 1440)]

theorem reindexCheck1911 : Integer.Sparse.reindex keyMap MixedData.row1911 = numericRow1911 := by decide +kernel

theorem numericCheck1911 (x : Master → ℝ) : Integer.Sparse.eval numericRow1911 x =
    (1440 : ℝ) * reducedSource1911 x := by
  norm_num [numericRow1911, reducedSource1911, Integer.Sparse.eval, Sparse.eval, nodeValue922, nodeValue924, nodeValue927, nodeValue933, nodeValue1041, nodeValue2332, nodeValue2334, nodeValue2337, nodeValue2342, nodeValue2425, nodeValue2428, nodeValue2432, nodeValue2480, nodeValue2482, nodeValue2556, nodeValue2561, nodeValue2593, nodeValue2594, nodeValue2595, nodeValue2598, nodeValue2605, nodeValue2723, nodeValue2766, nodeValue2767, nodeValue3931, nodeValue3965, nodeValue3981, nodeValue3999, nodeValue4000]
  ring

noncomputable def reducedSource1912 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4345 x + ((1 : ℝ) * Sparse.eval nodeValue4347 x + ((1 : ℝ) * Sparse.eval nodeValue4348 x + ((1 : ℝ) * Sparse.eval nodeValue4357 x + ((1 : ℝ) * Sparse.eval nodeValue4459 x + ((1 : ℝ) * Sparse.eval nodeValue4942 x + ((1 : ℝ) * Sparse.eval nodeValue4944 x + ((1 : ℝ) * Sparse.eval nodeValue4945 x + ((1 : ℝ) * Sparse.eval nodeValue4951 x + ((1 : ℝ) * Sparse.eval nodeValue5034 x + ((1 : ℝ) * Sparse.eval nodeValue5035 x + ((1 : ℝ) * Sparse.eval nodeValue5040 x + ((1 : ℝ) * Sparse.eval nodeValue5074 x + ((1 : ℝ) * Sparse.eval nodeValue5078 x + ((1 : ℝ) * Sparse.eval nodeValue5138 x + ((1 : ℝ) * Sparse.eval nodeValue5139 x + ((1 : ℝ) * Sparse.eval nodeValue5140 x + ((1 : ℝ) * Sparse.eval nodeValue5149 x + ((1 : ℝ) * Sparse.eval nodeValue5152 x + ((1 : ℝ) * Sparse.eval nodeValue5160 x + ((1 : ℝ) * Sparse.eval nodeValue5161 x + ((1 : ℝ) * Sparse.eval nodeValue5164 x + ((1 : ℝ) * Sparse.eval nodeValue5260 x + ((1 : ℝ) * Sparse.eval nodeValue5284 x + ((1 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5401 x + ((1 : ℝ) * Sparse.eval nodeValue5404 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5484 x + 0)))))))))))))))))))))))))))))

def numericRow1912 : Integer.Sparse Master := [(Sum.inr 2485, -1), (Sum.inr 2924, -1), (Sum.inr 2931, -1), (Sum.inr 3077, -1), (Sum.inr 3481, -1), (Sum.inr 3605, -1), (Sum.inr 3612, -1), (Sum.inr 3625, -1), (Sum.inr 3787, -1), (Sum.inr 3790, -1), (Sum.inr 3804, -1), (Sum.inr 3815, -1), (Sum.inr 3857, -1), (Sum.inr 3876, -1), (Sum.inr 3983, -2), (Sum.inr 4345, 4), (Sum.inr 4347, 4), (Sum.inr 4348, 4), (Sum.inr 4357, 4), (Sum.inr 4459, 4), (Sum.inr 4942, 4), (Sum.inr 4944, 4), (Sum.inr 4945, 4), (Sum.inr 4951, 4), (Sum.inr 5034, 4), (Sum.inr 5035, 4), (Sum.inr 5040, 4), (Sum.inr 5074, 4), (Sum.inr 5138, 4), (Sum.inr 5139, 4), (Sum.inr 5140, 4), (Sum.inr 5160, 4), (Sum.inr 5161, 4), (Sum.inr 5164, 4), (Sum.inr 5260, 4), (Sum.inr 5289, 4)]

theorem reindexCheck1912 : Integer.Sparse.reindex keyMap MixedData.row1912 = numericRow1912 := by decide +kernel

theorem numericCheck1912 (x : Master → ℝ) : Integer.Sparse.eval numericRow1912 x =
    (4 : ℝ) * reducedSource1912 x := by
  norm_num [numericRow1912, reducedSource1912, Integer.Sparse.eval, Sparse.eval, nodeValue4345, nodeValue4347, nodeValue4348, nodeValue4357, nodeValue4459, nodeValue4942, nodeValue4944, nodeValue4945, nodeValue4951, nodeValue5034, nodeValue5035, nodeValue5040, nodeValue5074, nodeValue5078, nodeValue5138, nodeValue5139, nodeValue5140, nodeValue5149, nodeValue5152, nodeValue5160, nodeValue5161, nodeValue5164, nodeValue5260, nodeValue5284, nodeValue5289, nodeValue5401, nodeValue5404, nodeValue5410, nodeValue5438, nodeValue5484]
  ring

noncomputable def reducedSource1913 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1668 x + ((1 : ℝ) * Sparse.eval nodeValue1669 x + ((1 : ℝ) * Sparse.eval nodeValue1676 x + ((1 : ℝ) * Sparse.eval nodeValue1682 x + ((1 : ℝ) * Sparse.eval nodeValue1714 x + ((1 : ℝ) * Sparse.eval nodeValue2652 x + ((1 : ℝ) * Sparse.eval nodeValue2658 x + ((1 : ℝ) * Sparse.eval nodeValue2670 x + ((1 : ℝ) * Sparse.eval nodeValue2719 x + ((1 : ℝ) * Sparse.eval nodeValue3407 x + ((1 : ℝ) * Sparse.eval nodeValue3413 x + ((1 : ℝ) * Sparse.eval nodeValue3418 x + ((1 : ℝ) * Sparse.eval nodeValue3451 x + ((1 : ℝ) * Sparse.eval nodeValue3454 x + ((1 : ℝ) * Sparse.eval nodeValue3463 x + ((1 : ℝ) * Sparse.eval nodeValue3481 x + ((1 : ℝ) * Sparse.eval nodeValue3517 x + ((1 : ℝ) * Sparse.eval nodeValue3523 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3558 x + ((1 : ℝ) * Sparse.eval nodeValue3565 x + ((1 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3605 x + ((1 : ℝ) * Sparse.eval nodeValue3612 x + ((1 : ℝ) * Sparse.eval nodeValue3625 x + ((1 : ℝ) * Sparse.eval nodeValue3804 x + ((1 : ℝ) * Sparse.eval nodeValue3815 x + ((1 : ℝ) * Sparse.eval nodeValue3816 x + ((1 : ℝ) * Sparse.eval nodeValue3857 x + ((1 : ℝ) * Sparse.eval nodeValue3983 x + 0)))))))))))))))))))))))))))))

def numericRow1913 : Integer.Sparse Master := [(Sum.inr 1668, 1), (Sum.inr 1669, 1), (Sum.inr 1676, 1), (Sum.inr 1682, 1), (Sum.inr 1714, 1), (Sum.inr 2652, 1), (Sum.inr 2658, 1), (Sum.inr 2670, 1), (Sum.inr 2719, 1), (Sum.inr 3407, 1), (Sum.inr 3413, 1), (Sum.inr 3418, 1), (Sum.inr 3451, 1), (Sum.inr 3454, 1), (Sum.inr 3463, 1), (Sum.inr 3481, 1), (Sum.inr 3517, 1), (Sum.inr 3523, 1), (Sum.inr 3540, 1), (Sum.inr 3558, 1), (Sum.inr 3565, 1), (Sum.inr 3572, 1), (Sum.inr 3605, 1), (Sum.inr 3612, 1), (Sum.inr 3625, 1), (Sum.inr 3804, 1), (Sum.inr 3815, 1), (Sum.inr 3857, 1), (Sum.inr 3983, 1)]

theorem reindexCheck1913 : Integer.Sparse.reindex keyMap MixedData.row1913 = numericRow1913 := by decide +kernel

theorem numericCheck1913 (x : Master → ℝ) : Integer.Sparse.eval numericRow1913 x =
    (1 : ℝ) * reducedSource1913 x := by
  norm_num [numericRow1913, reducedSource1913, Integer.Sparse.eval, Sparse.eval, nodeValue1668, nodeValue1669, nodeValue1676, nodeValue1682, nodeValue1714, nodeValue2652, nodeValue2658, nodeValue2670, nodeValue2719, nodeValue3407, nodeValue3413, nodeValue3418, nodeValue3451, nodeValue3454, nodeValue3463, nodeValue3481, nodeValue3517, nodeValue3523, nodeValue3540, nodeValue3558, nodeValue3565, nodeValue3572, nodeValue3605, nodeValue3612, nodeValue3625, nodeValue3804, nodeValue3815, nodeValue3816, nodeValue3857, nodeValue3983]

noncomputable def reducedSource1914 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4541 x + ((1 : ℝ) * Sparse.eval nodeValue4543 x + ((2 : ℝ) * Sparse.eval nodeValue4549 x + ((1 : ℝ) * Sparse.eval nodeValue4623 x + ((1 : ℝ) * Sparse.eval nodeValue4764 x + ((1 : ℝ) * Sparse.eval nodeValue4770 x + ((2 : ℝ) * Sparse.eval nodeValue4807 x + ((1 : ℝ) * Sparse.eval nodeValue4971 x + ((2 : ℝ) * Sparse.eval nodeValue4977 x + ((2 : ℝ) * Sparse.eval nodeValue5117 x + ((2 : ℝ) * Sparse.eval nodeValue5149 x + ((2 : ℝ) * Sparse.eval nodeValue5152 x + ((1 : ℝ) * Sparse.eval nodeValue5167 x + ((2 : ℝ) * Sparse.eval nodeValue5169 x + ((1 : ℝ) * Sparse.eval nodeValue5172 x + ((2 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5307 x + ((1 : ℝ) * Sparse.eval nodeValue5387 x + ((1 : ℝ) * Sparse.eval nodeValue5417 x + ((2 : ℝ) * Sparse.eval nodeValue5435 x + ((1 : ℝ) * Sparse.eval nodeValue5440 x + 0))))))))))))))))))))

def numericRow1914 : Integer.Sparse Master := [(Sum.inl 0, 143), (Sum.inl 6, 5), (Sum.inl 2, -50), (Sum.inl 7, -80), (Sum.inl 3, -160), (Sum.inl 1, -110), (Sum.inr 1126, -1440), (Sum.inr 1128, -1440), (Sum.inr 1134, -2880), (Sum.inr 1964, -1440), (Sum.inr 1970, -1440), (Sum.inr 2025, -2880), (Sum.inr 2182, -1440), (Sum.inr 2184, -1440), (Sum.inr 2186, -1440), (Sum.inr 2224, -2880), (Sum.inr 2807, -1440), (Sum.inr 2813, -2880), (Sum.inr 2893, -2880), (Sum.inr 2924, -2880), (Sum.inr 2931, -2880), (Sum.inr 3256, -1440), (Sum.inr 3265, -2880), (Sum.inr 3308, -1440), (Sum.inr 3590, -1440), (Sum.inr 3595, -2880), (Sum.inr 3599, -2880), (Sum.inr 3602, -1440), (Sum.inr 3605, -2880), (Sum.inr 3607, -2880), (Sum.inr 3612, -2880), (Sum.inr 3613, -1440), (Sum.inr 3632, -2880), (Sum.inr 3891, -1440), (Sum.inr 3897, -1440), (Sum.inr 3906, -2880)]

theorem reindexCheck1914 : Integer.Sparse.reindex keyMap MixedData.row1914 = numericRow1914 := by decide +kernel

theorem numericCheck1914 (x : Master → ℝ) : Integer.Sparse.eval numericRow1914 x =
    (5760 : ℝ) * reducedSource1914 x := by
  norm_num [numericRow1914, reducedSource1914, Integer.Sparse.eval, Sparse.eval, nodeValue4541, nodeValue4543, nodeValue4549, nodeValue4623, nodeValue4764, nodeValue4770, nodeValue4807, nodeValue4971, nodeValue4977, nodeValue5117, nodeValue5149, nodeValue5152, nodeValue5167, nodeValue5169, nodeValue5172, nodeValue5294, nodeValue5307, nodeValue5387, nodeValue5417, nodeValue5435, nodeValue5440]
  ring

noncomputable def reducedSource1915 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1126 x + ((1 : ℝ) * Sparse.eval nodeValue1128 x + ((2 : ℝ) * Sparse.eval nodeValue1134 x + ((1 : ℝ) * Sparse.eval nodeValue1300 x + ((1 : ℝ) * Sparse.eval nodeValue1964 x + ((1 : ℝ) * Sparse.eval nodeValue1970 x + ((2 : ℝ) * Sparse.eval nodeValue2025 x + ((1 : ℝ) * Sparse.eval nodeValue2807 x + ((2 : ℝ) * Sparse.eval nodeValue2813 x + ((2 : ℝ) * Sparse.eval nodeValue2893 x + ((2 : ℝ) * Sparse.eval nodeValue2924 x + ((2 : ℝ) * Sparse.eval nodeValue2931 x + ((1 : ℝ) * Sparse.eval nodeValue2958 x + ((1 : ℝ) * Sparse.eval nodeValue2959 x + ((2 : ℝ) * Sparse.eval nodeValue2960 x + ((2 : ℝ) * Sparse.eval nodeValue3101 x + ((1 : ℝ) * Sparse.eval nodeValue3122 x + ((1 : ℝ) * Sparse.eval nodeValue3736 x + ((1 : ℝ) * Sparse.eval nodeValue3823 x + ((2 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue4036 x + 0))))))))))))))))))))

def numericRow1915 : Integer.Sparse Master := [(Sum.inl 0, -143), (Sum.inl 6, -5), (Sum.inl 2, 50), (Sum.inl 7, 80), (Sum.inl 3, 160), (Sum.inl 1, 110), (Sum.inr 1126, 1440), (Sum.inr 1128, 1440), (Sum.inr 1134, 2880), (Sum.inr 1964, 1440), (Sum.inr 1970, 1440), (Sum.inr 2025, 2880), (Sum.inr 2807, 1440), (Sum.inr 2813, 2880), (Sum.inr 2893, 2880), (Sum.inr 2924, 2880), (Sum.inr 2931, 2880)]

theorem reindexCheck1915 : Integer.Sparse.reindex keyMap MixedData.row1915 = numericRow1915 := by decide +kernel

theorem numericCheck1915 (x : Master → ℝ) : Integer.Sparse.eval numericRow1915 x =
    (1440 : ℝ) * reducedSource1915 x := by
  norm_num [numericRow1915, reducedSource1915, Integer.Sparse.eval, Sparse.eval, nodeValue1126, nodeValue1128, nodeValue1134, nodeValue1300, nodeValue1964, nodeValue1970, nodeValue2025, nodeValue2807, nodeValue2813, nodeValue2893, nodeValue2924, nodeValue2931, nodeValue2958, nodeValue2959, nodeValue2960, nodeValue3101, nodeValue3122, nodeValue3736, nodeValue3823, nodeValue3853, nodeValue4036]
  ring

noncomputable def reducedSource1916 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4351 x + ((1 : ℝ) * Sparse.eval nodeValue4352 x + ((2 : ℝ) * Sparse.eval nodeValue4354 x + ((1 : ℝ) * Sparse.eval nodeValue4461 x + ((1 : ℝ) * Sparse.eval nodeValue4947 x + ((1 : ℝ) * Sparse.eval nodeValue4948 x + ((2 : ℝ) * Sparse.eval nodeValue4949 x + ((1 : ℝ) * Sparse.eval nodeValue5037 x + ((2 : ℝ) * Sparse.eval nodeValue5038 x + ((1 : ℝ) * Sparse.eval nodeValue5076 x + ((1 : ℝ) * Sparse.eval nodeValue5162 x + ((2 : ℝ) * Sparse.eval nodeValue5163 x + ((2 : ℝ) * Sparse.eval nodeValue5172 x + ((2 : ℝ) * Sparse.eval nodeValue5174 x + ((2 : ℝ) * Sparse.eval nodeValue5176 x + ((1 : ℝ) * Sparse.eval nodeValue5290 x + ((2 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5416 x + ((1 : ℝ) * Sparse.eval nodeValue5418 x + ((2 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + 0))))))))))))))))))))

def numericRow1916 : Integer.Sparse Master := [(Sum.inl 0, 143), (Sum.inl 6, 5), (Sum.inl 2, -50), (Sum.inl 7, -80), (Sum.inl 3, -160), (Sum.inl 1, -110), (Sum.inr 929, -1440), (Sum.inr 930, -1440), (Sum.inr 932, -2880), (Sum.inr 1044, -1440), (Sum.inr 1680, -1440), (Sum.inr 1681, -2880), (Sum.inr 1690, -1440), (Sum.inr 1737, -1440), (Sum.inr 2338, -1440), (Sum.inr 2339, -1440), (Sum.inr 2341, -2880), (Sum.inr 2429, -1440), (Sum.inr 2431, -2880), (Sum.inr 2483, -1440), (Sum.inr 2589, -1440), (Sum.inr 2590, -2880), (Sum.inr 2764, -1440), (Sum.inr 3416, -1440), (Sum.inr 3417, -2880), (Sum.inr 3420, -1440), (Sum.inr 3453, -2880), (Sum.inr 3455, -1440), (Sum.inr 3477, -1440), (Sum.inr 3563, -1440), (Sum.inr 3564, -2880), (Sum.inr 3581, -1440), (Sum.inr 3613, -2880), (Sum.inr 3614, -2880), (Sum.inr 3615, -2880), (Sum.inr 3632, -2880), (Sum.inr 3896, -1440), (Sum.inr 3898, -1440), (Sum.inr 4010, -1440)]

theorem reindexCheck1916 : Integer.Sparse.reindex keyMap MixedData.row1916 = numericRow1916 := by decide +kernel

theorem numericCheck1916 (x : Master → ℝ) : Integer.Sparse.eval numericRow1916 x =
    (5760 : ℝ) * reducedSource1916 x := by
  norm_num [numericRow1916, reducedSource1916, Integer.Sparse.eval, Sparse.eval, nodeValue4351, nodeValue4352, nodeValue4354, nodeValue4461, nodeValue4947, nodeValue4948, nodeValue4949, nodeValue5037, nodeValue5038, nodeValue5076, nodeValue5162, nodeValue5163, nodeValue5172, nodeValue5174, nodeValue5176, nodeValue5290, nodeValue5294, nodeValue5416, nodeValue5418, nodeValue5442, nodeValue5485]
  ring

noncomputable def reducedSource1917 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue929 x + ((1 : ℝ) * Sparse.eval nodeValue930 x + ((2 : ℝ) * Sparse.eval nodeValue932 x + ((1 : ℝ) * Sparse.eval nodeValue1044 x + ((1 : ℝ) * Sparse.eval nodeValue2338 x + ((1 : ℝ) * Sparse.eval nodeValue2339 x + ((2 : ℝ) * Sparse.eval nodeValue2341 x + ((1 : ℝ) * Sparse.eval nodeValue2429 x + ((2 : ℝ) * Sparse.eval nodeValue2431 x + ((1 : ℝ) * Sparse.eval nodeValue2483 x + ((1 : ℝ) * Sparse.eval nodeValue2589 x + ((2 : ℝ) * Sparse.eval nodeValue2590 x + ((2 : ℝ) * Sparse.eval nodeValue2599 x + ((2 : ℝ) * Sparse.eval nodeValue2601 x + ((2 : ℝ) * Sparse.eval nodeValue2604 x + ((1 : ℝ) * Sparse.eval nodeValue2764 x + ((2 : ℝ) * Sparse.eval nodeValue2768 x + ((1 : ℝ) * Sparse.eval nodeValue3933 x + ((1 : ℝ) * Sparse.eval nodeValue3967 x + ((1 : ℝ) * Sparse.eval nodeValue3998 x + ((2 : ℝ) * Sparse.eval nodeValue4001 x + 0))))))))))))))))))))

def numericRow1917 : Integer.Sparse Master := [(Sum.inl 0, -143), (Sum.inl 6, -5), (Sum.inl 2, 50), (Sum.inl 7, 80), (Sum.inl 3, 160), (Sum.inl 1, 110), (Sum.inr 929, 1440), (Sum.inr 930, 1440), (Sum.inr 932, 2880), (Sum.inr 1044, 1440), (Sum.inr 2338, 1440), (Sum.inr 2339, 1440), (Sum.inr 2341, 2880), (Sum.inr 2429, 1440), (Sum.inr 2431, 2880), (Sum.inr 2483, 1440), (Sum.inr 2589, 1440), (Sum.inr 2590, 2880), (Sum.inr 2764, 1440)]

theorem reindexCheck1917 : Integer.Sparse.reindex keyMap MixedData.row1917 = numericRow1917 := by decide +kernel

theorem numericCheck1917 (x : Master → ℝ) : Integer.Sparse.eval numericRow1917 x =
    (1440 : ℝ) * reducedSource1917 x := by
  norm_num [numericRow1917, reducedSource1917, Integer.Sparse.eval, Sparse.eval, nodeValue929, nodeValue930, nodeValue932, nodeValue1044, nodeValue2338, nodeValue2339, nodeValue2341, nodeValue2429, nodeValue2431, nodeValue2483, nodeValue2589, nodeValue2590, nodeValue2599, nodeValue2601, nodeValue2604, nodeValue2764, nodeValue2768, nodeValue3933, nodeValue3967, nodeValue3998, nodeValue4001]
  ring

noncomputable def reducedSource1918 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4805 x + ((1 : ℝ) * Sparse.eval nodeValue4838 x + ((2 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4869 x + ((1 : ℝ) * Sparse.eval nodeValue5072 x + ((1 : ℝ) * Sparse.eval nodeValue5076 x + ((1 : ℝ) * Sparse.eval nodeValue5099 x + ((2 : ℝ) * Sparse.eval nodeValue5101 x + ((1 : ℝ) * Sparse.eval nodeValue5104 x + ((2 : ℝ) * Sparse.eval nodeValue5105 x + ((1 : ℝ) * Sparse.eval nodeValue5137 x + ((2 : ℝ) * Sparse.eval nodeValue5138 x + ((2 : ℝ) * Sparse.eval nodeValue5149 x + ((1 : ℝ) * Sparse.eval nodeValue5150 x + ((1 : ℝ) * Sparse.eval nodeValue5168 x + ((2 : ℝ) * Sparse.eval nodeValue5169 x + ((2 : ℝ) * Sparse.eval nodeValue5170 x + ((2 : ℝ) * Sparse.eval nodeValue5173 x + ((1 : ℝ) * Sparse.eval nodeValue5187 x + ((2 : ℝ) * Sparse.eval nodeValue5204 x + ((1 : ℝ) * Sparse.eval nodeValue5205 x + 0))))))))))))))))))))

def numericRow1918 : Integer.Sparse Master := [(Sum.inl 0, 132), (Sum.inl 6, -15), (Sum.inl 2, 55), (Sum.inl 7, 80), (Sum.inl 8, 160), (Sum.inl 3, 80), (Sum.inl 1, 150), (Sum.inr 2023, -4320), (Sum.inr 2058, -8640), (Sum.inr 2110, -4320), (Sum.inr 2214, -4320), (Sum.inr 2216, -8640), (Sum.inr 2275, -4320), (Sum.inr 2479, -4320), (Sum.inr 2483, -4320), (Sum.inr 2509, -4320), (Sum.inr 2515, -8640), (Sum.inr 2556, -4320), (Sum.inr 2704, -4320), (Sum.inr 2881, -8640), (Sum.inr 2924, -8640), (Sum.inr 2954, -8640), (Sum.inr 3459, -4320), (Sum.inr 3477, -4320), (Sum.inr 3479, -8640), (Sum.inr 3521, -4320), (Sum.inr 3603, -4320), (Sum.inr 3605, -8640), (Sum.inr 3606, -8640), (Sum.inr 3607, -8640), (Sum.inr 3624, -8640), (Sum.inr 5138, 34560), (Sum.inr 5150, 17280), (Sum.inr 5173, 34560), (Sum.inr 5187, 17280), (Sum.inr 5205, 17280)]

theorem reindexCheck1918 : Integer.Sparse.reindex keyMap MixedData.row1918 = numericRow1918 := by decide +kernel

theorem numericCheck1918 (x : Master → ℝ) : Integer.Sparse.eval numericRow1918 x =
    (17280 : ℝ) * reducedSource1918 x := by
  norm_num [numericRow1918, reducedSource1918, Integer.Sparse.eval, Sparse.eval, nodeValue4805, nodeValue4838, nodeValue4839, nodeValue4869, nodeValue5072, nodeValue5076, nodeValue5099, nodeValue5101, nodeValue5104, nodeValue5105, nodeValue5137, nodeValue5138, nodeValue5149, nodeValue5150, nodeValue5168, nodeValue5169, nodeValue5170, nodeValue5173, nodeValue5187, nodeValue5204, nodeValue5205]
  ring

noncomputable def reducedSource1919 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1156 x + ((1 : ℝ) * Sparse.eval nodeValue2353 x + ((1 : ℝ) * Sparse.eval nodeValue2553 x + ((1 : ℝ) * Sparse.eval nodeValue2566 x + ((1 : ℝ) * Sparse.eval nodeValue2587 x + ((1 : ℝ) * Sparse.eval nodeValue2590 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1919 : Integer.Sparse Master := [(Sum.inr 1156, 1), (Sum.inr 2353, 1), (Sum.inr 2553, 1), (Sum.inr 2566, 1), (Sum.inr 2587, 1), (Sum.inr 2590, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1919 : Integer.Sparse.reindex keyMap MixedData.row1919 = numericRow1919 := by decide +kernel

theorem numericCheck1919 (x : Master → ℝ) : Integer.Sparse.eval numericRow1919 x =
    (1 : ℝ) * reducedSource1919 x := by
  norm_num [numericRow1919, reducedSource1919, Integer.Sparse.eval, Sparse.eval, nodeValue1156, nodeValue2353, nodeValue2553, nodeValue2566, nodeValue2587, nodeValue2590, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
