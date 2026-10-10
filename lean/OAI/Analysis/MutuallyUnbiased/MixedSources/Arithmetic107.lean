import OAI.Analysis.MutuallyUnbiased.MixedData.Source13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values85
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1712 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1119 x + ((1 : ℝ) * Sparse.eval nodeValue2325 x + ((1 : ℝ) * Sparse.eval nodeValue2347 x + ((1 : ℝ) * Sparse.eval nodeValue2355 x + ((1 : ℝ) * Sparse.eval nodeValue2482 x + ((1 : ℝ) * Sparse.eval nodeValue2488 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1712 : Integer.Sparse Master := [(Sum.inr 1119, 1), (Sum.inr 2325, 1), (Sum.inr 2347, 1), (Sum.inr 2355, 1), (Sum.inr 2482, 1), (Sum.inr 2488, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1712 : Integer.Sparse.reindex keyMap MixedData.row1712 = numericRow1712 := by decide +kernel

theorem numericCheck1712 (x : Master → ℝ) : Integer.Sparse.eval numericRow1712 x =
    (1 : ℝ) * reducedSource1712 x := by
  norm_num [numericRow1712, reducedSource1712, Integer.Sparse.eval, Sparse.eval, nodeValue1119, nodeValue2325, nodeValue2347, nodeValue2355, nodeValue2482, nodeValue2488, nodeValue4092]

noncomputable def reducedSource1713 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1111 x + ((1 : ℝ) * Sparse.eval nodeValue2319 x + ((1 : ℝ) * Sparse.eval nodeValue2436 x + ((1 : ℝ) * Sparse.eval nodeValue2479 x + ((2 : ℝ) * Sparse.eval nodeValue2482 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow1713 : Integer.Sparse Master := [(Sum.inr 1111, 1), (Sum.inr 2436, 1), (Sum.inr 2479, 1), (Sum.inr 2482, 2), (Sum.inr 4092, -1)]

theorem reindexCheck1713 : Integer.Sparse.reindex keyMap MixedData.row1713 = numericRow1713 := by decide +kernel

theorem numericCheck1713 (x : Master → ℝ) : Integer.Sparse.eval numericRow1713 x =
    (1 : ℝ) * reducedSource1713 x := by
  norm_num [numericRow1713, reducedSource1713, Integer.Sparse.eval, Sparse.eval, nodeValue1111, nodeValue2319, nodeValue2436, nodeValue2479, nodeValue2482, nodeValue4092]

noncomputable def reducedSource1714 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1131 x + ((1 : ℝ) * Sparse.eval nodeValue2334 x + ((1 : ℝ) * Sparse.eval nodeValue2425 x + ((1 : ℝ) * Sparse.eval nodeValue2482 x + ((1 : ℝ) * Sparse.eval nodeValue2511 x + ((1 : ℝ) * Sparse.eval nodeValue2517 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1714 : Integer.Sparse Master := [(Sum.inr 1131, 1), (Sum.inr 2334, 1), (Sum.inr 2425, 1), (Sum.inr 2482, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1714 : Integer.Sparse.reindex keyMap MixedData.row1714 = numericRow1714 := by decide +kernel

theorem numericCheck1714 (x : Master → ℝ) : Integer.Sparse.eval numericRow1714 x =
    (1 : ℝ) * reducedSource1714 x := by
  norm_num [numericRow1714, reducedSource1714, Integer.Sparse.eval, Sparse.eval, nodeValue1131, nodeValue2334, nodeValue2425, nodeValue2482, nodeValue2511, nodeValue2517, nodeValue4092]

noncomputable def reducedSource1715 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4287 x + ((1 : ℝ) * Sparse.eval nodeValue4289 x + ((1 : ℝ) * Sparse.eval nodeValue4295 x + ((1 : ℝ) * Sparse.eval nodeValue4303 x + ((1 : ℝ) * Sparse.eval nodeValue4322 x + ((1 : ℝ) * Sparse.eval nodeValue4325 x + ((1 : ℝ) * Sparse.eval nodeValue4346 x + ((1 : ℝ) * Sparse.eval nodeValue4401 x + ((1 : ℝ) * Sparse.eval nodeValue4460 x + ((1 : ℝ) * Sparse.eval nodeValue4902 x + ((1 : ℝ) * Sparse.eval nodeValue4907 x + ((1 : ℝ) * Sparse.eval nodeValue4913 x + ((1 : ℝ) * Sparse.eval nodeValue4927 x + ((1 : ℝ) * Sparse.eval nodeValue4943 x + ((1 : ℝ) * Sparse.eval nodeValue4986 x + ((1 : ℝ) * Sparse.eval nodeValue5000 x + ((1 : ℝ) * Sparse.eval nodeValue5033 x + ((1 : ℝ) * Sparse.eval nodeValue5047 x + ((1 : ℝ) * Sparse.eval nodeValue5073 x + ((1 : ℝ) * Sparse.eval nodeValue5075 x + ((1 : ℝ) * Sparse.eval nodeValue5081 x + ((1 : ℝ) * Sparse.eval nodeValue5102 x + ((1 : ℝ) * Sparse.eval nodeValue5137 x + ((1 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5169 x + ((1 : ℝ) * Sparse.eval nodeValue5171 x + ((1 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5261 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5483 x + 0)))))))))))))))))))))))))))))

def numericRow1715 : Integer.Sparse Master := [(Sum.inl 0, 199), (Sum.inl 5, 40), (Sum.inl 6, 5), (Sum.inl 8, 80), (Sum.inl 1, 60), (Sum.inr 865, -4320), (Sum.inr 867, -4320), (Sum.inr 873, -4320), (Sum.inr 881, -4320), (Sum.inr 900, -4320), (Sum.inr 903, -4320), (Sum.inr 924, -4320), (Sum.inr 982, -4320), (Sum.inr 1043, -4320), (Sum.inr 1553, -4320), (Sum.inr 1555, -4320), (Sum.inr 1559, -4320), (Sum.inr 1569, -4320), (Sum.inr 1588, -4320), (Sum.inr 1591, -4320), (Sum.inr 1617, -4320), (Sum.inr 1674, -4320), (Sum.inr 1725, -4320), (Sum.inr 2295, -4320), (Sum.inr 2300, -4320), (Sum.inr 2306, -4320), (Sum.inr 2317, -4320), (Sum.inr 2334, -4320), (Sum.inr 2371, -4320), (Sum.inr 2385, -4320), (Sum.inr 2425, -4320), (Sum.inr 2449, -4320), (Sum.inr 2480, -4320), (Sum.inr 2482, -4320), (Sum.inr 2489, -4320), (Sum.inr 2512, -4320), (Sum.inr 2556, -4320), (Sum.inr 2561, -4320), (Sum.inr 2723, -4320), (Sum.inr 2726, -4320), (Sum.inr 3315, -4320), (Sum.inr 3318, -4320), (Sum.inr 3325, -4320), (Sum.inr 3335, -4320), (Sum.inr 3353, -4320), (Sum.inr 3399, -4320), (Sum.inr 3411, -4320), (Sum.inr 3432, -4320), (Sum.inr 3449, -4320), (Sum.inr 3467, -4320), (Sum.inr 3468, -4320), (Sum.inr 3471, -4320), (Sum.inr 3482, -4320), (Sum.inr 3521, -4320), (Sum.inr 3522, -4320), (Sum.inr 3544, -4320), (Sum.inr 3545, -4320), (Sum.inr 3607, -4320), (Sum.inr 3608, -4320), (Sum.inr 3627, -4320), (Sum.inr 4047, -4320)]

theorem reindexCheck1715 : Integer.Sparse.reindex keyMap MixedData.row1715 = numericRow1715 := by decide +kernel

theorem numericCheck1715 (x : Master → ℝ) : Integer.Sparse.eval numericRow1715 x =
    (17280 : ℝ) * reducedSource1715 x := by
  norm_num [numericRow1715, reducedSource1715, Integer.Sparse.eval, Sparse.eval, nodeValue4287, nodeValue4289, nodeValue4295, nodeValue4303, nodeValue4322, nodeValue4325, nodeValue4346, nodeValue4401, nodeValue4460, nodeValue4902, nodeValue4907, nodeValue4913, nodeValue4927, nodeValue4943, nodeValue4986, nodeValue5000, nodeValue5033, nodeValue5047, nodeValue5073, nodeValue5075, nodeValue5081, nodeValue5102, nodeValue5137, nodeValue5141, nodeValue5169, nodeValue5171, nodeValue5259, nodeValue5261, nodeValue5293, nodeValue5483]; ring

noncomputable def reducedSource1716 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4326 x + ((1 : ℝ) * Sparse.eval nodeValue4330 x + ((1 : ℝ) * Sparse.eval nodeValue4334 x + ((1 : ℝ) * Sparse.eval nodeValue4346 x + ((1 : ℝ) * Sparse.eval nodeValue4460 x + ((1 : ℝ) * Sparse.eval nodeValue4532 x + ((1 : ℝ) * Sparse.eval nodeValue4536 x + ((1 : ℝ) * Sparse.eval nodeValue4552 x + ((1 : ℝ) * Sparse.eval nodeValue4605 x + ((1 : ℝ) * Sparse.eval nodeValue4663 x + ((1 : ℝ) * Sparse.eval nodeValue4669 x + ((1 : ℝ) * Sparse.eval nodeValue4681 x + ((1 : ℝ) * Sparse.eval nodeValue4756 x + ((1 : ℝ) * Sparse.eval nodeValue4760 x + ((1 : ℝ) * Sparse.eval nodeValue4771 x + ((1 : ℝ) * Sparse.eval nodeValue4776 x + ((1 : ℝ) * Sparse.eval nodeValue4801 x + ((2 : ℝ) * Sparse.eval nodeValue4804 x + ((1 : ℝ) * Sparse.eval nodeValue4810 x + ((1 : ℝ) * Sparse.eval nodeValue4834 x + ((1 : ℝ) * Sparse.eval nodeValue4841 x + ((1 : ℝ) * Sparse.eval nodeValue4868 x + ((1 : ℝ) * Sparse.eval nodeValue4894 x + ((1 : ℝ) * Sparse.eval nodeValue4897 x + ((1 : ℝ) * Sparse.eval nodeValue5133 x + ((1 : ℝ) * Sparse.eval nodeValue5140 x + ((1 : ℝ) * Sparse.eval nodeValue5161 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5272 x + 0))))))))))))))))))))))))))))

def numericRow1716 : Integer.Sparse Master := [(Sum.inr 924, -1), (Sum.inr 1043, -1), (Sum.inr 1239, -1), (Sum.inr 1674, -1), (Sum.inr 1725, -1), (Sum.inr 1807, -1), (Sum.inr 1960, -1), (Sum.inr 2019, -1), (Sum.inr 2022, -2), (Sum.inr 2028, -1), (Sum.inr 2109, -1), (Sum.inr 2151, -1), (Sum.inr 2173, -1), (Sum.inr 2190, -1), (Sum.inr 2203, -2), (Sum.inr 2215, -1), (Sum.inr 2226, -1), (Sum.inr 2261, -1), (Sum.inr 2722, -1), (Sum.inr 2740, -2), (Sum.inr 3533, -1), (Sum.inr 4330, 4), (Sum.inr 4334, 4), (Sum.inr 4532, 4), (Sum.inr 4536, 4), (Sum.inr 4552, 4), (Sum.inr 4663, 4), (Sum.inr 4669, 4), (Sum.inr 4756, 4), (Sum.inr 4771, 4), (Sum.inr 4776, 4), (Sum.inr 5140, 4), (Sum.inr 5161, 4)]

theorem reindexCheck1716 : Integer.Sparse.reindex keyMap MixedData.row1716 = numericRow1716 := by decide +kernel

theorem numericCheck1716 (x : Master → ℝ) : Integer.Sparse.eval numericRow1716 x =
    (4 : ℝ) * reducedSource1716 x := by
  norm_num [numericRow1716, reducedSource1716, Integer.Sparse.eval, Sparse.eval, nodeValue4326, nodeValue4330, nodeValue4334, nodeValue4346, nodeValue4460, nodeValue4532, nodeValue4536, nodeValue4552, nodeValue4605, nodeValue4663, nodeValue4669, nodeValue4681, nodeValue4756, nodeValue4760, nodeValue4771, nodeValue4776, nodeValue4801, nodeValue4804, nodeValue4810, nodeValue4834, nodeValue4841, nodeValue4868, nodeValue4894, nodeValue4897, nodeValue5133, nodeValue5140, nodeValue5161, nodeValue5258, nodeValue5272]; ring

noncomputable def reducedSource1717 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1116 x + ((1 : ℝ) * Sparse.eval nodeValue1118 x + ((1 : ℝ) * Sparse.eval nodeValue1121 x + ((1 : ℝ) * Sparse.eval nodeValue1137 x + ((1 : ℝ) * Sparse.eval nodeValue1271 x + ((1 : ℝ) * Sparse.eval nodeValue1329 x + ((1 : ℝ) * Sparse.eval nodeValue1334 x + ((1 : ℝ) * Sparse.eval nodeValue1342 x + ((1 : ℝ) * Sparse.eval nodeValue1416 x + ((1 : ℝ) * Sparse.eval nodeValue2800 x + ((1 : ℝ) * Sparse.eval nodeValue2803 x + ((1 : ℝ) * Sparse.eval nodeValue2816 x + ((1 : ℝ) * Sparse.eval nodeValue2890 x + ((1 : ℝ) * Sparse.eval nodeValue2895 x + ((1 : ℝ) * Sparse.eval nodeValue2901 x + ((1 : ℝ) * Sparse.eval nodeValue2904 x + ((1 : ℝ) * Sparse.eval nodeValue2940 x + ((2 : ℝ) * Sparse.eval nodeValue2941 x + ((1 : ℝ) * Sparse.eval nodeValue2942 x + ((1 : ℝ) * Sparse.eval nodeValue2964 x + ((1 : ℝ) * Sparse.eval nodeValue2966 x + ((1 : ℝ) * Sparse.eval nodeValue3004 x + ((1 : ℝ) * Sparse.eval nodeValue3089 x + ((1 : ℝ) * Sparse.eval nodeValue3113 x + ((1 : ℝ) * Sparse.eval nodeValue3114 x + ((1 : ℝ) * Sparse.eval nodeValue3205 x + ((1 : ℝ) * Sparse.eval nodeValue3206 x + ((1 : ℝ) * Sparse.eval nodeValue3214 x + ((1 : ℝ) * Sparse.eval nodeValue3230 x + 0))))))))))))))))))))))))))))

def numericRow1717 : Integer.Sparse Master := [(Sum.inl 0, -106), (Sum.inl 5, -20), (Sum.inl 6, 20), (Sum.inl 2, 130), (Sum.inl 35, 80), (Sum.inl 26, 80), (Sum.inl 1, 140), (Sum.inr 1116, 1080), (Sum.inr 1118, 1080), (Sum.inr 1121, 1080), (Sum.inr 1137, 1080), (Sum.inr 1334, 1080), (Sum.inr 2800, 1080), (Sum.inr 2803, 1080), (Sum.inr 2816, 1080), (Sum.inr 2890, 1080), (Sum.inr 2895, 1080), (Sum.inr 2942, 1080), (Sum.inr 2964, 1080)]

theorem reindexCheck1717 : Integer.Sparse.reindex keyMap MixedData.row1717 = numericRow1717 := by decide +kernel

theorem numericCheck1717 (x : Master → ℝ) : Integer.Sparse.eval numericRow1717 x =
    (1080 : ℝ) * reducedSource1717 x := by
  norm_num [numericRow1717, reducedSource1717, Integer.Sparse.eval, Sparse.eval, nodeValue1116, nodeValue1118, nodeValue1121, nodeValue1137, nodeValue1271, nodeValue1329, nodeValue1334, nodeValue1342, nodeValue1416, nodeValue2800, nodeValue2803, nodeValue2816, nodeValue2890, nodeValue2895, nodeValue2901, nodeValue2904, nodeValue2940, nodeValue2941, nodeValue2942, nodeValue2964, nodeValue2966, nodeValue3004, nodeValue3089, nodeValue3113, nodeValue3114, nodeValue3205, nodeValue3206, nodeValue3214, nodeValue3230]; ring

noncomputable def reducedSource1718 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1663 x + ((1 : ℝ) * Sparse.eval nodeValue1672 x + ((1 : ℝ) * Sparse.eval nodeValue1674 x + ((1 : ℝ) * Sparse.eval nodeValue1679 x + ((1 : ℝ) * Sparse.eval nodeValue1725 x + ((1 : ℝ) * Sparse.eval nodeValue2140 x + ((1 : ℝ) * Sparse.eval nodeValue2149 x + ((1 : ℝ) * Sparse.eval nodeValue2151 x + ((1 : ℝ) * Sparse.eval nodeValue2155 x + ((1 : ℝ) * Sparse.eval nodeValue2172 x + ((1 : ℝ) * Sparse.eval nodeValue2173 x + ((1 : ℝ) * Sparse.eval nodeValue2176 x + ((1 : ℝ) * Sparse.eval nodeValue2189 x + ((1 : ℝ) * Sparse.eval nodeValue2190 x + ((1 : ℝ) * Sparse.eval nodeValue2200 x + ((2 : ℝ) * Sparse.eval nodeValue2203 x + ((1 : ℝ) * Sparse.eval nodeValue2205 x + ((1 : ℝ) * Sparse.eval nodeValue2212 x + ((1 : ℝ) * Sparse.eval nodeValue2215 x + ((1 : ℝ) * Sparse.eval nodeValue2226 x + ((1 : ℝ) * Sparse.eval nodeValue2228 x + ((1 : ℝ) * Sparse.eval nodeValue2261 x + ((1 : ℝ) * Sparse.eval nodeValue2264 x + ((1 : ℝ) * Sparse.eval nodeValue2292 x + ((1 : ℝ) * Sparse.eval nodeValue2670 x + ((1 : ℝ) * Sparse.eval nodeValue2693 x + ((1 : ℝ) * Sparse.eval nodeValue2719 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue2740 x + 0))))))))))))))))))))))))))))

def numericRow1718 : Integer.Sparse Master := [(Sum.inr 1672, 1), (Sum.inr 1674, 1), (Sum.inr 1679, 1), (Sum.inr 1725, 1), (Sum.inr 2140, 1), (Sum.inr 2149, 1), (Sum.inr 2151, 1), (Sum.inr 2155, 1), (Sum.inr 2172, 1), (Sum.inr 2173, 1), (Sum.inr 2176, 1), (Sum.inr 2189, 1), (Sum.inr 2190, 1), (Sum.inr 2200, 1), (Sum.inr 2203, 2), (Sum.inr 2212, 1), (Sum.inr 2215, 1), (Sum.inr 2226, 1), (Sum.inr 2261, 1), (Sum.inr 2670, 1), (Sum.inr 2719, 1), (Sum.inr 2722, 1), (Sum.inr 2740, 1)]

theorem reindexCheck1718 : Integer.Sparse.reindex keyMap MixedData.row1718 = numericRow1718 := by decide +kernel

theorem numericCheck1718 (x : Master → ℝ) : Integer.Sparse.eval numericRow1718 x =
    (1 : ℝ) * reducedSource1718 x := by
  norm_num [numericRow1718, reducedSource1718, Integer.Sparse.eval, Sparse.eval, nodeValue1663, nodeValue1672, nodeValue1674, nodeValue1679, nodeValue1725, nodeValue2140, nodeValue2149, nodeValue2151, nodeValue2155, nodeValue2172, nodeValue2173, nodeValue2176, nodeValue2189, nodeValue2190, nodeValue2200, nodeValue2203, nodeValue2205, nodeValue2212, nodeValue2215, nodeValue2226, nodeValue2228, nodeValue2261, nodeValue2264, nodeValue2292, nodeValue2670, nodeValue2693, nodeValue2719, nodeValue2722, nodeValue2740]

noncomputable def reducedSource1719 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue912 x + ((1 : ℝ) * Sparse.eval nodeValue1795 x + ((1 : ℝ) * Sparse.eval nodeValue1955 x + ((1 : ℝ) * Sparse.eval nodeValue1978 x + ((1 : ℝ) * Sparse.eval nodeValue2022 x + ((1 : ℝ) * Sparse.eval nodeValue2028 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow1719 : Integer.Sparse Master := [(Sum.inr 912, 1), (Sum.inr 1795, 1), (Sum.inr 1955, 1), (Sum.inr 1978, 1), (Sum.inr 2022, 1), (Sum.inr 2028, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1719 : Integer.Sparse.reindex keyMap MixedData.row1719 = numericRow1719 := by decide +kernel

theorem numericCheck1719 (x : Master → ℝ) : Integer.Sparse.eval numericRow1719 x =
    (1 : ℝ) * reducedSource1719 x := by
  norm_num [numericRow1719, reducedSource1719, Integer.Sparse.eval, Sparse.eval, nodeValue912, nodeValue1795, nodeValue1955, nodeValue1978, nodeValue2022, nodeValue2028, nodeValue4084]

noncomputable def reducedSource1720 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1147 x + ((1 : ℝ) * Sparse.eval nodeValue1955 x + ((1 : ℝ) * Sparse.eval nodeValue1960 x + ((2 : ℝ) * Sparse.eval nodeValue2022 x + ((1 : ℝ) * Sparse.eval nodeValue2552 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1720 : Integer.Sparse Master := [(Sum.inr 1147, 1), (Sum.inr 1955, 1), (Sum.inr 1960, 1), (Sum.inr 2022, 2), (Sum.inr 4084, -1)]

theorem reindexCheck1720 : Integer.Sparse.reindex keyMap MixedData.row1720 = numericRow1720 := by decide +kernel

theorem numericCheck1720 (x : Master → ℝ) : Integer.Sparse.eval numericRow1720 x =
    (1 : ℝ) * reducedSource1720 x := by
  norm_num [numericRow1720, reducedSource1720, Integer.Sparse.eval, Sparse.eval, nodeValue1147, nodeValue1955, nodeValue1960, nodeValue2022, nodeValue2552, nodeValue4084]

noncomputable def reducedSource1721 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue904 x + ((1 : ℝ) * Sparse.eval nodeValue1789 x + ((1 : ℝ) * Sparse.eval nodeValue1972 x + ((1 : ℝ) * Sparse.eval nodeValue2019 x + ((2 : ℝ) * Sparse.eval nodeValue2022 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1721 : Integer.Sparse Master := [(Sum.inr 1789, 1), (Sum.inr 1972, 1), (Sum.inr 2019, 1), (Sum.inr 2022, 2), (Sum.inr 4084, -1)]

theorem reindexCheck1721 : Integer.Sparse.reindex keyMap MixedData.row1721 = numericRow1721 := by decide +kernel

theorem numericCheck1721 (x : Master → ℝ) : Integer.Sparse.eval numericRow1721 x =
    (1 : ℝ) * reducedSource1721 x := by
  norm_num [numericRow1721, reducedSource1721, Integer.Sparse.eval, Sparse.eval, nodeValue904, nodeValue1789, nodeValue1972, nodeValue2019, nodeValue2022, nodeValue4084]

noncomputable def reducedSource1722 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue924 x + ((1 : ℝ) * Sparse.eval nodeValue1807 x + ((1 : ℝ) * Sparse.eval nodeValue1960 x + ((1 : ℝ) * Sparse.eval nodeValue2022 x + ((1 : ℝ) * Sparse.eval nodeValue2053 x + ((1 : ℝ) * Sparse.eval nodeValue2060 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow1722 : Integer.Sparse Master := [(Sum.inr 924, 1), (Sum.inr 1807, 1), (Sum.inr 1960, 1), (Sum.inr 2022, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1722 : Integer.Sparse.reindex keyMap MixedData.row1722 = numericRow1722 := by decide +kernel

theorem numericCheck1722 (x : Master → ℝ) : Integer.Sparse.eval numericRow1722 x =
    (1 : ℝ) * reducedSource1722 x := by
  norm_num [numericRow1722, reducedSource1722, Integer.Sparse.eval, Sparse.eval, nodeValue924, nodeValue1807, nodeValue1960, nodeValue2022, nodeValue2053, nodeValue2060, nodeValue4084]

noncomputable def reducedSource1723 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4196 x + ((1 : ℝ) * Sparse.eval nodeValue4198 x + ((1 : ℝ) * Sparse.eval nodeValue4204 x + ((1 : ℝ) * Sparse.eval nodeValue4212 x + ((1 : ℝ) * Sparse.eval nodeValue4251 x + ((1 : ℝ) * Sparse.eval nodeValue4320 x + ((1 : ℝ) * Sparse.eval nodeValue4324 x + ((1 : ℝ) * Sparse.eval nodeValue4343 x + ((1 : ℝ) * Sparse.eval nodeValue4398 x + ((1 : ℝ) * Sparse.eval nodeValue4631 x + ((1 : ℝ) * Sparse.eval nodeValue4637 x + ((1 : ℝ) * Sparse.eval nodeValue4644 x + ((1 : ℝ) * Sparse.eval nodeValue4706 x + ((1 : ℝ) * Sparse.eval nodeValue4709 x + ((1 : ℝ) * Sparse.eval nodeValue4728 x + ((1 : ℝ) * Sparse.eval nodeValue4760 x + ((1 : ℝ) * Sparse.eval nodeValue4769 x + ((1 : ℝ) * Sparse.eval nodeValue4779 x + ((1 : ℝ) * Sparse.eval nodeValue4788 x + ((1 : ℝ) * Sparse.eval nodeValue4802 x + ((1 : ℝ) * Sparse.eval nodeValue4804 x + ((1 : ℝ) * Sparse.eval nodeValue4811 x + ((1 : ℝ) * Sparse.eval nodeValue4832 x + ((1 : ℝ) * Sparse.eval nodeValue4835 x + ((1 : ℝ) * Sparse.eval nodeValue4888 x + ((1 : ℝ) * Sparse.eval nodeValue5134 x + ((1 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5168 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + 0)))))))))))))))))))))))))))))

def numericRow1723 : Integer.Sparse Master := [(Sum.inl 0, 86), (Sum.inl 6, -5), (Sum.inl 2, 20), (Sum.inl 7, 80), (Sum.inl 3, 160), (Sum.inl 4, 80), (Sum.inl 1, 155), (Sum.inr 699, -4320), (Sum.inr 701, -4320), (Sum.inr 707, -4320), (Sum.inr 715, -4320), (Sum.inr 748, -4320), (Sum.inr 750, -4320), (Sum.inr 753, -4320), (Sum.inr 763, -4320), (Sum.inr 785, -4320), (Sum.inr 804, -4320), (Sum.inr 898, -4320), (Sum.inr 902, -4320), (Sum.inr 921, -4320), (Sum.inr 979, -4320), (Sum.inr 1586, -4320), (Sum.inr 1590, -4320), (Sum.inr 1599, -4320), (Sum.inr 1666, -4320), (Sum.inr 1760, -4320), (Sum.inr 1766, -4320), (Sum.inr 1773, -4320), (Sum.inr 1836, -4320), (Sum.inr 1841, -4320), (Sum.inr 1850, -4320), (Sum.inr 1860, -4320), (Sum.inr 1863, -4320), (Sum.inr 1883, -4320), (Sum.inr 1888, -4320), (Sum.inr 1897, -4320), (Sum.inr 1907, -4320), (Sum.inr 1960, -4320), (Sum.inr 1969, -4320), (Sum.inr 1987, -4320), (Sum.inr 1996, -4320), (Sum.inr 2003, -4320), (Sum.inr 2006, -4320), (Sum.inr 2020, -4320), (Sum.inr 2022, -4320), (Sum.inr 2029, -4320), (Sum.inr 2052, -4320), (Sum.inr 2054, -4320), (Sum.inr 2173, -4320), (Sum.inr 2185, -4320), (Sum.inr 2193, -4320), (Sum.inr 2202, -4320), (Sum.inr 2203, -4320), (Sum.inr 2206, -4320), (Sum.inr 2225, -4320), (Sum.inr 2244, -4320), (Sum.inr 2262, -4320), (Sum.inr 2553, -4320), (Sum.inr 2561, -4320), (Sum.inr 2722, -4320), (Sum.inr 3514, -4320), (Sum.inr 3522, -4320), (Sum.inr 3533, -4320), (Sum.inr 3603, -4320), (Sum.inr 3903, -4320)]

theorem reindexCheck1723 : Integer.Sparse.reindex keyMap MixedData.row1723 = numericRow1723 := by decide +kernel

theorem numericCheck1723 (x : Master → ℝ) : Integer.Sparse.eval numericRow1723 x =
    (17280 : ℝ) * reducedSource1723 x := by
  norm_num [numericRow1723, reducedSource1723, Integer.Sparse.eval, Sparse.eval, nodeValue4196, nodeValue4198, nodeValue4204, nodeValue4212, nodeValue4251, nodeValue4320, nodeValue4324, nodeValue4343, nodeValue4398, nodeValue4631, nodeValue4637, nodeValue4644, nodeValue4706, nodeValue4709, nodeValue4728, nodeValue4760, nodeValue4769, nodeValue4779, nodeValue4788, nodeValue4802, nodeValue4804, nodeValue4811, nodeValue4832, nodeValue4835, nodeValue4888, nodeValue5134, nodeValue5141, nodeValue5168, nodeValue5258, nodeValue5434]; ring

noncomputable def reducedSource1724 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2391 x + ((1 : ℝ) * Sparse.eval nodeValue2535 x + ((1 : ℝ) * Sparse.eval nodeValue2539 x + ((1 : ℝ) * Sparse.eval nodeValue2585 x + ((1 : ℝ) * Sparse.eval nodeValue2686 x + ((1 : ℝ) * Sparse.eval nodeValue3770 x + ((-1 : ℝ) * Sparse.eval nodeValue4089 x + 0))))))

def numericRow1724 : Integer.Sparse Master := [(Sum.inr 2391, 1), (Sum.inr 2535, 1), (Sum.inr 2539, 1), (Sum.inr 2585, 1), (Sum.inr 2686, 1), (Sum.inr 3770, 1), (Sum.inr 4089, -1)]

theorem reindexCheck1724 : Integer.Sparse.reindex keyMap MixedData.row1724 = numericRow1724 := by decide +kernel

theorem numericCheck1724 (x : Master → ℝ) : Integer.Sparse.eval numericRow1724 x =
    (1 : ℝ) * reducedSource1724 x := by
  norm_num [numericRow1724, reducedSource1724, Integer.Sparse.eval, Sparse.eval, nodeValue2391, nodeValue2535, nodeValue2539, nodeValue2585, nodeValue2686, nodeValue3770, nodeValue4089]

noncomputable def reducedSource1725 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1921 x + ((1 : ℝ) * Sparse.eval nodeValue1924 x + ((1 : ℝ) * Sparse.eval nodeValue1928 x + ((1 : ℝ) * Sparse.eval nodeValue1945 x + ((1 : ℝ) * Sparse.eval nodeValue2215 x + ((1 : ℝ) * Sparse.eval nodeValue3478 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

def numericRow1725 : Integer.Sparse Master := [(Sum.inr 1921, 1), (Sum.inr 1924, 1), (Sum.inr 1928, 1), (Sum.inr 2215, 1), (Sum.inr 3478, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1725 : Integer.Sparse.reindex keyMap MixedData.row1725 = numericRow1725 := by decide +kernel

theorem numericCheck1725 (x : Master → ℝ) : Integer.Sparse.eval numericRow1725 x =
    (1 : ℝ) * reducedSource1725 x := by
  norm_num [numericRow1725, reducedSource1725, Integer.Sparse.eval, Sparse.eval, nodeValue1921, nodeValue1924, nodeValue1928, nodeValue1945, nodeValue2215, nodeValue3478, nodeValue4082]

noncomputable def reducedSource1726 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1924 x + ((1 : ℝ) * Sparse.eval nodeValue2534 x + ((1 : ℝ) * Sparse.eval nodeValue2538 x + ((1 : ℝ) * Sparse.eval nodeValue2584 x + ((1 : ℝ) * Sparse.eval nodeValue2685 x + ((1 : ℝ) * Sparse.eval nodeValue3478 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0))))))

def numericRow1726 : Integer.Sparse Master := [(Sum.inr 1924, 1), (Sum.inr 2534, 1), (Sum.inr 2538, 1), (Sum.inr 2584, 1), (Sum.inr 2685, 1), (Sum.inr 3478, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1726 : Integer.Sparse.reindex keyMap MixedData.row1726 = numericRow1726 := by decide +kernel

theorem numericCheck1726 (x : Master → ℝ) : Integer.Sparse.eval numericRow1726 x =
    (1 : ℝ) * reducedSource1726 x := by
  norm_num [numericRow1726, reducedSource1726, Integer.Sparse.eval, Sparse.eval, nodeValue1924, nodeValue2534, nodeValue2538, nodeValue2584, nodeValue2685, nodeValue3478, nodeValue4082]

noncomputable def reducedSource1727 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2377 x + ((1 : ℝ) * Sparse.eval nodeValue2379 x + ((2 : ℝ) * Sparse.eval nodeValue2382 x + ((1 : ℝ) * Sparse.eval nodeValue2661 x + ((1 : ℝ) * Sparse.eval nodeValue3757 x + ((-1 : ℝ) * Sparse.eval nodeValue4088 x + 0)))))

def numericRow1727 : Integer.Sparse Master := [(Sum.inr 2379, 1), (Sum.inr 2382, 2), (Sum.inr 2661, 1), (Sum.inr 3757, 1), (Sum.inr 4088, -1)]

theorem reindexCheck1727 : Integer.Sparse.reindex keyMap MixedData.row1727 = numericRow1727 := by decide +kernel

theorem numericCheck1727 (x : Master → ℝ) : Integer.Sparse.eval numericRow1727 x =
    (1 : ℝ) * reducedSource1727 x := by
  norm_num [numericRow1727, reducedSource1727, Integer.Sparse.eval, Sparse.eval, nodeValue2377, nodeValue2379, nodeValue2382, nodeValue2661, nodeValue3757, nodeValue4088]

end MUB6.Certificate.MixedSourceBridge

end OAI
