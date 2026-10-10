import OAI.Analysis.MutuallyUnbiased.MixedData.Source4
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values85
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource576 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2088 x + ((1 : ℝ) * Sparse.eval nodeValue2090 x + ((1 : ℝ) * Sparse.eval nodeValue2094 x + ((1 : ℝ) * Sparse.eval nodeValue2107 x + ((1 : ℝ) * Sparse.eval nodeValue2244 x + ((1 : ℝ) * Sparse.eval nodeValue3572 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

def numericRow576 : Integer.Sparse Master := [(Sum.inr 2088, 1), (Sum.inr 2090, 1), (Sum.inr 2094, 1), (Sum.inr 2107, 1), (Sum.inr 2244, 1), (Sum.inr 3572, 1), (Sum.inr 4083, -1)]

theorem reindexCheck576 : Integer.Sparse.reindex keyMap MixedData.row576 = numericRow576 := by decide +kernel

theorem numericCheck576 (x : Master → ℝ) : Integer.Sparse.eval numericRow576 x =
    (1 : ℝ) * reducedSource576 x := by
  norm_num [numericRow576, reducedSource576, Integer.Sparse.eval, Sparse.eval, nodeValue2088, nodeValue2090, nodeValue2094, nodeValue2107, nodeValue2244, nodeValue3572, nodeValue4083]

noncomputable def reducedSource577 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1020 x + ((2 : ℝ) * Sparse.eval nodeValue2088 x + ((1 : ℝ) * Sparse.eval nodeValue2243 x + ((2 : ℝ) * Sparse.eval nodeValue2244 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

def numericRow577 : Integer.Sparse Master := [(Sum.inr 2088, 2), (Sum.inr 2243, 1), (Sum.inr 2244, 2), (Sum.inr 4083, -1)]

theorem reindexCheck577 : Integer.Sparse.reindex keyMap MixedData.row577 = numericRow577 := by decide +kernel

theorem numericCheck577 (x : Master → ℝ) : Integer.Sparse.eval numericRow577 x =
    (1 : ℝ) * reducedSource577 x := by
  norm_num [numericRow577, reducedSource577, Integer.Sparse.eval, Sparse.eval, nodeValue1020, nodeValue2088, nodeValue2243, nodeValue2244, nodeValue4083]

noncomputable def reducedSource578 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4249 x + ((1 : ℝ) * Sparse.eval nodeValue4251 x + ((1 : ℝ) * Sparse.eval nodeValue4256 x + ((2 : ℝ) * Sparse.eval nodeValue4265 x + ((1 : ℝ) * Sparse.eval nodeValue4728 x + ((1 : ℝ) * Sparse.eval nodeValue4732 x + ((2 : ℝ) * Sparse.eval nodeValue4737 x + ((2 : ℝ) * Sparse.eval nodeValue4802 x + ((2 : ℝ) * Sparse.eval nodeValue4804 x + ((2 : ℝ) * Sparse.eval nodeValue4811 x + ((1 : ℝ) * Sparse.eval nodeValue4831 x + ((1 : ℝ) * Sparse.eval nodeValue4832 x + ((4 : ℝ) * Sparse.eval nodeValue4835 x + ((1 : ℝ) * Sparse.eval nodeValue4887 x + ((3 : ℝ) * Sparse.eval nodeValue4888 x + ((1 : ℝ) * Sparse.eval nodeValue5405 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((1 : ℝ) * Sparse.eval nodeValue5452 x + 0))))))))))))))))))

def numericRow578 : Integer.Sparse Master := [(Sum.inl 0, 269), (Sum.inl 2, 45), (Sum.inl 3, 240), (Sum.inl 12, 240), (Sum.inl 4, 160), (Sum.inl 1, -180), (Sum.inr 783, -4320), (Sum.inr 785, -4320), (Sum.inr 790, -4320), (Sum.inr 803, -4320), (Sum.inr 804, -4320), (Sum.inr 807, -17280), (Sum.inr 848, -4320), (Sum.inr 1897, -4320), (Sum.inr 1901, -4320), (Sum.inr 1907, -4320), (Sum.inr 1909, -17280), (Sum.inr 1941, -4320), (Sum.inr 2020, -8640), (Sum.inr 2022, -8640), (Sum.inr 2029, -8640), (Sum.inr 2051, -4320), (Sum.inr 2052, -4320), (Sum.inr 2054, -17280), (Sum.inr 2191, -4320), (Sum.inr 2193, -4320), (Sum.inr 2202, -8640), (Sum.inr 2203, -8640), (Sum.inr 2206, -17280), (Sum.inr 2225, -8640), (Sum.inr 2243, -8640), (Sum.inr 2244, -12960), (Sum.inr 2262, -12960), (Sum.inr 3800, -4320), (Sum.inr 3805, -4320), (Sum.inr 3902, -4320), (Sum.inr 3903, -8640)]

theorem reindexCheck578 : Integer.Sparse.reindex keyMap MixedData.row578 = numericRow578 := by decide +kernel

theorem numericCheck578 (x : Master → ℝ) : Integer.Sparse.eval numericRow578 x =
    (17280 : ℝ) * reducedSource578 x := by
  norm_num [numericRow578, reducedSource578, Integer.Sparse.eval, Sparse.eval, nodeValue4249, nodeValue4251, nodeValue4256, nodeValue4265, nodeValue4728, nodeValue4732, nodeValue4737, nodeValue4802, nodeValue4804, nodeValue4811, nodeValue4831, nodeValue4832, nodeValue4835, nodeValue4887, nodeValue4888, nodeValue5405, nodeValue5434, nodeValue5439, nodeValue5452]; ring

noncomputable def reducedSource579 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue783 x + ((1 : ℝ) * Sparse.eval nodeValue785 x + ((1 : ℝ) * Sparse.eval nodeValue790 x + ((2 : ℝ) * Sparse.eval nodeValue807 x + ((1 : ℝ) * Sparse.eval nodeValue1897 x + ((1 : ℝ) * Sparse.eval nodeValue1901 x + ((2 : ℝ) * Sparse.eval nodeValue1909 x + ((2 : ℝ) * Sparse.eval nodeValue2020 x + ((2 : ℝ) * Sparse.eval nodeValue2022 x + ((2 : ℝ) * Sparse.eval nodeValue2029 x + ((2 : ℝ) * Sparse.eval nodeValue2054 x + ((1 : ℝ) * Sparse.eval nodeValue2191 x + ((1 : ℝ) * Sparse.eval nodeValue2193 x + ((2 : ℝ) * Sparse.eval nodeValue2206 x + ((1 : ℝ) * Sparse.eval nodeValue2243 x + ((1 : ℝ) * Sparse.eval nodeValue2244 x + ((2 : ℝ) * Sparse.eval nodeValue2262 x + ((1 : ℝ) * Sparse.eval nodeValue3800 x + ((2 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3902 x + ((1 : ℝ) * Sparse.eval nodeValue3911 x + 0))))))))))))))))))))

def numericRow579 : Integer.Sparse Master := [(Sum.inl 0, -83), (Sum.inl 2, -25), (Sum.inl 3, -80), (Sum.inl 12, -40), (Sum.inl 4, -80), (Sum.inl 1, 110), (Sum.inr 783, 2160), (Sum.inr 785, 2160), (Sum.inr 790, 2160), (Sum.inr 807, 4320), (Sum.inr 1897, 2160), (Sum.inr 1901, 2160), (Sum.inr 1909, 4320), (Sum.inr 2020, 4320), (Sum.inr 2022, 4320), (Sum.inr 2029, 4320), (Sum.inr 2054, 4320), (Sum.inr 2191, 2160), (Sum.inr 2193, 2160), (Sum.inr 2206, 4320), (Sum.inr 2243, 2160), (Sum.inr 2244, 2160), (Sum.inr 2262, 4320), (Sum.inr 3800, 2160), (Sum.inr 3902, 2160)]

theorem reindexCheck579 : Integer.Sparse.reindex keyMap MixedData.row579 = numericRow579 := by decide +kernel

theorem numericCheck579 (x : Master → ℝ) : Integer.Sparse.eval numericRow579 x =
    (2160 : ℝ) * reducedSource579 x := by
  norm_num [numericRow579, reducedSource579, Integer.Sparse.eval, Sparse.eval, nodeValue783, nodeValue785, nodeValue790, nodeValue807, nodeValue1897, nodeValue1901, nodeValue1909, nodeValue2020, nodeValue2022, nodeValue2029, nodeValue2054, nodeValue2191, nodeValue2193, nodeValue2206, nodeValue2243, nodeValue2244, nodeValue2262, nodeValue3800, nodeValue3852, nodeValue3902, nodeValue3911]; ring

noncomputable def reducedSource580 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4455 x + ((1 : ℝ) * Sparse.eval nodeValue4457 x + ((2 : ℝ) * Sparse.eval nodeValue4459 x + ((1 : ℝ) * Sparse.eval nodeValue4495 x + ((1 : ℝ) * Sparse.eval nodeValue4801 x + ((2 : ℝ) * Sparse.eval nodeValue4803 x + ((1 : ℝ) * Sparse.eval nodeValue4831 x + ((1 : ℝ) * Sparse.eval nodeValue4863 x + ((1 : ℝ) * Sparse.eval nodeValue4865 x + ((2 : ℝ) * Sparse.eval nodeValue4867 x + ((1 : ℝ) * Sparse.eval nodeValue4885 x + ((2 : ℝ) * Sparse.eval nodeValue4888 x + ((1 : ℝ) * Sparse.eval nodeValue4889 x + ((2 : ℝ) * Sparse.eval nodeValue4891 x + ((2 : ℝ) * Sparse.eval nodeValue4894 x + ((2 : ℝ) * Sparse.eval nodeValue4895 x + ((2 : ℝ) * Sparse.eval nodeValue4896 x + ((1 : ℝ) * Sparse.eval nodeValue5250 x + ((1 : ℝ) * Sparse.eval nodeValue5282 x + ((1 : ℝ) * Sparse.eval nodeValue5284 x + ((2 : ℝ) * Sparse.eval nodeValue5293 x + 0))))))))))))))))))))

def numericRow580 : Integer.Sparse Master := [(Sum.inl 0, 4), (Sum.inl 2, -5), (Sum.inl 1, -5), (Sum.inr 1040, -180), (Sum.inr 1079, -180), (Sum.inr 1707, -180), (Sum.inr 1708, -180), (Sum.inr 2019, -180), (Sum.inr 2051, -180), (Sum.inr 2106, -180), (Sum.inr 2190, -180), (Sum.inr 2191, -180), (Sum.inr 2242, -180), (Sum.inr 2244, -360), (Sum.inr 2245, -180), (Sum.inr 2262, -360), (Sum.inr 2266, -360), (Sum.inr 2277, -180), (Sum.inr 2278, -360), (Sum.inr 3077, -180), (Sum.inr 3625, -180), (Sum.inr 3627, -360), (Sum.inr 4459, 1440), (Sum.inr 4803, 1440), (Sum.inr 4863, 720), (Sum.inr 4867, 1440), (Sum.inr 4885, 720), (Sum.inr 4891, 1440), (Sum.inr 5282, 720)]

theorem reindexCheck580 : Integer.Sparse.reindex keyMap MixedData.row580 = numericRow580 := by decide +kernel

theorem numericCheck580 (x : Master → ℝ) : Integer.Sparse.eval numericRow580 x =
    (720 : ℝ) * reducedSource580 x := by
  norm_num [numericRow580, reducedSource580, Integer.Sparse.eval, Sparse.eval, nodeValue4455, nodeValue4457, nodeValue4459, nodeValue4495, nodeValue4801, nodeValue4803, nodeValue4831, nodeValue4863, nodeValue4865, nodeValue4867, nodeValue4885, nodeValue4888, nodeValue4889, nodeValue4891, nodeValue4894, nodeValue4895, nodeValue4896, nodeValue5250, nodeValue5282, nodeValue5284, nodeValue5293]; ring

noncomputable def reducedSource581 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1698 x + ((1 : ℝ) * Sparse.eval nodeValue1707 x + ((1 : ℝ) * Sparse.eval nodeValue1708 x + ((2 : ℝ) * Sparse.eval nodeValue1714 x + ((1 : ℝ) * Sparse.eval nodeValue2190 x + ((1 : ℝ) * Sparse.eval nodeValue2191 x + ((2 : ℝ) * Sparse.eval nodeValue2195 x + ((1 : ℝ) * Sparse.eval nodeValue2232 x + ((1 : ℝ) * Sparse.eval nodeValue2233 x + ((1 : ℝ) * Sparse.eval nodeValue2242 x + ((2 : ℝ) * Sparse.eval nodeValue2244 x + ((1 : ℝ) * Sparse.eval nodeValue2245 x + ((2 : ℝ) * Sparse.eval nodeValue2251 x + ((2 : ℝ) * Sparse.eval nodeValue2253 x + ((2 : ℝ) * Sparse.eval nodeValue2264 x + ((2 : ℝ) * Sparse.eval nodeValue2265 x + ((2 : ℝ) * Sparse.eval nodeValue2278 x + ((1 : ℝ) * Sparse.eval nodeValue2709 x + ((1 : ℝ) * Sparse.eval nodeValue2751 x + ((1 : ℝ) * Sparse.eval nodeValue2753 x + ((2 : ℝ) * Sparse.eval nodeValue2767 x + 0))))))))))))))))))))

def numericRow581 : Integer.Sparse Master := [(Sum.inl 0, -114), (Sum.inl 2, 145), (Sum.inl 3, -160), (Sum.inl 13, -80), (Sum.inl 12, -80), (Sum.inl 1, 175), (Sum.inr 1707, 4320), (Sum.inr 1708, 4320), (Sum.inr 1714, 8640), (Sum.inr 2190, 4320), (Sum.inr 2191, 4320), (Sum.inr 2195, 8640), (Sum.inr 2232, 4320), (Sum.inr 2233, 4320), (Sum.inr 2242, 4320), (Sum.inr 2244, 8640), (Sum.inr 2245, 4320), (Sum.inr 2251, 8640), (Sum.inr 2253, 8640), (Sum.inr 2278, 8640), (Sum.inr 2751, 4320)]

theorem reindexCheck581 : Integer.Sparse.reindex keyMap MixedData.row581 = numericRow581 := by decide +kernel

theorem numericCheck581 (x : Master → ℝ) : Integer.Sparse.eval numericRow581 x =
    (4320 : ℝ) * reducedSource581 x := by
  norm_num [numericRow581, reducedSource581, Integer.Sparse.eval, Sparse.eval, nodeValue1698, nodeValue1707, nodeValue1708, nodeValue1714, nodeValue2190, nodeValue2191, nodeValue2195, nodeValue2232, nodeValue2233, nodeValue2242, nodeValue2244, nodeValue2245, nodeValue2251, nodeValue2253, nodeValue2264, nodeValue2265, nodeValue2278, nodeValue2709, nodeValue2751, nodeValue2753, nodeValue2767]; ring

noncomputable def reducedSource582 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1405 x + ((2 : ℝ) * Sparse.eval nodeValue1406 x + ((1 : ℝ) * Sparse.eval nodeValue1414 x + ((1 : ℝ) * Sparse.eval nodeValue1441 x + ((1 : ℝ) * Sparse.eval nodeValue3065 x + ((1 : ℝ) * Sparse.eval nodeValue3077 x + ((1 : ℝ) * Sparse.eval nodeValue3078 x + ((2 : ℝ) * Sparse.eval nodeValue3102 x + ((1 : ℝ) * Sparse.eval nodeValue3179 x + ((2 : ℝ) * Sparse.eval nodeValue3180 x + ((1 : ℝ) * Sparse.eval nodeValue3185 x + ((2 : ℝ) * Sparse.eval nodeValue3202 x + ((1 : ℝ) * Sparse.eval nodeValue3205 x + ((1 : ℝ) * Sparse.eval nodeValue3209 x + ((1 : ℝ) * Sparse.eval nodeValue3221 x + ((2 : ℝ) * Sparse.eval nodeValue3222 x + ((1 : ℝ) * Sparse.eval nodeValue3223 x + ((2 : ℝ) * Sparse.eval nodeValue3225 x + ((2 : ℝ) * Sparse.eval nodeValue3227 x + ((2 : ℝ) * Sparse.eval nodeValue3229 x + ((2 : ℝ) * Sparse.eval nodeValue3230 x + 0))))))))))))))))))))

def numericRow582 : Integer.Sparse Master := [(Sum.inl 0, -111), (Sum.inl 2, 160), (Sum.inl 3, 80), (Sum.inl 13, 80), (Sum.inl 1, 175), (Sum.inr 1406, 2160), (Sum.inr 3077, 1080), (Sum.inr 3078, 1080), (Sum.inr 3179, 1080), (Sum.inr 3180, 2160), (Sum.inr 3202, 2160), (Sum.inr 3221, 1080), (Sum.inr 3222, 2160)]

theorem reindexCheck582 : Integer.Sparse.reindex keyMap MixedData.row582 = numericRow582 := by decide +kernel

theorem numericCheck582 (x : Master → ℝ) : Integer.Sparse.eval numericRow582 x =
    (1080 : ℝ) * reducedSource582 x := by
  norm_num [numericRow582, reducedSource582, Integer.Sparse.eval, Sparse.eval, nodeValue1405, nodeValue1406, nodeValue1414, nodeValue1441, nodeValue3065, nodeValue3077, nodeValue3078, nodeValue3102, nodeValue3179, nodeValue3180, nodeValue3185, nodeValue3202, nodeValue3205, nodeValue3209, nodeValue3221, nodeValue3222, nodeValue3223, nodeValue3225, nodeValue3227, nodeValue3229, nodeValue3230]; ring

noncomputable def reducedSource583 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1038 x + ((1 : ℝ) * Sparse.eval nodeValue1040 x + ((2 : ℝ) * Sparse.eval nodeValue1042 x + ((1 : ℝ) * Sparse.eval nodeValue1079 x + ((1 : ℝ) * Sparse.eval nodeValue2262 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow583 : Integer.Sparse Master := [(Sum.inr 1040, 1), (Sum.inr 1042, 2), (Sum.inr 1079, 1), (Sum.inr 2262, 1), (Sum.inr 4084, -1)]

theorem reindexCheck583 : Integer.Sparse.reindex keyMap MixedData.row583 = numericRow583 := by decide +kernel

theorem numericCheck583 (x : Master → ℝ) : Integer.Sparse.eval numericRow583 x =
    (1 : ℝ) * reducedSource583 x := by
  norm_num [numericRow583, reducedSource583, Integer.Sparse.eval, Sparse.eval, nodeValue1038, nodeValue1040, nodeValue1042, nodeValue1079, nodeValue2262, nodeValue4084]

noncomputable def reducedSource584 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4083 x + ((2 : ℝ) * Sparse.eval nodeValue4458 x + ((1 : ℝ) * Sparse.eval nodeValue4463 x + ((1 : ℝ) * Sparse.eval nodeValue4467 x + ((1 : ℝ) * Sparse.eval nodeValue4502 x + ((2 : ℝ) * Sparse.eval nodeValue4802 x + ((2 : ℝ) * Sparse.eval nodeValue4807 x + ((2 : ℝ) * Sparse.eval nodeValue4811 x + ((2 : ℝ) * Sparse.eval nodeValue4838 x + ((2 : ℝ) * Sparse.eval nodeValue4866 x + ((1 : ℝ) * Sparse.eval nodeValue4871 x + ((1 : ℝ) * Sparse.eval nodeValue4875 x + ((2 : ℝ) * Sparse.eval nodeValue4888 x + ((1 : ℝ) * Sparse.eval nodeValue4890 x + ((2 : ℝ) * Sparse.eval nodeValue4893 x + ((2 : ℝ) * Sparse.eval nodeValue4895 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5304 x + ((1 : ℝ) * Sparse.eval nodeValue5306 x + ((1 : ℝ) * Sparse.eval nodeValue5307 x + 0)))))))))))))))))))

def numericRow584 : Integer.Sparse Master := [(Sum.inl 0, 19), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 1, 110), (Sum.inr 1041, -4320), (Sum.inr 1046, -2160), (Sum.inr 1050, -2160), (Sum.inr 1724, -4320), (Sum.inr 1750, -2160), (Sum.inr 1751, -2160), (Sum.inr 2020, -4320), (Sum.inr 2025, -4320), (Sum.inr 2029, -4320), (Sum.inr 2107, -4320), (Sum.inr 2112, -2160), (Sum.inr 2116, -2160), (Sum.inr 2202, -4320), (Sum.inr 2224, -4320), (Sum.inr 2225, -4320), (Sum.inr 2244, -4320), (Sum.inr 2247, -2160), (Sum.inr 2260, -4320), (Sum.inr 2262, -4320), (Sum.inr 2287, -2160), (Sum.inr 2288, -2160), (Sum.inr 2290, -2160), (Sum.inr 2739, -4320), (Sum.inr 2782, -2160), (Sum.inr 3534, -4320), (Sum.inr 3583, -2160), (Sum.inr 3623, -2160), (Sum.inr 4083, 8640)]

theorem reindexCheck584 : Integer.Sparse.reindex keyMap MixedData.row584 = numericRow584 := by decide +kernel

theorem numericCheck584 (x : Master → ℝ) : Integer.Sparse.eval numericRow584 x =
    (8640 : ℝ) * reducedSource584 x := by
  norm_num [numericRow584, reducedSource584, Integer.Sparse.eval, Sparse.eval, nodeValue4083, nodeValue4458, nodeValue4463, nodeValue4467, nodeValue4502, nodeValue4802, nodeValue4807, nodeValue4811, nodeValue4838, nodeValue4866, nodeValue4871, nodeValue4875, nodeValue4888, nodeValue4890, nodeValue4893, nodeValue4895, nodeValue5271, nodeValue5304, nodeValue5306, nodeValue5307]; ring

noncomputable def reducedSource585 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1724 x + ((1 : ℝ) * Sparse.eval nodeValue1750 x + ((1 : ℝ) * Sparse.eval nodeValue1751 x + ((1 : ℝ) * Sparse.eval nodeValue1753 x + ((2 : ℝ) * Sparse.eval nodeValue2202 x + ((2 : ℝ) * Sparse.eval nodeValue2224 x + ((2 : ℝ) * Sparse.eval nodeValue2225 x + ((2 : ℝ) * Sparse.eval nodeValue2227 x + ((2 : ℝ) * Sparse.eval nodeValue2260 x + ((2 : ℝ) * Sparse.eval nodeValue2262 x + ((2 : ℝ) * Sparse.eval nodeValue2263 x + ((1 : ℝ) * Sparse.eval nodeValue2287 x + ((1 : ℝ) * Sparse.eval nodeValue2288 x + ((1 : ℝ) * Sparse.eval nodeValue2290 x + ((2 : ℝ) * Sparse.eval nodeValue2291 x + ((2 : ℝ) * Sparse.eval nodeValue2739 x + ((1 : ℝ) * Sparse.eval nodeValue2782 x + ((1 : ℝ) * Sparse.eval nodeValue2784 x + ((1 : ℝ) * Sparse.eval nodeValue2785 x + ((1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))))))))))))))))

def numericRow585 : Integer.Sparse Master := [(Sum.inl 0, -19), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 1, -110), (Sum.inr 1724, 4320), (Sum.inr 1750, 2160), (Sum.inr 1751, 2160), (Sum.inr 2202, 4320), (Sum.inr 2224, 4320), (Sum.inr 2225, 4320), (Sum.inr 2260, 4320), (Sum.inr 2262, 4320), (Sum.inr 2287, 2160), (Sum.inr 2288, 2160), (Sum.inr 2290, 2160), (Sum.inr 2739, 4320), (Sum.inr 2782, 2160), (Sum.inr 4083, 2160)]

theorem reindexCheck585 : Integer.Sparse.reindex keyMap MixedData.row585 = numericRow585 := by decide +kernel

theorem numericCheck585 (x : Master → ℝ) : Integer.Sparse.eval numericRow585 x =
    (2160 : ℝ) * reducedSource585 x := by
  norm_num [numericRow585, reducedSource585, Integer.Sparse.eval, Sparse.eval, nodeValue1724, nodeValue1750, nodeValue1751, nodeValue1753, nodeValue2202, nodeValue2224, nodeValue2225, nodeValue2227, nodeValue2260, nodeValue2262, nodeValue2263, nodeValue2287, nodeValue2288, nodeValue2290, nodeValue2291, nodeValue2739, nodeValue2782, nodeValue2784, nodeValue2785, nodeValue4083]; ring

noncomputable def reducedSource586 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2107 x + ((1 : ℝ) * Sparse.eval nodeValue2112 x + ((1 : ℝ) * Sparse.eval nodeValue2116 x + ((1 : ℝ) * Sparse.eval nodeValue2265 x + ((1 : ℝ) * Sparse.eval nodeValue3583 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow586 : Integer.Sparse Master := [(Sum.inr 2107, 2), (Sum.inr 2112, 1), (Sum.inr 2116, 1), (Sum.inr 3583, 1), (Sum.inr 4083, -1)]

theorem reindexCheck586 : Integer.Sparse.reindex keyMap MixedData.row586 = numericRow586 := by decide +kernel

theorem numericCheck586 (x : Master → ℝ) : Integer.Sparse.eval numericRow586 x =
    (1 : ℝ) * reducedSource586 x := by
  norm_num [numericRow586, reducedSource586, Integer.Sparse.eval, Sparse.eval, nodeValue2107, nodeValue2112, nodeValue2116, nodeValue2265, nodeValue3583, nodeValue4083]

noncomputable def reducedSource587 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4084 x + ((2 : ℝ) * Sparse.eval nodeValue4495 x + ((1 : ℝ) * Sparse.eval nodeValue4498 x + ((1 : ℝ) * Sparse.eval nodeValue4499 x + ((1 : ℝ) * Sparse.eval nodeValue4503 x + ((2 : ℝ) * Sparse.eval nodeValue4831 x + ((2 : ℝ) * Sparse.eval nodeValue4834 x + ((2 : ℝ) * Sparse.eval nodeValue4835 x + ((2 : ℝ) * Sparse.eval nodeValue4839 x + ((2 : ℝ) * Sparse.eval nodeValue4888 x + ((2 : ℝ) * Sparse.eval nodeValue4889 x + ((1 : ℝ) * Sparse.eval nodeValue4894 x + ((2 : ℝ) * Sparse.eval nodeValue4895 x + ((2 : ℝ) * Sparse.eval nodeValue4896 x + ((1 : ℝ) * Sparse.eval nodeValue4898 x + ((1 : ℝ) * Sparse.eval nodeValue4901 x + ((2 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5309 x + 0)))))))))))))))))))

def numericRow587 : Integer.Sparse Master := [(Sum.inl 0, 43), (Sum.inl 2, -55), (Sum.inl 3, -80), (Sum.inl 1, -70), (Sum.inr 1079, -4320), (Sum.inr 1083, -2160), (Sum.inr 1087, -2160), (Sum.inr 1708, -4320), (Sum.inr 1728, -2160), (Sum.inr 1739, -2160), (Sum.inr 2051, -4320), (Sum.inr 2054, -4320), (Sum.inr 2058, -4320), (Sum.inr 2191, -4320), (Sum.inr 2206, -4320), (Sum.inr 2216, -4320), (Sum.inr 2244, -4320), (Sum.inr 2245, -4320), (Sum.inr 2262, -4320), (Sum.inr 2266, -4320), (Sum.inr 2277, -4320), (Sum.inr 2278, -4320), (Sum.inr 2279, -4320), (Sum.inr 2723, -4320), (Sum.inr 3544, -4320), (Sum.inr 3627, -2160), (Sum.inr 3632, -2160), (Sum.inr 4084, 8640)]

theorem reindexCheck587 : Integer.Sparse.reindex keyMap MixedData.row587 = numericRow587 := by decide +kernel

theorem numericCheck587 (x : Master → ℝ) : Integer.Sparse.eval numericRow587 x =
    (8640 : ℝ) * reducedSource587 x := by
  norm_num [numericRow587, reducedSource587, Integer.Sparse.eval, Sparse.eval, nodeValue4084, nodeValue4495, nodeValue4498, nodeValue4499, nodeValue4503, nodeValue4831, nodeValue4834, nodeValue4835, nodeValue4839, nodeValue4888, nodeValue4889, nodeValue4894, nodeValue4895, nodeValue4896, nodeValue4898, nodeValue4901, nodeValue5259, nodeValue5293, nodeValue5294, nodeValue5309]; ring

noncomputable def reducedSource588 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4084 x + ((2 : ℝ) * Sparse.eval nodeValue4457 x + ((1 : ℝ) * Sparse.eval nodeValue4460 x + ((1 : ℝ) * Sparse.eval nodeValue4466 x + ((1 : ℝ) * Sparse.eval nodeValue4498 x + ((2 : ℝ) * Sparse.eval nodeValue4801 x + ((2 : ℝ) * Sparse.eval nodeValue4804 x + ((2 : ℝ) * Sparse.eval nodeValue4810 x + ((2 : ℝ) * Sparse.eval nodeValue4834 x + ((2 : ℝ) * Sparse.eval nodeValue4865 x + ((1 : ℝ) * Sparse.eval nodeValue4868 x + ((1 : ℝ) * Sparse.eval nodeValue4874 x + ((2 : ℝ) * Sparse.eval nodeValue4888 x + ((2 : ℝ) * Sparse.eval nodeValue4894 x + ((1 : ℝ) * Sparse.eval nodeValue4895 x + ((1 : ℝ) * Sparse.eval nodeValue4896 x + ((1 : ℝ) * Sparse.eval nodeValue4897 x + ((2 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5308 x + 0))))))))))))))))))))

def numericRow588 : Integer.Sparse Master := [(Sum.inl 0, 4), (Sum.inl 2, -5), (Sum.inl 1, -5), (Sum.inr 1040, -720), (Sum.inr 1043, -360), (Sum.inr 1049, -360), (Sum.inr 1707, -720), (Sum.inr 1725, -360), (Sum.inr 1738, -360), (Sum.inr 2019, -720), (Sum.inr 2022, -720), (Sum.inr 2028, -720), (Sum.inr 2106, -720), (Sum.inr 2109, -360), (Sum.inr 2115, -360), (Sum.inr 2190, -720), (Sum.inr 2203, -720), (Sum.inr 2215, -720), (Sum.inr 2242, -720), (Sum.inr 2244, -720), (Sum.inr 2261, -360), (Sum.inr 2262, -720), (Sum.inr 2266, -360), (Sum.inr 2276, -360), (Sum.inr 2278, -360), (Sum.inr 2722, -720), (Sum.inr 2765, -360), (Sum.inr 3533, -720), (Sum.inr 3582, -360), (Sum.inr 3627, -360), (Sum.inr 4084, 1440)]

theorem reindexCheck588 : Integer.Sparse.reindex keyMap MixedData.row588 = numericRow588 := by decide +kernel

theorem numericCheck588 (x : Master → ℝ) : Integer.Sparse.eval numericRow588 x =
    (1440 : ℝ) * reducedSource588 x := by
  norm_num [numericRow588, reducedSource588, Integer.Sparse.eval, Sparse.eval, nodeValue4084, nodeValue4457, nodeValue4460, nodeValue4466, nodeValue4498, nodeValue4801, nodeValue4804, nodeValue4810, nodeValue4834, nodeValue4865, nodeValue4868, nodeValue4874, nodeValue4888, nodeValue4894, nodeValue4895, nodeValue4896, nodeValue4897, nodeValue5258, nodeValue5291, nodeValue5293, nodeValue5308]; ring

noncomputable def reducedSource589 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4084 x + ((3 : ℝ) * Sparse.eval nodeValue4499 x + ((1 : ℝ) * Sparse.eval nodeValue4507 x + ((1 : ℝ) * Sparse.eval nodeValue4511 x + ((6 : ℝ) * Sparse.eval nodeValue4835 x + ((3 : ℝ) * Sparse.eval nodeValue4843 x + ((3 : ℝ) * Sparse.eval nodeValue4846 x + ((3 : ℝ) * Sparse.eval nodeValue4895 x + ((3 : ℝ) * Sparse.eval nodeValue4896 x + ((1 : ℝ) * Sparse.eval nodeValue4899 x + ((3 : ℝ) * Sparse.eval nodeValue5275 x + ((1 : ℝ) * Sparse.eval nodeValue5309 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + 0))))))))))))

def numericRow589 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 2, -1), (Sum.inl 3, 16), (Sum.inl 1, 2), (Sum.inr 1083, -432), (Sum.inr 1091, -144), (Sum.inr 1728, -432), (Sum.inr 1756, -144), (Sum.inr 2054, -864), (Sum.inr 2062, -432), (Sum.inr 2206, -864), (Sum.inr 2230, -432), (Sum.inr 2266, -432), (Sum.inr 2278, -432), (Sum.inr 2281, -144), (Sum.inr 2294, -144), (Sum.inr 2743, -432), (Sum.inr 3548, -432), (Sum.inr 3633, -144), (Sum.inr 4084, 576)]

theorem reindexCheck589 : Integer.Sparse.reindex keyMap MixedData.row589 = numericRow589 := by decide +kernel

theorem numericCheck589 (x : Master → ℝ) : Integer.Sparse.eval numericRow589 x =
    (576 : ℝ) * reducedSource589 x := by
  norm_num [numericRow589, reducedSource589, Integer.Sparse.eval, Sparse.eval, nodeValue4084, nodeValue4499, nodeValue4507, nodeValue4511, nodeValue4835, nodeValue4843, nodeValue4846, nodeValue4895, nodeValue4896, nodeValue4899, nodeValue5275, nodeValue5309, nodeValue5310]; ring

noncomputable def reducedSource590 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4069 x + ((1 : ℝ) * Sparse.eval nodeValue4070 x + ((1 : ℝ) * Sparse.eval nodeValue4071 x + ((6 : ℝ) * Sparse.eval nodeValue4080 x + ((3 : ℝ) * Sparse.eval nodeValue4081 x + ((3 : ℝ) * Sparse.eval nodeValue4082 x + ((3 : ℝ) * Sparse.eval nodeValue4083 x + ((4 : ℝ) * Sparse.eval nodeValue4084 x + ((1 : ℝ) * Sparse.eval nodeValue4085 x + ((3 : ℝ) * Sparse.eval nodeValue4092 x + ((1 : ℝ) * Sparse.eval nodeValue4093 x + ((1 : ℝ) * Sparse.eval nodeValue4094 x + 0)))))))))))

def numericRow590 : Integer.Sparse Master := [(Sum.inl 0, -3), (Sum.inl 1, -5), (Sum.inr 4069, 120), (Sum.inr 4070, 40), (Sum.inr 4071, 40), (Sum.inr 4080, 240), (Sum.inr 4081, 120), (Sum.inr 4082, 120), (Sum.inr 4083, 120), (Sum.inr 4084, 160), (Sum.inr 4085, 40), (Sum.inr 4092, 120)]

theorem reindexCheck590 : Integer.Sparse.reindex keyMap MixedData.row590 = numericRow590 := by decide +kernel

theorem numericCheck590 (x : Master → ℝ) : Integer.Sparse.eval numericRow590 x =
    (40 : ℝ) * reducedSource590 x := by
  norm_num [numericRow590, reducedSource590, Integer.Sparse.eval, Sparse.eval, nodeValue4069, nodeValue4070, nodeValue4071, nodeValue4080, nodeValue4081, nodeValue4082, nodeValue4083, nodeValue4084, nodeValue4085, nodeValue4092, nodeValue4093, nodeValue4094]; ring

noncomputable def reducedSource591 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1210 x + ((1 : ℝ) * Sparse.eval nodeValue1216 x + ((1 : ℝ) * Sparse.eval nodeValue1228 x + ((1 : ℝ) * Sparse.eval nodeValue1260 x + ((2 : ℝ) * Sparse.eval nodeValue2860 x + ((1 : ℝ) * Sparse.eval nodeValue2864 x + ((1 : ℝ) * Sparse.eval nodeValue2874 x + ((2 : ℝ) * Sparse.eval nodeValue2984 x + ((1 : ℝ) * Sparse.eval nodeValue2988 x + ((1 : ℝ) * Sparse.eval nodeValue2996 x + ((2 : ℝ) * Sparse.eval nodeValue3016 x + ((1 : ℝ) * Sparse.eval nodeValue3023 x + ((1 : ℝ) * Sparse.eval nodeValue3037 x + ((2 : ℝ) * Sparse.eval nodeValue3086 x + ((2 : ℝ) * Sparse.eval nodeValue3089 x + ((2 : ℝ) * Sparse.eval nodeValue3097 x + ((2 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3801 x + ((1 : ℝ) * Sparse.eval nodeValue3954 x + ((1 : ℝ) * Sparse.eval nodeValue3977 x + ((2 : ℝ) * Sparse.eval nodeValue3982 x + 0))))))))))))))))))))

def numericRow591 : Integer.Sparse Master := [(Sum.inl 0, -604), (Sum.inl 5, -160), (Sum.inl 6, 20), (Sum.inl 2, -30), (Sum.inl 7, 320), (Sum.inl 35, 320), (Sum.inl 3, 640), (Sum.inl 13, 160), (Sum.inl 52, 320), (Sum.inl 12, 320), (Sum.inl 1, 290), (Sum.inr 1210, 17280), (Sum.inr 1216, 8640), (Sum.inr 1228, 8640), (Sum.inr 1260, 8640), (Sum.inr 2860, 17280), (Sum.inr 2864, 8640), (Sum.inr 2874, 8640), (Sum.inr 2984, 17280), (Sum.inr 3016, 17280), (Sum.inr 3023, 8640), (Sum.inr 3037, 8640), (Sum.inr 3086, 17280), (Sum.inr 3097, 17280), (Sum.inr 3801, 8640), (Sum.inr 3954, 8640)]

theorem reindexCheck591 : Integer.Sparse.reindex keyMap MixedData.row591 = numericRow591 := by decide +kernel

theorem numericCheck591 (x : Master → ℝ) : Integer.Sparse.eval numericRow591 x =
    (8640 : ℝ) * reducedSource591 x := by
  norm_num [numericRow591, reducedSource591, Integer.Sparse.eval, Sparse.eval, nodeValue1210, nodeValue1216, nodeValue1228, nodeValue1260, nodeValue2860, nodeValue2864, nodeValue2874, nodeValue2984, nodeValue2988, nodeValue2996, nodeValue3016, nodeValue3023, nodeValue3037, nodeValue3086, nodeValue3089, nodeValue3097, nodeValue3109, nodeValue3801, nodeValue3954, nodeValue3977, nodeValue3982]; ring

end MUB6.Certificate.MixedSourceBridge

end OAI
