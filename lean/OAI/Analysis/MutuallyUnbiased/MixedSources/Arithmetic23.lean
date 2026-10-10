import OAI.Analysis.MutuallyUnbiased.MixedData.Source2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource368 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1044 x + ((1 : ℝ) * Sparse.eval nodeValue1046 x + ((1 : ℝ) * Sparse.eval nodeValue1049 x + ((1 : ℝ) * Sparse.eval nodeValue1087 x + ((2 : ℝ) * Sparse.eval nodeValue2483 x + ((2 : ℝ) * Sparse.eval nodeValue2485 x + ((2 : ℝ) * Sparse.eval nodeValue2488 x + ((2 : ℝ) * Sparse.eval nodeValue2515 x + ((2 : ℝ) * Sparse.eval nodeValue2599 x + ((1 : ℝ) * Sparse.eval nodeValue2601 x + ((1 : ℝ) * Sparse.eval nodeValue2604 x + ((2 : ℝ) * Sparse.eval nodeValue2764 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((2 : ℝ) * Sparse.eval nodeValue2768 x + ((1 : ℝ) * Sparse.eval nodeValue2770 x + ((1 : ℝ) * Sparse.eval nodeValue2782 x + ((1 : ℝ) * Sparse.eval nodeValue2788 x + ((2 : ℝ) * Sparse.eval nodeValue3982 x + ((1 : ℝ) * Sparse.eval nodeValue4001 x + ((1 : ℝ) * Sparse.eval nodeValue4017 x + ((1 : ℝ) * Sparse.eval nodeValue4019 x + 0))))))))))))))))))))

def numericRow368 : Integer.Sparse Master := [(Sum.inl 0, -71), (Sum.inl 2, -25), (Sum.inl 3, -80), (Sum.inl 1, 50), (Sum.inr 1044, 1440), (Sum.inr 1046, 720), (Sum.inr 1049, 720), (Sum.inr 1087, 720), (Sum.inr 2483, 1440), (Sum.inr 2485, 1440), (Sum.inr 2488, 1440), (Sum.inr 2515, 1440), (Sum.inr 2764, 1440), (Sum.inr 2765, 720), (Sum.inr 2782, 720)]

theorem reindexCheck368 : Integer.Sparse.reindex keyMap MixedData.row368 = numericRow368 := by decide +kernel

theorem numericCheck368 (x : Master → ℝ) : Integer.Sparse.eval numericRow368 x =
    (720 : ℝ) * reducedSource368 x := by
  norm_num [numericRow368, reducedSource368, Integer.Sparse.eval, Sparse.eval, nodeValue1044, nodeValue1046, nodeValue1049, nodeValue1087, nodeValue2483, nodeValue2485, nodeValue2488, nodeValue2515, nodeValue2599, nodeValue2601, nodeValue2604, nodeValue2764, nodeValue2765, nodeValue2768, nodeValue2770, nodeValue2782, nodeValue2788, nodeValue3982, nodeValue4001, nodeValue4017, nodeValue4019]; ring

noncomputable def reducedSource369 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4889 x + ((1 : ℝ) * Sparse.eval nodeValue4895 x + ((1 : ℝ) * Sparse.eval nodeValue4896 x + ((1 : ℝ) * Sparse.eval nodeValue4898 x + ((2 : ℝ) * Sparse.eval nodeValue5251 x + ((2 : ℝ) * Sparse.eval nodeValue5258 x + ((2 : ℝ) * Sparse.eval nodeValue5259 x + ((2 : ℝ) * Sparse.eval nodeValue5260 x + ((2 : ℝ) * Sparse.eval nodeValue5267 x + ((2 : ℝ) * Sparse.eval nodeValue5270 x + ((1 : ℝ) * Sparse.eval nodeValue5272 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5276 x + ((2 : ℝ) * Sparse.eval nodeValue5284 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((2 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5295 x + ((1 : ℝ) * Sparse.eval nodeValue5302 x + ((1 : ℝ) * Sparse.eval nodeValue5308 x + ((1 : ℝ) * Sparse.eval nodeValue5309 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + 0))))))))))))))))))))

def numericRow369 : Integer.Sparse Master := [(Sum.inl 0, 77), (Sum.inl 2, -95), (Sum.inl 3, 80), (Sum.inl 1, -80), (Sum.inr 2245, -4320), (Sum.inr 2266, -2160), (Sum.inr 2277, -4320), (Sum.inr 2278, -2160), (Sum.inr 2279, -4320), (Sum.inr 2722, -4320), (Sum.inr 2723, -4320), (Sum.inr 2740, -4320), (Sum.inr 3054, -2160), (Sum.inr 3077, -4320), (Sum.inr 3533, -4320), (Sum.inr 3544, -4320), (Sum.inr 3625, -4320), (Sum.inr 3626, -2160), (Sum.inr 3627, -2160), (Sum.inr 3632, -4320), (Sum.inr 3633, -2160), (Sum.inr 5251, 17280), (Sum.inr 5260, 17280), (Sum.inr 5267, 17280), (Sum.inr 5270, 17280), (Sum.inr 5276, 8640), (Sum.inr 5295, 8640)]

theorem reindexCheck369 : Integer.Sparse.reindex keyMap MixedData.row369 = numericRow369 := by decide +kernel

theorem numericCheck369 (x : Master → ℝ) : Integer.Sparse.eval numericRow369 x =
    (8640 : ℝ) * reducedSource369 x := by
  norm_num [numericRow369, reducedSource369, Integer.Sparse.eval, Sparse.eval, nodeValue4889, nodeValue4895, nodeValue4896, nodeValue4898, nodeValue5251, nodeValue5258, nodeValue5259, nodeValue5260, nodeValue5267, nodeValue5270, nodeValue5272, nodeValue5274, nodeValue5276, nodeValue5284, nodeValue5293, nodeValue5294, nodeValue5295, nodeValue5302, nodeValue5308, nodeValue5309, nodeValue5310]; ring

noncomputable def reducedSource370 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2245 x + ((1 : ℝ) * Sparse.eval nodeValue2265 x + ((1 : ℝ) * Sparse.eval nodeValue2266 x + ((1 : ℝ) * Sparse.eval nodeValue2279 x + ((2 : ℝ) * Sparse.eval nodeValue2710 x + ((2 : ℝ) * Sparse.eval nodeValue2723 x + ((2 : ℝ) * Sparse.eval nodeValue2724 x + ((2 : ℝ) * Sparse.eval nodeValue2732 x + ((2 : ℝ) * Sparse.eval nodeValue2753 x + ((2 : ℝ) * Sparse.eval nodeValue2754 x + ((1 : ℝ) * Sparse.eval nodeValue2767 x + ((2 : ℝ) * Sparse.eval nodeValue2768 x + ((1 : ℝ) * Sparse.eval nodeValue2769 x + ((1 : ℝ) * Sparse.eval nodeValue2776 x + ((1 : ℝ) * Sparse.eval nodeValue2777 x + ((1 : ℝ) * Sparse.eval nodeValue2787 x + ((1 : ℝ) * Sparse.eval nodeValue2788 x + ((2 : ℝ) * Sparse.eval nodeValue3089 x + ((1 : ℝ) * Sparse.eval nodeValue3112 x + ((1 : ℝ) * Sparse.eval nodeValue3113 x + ((1 : ℝ) * Sparse.eval nodeValue3124 x + 0))))))))))))))))))))

def numericRow370 : Integer.Sparse Master := [(Sum.inl 0, -53), (Sum.inl 2, 65), (Sum.inl 3, -80), (Sum.inl 1, 50), (Sum.inr 2245, 1440), (Sum.inr 2266, 720), (Sum.inr 2279, 720), (Sum.inr 2710, 1440), (Sum.inr 2723, 1440), (Sum.inr 2724, 1440), (Sum.inr 2732, 1440), (Sum.inr 2754, 1440), (Sum.inr 2769, 720), (Sum.inr 2777, 720)]

theorem reindexCheck370 : Integer.Sparse.reindex keyMap MixedData.row370 = numericRow370 := by decide +kernel

theorem numericCheck370 (x : Master → ℝ) : Integer.Sparse.eval numericRow370 x =
    (720 : ℝ) * reducedSource370 x := by
  norm_num [numericRow370, reducedSource370, Integer.Sparse.eval, Sparse.eval, nodeValue2245, nodeValue2265, nodeValue2266, nodeValue2279, nodeValue2710, nodeValue2723, nodeValue2724, nodeValue2732, nodeValue2753, nodeValue2754, nodeValue2767, nodeValue2768, nodeValue2769, nodeValue2776, nodeValue2777, nodeValue2787, nodeValue2788, nodeValue3089, nodeValue3112, nodeValue3113, nodeValue3124]; ring

noncomputable def reducedSource371 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1229 x + ((1 : ℝ) * Sparse.eval nodeValue1231 x + ((1 : ℝ) * Sparse.eval nodeValue1245 x + ((1 : ℝ) * Sparse.eval nodeValue1292 x + ((2 : ℝ) * Sparse.eval nodeValue1639 x + ((1 : ℝ) * Sparse.eval nodeValue1651 x + ((1 : ℝ) * Sparse.eval nodeValue1716 x + ((2 : ℝ) * Sparse.eval nodeValue2875 x + ((1 : ℝ) * Sparse.eval nodeValue2888 x + ((2 : ℝ) * Sparse.eval nodeValue2921 x + ((2 : ℝ) * Sparse.eval nodeValue2930 x + ((2 : ℝ) * Sparse.eval nodeValue2952 x + ((2 : ℝ) * Sparse.eval nodeValue3024 x + ((1 : ℝ) * Sparse.eval nodeValue3052 x + ((2 : ℝ) * Sparse.eval nodeValue3097 x + ((1 : ℝ) * Sparse.eval nodeValue3103 x + ((1 : ℝ) * Sparse.eval nodeValue3119 x + ((2 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((1 : ℝ) * Sparse.eval nodeValue3626 x + ((1 : ℝ) * Sparse.eval nodeValue3987 x + 0))))))))))))))))))))

def numericRow371 : Integer.Sparse Master := [(Sum.inl 0, -45), (Sum.inl 2, -5), (Sum.inl 3, 240), (Sum.inl 26, 160), (Sum.inl 4, 160), (Sum.inl 1, 60), (Sum.inr 1229, 4320), (Sum.inr 1231, 2160), (Sum.inr 1245, 2160), (Sum.inr 1292, 2160), (Sum.inr 1639, 4320), (Sum.inr 1651, 2160), (Sum.inr 1716, 2160), (Sum.inr 2875, 4320), (Sum.inr 2888, 2160), (Sum.inr 2921, 4320), (Sum.inr 2930, 4320), (Sum.inr 2952, 4320), (Sum.inr 3024, 4320), (Sum.inr 3052, 2160), (Sum.inr 3097, 4320), (Sum.inr 3573, 4320), (Sum.inr 3584, 2160), (Sum.inr 3626, 2160)]

theorem reindexCheck371 : Integer.Sparse.reindex keyMap MixedData.row371 = numericRow371 := by decide +kernel

theorem numericCheck371 (x : Master → ℝ) : Integer.Sparse.eval numericRow371 x =
    (2160 : ℝ) * reducedSource371 x := by
  norm_num [numericRow371, reducedSource371, Integer.Sparse.eval, Sparse.eval, nodeValue1229, nodeValue1231, nodeValue1245, nodeValue1292, nodeValue1639, nodeValue1651, nodeValue1716, nodeValue2875, nodeValue2888, nodeValue2921, nodeValue2930, nodeValue2952, nodeValue3024, nodeValue3052, nodeValue3097, nodeValue3103, nodeValue3119, nodeValue3573, nodeValue3584, nodeValue3626, nodeValue3987]; ring

noncomputable def reducedSource372 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1070 x + ((1 : ℝ) * Sparse.eval nodeValue1072 x + ((1 : ℝ) * Sparse.eval nodeValue1076 x + ((1 : ℝ) * Sparse.eval nodeValue1084 x + ((2 : ℝ) * Sparse.eval nodeValue2500 x + ((2 : ℝ) * Sparse.eval nodeValue2502 x + ((2 : ℝ) * Sparse.eval nodeValue2506 x + ((2 : ℝ) * Sparse.eval nodeValue2513 x + ((2 : ℝ) * Sparse.eval nodeValue2681 x + ((1 : ℝ) * Sparse.eval nodeValue2683 x + ((1 : ℝ) * Sparse.eval nodeValue2687 x + ((2 : ℝ) * Sparse.eval nodeValue2735 x + ((1 : ℝ) * Sparse.eval nodeValue2737 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + ((2 : ℝ) * Sparse.eval nodeValue2773 x + ((1 : ℝ) * Sparse.eval nodeValue2774 x + ((1 : ℝ) * Sparse.eval nodeValue2776 x + ((2 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3582 x + ((1 : ℝ) * Sparse.eval nodeValue3583 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + 0))))))))))))))))))))

def numericRow372 : Integer.Sparse Master := [(Sum.inl 0, -29), (Sum.inl 2, 5), (Sum.inl 3, 160), (Sum.inl 13, 80), (Sum.inl 12, 80), (Sum.inl 4, 80), (Sum.inl 1, -10), (Sum.inr 1070, 4320), (Sum.inr 1072, 2160), (Sum.inr 1076, 2160), (Sum.inr 1084, 2160), (Sum.inr 2500, 4320), (Sum.inr 2502, 4320), (Sum.inr 2506, 4320), (Sum.inr 2513, 4320), (Sum.inr 2681, 4320), (Sum.inr 2683, 2160), (Sum.inr 2687, 2160), (Sum.inr 2735, 4320), (Sum.inr 2737, 2160), (Sum.inr 2744, 2160), (Sum.inr 2773, 4320), (Sum.inr 2774, 2160), (Sum.inr 3572, 4320), (Sum.inr 3582, 2160), (Sum.inr 3583, 2160)]

theorem reindexCheck372 : Integer.Sparse.reindex keyMap MixedData.row372 = numericRow372 := by decide +kernel

theorem numericCheck372 (x : Master → ℝ) : Integer.Sparse.eval numericRow372 x =
    (2160 : ℝ) * reducedSource372 x := by
  norm_num [numericRow372, reducedSource372, Integer.Sparse.eval, Sparse.eval, nodeValue1070, nodeValue1072, nodeValue1076, nodeValue1084, nodeValue2500, nodeValue2502, nodeValue2506, nodeValue2513, nodeValue2681, nodeValue2683, nodeValue2687, nodeValue2735, nodeValue2737, nodeValue2744, nodeValue2773, nodeValue2774, nodeValue2776, nodeValue3572, nodeValue3582, nodeValue3583, nodeValue3888]; ring

noncomputable def reducedSource373 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2769 x + ((2 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3054 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((1 : ℝ) * Sparse.eval nodeValue3913 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow373 : Integer.Sparse Master := [(Sum.inr 2769, 1), (Sum.inr 3051, 2), (Sum.inr 3054, 1), (Sum.inr 3055, 1), (Sum.inr 3913, 1), (Sum.inr 4092, -1)]

theorem reindexCheck373 : Integer.Sparse.reindex keyMap MixedData.row373 = numericRow373 := by decide +kernel

theorem numericCheck373 (x : Master → ℝ) : Integer.Sparse.eval numericRow373 x =
    (1 : ℝ) * reducedSource373 x := by
  norm_num [numericRow373, reducedSource373, Integer.Sparse.eval, Sparse.eval, nodeValue2769, nodeValue3051, nodeValue3054, nodeValue3055, nodeValue3913, nodeValue4092]

noncomputable def reducedSource374 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1268 x + ((1 : ℝ) * Sparse.eval nodeValue1272 x + ((1 : ℝ) * Sparse.eval nodeValue1273 x + ((1 : ℝ) * Sparse.eval nodeValue1306 x + ((1 : ℝ) * Sparse.eval nodeValue2769 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow374 : Integer.Sparse Master := [(Sum.inr 1268, 2), (Sum.inr 1272, 1), (Sum.inr 1273, 1), (Sum.inr 1306, 1), (Sum.inr 2769, 1), (Sum.inr 4092, -1)]

theorem reindexCheck374 : Integer.Sparse.reindex keyMap MixedData.row374 = numericRow374 := by decide +kernel

theorem numericCheck374 (x : Master → ℝ) : Integer.Sparse.eval numericRow374 x =
    (1 : ℝ) * reducedSource374 x := by
  norm_num [numericRow374, reducedSource374, Integer.Sparse.eval, Sparse.eval, nodeValue1268, nodeValue1272, nodeValue1273, nodeValue1306, nodeValue2769, nodeValue4092]

noncomputable def reducedSource375 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1268 x + ((1 : ℝ) * Sparse.eval nodeValue2571 x + ((1 : ℝ) * Sparse.eval nodeValue2639 x + ((1 : ℝ) * Sparse.eval nodeValue2759 x + ((1 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue2769 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow375 : Integer.Sparse Master := [(Sum.inr 1268, 1), (Sum.inr 2571, 1), (Sum.inr 2639, 1), (Sum.inr 2759, 1), (Sum.inr 2763, 1), (Sum.inr 2769, 1), (Sum.inr 4092, -1)]

theorem reindexCheck375 : Integer.Sparse.reindex keyMap MixedData.row375 = numericRow375 := by decide +kernel

theorem numericCheck375 (x : Master → ℝ) : Integer.Sparse.eval numericRow375 x =
    (1 : ℝ) * reducedSource375 x := by
  norm_num [numericRow375, reducedSource375, Integer.Sparse.eval, Sparse.eval, nodeValue1268, nodeValue2571, nodeValue2639, nodeValue2759, nodeValue2763, nodeValue2769, nodeValue4092]

noncomputable def reducedSource376 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1433 x + ((1 : ℝ) * Sparse.eval nodeValue2571 x + ((1 : ℝ) * Sparse.eval nodeValue2575 x + ((1 : ℝ) * Sparse.eval nodeValue2600 x + ((1 : ℝ) * Sparse.eval nodeValue2769 x + ((1 : ℝ) * Sparse.eval nodeValue3051 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow376 : Integer.Sparse Master := [(Sum.inr 1433, 1), (Sum.inr 2571, 1), (Sum.inr 2575, 1), (Sum.inr 2600, 1), (Sum.inr 2769, 1), (Sum.inr 3051, 1), (Sum.inr 4092, -1)]

theorem reindexCheck376 : Integer.Sparse.reindex keyMap MixedData.row376 = numericRow376 := by decide +kernel

theorem numericCheck376 (x : Master → ℝ) : Integer.Sparse.eval numericRow376 x =
    (1 : ℝ) * reducedSource376 x := by
  norm_num [numericRow376, reducedSource376, Integer.Sparse.eval, Sparse.eval, nodeValue1433, nodeValue2571, nodeValue2575, nodeValue2600, nodeValue2769, nodeValue3051, nodeValue4092]

noncomputable def reducedSource377 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1437 x + ((2 : ℝ) * Sparse.eval nodeValue2639 x + ((1 : ℝ) * Sparse.eval nodeValue2643 x + ((1 : ℝ) * Sparse.eval nodeValue2769 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow377 : Integer.Sparse Master := [(Sum.inr 1437, 1), (Sum.inr 2639, 2), (Sum.inr 2643, 1), (Sum.inr 2769, 1), (Sum.inr 3055, 1), (Sum.inr 4092, -1)]

theorem reindexCheck377 : Integer.Sparse.reindex keyMap MixedData.row377 = numericRow377 := by decide +kernel

theorem numericCheck377 (x : Master → ℝ) : Integer.Sparse.eval numericRow377 x =
    (1 : ℝ) * reducedSource377 x := by
  norm_num [numericRow377, reducedSource377, Integer.Sparse.eval, Sparse.eval, nodeValue1437, nodeValue2639, nodeValue2643, nodeValue2769, nodeValue3055, nodeValue4092]

noncomputable def reducedSource378 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1273 x + ((2 : ℝ) * Sparse.eval nodeValue2575 x + ((1 : ℝ) * Sparse.eval nodeValue2643 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((1 : ℝ) * Sparse.eval nodeValue2769 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow378 : Integer.Sparse Master := [(Sum.inr 1273, 1), (Sum.inr 2575, 2), (Sum.inr 2643, 1), (Sum.inr 2765, 1), (Sum.inr 2769, 1), (Sum.inr 4092, -1)]

theorem reindexCheck378 : Integer.Sparse.reindex keyMap MixedData.row378 = numericRow378 := by decide +kernel

theorem numericCheck378 (x : Master → ℝ) : Integer.Sparse.eval numericRow378 x =
    (1 : ℝ) * reducedSource378 x := by
  norm_num [numericRow378, reducedSource378, Integer.Sparse.eval, Sparse.eval, nodeValue1273, nodeValue2575, nodeValue2643, nodeValue2765, nodeValue2769, nodeValue4092]

noncomputable def reducedSource379 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1272 x + ((2 : ℝ) * Sparse.eval nodeValue1433 x + ((1 : ℝ) * Sparse.eval nodeValue1436 x + ((1 : ℝ) * Sparse.eval nodeValue1437 x + ((1 : ℝ) * Sparse.eval nodeValue2769 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow379 : Integer.Sparse Master := [(Sum.inr 1272, 1), (Sum.inr 1433, 2), (Sum.inr 1436, 1), (Sum.inr 1437, 1), (Sum.inr 2769, 1), (Sum.inr 4092, -1)]

theorem reindexCheck379 : Integer.Sparse.reindex keyMap MixedData.row379 = numericRow379 := by decide +kernel

theorem numericCheck379 (x : Master → ℝ) : Integer.Sparse.eval numericRow379 x =
    (1 : ℝ) * reducedSource379 x := by
  norm_num [numericRow379, reducedSource379, Integer.Sparse.eval, Sparse.eval, nodeValue1272, nodeValue1433, nodeValue1436, nodeValue1437, nodeValue2769, nodeValue4092]

noncomputable def reducedSource380 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1656 x + ((1 : ℝ) * Sparse.eval nodeValue1657 x + ((1 : ℝ) * Sparse.eval nodeValue1661 x + ((1 : ℝ) * Sparse.eval nodeValue1745 x + ((2 : ℝ) * Sparse.eval nodeValue2259 x + ((1 : ℝ) * Sparse.eval nodeValue2287 x + ((1 : ℝ) * Sparse.eval nodeValue2290 x + ((2 : ℝ) * Sparse.eval nodeValue2584 x + ((1 : ℝ) * Sparse.eval nodeValue2603 x + ((2 : ℝ) * Sparse.eval nodeValue2717 x + ((2 : ℝ) * Sparse.eval nodeValue2735 x + ((2 : ℝ) * Sparse.eval nodeValue2738 x + ((1 : ℝ) * Sparse.eval nodeValue2761 x + ((2 : ℝ) * Sparse.eval nodeValue2762 x + ((2 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue2781 x + ((1 : ℝ) * Sparse.eval nodeValue2782 x + ((1 : ℝ) * Sparse.eval nodeValue2784 x + ((2 : ℝ) * Sparse.eval nodeValue3096 x + ((1 : ℝ) * Sparse.eval nodeValue3118 x + ((1 : ℝ) * Sparse.eval nodeValue3119 x + 0))))))))))))))))))))

def numericRow380 : Integer.Sparse Master := [(Sum.inl 0, -64), (Sum.inl 2, -40), (Sum.inl 3, 320), (Sum.inl 26, 160), (Sum.inl 4, 160), (Sum.inl 1, -200), (Sum.inr 1656, 8640), (Sum.inr 1657, 4320), (Sum.inr 1661, 4320), (Sum.inr 1745, 4320), (Sum.inr 2259, 8640), (Sum.inr 2287, 4320), (Sum.inr 2290, 4320), (Sum.inr 2584, 8640), (Sum.inr 2603, 4320), (Sum.inr 2717, 8640), (Sum.inr 2735, 8640), (Sum.inr 2738, 8640), (Sum.inr 2761, 4320), (Sum.inr 2762, 8640), (Sum.inr 2763, 8640), (Sum.inr 2781, 4320), (Sum.inr 2782, 4320), (Sum.inr 3096, 8640), (Sum.inr 3118, 4320)]

theorem reindexCheck380 : Integer.Sparse.reindex keyMap MixedData.row380 = numericRow380 := by decide +kernel

theorem numericCheck380 (x : Master → ℝ) : Integer.Sparse.eval numericRow380 x =
    (4320 : ℝ) * reducedSource380 x := by
  norm_num [numericRow380, reducedSource380, Integer.Sparse.eval, Sparse.eval, nodeValue1656, nodeValue1657, nodeValue1661, nodeValue1745, nodeValue2259, nodeValue2287, nodeValue2290, nodeValue2584, nodeValue2603, nodeValue2717, nodeValue2735, nodeValue2738, nodeValue2761, nodeValue2762, nodeValue2763, nodeValue2781, nodeValue2782, nodeValue2784, nodeValue3096, nodeValue3118, nodeValue3119]; ring

noncomputable def reducedSource381 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3098 x + ((2 : ℝ) * Sparse.eval nodeValue3572 x + ((2 : ℝ) * Sparse.eval nodeValue3583 x + ((1 : ℝ) * Sparse.eval nodeValue3623 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

def numericRow381 : Integer.Sparse Master := [(Sum.inr 3098, 1), (Sum.inr 3572, 2), (Sum.inr 3583, 2), (Sum.inr 3623, 1), (Sum.inr 4083, -1)]

theorem reindexCheck381 : Integer.Sparse.reindex keyMap MixedData.row381 = numericRow381 := by decide +kernel

theorem numericCheck381 (x : Master → ℝ) : Integer.Sparse.eval numericRow381 x =
    (1 : ℝ) * reducedSource381 x := by
  norm_num [numericRow381, reducedSource381, Integer.Sparse.eval, Sparse.eval, nodeValue3098, nodeValue3572, nodeValue3583, nodeValue3623, nodeValue4083]

noncomputable def reducedSource382 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1404 x + ((1 : ℝ) * Sparse.eval nodeValue1408 x + ((1 : ℝ) * Sparse.eval nodeValue1418 x + ((1 : ℝ) * Sparse.eval nodeValue1440 x + ((1 : ℝ) * Sparse.eval nodeValue3098 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow382 : Integer.Sparse Master := [(Sum.inr 1404, 2), (Sum.inr 1408, 1), (Sum.inr 1418, 1), (Sum.inr 1440, 1), (Sum.inr 3098, 1), (Sum.inr 4083, -1)]

theorem reindexCheck382 : Integer.Sparse.reindex keyMap MixedData.row382 = numericRow382 := by decide +kernel

theorem numericCheck382 (x : Master → ℝ) : Integer.Sparse.eval numericRow382 x =
    (1 : ℝ) * reducedSource382 x := by
  norm_num [numericRow382, reducedSource382, Integer.Sparse.eval, Sparse.eval, nodeValue1404, nodeValue1408, nodeValue1418, nodeValue1440, nodeValue3098, nodeValue4083]

noncomputable def reducedSource383 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1404 x + ((1 : ℝ) * Sparse.eval nodeValue2952 x + ((1 : ℝ) * Sparse.eval nodeValue2983 x + ((1 : ℝ) * Sparse.eval nodeValue3075 x + ((1 : ℝ) * Sparse.eval nodeValue3096 x + ((1 : ℝ) * Sparse.eval nodeValue3098 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

def numericRow383 : Integer.Sparse Master := [(Sum.inr 1404, 1), (Sum.inr 2952, 1), (Sum.inr 2983, 1), (Sum.inr 3075, 1), (Sum.inr 3096, 1), (Sum.inr 3098, 1), (Sum.inr 4083, -1)]

theorem reindexCheck383 : Integer.Sparse.reindex keyMap MixedData.row383 = numericRow383 := by decide +kernel

theorem numericCheck383 (x : Master → ℝ) : Integer.Sparse.eval numericRow383 x =
    (1 : ℝ) * reducedSource383 x := by
  norm_num [numericRow383, reducedSource383, Integer.Sparse.eval, Sparse.eval, nodeValue1404, nodeValue2952, nodeValue2983, nodeValue3075, nodeValue3096, nodeValue3098, nodeValue4083]

end MUB6.Certificate.MixedSourceBridge

end OAI
