import OAI.Analysis.MutuallyUnbiased.MixedData.Source7
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
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

noncomputable def reducedSource896 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4848 x + ((2 : ℝ) * Sparse.eval nodeValue4849 x + ((2 : ℝ) * Sparse.eval nodeValue4852 x + ((2 : ℝ) * Sparse.eval nodeValue5378 x + ((2 : ℝ) * Sparse.eval nodeValue5379 x + ((2 : ℝ) * Sparse.eval nodeValue5381 x + ((2 : ℝ) * Sparse.eval nodeValue5382 x + ((2 : ℝ) * Sparse.eval nodeValue5397 x + ((2 : ℝ) * Sparse.eval nodeValue5411 x + ((2 : ℝ) * Sparse.eval nodeValue5420 x + ((2 : ℝ) * Sparse.eval nodeValue5421 x + ((2 : ℝ) * Sparse.eval nodeValue5424 x + ((2 : ℝ) * Sparse.eval nodeValue5425 x + ((2 : ℝ) * Sparse.eval nodeValue5446 x + ((2 : ℝ) * Sparse.eval nodeValue5477 x + ((1 : ℝ) * Sparse.eval nodeValue5483 x + 0)))))))))))))))

def numericRow896 : Integer.Sparse Master := [(Sum.inl 0, 11), (Sum.inl 2, 5), (Sum.inl 1, -10), (Sum.inr 3719, -1440), (Sum.inr 3782, -1440), (Sum.inr 3795, -1440), (Sum.inr 3796, -1440), (Sum.inr 3809, -1440), (Sum.inr 3813, -1440), (Sum.inr 3838, -1440), (Sum.inr 3843, -1440), (Sum.inr 4047, -720), (Sum.inr 4848, 2880), (Sum.inr 4849, 5760), (Sum.inr 4852, 5760), (Sum.inr 5379, 5760), (Sum.inr 5381, 5760), (Sum.inr 5382, 5760), (Sum.inr 5420, 5760), (Sum.inr 5421, 5760), (Sum.inr 5425, 5760), (Sum.inr 5446, 5760)]

theorem reindexCheck896 : Integer.Sparse.reindex keyMap MixedData.row896 = numericRow896 := by decide +kernel

theorem numericCheck896 (x : Master → ℝ) : Integer.Sparse.eval numericRow896 x =
    (2880 : ℝ) * reducedSource896 x := by
  norm_num [numericRow896, reducedSource896, Integer.Sparse.eval, Sparse.eval, nodeValue4848, nodeValue4849, nodeValue4852, nodeValue5378, nodeValue5379, nodeValue5381, nodeValue5382, nodeValue5397, nodeValue5411, nodeValue5420, nodeValue5421, nodeValue5424, nodeValue5425, nodeValue5446, nodeValue5477, nodeValue5483]
  ring

noncomputable def reducedSource897 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2085 x + ((1 : ℝ) * Sparse.eval nodeValue2086 x + ((1 : ℝ) * Sparse.eval nodeValue2089 x + ((1 : ℝ) * Sparse.eval nodeValue2098 x + ((1 : ℝ) * Sparse.eval nodeValue2250 x + ((1 : ℝ) * Sparse.eval nodeValue3723 x + ((1 : ℝ) * Sparse.eval nodeValue3724 x + ((1 : ℝ) * Sparse.eval nodeValue3727 x + ((1 : ℝ) * Sparse.eval nodeValue3730 x + ((1 : ℝ) * Sparse.eval nodeValue3795 x + ((1 : ℝ) * Sparse.eval nodeValue3796 x + ((1 : ℝ) * Sparse.eval nodeValue3813 x + ((1 : ℝ) * Sparse.eval nodeValue3826 x + ((1 : ℝ) * Sparse.eval nodeValue3827 x + ((1 : ℝ) * Sparse.eval nodeValue3830 x + ((1 : ℝ) * Sparse.eval nodeValue3832 x + ((1 : ℝ) * Sparse.eval nodeValue3834 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3866 x + ((1 : ℝ) * Sparse.eval nodeValue3870 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3873 x + ((1 : ℝ) * Sparse.eval nodeValue3881 x + ((1 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3971 x + ((1 : ℝ) * Sparse.eval nodeValue3981 x + ((1 : ℝ) * Sparse.eval nodeValue3989 x + ((1 : ℝ) * Sparse.eval nodeValue3990 x + 0)))))))))))))))))))))))))))))

def numericRow897 : Integer.Sparse Master := [(Sum.inl 0, -171), (Sum.inl 6, -5), (Sum.inl 2, 5), (Sum.inl 7, 160), (Sum.inl 35, 160), (Sum.inl 51, -240), (Sum.inl 3, 1280), (Sum.inl 13, 240), (Sum.inl 52, 80), (Sum.inl 23, -480), (Sum.inl 54, -240), (Sum.inl 24, -240), (Sum.inl 55, -480), (Sum.inl 12, 480), (Sum.inl 25, -240), (Sum.inl 26, 240), (Sum.inl 4, 400), (Sum.inl 27, 60), (Sum.inl 1, 5), (Sum.inr 2085, 4320), (Sum.inr 2086, 4320), (Sum.inr 2089, 4320), (Sum.inr 2098, 4320), (Sum.inr 2250, 4320), (Sum.inr 3723, 4320), (Sum.inr 3724, 4320), (Sum.inr 3730, 4320), (Sum.inr 3795, 4320), (Sum.inr 3796, 4320), (Sum.inr 3813, 4320), (Sum.inr 3826, 4320), (Sum.inr 3827, 4320), (Sum.inr 3832, 4320), (Sum.inr 3834, 4320), (Sum.inr 3838, 4320), (Sum.inr 3840, 4320), (Sum.inr 3866, 4320), (Sum.inr 3870, 4320), (Sum.inr 3872, 4320), (Sum.inr 3873, 4320), (Sum.inr 3881, 4320), (Sum.inr 3884, 4320)]

theorem reindexCheck897 : Integer.Sparse.reindex keyMap MixedData.row897 = numericRow897 := by decide +kernel

theorem numericCheck897 (x : Master → ℝ) : Integer.Sparse.eval numericRow897 x =
    (4320 : ℝ) * reducedSource897 x := by
  norm_num [numericRow897, reducedSource897, Integer.Sparse.eval, Sparse.eval, nodeValue2085, nodeValue2086, nodeValue2089, nodeValue2098, nodeValue2250, nodeValue3723, nodeValue3724, nodeValue3727, nodeValue3730, nodeValue3795, nodeValue3796, nodeValue3813, nodeValue3826, nodeValue3827, nodeValue3830, nodeValue3832, nodeValue3834, nodeValue3838, nodeValue3840, nodeValue3866, nodeValue3870, nodeValue3872, nodeValue3873, nodeValue3881, nodeValue3883, nodeValue3884, nodeValue3971, nodeValue3981, nodeValue3989, nodeValue3990]
  ring

noncomputable def reducedSource898 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5073 x + ((1 : ℝ) * Sparse.eval nodeValue5075 x + ((1 : ℝ) * Sparse.eval nodeValue5081 x + ((1 : ℝ) * Sparse.eval nodeValue5102 x + ((1 : ℝ) * Sparse.eval nodeValue5137 x + ((1 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5169 x + ((1 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5352 x + ((1 : ℝ) * Sparse.eval nodeValue5356 x + ((1 : ℝ) * Sparse.eval nodeValue5368 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5460 x + ((1 : ℝ) * Sparse.eval nodeValue5465 x + ((1 : ℝ) * Sparse.eval nodeValue5469 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5476 x + ((1 : ℝ) * Sparse.eval nodeValue5477 x + ((2 : ℝ) * Sparse.eval nodeValue5482 x + ((2 : ℝ) * Sparse.eval nodeValue5483 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + ((1 : ℝ) * Sparse.eval nodeValue5486 x + ((1 : ℝ) * Sparse.eval nodeValue5487 x + ((1 : ℝ) * Sparse.eval nodeValue5490 x + ((1 : ℝ) * Sparse.eval nodeValue5491 x + ((1 : ℝ) * Sparse.eval nodeValue5493 x + ((1 : ℝ) * Sparse.eval nodeValue5499 x + 0)))))))))))))))))))))))))))

def numericRow898 : Integer.Sparse Master := [(Sum.inl 0, 763), (Sum.inl 2, -120), (Sum.inl 4, 80), (Sum.inl 1, 645), (Sum.inr 2480, -4320), (Sum.inr 2482, -4320), (Sum.inr 2489, -4320), (Sum.inr 2512, -4320), (Sum.inr 2556, -4320), (Sum.inr 2561, -4320), (Sum.inr 2723, -4320), (Sum.inr 3467, -4320), (Sum.inr 3468, -4320), (Sum.inr 3471, -4320), (Sum.inr 3482, -4320), (Sum.inr 3521, -4320), (Sum.inr 3522, -4320), (Sum.inr 3544, -4320), (Sum.inr 3607, -4320), (Sum.inr 3627, -4320), (Sum.inr 3690, -4320), (Sum.inr 3694, -4320), (Sum.inr 3705, -4320), (Sum.inr 3764, -4320), (Sum.inr 3767, -4320), (Sum.inr 3773, -4320), (Sum.inr 3903, -4320), (Sum.inr 3945, -4320), (Sum.inr 3952, -4320), (Sum.inr 3958, -4320), (Sum.inr 3961, -4320), (Sum.inr 4010, -4320), (Sum.inr 4042, -4320), (Sum.inr 4045, -4320), (Sum.inr 4046, -8640), (Sum.inr 4047, -8640)]

theorem reindexCheck898 : Integer.Sparse.reindex keyMap MixedData.row898 = numericRow898 := by decide +kernel

theorem numericCheck898 (x : Master → ℝ) : Integer.Sparse.eval numericRow898 x =
    (17280 : ℝ) * reducedSource898 x := by
  norm_num [numericRow898, reducedSource898, Integer.Sparse.eval, Sparse.eval, nodeValue5073, nodeValue5075, nodeValue5081, nodeValue5102, nodeValue5137, nodeValue5141, nodeValue5169, nodeValue5259, nodeValue5293, nodeValue5352, nodeValue5356, nodeValue5368, nodeValue5434, nodeValue5460, nodeValue5465, nodeValue5469, nodeValue5473, nodeValue5476, nodeValue5477, nodeValue5482, nodeValue5483, nodeValue5485, nodeValue5486, nodeValue5487, nodeValue5490, nodeValue5491, nodeValue5493, nodeValue5499]
  ring

noncomputable def reducedSource899 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2480 x + ((1 : ℝ) * Sparse.eval nodeValue2482 x + ((1 : ℝ) * Sparse.eval nodeValue2489 x + ((1 : ℝ) * Sparse.eval nodeValue2512 x + ((1 : ℝ) * Sparse.eval nodeValue2556 x + ((1 : ℝ) * Sparse.eval nodeValue2561 x + ((1 : ℝ) * Sparse.eval nodeValue2595 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2767 x + ((1 : ℝ) * Sparse.eval nodeValue3690 x + ((1 : ℝ) * Sparse.eval nodeValue3694 x + ((1 : ℝ) * Sparse.eval nodeValue3705 x + ((1 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3921 x + ((1 : ℝ) * Sparse.eval nodeValue3931 x + ((1 : ℝ) * Sparse.eval nodeValue3945 x + ((1 : ℝ) * Sparse.eval nodeValue3958 x + ((1 : ℝ) * Sparse.eval nodeValue3965 x + ((1 : ℝ) * Sparse.eval nodeValue3971 x + ((1 : ℝ) * Sparse.eval nodeValue3980 x + ((2 : ℝ) * Sparse.eval nodeValue3981 x + ((1 : ℝ) * Sparse.eval nodeValue3984 x + ((1 : ℝ) * Sparse.eval nodeValue3992 x + ((1 : ℝ) * Sparse.eval nodeValue3999 x + ((1 : ℝ) * Sparse.eval nodeValue4000 x + ((1 : ℝ) * Sparse.eval nodeValue4013 x + ((1 : ℝ) * Sparse.eval nodeValue4014 x + ((1 : ℝ) * Sparse.eval nodeValue4018 x + ((1 : ℝ) * Sparse.eval nodeValue4054 x + 0))))))))))))))))))))))))))))

def numericRow899 : Integer.Sparse Master := [(Sum.inl 0, -27), (Sum.inl 2, 5), (Sum.inl 1, -20), (Sum.inr 2480, 180), (Sum.inr 2482, 180), (Sum.inr 2489, 180), (Sum.inr 2512, 180), (Sum.inr 2556, 180), (Sum.inr 2561, 180), (Sum.inr 2723, 180), (Sum.inr 3690, 180), (Sum.inr 3694, 180), (Sum.inr 3705, 180), (Sum.inr 3945, 180), (Sum.inr 3958, 180)]

theorem reindexCheck899 : Integer.Sparse.reindex keyMap MixedData.row899 = numericRow899 := by decide +kernel

theorem numericCheck899 (x : Master → ℝ) : Integer.Sparse.eval numericRow899 x =
    (180 : ℝ) * reducedSource899 x := by
  norm_num [numericRow899, reducedSource899, Integer.Sparse.eval, Sparse.eval, nodeValue2480, nodeValue2482, nodeValue2489, nodeValue2512, nodeValue2556, nodeValue2561, nodeValue2595, nodeValue2723, nodeValue2767, nodeValue3690, nodeValue3694, nodeValue3705, nodeValue3852, nodeValue3921, nodeValue3931, nodeValue3945, nodeValue3958, nodeValue3965, nodeValue3971, nodeValue3980, nodeValue3981, nodeValue3984, nodeValue3992, nodeValue3999, nodeValue4000, nodeValue4013, nodeValue4014, nodeValue4018, nodeValue4054]
  ring

noncomputable def reducedSource900 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue5405 x + ((2 : ℝ) * Sparse.eval nodeValue5409 x + ((2 : ℝ) * Sparse.eval nodeValue5410 x + ((2 : ℝ) * Sparse.eval nodeValue5411 x + ((2 : ℝ) * Sparse.eval nodeValue5424 x + ((2 : ℝ) * Sparse.eval nodeValue5428 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + ((2 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5445 x + ((2 : ℝ) * Sparse.eval nodeValue5446 x + ((2 : ℝ) * Sparse.eval nodeValue5471 x + ((2 : ℝ) * Sparse.eval nodeValue5473 x + ((2 : ℝ) * Sparse.eval nodeValue5477 x + ((1 : ℝ) * Sparse.eval nodeValue5483 x + ((2 : ℝ) * Sparse.eval nodeValue5487 x + 0)))))))))))))))

def numericRow900 : Integer.Sparse Master := [(Sum.inl 0, 81), (Sum.inl 2, 40), (Sum.inl 3, 80), (Sum.inl 4, 80), (Sum.inl 1, -65), (Sum.inr 3800, -4320), (Sum.inr 3805, -4320), (Sum.inr 3809, -4320), (Sum.inr 3813, -4320), (Sum.inr 3838, -4320), (Sum.inr 3843, -4320), (Sum.inr 3845, -8640), (Sum.inr 3857, -4320), (Sum.inr 3876, -4320), (Sum.inr 3903, -4320), (Sum.inr 3958, -4320), (Sum.inr 3961, -4320), (Sum.inr 4047, -2160), (Sum.inr 5445, 8640), (Sum.inr 5446, 17280)]

theorem reindexCheck900 : Integer.Sparse.reindex keyMap MixedData.row900 = numericRow900 := by decide +kernel

theorem numericCheck900 (x : Master → ℝ) : Integer.Sparse.eval numericRow900 x =
    (8640 : ℝ) * reducedSource900 x := by
  norm_num [numericRow900, reducedSource900, Integer.Sparse.eval, Sparse.eval, nodeValue5405, nodeValue5409, nodeValue5410, nodeValue5411, nodeValue5424, nodeValue5428, nodeValue5434, nodeValue5438, nodeValue5442, nodeValue5445, nodeValue5446, nodeValue5471, nodeValue5473, nodeValue5477, nodeValue5483, nodeValue5487]
  ring

noncomputable def reducedSource901 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5065 x + ((2 : ℝ) * Sparse.eval nodeValue5067 x + ((2 : ℝ) * Sparse.eval nodeValue5073 x + ((2 : ℝ) * Sparse.eval nodeValue5074 x + ((1 : ℝ) * Sparse.eval nodeValue5250 x + ((1 : ℝ) * Sparse.eval nodeValue5284 x + ((1 : ℝ) * Sparse.eval nodeValue5348 x + ((2 : ℝ) * Sparse.eval nodeValue5352 x + ((2 : ℝ) * Sparse.eval nodeValue5353 x + ((2 : ℝ) * Sparse.eval nodeValue5401 x + ((1 : ℝ) * Sparse.eval nodeValue5406 x + ((2 : ℝ) * Sparse.eval nodeValue5408 x + ((2 : ℝ) * Sparse.eval nodeValue5410 x + ((2 : ℝ) * Sparse.eval nodeValue5430 x + ((1 : ℝ) * Sparse.eval nodeValue5433 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((1 : ℝ) * Sparse.eval nodeValue5471 x + ((2 : ℝ) * Sparse.eval nodeValue5480 x + ((1 : ℝ) * Sparse.eval nodeValue5482 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + 0)))))))))))))))))))

def numericRow901 : Integer.Sparse Master := [(Sum.inl 0, 79), (Sum.inl 2, -55), (Sum.inl 3, -80), (Sum.inl 12, -40), (Sum.inl 4, -80), (Sum.inl 1, 230), (Sum.inr 2480, -4320), (Sum.inr 3077, -2160), (Sum.inr 3467, -4320), (Sum.inr 3625, -2160), (Sum.inr 3690, -4320), (Sum.inr 3764, -4320), (Sum.inr 3787, -4320), (Sum.inr 3801, -2160), (Sum.inr 3804, -4320), (Sum.inr 3812, -2160), (Sum.inr 3901, -2160), (Sum.inr 3902, -2160), (Sum.inr 4010, -2160), (Sum.inr 4046, -2160), (Sum.inr 5065, 8640), (Sum.inr 5067, 17280), (Sum.inr 5074, 17280), (Sum.inr 5348, 8640), (Sum.inr 5353, 17280), (Sum.inr 5430, 17280), (Sum.inr 5480, 17280)]

theorem reindexCheck901 : Integer.Sparse.reindex keyMap MixedData.row901 = numericRow901 := by decide +kernel

theorem numericCheck901 (x : Master → ℝ) : Integer.Sparse.eval numericRow901 x =
    (8640 : ℝ) * reducedSource901 x := by
  norm_num [numericRow901, reducedSource901, Integer.Sparse.eval, Sparse.eval, nodeValue5065, nodeValue5067, nodeValue5073, nodeValue5074, nodeValue5250, nodeValue5284, nodeValue5348, nodeValue5352, nodeValue5353, nodeValue5401, nodeValue5406, nodeValue5408, nodeValue5410, nodeValue5430, nodeValue5433, nodeValue5439, nodeValue5471, nodeValue5480, nodeValue5482, nodeValue5485]
  ring

noncomputable def reducedSource902 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue3463 x + ((1 : ℝ) * Sparse.eval nodeValue3466 x + ((2 : ℝ) * Sparse.eval nodeValue3467 x + ((2 : ℝ) * Sparse.eval nodeValue3476 x + ((1 : ℝ) * Sparse.eval nodeValue3531 x + ((1 : ℝ) * Sparse.eval nodeValue3625 x + ((2 : ℝ) * Sparse.eval nodeValue3761 x + ((2 : ℝ) * Sparse.eval nodeValue3764 x + ((1 : ℝ) * Sparse.eval nodeValue3768 x + ((2 : ℝ) * Sparse.eval nodeValue3804 x + ((2 : ℝ) * Sparse.eval nodeValue3806 x + ((1 : ℝ) * Sparse.eval nodeValue3812 x + ((2 : ℝ) * Sparse.eval nodeValue3816 x + ((2 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3851 x + ((1 : ℝ) * Sparse.eval nodeValue3858 x + ((1 : ℝ) * Sparse.eval nodeValue3956 x + ((2 : ℝ) * Sparse.eval nodeValue3978 x + ((1 : ℝ) * Sparse.eval nodeValue3980 x + ((1 : ℝ) * Sparse.eval nodeValue3984 x + 0)))))))))))))))))))

def numericRow902 : Integer.Sparse Master := [(Sum.inl 0, -79), (Sum.inl 2, 55), (Sum.inl 3, 80), (Sum.inl 12, 40), (Sum.inl 4, 80), (Sum.inl 1, -230), (Sum.inr 3463, 4320), (Sum.inr 3466, 2160), (Sum.inr 3467, 4320), (Sum.inr 3476, 4320), (Sum.inr 3625, 2160), (Sum.inr 3761, 4320), (Sum.inr 3764, 4320), (Sum.inr 3768, 2160), (Sum.inr 3804, 4320), (Sum.inr 3812, 2160), (Sum.inr 3848, 4320), (Sum.inr 3978, 4320)]

theorem reindexCheck902 : Integer.Sparse.reindex keyMap MixedData.row902 = numericRow902 := by decide +kernel

theorem numericCheck902 (x : Master → ℝ) : Integer.Sparse.eval numericRow902 x =
    (2160 : ℝ) * reducedSource902 x := by
  norm_num [numericRow902, reducedSource902, Integer.Sparse.eval, Sparse.eval, nodeValue3463, nodeValue3466, nodeValue3467, nodeValue3476, nodeValue3531, nodeValue3625, nodeValue3761, nodeValue3764, nodeValue3768, nodeValue3804, nodeValue3806, nodeValue3812, nodeValue3816, nodeValue3848, nodeValue3851, nodeValue3858, nodeValue3956, nodeValue3978, nodeValue3980, nodeValue3984]
  ring

noncomputable def reducedSource903 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5072 x + ((2 : ℝ) * Sparse.eval nodeValue5074 x + ((1 : ℝ) * Sparse.eval nodeValue5098 x + ((1 : ℝ) * Sparse.eval nodeValue5256 x + ((1 : ℝ) * Sparse.eval nodeValue5351 x + ((2 : ℝ) * Sparse.eval nodeValue5353 x + ((1 : ℝ) * Sparse.eval nodeValue5365 x + ((1 : ℝ) * Sparse.eval nodeValue5400 x + ((2 : ℝ) * Sparse.eval nodeValue5402 x + ((1 : ℝ) * Sparse.eval nodeValue5405 x + ((2 : ℝ) * Sparse.eval nodeValue5406 x + ((2 : ℝ) * Sparse.eval nodeValue5407 x + ((2 : ℝ) * Sparse.eval nodeValue5409 x + ((2 : ℝ) * Sparse.eval nodeValue5410 x + ((2 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5429 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((2 : ℝ) * Sparse.eval nodeValue5471 x + ((2 : ℝ) * Sparse.eval nodeValue5483 x + 0))))))))))))))))))

def numericRow903 : Integer.Sparse Master := [(Sum.inl 0, 114), (Sum.inl 2, 55), (Sum.inl 3, 80), (Sum.inl 4, 80), (Sum.inl 1, -95), (Sum.inr 2479, -2160), (Sum.inr 2508, -2160), (Sum.inr 3459, -2160), (Sum.inr 3460, -2160), (Sum.inr 3689, -2160), (Sum.inr 3703, -2160), (Sum.inr 3757, -2160), (Sum.inr 3758, -2160), (Sum.inr 3786, -2160), (Sum.inr 3799, -2160), (Sum.inr 3800, -2160), (Sum.inr 3801, -4320), (Sum.inr 3805, -2160), (Sum.inr 3809, -4320), (Sum.inr 3812, -4320), (Sum.inr 3813, -4320), (Sum.inr 3903, -4320), (Sum.inr 4047, -4320), (Sum.inr 5074, 17280), (Sum.inr 5353, 17280), (Sum.inr 5402, 17280), (Sum.inr 5407, 17280), (Sum.inr 5429, 8640)]

theorem reindexCheck903 : Integer.Sparse.reindex keyMap MixedData.row903 = numericRow903 := by decide +kernel

theorem numericCheck903 (x : Master → ℝ) : Integer.Sparse.eval numericRow903 x =
    (8640 : ℝ) * reducedSource903 x := by
  norm_num [numericRow903, reducedSource903, Integer.Sparse.eval, Sparse.eval, nodeValue5072, nodeValue5074, nodeValue5098, nodeValue5256, nodeValue5351, nodeValue5353, nodeValue5365, nodeValue5400, nodeValue5402, nodeValue5405, nodeValue5406, nodeValue5407, nodeValue5409, nodeValue5410, nodeValue5411, nodeValue5429, nodeValue5434, nodeValue5471, nodeValue5483]
  ring

noncomputable def reducedSource904 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3459 x + ((1 : ℝ) * Sparse.eval nodeValue3460 x + ((2 : ℝ) * Sparse.eval nodeValue3463 x + ((1 : ℝ) * Sparse.eval nodeValue3525 x + ((1 : ℝ) * Sparse.eval nodeValue3757 x + ((1 : ℝ) * Sparse.eval nodeValue3758 x + ((2 : ℝ) * Sparse.eval nodeValue3761 x + ((1 : ℝ) * Sparse.eval nodeValue3799 x + ((1 : ℝ) * Sparse.eval nodeValue3801 x + ((2 : ℝ) * Sparse.eval nodeValue3802 x + ((2 : ℝ) * Sparse.eval nodeValue3803 x + ((2 : ℝ) * Sparse.eval nodeValue3807 x + ((2 : ℝ) * Sparse.eval nodeValue3808 x + ((2 : ℝ) * Sparse.eval nodeValue3813 x + ((1 : ℝ) * Sparse.eval nodeValue3846 x + ((1 : ℝ) * Sparse.eval nodeValue3847 x + ((2 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3953 x + ((1 : ℝ) * Sparse.eval nodeValue3976 x + ((1 : ℝ) * Sparse.eval nodeValue3977 x + ((2 : ℝ) * Sparse.eval nodeValue3981 x + 0))))))))))))))))))))

def numericRow904 : Integer.Sparse Master := [(Sum.inl 0, -116), (Sum.inl 2, -25), (Sum.inl 3, 400), (Sum.inl 13, 160), (Sum.inl 12, 240), (Sum.inl 4, 80), (Sum.inl 1, -25), (Sum.inr 3459, 2160), (Sum.inr 3460, 2160), (Sum.inr 3463, 4320), (Sum.inr 3757, 2160), (Sum.inr 3758, 2160), (Sum.inr 3761, 4320), (Sum.inr 3799, 2160), (Sum.inr 3801, 2160), (Sum.inr 3802, 4320), (Sum.inr 3803, 4320), (Sum.inr 3813, 4320), (Sum.inr 3846, 2160)]

theorem reindexCheck904 : Integer.Sparse.reindex keyMap MixedData.row904 = numericRow904 := by decide +kernel

theorem numericCheck904 (x : Master → ℝ) : Integer.Sparse.eval numericRow904 x =
    (2160 : ℝ) * reducedSource904 x := by
  norm_num [numericRow904, reducedSource904, Integer.Sparse.eval, Sparse.eval, nodeValue3459, nodeValue3460, nodeValue3463, nodeValue3525, nodeValue3757, nodeValue3758, nodeValue3761, nodeValue3799, nodeValue3801, nodeValue3802, nodeValue3803, nodeValue3807, nodeValue3808, nodeValue3813, nodeValue3846, nodeValue3847, nodeValue3852, nodeValue3953, nodeValue3976, nodeValue3977, nodeValue3981]
  ring

noncomputable def reducedSource905 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5138 x + ((1 : ℝ) * Sparse.eval nodeValue5139 x + ((1 : ℝ) * Sparse.eval nodeValue5140 x + ((1 : ℝ) * Sparse.eval nodeValue5170 x + ((1 : ℝ) * Sparse.eval nodeValue5185 x + ((1 : ℝ) * Sparse.eval nodeValue5189 x + ((1 : ℝ) * Sparse.eval nodeValue5199 x + ((1 : ℝ) * Sparse.eval nodeValue5226 x + ((1 : ℝ) * Sparse.eval nodeValue5229 x + ((1 : ℝ) * Sparse.eval nodeValue5236 x + ((1 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5260 x + ((1 : ℝ) * Sparse.eval nodeValue5289 x + ((1 : ℝ) * Sparse.eval nodeValue5401 x + ((1 : ℝ) * Sparse.eval nodeValue5404 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5419 x + ((1 : ℝ) * Sparse.eval nodeValue5421 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5430 x + ((1 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((1 : ℝ) * Sparse.eval nodeValue5440 x + ((1 : ℝ) * Sparse.eval nodeValue5446 x + ((1 : ℝ) * Sparse.eval nodeValue5448 x + ((1 : ℝ) * Sparse.eval nodeValue5480 x + ((2 : ℝ) * Sparse.eval nodeValue5484 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + 0))))))))))))))))))))))))))))

def numericRow905 : Integer.Sparse Master := [(Sum.inl 0, 41), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, 40), (Sum.inl 4, 80), (Sum.inl 1, 70), (Sum.inr 2723, -2160), (Sum.inr 2954, -2160), (Sum.inr 3544, -2160), (Sum.inr 3606, -2160), (Sum.inr 3787, -2160), (Sum.inr 3790, -2160), (Sum.inr 3804, -2160), (Sum.inr 3815, -2160), (Sum.inr 3838, -2160), (Sum.inr 3843, -2160), (Sum.inr 3849, -2160), (Sum.inr 3857, -2160), (Sum.inr 3875, -2160), (Sum.inr 3876, -2160), (Sum.inr 3885, -4320), (Sum.inr 3902, -2160), (Sum.inr 3983, -8640), (Sum.inr 4010, -2160), (Sum.inr 5138, 8640), (Sum.inr 5139, 8640), (Sum.inr 5140, 8640), (Sum.inr 5185, 8640), (Sum.inr 5189, 8640), (Sum.inr 5199, 8640), (Sum.inr 5226, 8640), (Sum.inr 5229, 8640), (Sum.inr 5236, 8640), (Sum.inr 5260, 8640), (Sum.inr 5289, 8640), (Sum.inr 5419, 8640), (Sum.inr 5421, 8640), (Sum.inr 5430, 8640), (Sum.inr 5446, 8640), (Sum.inr 5480, 8640)]

theorem reindexCheck905 : Integer.Sparse.reindex keyMap MixedData.row905 = numericRow905 := by decide +kernel

theorem numericCheck905 (x : Master → ℝ) : Integer.Sparse.eval numericRow905 x =
    (8640 : ℝ) * reducedSource905 x := by
  norm_num [numericRow905, reducedSource905, Integer.Sparse.eval, Sparse.eval, nodeValue5138, nodeValue5139, nodeValue5140, nodeValue5170, nodeValue5185, nodeValue5189, nodeValue5199, nodeValue5226, nodeValue5229, nodeValue5236, nodeValue5259, nodeValue5260, nodeValue5289, nodeValue5401, nodeValue5404, nodeValue5410, nodeValue5419, nodeValue5421, nodeValue5424, nodeValue5430, nodeValue5431, nodeValue5438, nodeValue5439, nodeValue5440, nodeValue5446, nodeValue5448, nodeValue5480, nodeValue5484, nodeValue5485]
  ring

noncomputable def reducedSource906 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2669 x + ((1 : ℝ) * Sparse.eval nodeValue2670 x + ((1 : ℝ) * Sparse.eval nodeValue2673 x + ((1 : ℝ) * Sparse.eval nodeValue2682 x + ((1 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue3517 x + ((1 : ℝ) * Sparse.eval nodeValue3523 x + ((1 : ℝ) * Sparse.eval nodeValue3529 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3542 x + ((1 : ℝ) * Sparse.eval nodeValue3544 x + ((1 : ℝ) * Sparse.eval nodeValue3578 x + ((1 : ℝ) * Sparse.eval nodeValue3606 x + ((1 : ℝ) * Sparse.eval nodeValue3804 x + ((1 : ℝ) * Sparse.eval nodeValue3815 x + ((1 : ℝ) * Sparse.eval nodeValue3816 x + ((1 : ℝ) * Sparse.eval nodeValue3842 x + ((1 : ℝ) * Sparse.eval nodeValue3843 x + ((1 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3849 x + ((1 : ℝ) * Sparse.eval nodeValue3857 x + ((1 : ℝ) * Sparse.eval nodeValue3858 x + ((1 : ℝ) * Sparse.eval nodeValue3859 x + ((1 : ℝ) * Sparse.eval nodeValue3873 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3885 x + ((1 : ℝ) * Sparse.eval nodeValue3978 x + ((1 : ℝ) * Sparse.eval nodeValue3983 x + ((1 : ℝ) * Sparse.eval nodeValue3997 x + ((1 : ℝ) * Sparse.eval nodeValue3998 x + 0)))))))))))))))))))))))))))))

def numericRow906 : Integer.Sparse Master := [(Sum.inl 0, -194), (Sum.inl 2, 60), (Sum.inl 3, -640), (Sum.inl 12, -160), (Sum.inl 26, -160), (Sum.inl 4, -320), (Sum.inl 1, -290), (Sum.inr 2669, 8640), (Sum.inr 2670, 8640), (Sum.inr 2673, 8640), (Sum.inr 2682, 8640), (Sum.inr 2763, 8640), (Sum.inr 3517, 8640), (Sum.inr 3523, 8640), (Sum.inr 3529, 8640), (Sum.inr 3540, 8640), (Sum.inr 3542, 8640), (Sum.inr 3544, 8640), (Sum.inr 3578, 8640), (Sum.inr 3606, 8640), (Sum.inr 3804, 8640), (Sum.inr 3815, 8640), (Sum.inr 3842, 8640), (Sum.inr 3843, 8640), (Sum.inr 3848, 8640), (Sum.inr 3849, 8640), (Sum.inr 3857, 8640), (Sum.inr 3873, 8640), (Sum.inr 3884, 8640), (Sum.inr 3885, 8640), (Sum.inr 3978, 8640), (Sum.inr 3983, 8640)]

theorem reindexCheck906 : Integer.Sparse.reindex keyMap MixedData.row906 = numericRow906 := by decide +kernel

theorem numericCheck906 (x : Master → ℝ) : Integer.Sparse.eval numericRow906 x =
    (8640 : ℝ) * reducedSource906 x := by
  norm_num [numericRow906, reducedSource906, Integer.Sparse.eval, Sparse.eval, nodeValue2669, nodeValue2670, nodeValue2673, nodeValue2682, nodeValue2763, nodeValue3517, nodeValue3523, nodeValue3529, nodeValue3540, nodeValue3542, nodeValue3544, nodeValue3578, nodeValue3606, nodeValue3804, nodeValue3815, nodeValue3816, nodeValue3842, nodeValue3843, nodeValue3848, nodeValue3849, nodeValue3857, nodeValue3858, nodeValue3859, nodeValue3873, nodeValue3884, nodeValue3885, nodeValue3978, nodeValue3983, nodeValue3997, nodeValue3998]
  ring

noncomputable def reducedSource907 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2621 x + ((1 : ℝ) * Sparse.eval nodeValue3115 x + ((1 : ℝ) * Sparse.eval nodeValue3790 x + ((1 : ℝ) * Sparse.eval nodeValue3825 x + ((2 : ℝ) * Sparse.eval nodeValue3876 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow907 : Integer.Sparse Master := [(Sum.inr 2621, 1), (Sum.inr 3115, 1), (Sum.inr 3790, 1), (Sum.inr 3825, 1), (Sum.inr 3876, 2), (Sum.inr 4091, -1)]

theorem reindexCheck907 : Integer.Sparse.reindex keyMap MixedData.row907 = numericRow907 := by decide +kernel

theorem numericCheck907 (x : Master → ℝ) : Integer.Sparse.eval numericRow907 x =
    (1 : ℝ) * reducedSource907 x := by
  norm_num [numericRow907, reducedSource907, Integer.Sparse.eval, Sparse.eval, nodeValue2621, nodeValue3115, nodeValue3790, nodeValue3825, nodeValue3876, nodeValue4091]

noncomputable def reducedSource908 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4826 x + ((1 : ℝ) * Sparse.eval nodeValue4827 x + ((1 : ℝ) * Sparse.eval nodeValue4828 x + ((1 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4866 x + ((1 : ℝ) * Sparse.eval nodeValue5070 x + ((1 : ℝ) * Sparse.eval nodeValue5080 x + ((1 : ℝ) * Sparse.eval nodeValue5095 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((1 : ℝ) * Sparse.eval nodeValue5349 x + ((1 : ℝ) * Sparse.eval nodeValue5355 x + ((1 : ℝ) * Sparse.eval nodeValue5363 x + ((1 : ℝ) * Sparse.eval nodeValue5364 x + ((1 : ℝ) * Sparse.eval nodeValue5370 x + ((1 : ℝ) * Sparse.eval nodeValue5380 x + ((1 : ℝ) * Sparse.eval nodeValue5388 x + ((1 : ℝ) * Sparse.eval nodeValue5397 x + ((1 : ℝ) * Sparse.eval nodeValue5401 x + ((1 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5432 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5435 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + ((1 : ℝ) * Sparse.eval nodeValue5450 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5481 x + ((1 : ℝ) * Sparse.eval nodeValue5484 x + ((1 : ℝ) * Sparse.eval nodeValue5490 x + ((1 : ℝ) * Sparse.eval nodeValue5492 x + 0)))))))))))))))))))))))))))))

def numericRow908 : Integer.Sparse Master := [(Sum.inl 0, 1347), (Sum.inl 5, 60), (Sum.inl 2, 135), (Sum.inl 7, 240), (Sum.inl 3, 720), (Sum.inl 24, -720), (Sum.inl 12, 240), (Sum.inl 27, -180), (Sum.inl 1, -1680), (Sum.inr 2046, -12960), (Sum.inr 2047, -12960), (Sum.inr 2048, -12960), (Sum.inr 2058, -12960), (Sum.inr 2077, -12960), (Sum.inr 2079, -12960), (Sum.inr 2082, -12960), (Sum.inr 2107, -12960), (Sum.inr 2216, -12960), (Sum.inr 2260, -12960), (Sum.inr 2477, -12960), (Sum.inr 2488, -12960), (Sum.inr 2505, -12960), (Sum.inr 2765, -12960), (Sum.inr 3444, -12960), (Sum.inr 3448, -12960), (Sum.inr 3478, -12960), (Sum.inr 3582, -12960), (Sum.inr 3687, -12960), (Sum.inr 3693, -12960), (Sum.inr 3701, -12960), (Sum.inr 3702, -25920), (Sum.inr 3706, -12960), (Sum.inr 3721, -12960), (Sum.inr 3749, -12960), (Sum.inr 3751, -12960), (Sum.inr 3770, -12960), (Sum.inr 3771, -12960), (Sum.inr 3782, -12960), (Sum.inr 3787, -12960), (Sum.inr 3796, -12960), (Sum.inr 3804, -12960), (Sum.inr 3836, -12960), (Sum.inr 3849, -12960), (Sum.inr 3850, -25920), (Sum.inr 3857, -12960), (Sum.inr 3875, -12960), (Sum.inr 3876, -12960), (Sum.inr 3892, -12960), (Sum.inr 3903, -12960), (Sum.inr 3906, -12960), (Sum.inr 3907, -12960), (Sum.inr 3910, -12960), (Sum.inr 3913, -12960), (Sum.inr 3983, -25920)]

theorem reindexCheck908 : Integer.Sparse.reindex keyMap MixedData.row908 = numericRow908 := by decide +kernel

theorem numericCheck908 (x : Master → ℝ) : Integer.Sparse.eval numericRow908 x =
    (51840 : ℝ) * reducedSource908 x := by
  norm_num [numericRow908, reducedSource908, Integer.Sparse.eval, Sparse.eval, nodeValue4826, nodeValue4827, nodeValue4828, nodeValue4839, nodeValue4866, nodeValue5070, nodeValue5080, nodeValue5095, nodeValue5291, nodeValue5349, nodeValue5355, nodeValue5363, nodeValue5364, nodeValue5370, nodeValue5380, nodeValue5388, nodeValue5397, nodeValue5401, nodeValue5431, nodeValue5432, nodeValue5434, nodeValue5435, nodeValue5438, nodeValue5443, nodeValue5450, nodeValue5451, nodeValue5481, nodeValue5484, nodeValue5490, nodeValue5492]
  ring

noncomputable def reducedSource909 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2077 x + ((1 : ℝ) * Sparse.eval nodeValue2079 x + ((1 : ℝ) * Sparse.eval nodeValue2082 x + ((1 : ℝ) * Sparse.eval nodeValue2107 x + ((1 : ℝ) * Sparse.eval nodeValue2216 x + ((1 : ℝ) * Sparse.eval nodeValue2477 x + ((1 : ℝ) * Sparse.eval nodeValue2488 x + ((1 : ℝ) * Sparse.eval nodeValue2505 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((1 : ℝ) * Sparse.eval nodeValue3687 x + ((1 : ℝ) * Sparse.eval nodeValue3693 x + ((1 : ℝ) * Sparse.eval nodeValue3702 x + ((1 : ℝ) * Sparse.eval nodeValue3721 x + ((1 : ℝ) * Sparse.eval nodeValue3737 x + ((1 : ℝ) * Sparse.eval nodeValue3751 x + ((1 : ℝ) * Sparse.eval nodeValue3771 x + ((1 : ℝ) * Sparse.eval nodeValue3787 x + ((1 : ℝ) * Sparse.eval nodeValue3796 x + ((1 : ℝ) * Sparse.eval nodeValue3850 x + ((1 : ℝ) * Sparse.eval nodeValue3875 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3887 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + ((1 : ℝ) * Sparse.eval nodeValue3906 x + ((1 : ℝ) * Sparse.eval nodeValue3907 x + ((1 : ℝ) * Sparse.eval nodeValue3979 x + ((1 : ℝ) * Sparse.eval nodeValue3982 x + ((1 : ℝ) * Sparse.eval nodeValue3983 x + ((1 : ℝ) * Sparse.eval nodeValue4013 x + ((1 : ℝ) * Sparse.eval nodeValue4017 x + 0)))))))))))))))))))))))))))))

def numericRow909 : Integer.Sparse Master := [(Sum.inl 0, -810), (Sum.inl 5, -60), (Sum.inl 2, -45), (Sum.inl 7, -240), (Sum.inl 3, -720), (Sum.inl 24, 720), (Sum.inl 12, -240), (Sum.inl 4, -240), (Sum.inl 27, 180), (Sum.inl 1, 1185), (Sum.inr 2077, 12960), (Sum.inr 2079, 12960), (Sum.inr 2082, 12960), (Sum.inr 2107, 12960), (Sum.inr 2216, 12960), (Sum.inr 2477, 12960), (Sum.inr 2488, 12960), (Sum.inr 2505, 12960), (Sum.inr 2765, 12960), (Sum.inr 3687, 12960), (Sum.inr 3693, 12960), (Sum.inr 3702, 12960), (Sum.inr 3721, 12960), (Sum.inr 3751, 12960), (Sum.inr 3771, 12960), (Sum.inr 3787, 12960), (Sum.inr 3796, 12960), (Sum.inr 3850, 12960), (Sum.inr 3875, 12960), (Sum.inr 3876, 12960), (Sum.inr 3906, 12960), (Sum.inr 3907, 12960), (Sum.inr 3983, 12960)]

theorem reindexCheck909 : Integer.Sparse.reindex keyMap MixedData.row909 = numericRow909 := by decide +kernel

theorem numericCheck909 (x : Master → ℝ) : Integer.Sparse.eval numericRow909 x =
    (12960 : ℝ) * reducedSource909 x := by
  norm_num [numericRow909, reducedSource909, Integer.Sparse.eval, Sparse.eval, nodeValue2077, nodeValue2079, nodeValue2082, nodeValue2107, nodeValue2216, nodeValue2477, nodeValue2488, nodeValue2505, nodeValue2765, nodeValue3687, nodeValue3693, nodeValue3702, nodeValue3721, nodeValue3737, nodeValue3751, nodeValue3771, nodeValue3787, nodeValue3796, nodeValue3850, nodeValue3875, nodeValue3876, nodeValue3887, nodeValue3888, nodeValue3906, nodeValue3907, nodeValue3979, nodeValue3982, nodeValue3983, nodeValue4013, nodeValue4017]
  ring

noncomputable def reducedSource910 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5160 x + ((1 : ℝ) * Sparse.eval nodeValue5163 x + ((1 : ℝ) * Sparse.eval nodeValue5164 x + ((1 : ℝ) * Sparse.eval nodeValue5173 x + ((1 : ℝ) * Sparse.eval nodeValue5263 x + ((1 : ℝ) * Sparse.eval nodeValue5264 x + ((1 : ℝ) * Sparse.eval nodeValue5267 x + ((1 : ℝ) * Sparse.eval nodeValue5299 x + ((1 : ℝ) * Sparse.eval nodeValue5304 x + ((1 : ℝ) * Sparse.eval nodeValue5382 x + ((1 : ℝ) * Sparse.eval nodeValue5384 x + ((1 : ℝ) * Sparse.eval nodeValue5385 x + ((1 : ℝ) * Sparse.eval nodeValue5400 x + ((1 : ℝ) * Sparse.eval nodeValue5409 x + ((1 : ℝ) * Sparse.eval nodeValue5414 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5425 x + ((2 : ℝ) * Sparse.eval nodeValue5428 x + ((1 : ℝ) * Sparse.eval nodeValue5430 x + ((1 : ℝ) * Sparse.eval nodeValue5432 x + ((1 : ℝ) * Sparse.eval nodeValue5436 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + ((1 : ℝ) * Sparse.eval nodeValue5446 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5471 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5483 x + 0))))))))))))))))))))))))))))

def numericRow910 : Integer.Sparse Master := [(Sum.inl 0, 66), (Sum.inl 2, 25), (Sum.inl 3, -160), (Sum.inl 12, -80), (Sum.inl 4, -80), (Sum.inl 1, -5), (Sum.inr 2590, -2160), (Sum.inr 2782, -2160), (Sum.inr 3564, -2160), (Sum.inr 3583, -2160), (Sum.inr 3732, -2160), (Sum.inr 3786, -2160), (Sum.inr 3799, -2160), (Sum.inr 3811, -2160), (Sum.inr 3838, -2160), (Sum.inr 3843, -2160), (Sum.inr 3845, -8640), (Sum.inr 3850, -4320), (Sum.inr 3857, -2160), (Sum.inr 3876, -2160), (Sum.inr 3907, -2160), (Sum.inr 3913, -2160), (Sum.inr 3958, -2160), (Sum.inr 3961, -2160), (Sum.inr 4047, -2160), (Sum.inr 5160, 8640), (Sum.inr 5164, 8640), (Sum.inr 5173, 8640), (Sum.inr 5263, 8640), (Sum.inr 5264, 8640), (Sum.inr 5267, 8640), (Sum.inr 5299, 8640), (Sum.inr 5382, 8640), (Sum.inr 5385, 8640), (Sum.inr 5414, 8640), (Sum.inr 5425, 8640), (Sum.inr 5430, 8640), (Sum.inr 5436, 8640), (Sum.inr 5446, 8640)]

theorem reindexCheck910 : Integer.Sparse.reindex keyMap MixedData.row910 = numericRow910 := by decide +kernel

theorem numericCheck910 (x : Master → ℝ) : Integer.Sparse.eval numericRow910 x =
    (8640 : ℝ) * reducedSource910 x := by
  norm_num [numericRow910, reducedSource910, Integer.Sparse.eval, Sparse.eval, nodeValue5160, nodeValue5163, nodeValue5164, nodeValue5173, nodeValue5263, nodeValue5264, nodeValue5267, nodeValue5299, nodeValue5304, nodeValue5382, nodeValue5384, nodeValue5385, nodeValue5400, nodeValue5409, nodeValue5414, nodeValue5424, nodeValue5425, nodeValue5428, nodeValue5430, nodeValue5432, nodeValue5436, nodeValue5438, nodeValue5442, nodeValue5443, nodeValue5446, nodeValue5451, nodeValue5471, nodeValue5473, nodeValue5483]
  ring

noncomputable def reducedSource911 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2728 x + ((1 : ℝ) * Sparse.eval nodeValue2729 x + ((1 : ℝ) * Sparse.eval nodeValue2732 x + ((1 : ℝ) * Sparse.eval nodeValue2735 x + ((1 : ℝ) * Sparse.eval nodeValue2773 x + ((1 : ℝ) * Sparse.eval nodeValue3558 x + ((1 : ℝ) * Sparse.eval nodeValue3564 x + ((1 : ℝ) * Sparse.eval nodeValue3565 x + ((1 : ℝ) * Sparse.eval nodeValue3583 x + ((1 : ℝ) * Sparse.eval nodeValue3799 x + ((1 : ℝ) * Sparse.eval nodeValue3807 x + ((1 : ℝ) * Sparse.eval nodeValue3811 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3850 x + ((1 : ℝ) * Sparse.eval nodeValue3861 x + ((1 : ℝ) * Sparse.eval nodeValue3866 x + ((1 : ℝ) * Sparse.eval nodeValue3868 x + ((1 : ℝ) * Sparse.eval nodeValue3869 x + ((1 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3881 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + ((1 : ℝ) * Sparse.eval nodeValue3889 x + ((1 : ℝ) * Sparse.eval nodeValue3976 x + ((1 : ℝ) * Sparse.eval nodeValue3981 x + ((1 : ℝ) * Sparse.eval nodeValue3995 x + ((1 : ℝ) * Sparse.eval nodeValue4003 x + 0)))))))))))))))))))))))))))))

def numericRow911 : Integer.Sparse Master := [(Sum.inl 0, -390), (Sum.inl 2, -230), (Sum.inl 3, 160), (Sum.inl 12, 160), (Sum.inl 4, 160), (Sum.inl 1, 200), (Sum.inl 31, 480), (Sum.inr 2728, 8640), (Sum.inr 2729, 8640), (Sum.inr 2732, 8640), (Sum.inr 2735, 8640), (Sum.inr 2773, 8640), (Sum.inr 3558, 8640), (Sum.inr 3564, 8640), (Sum.inr 3565, 8640), (Sum.inr 3583, 8640), (Sum.inr 3799, 8640), (Sum.inr 3811, 8640), (Sum.inr 3838, 8640), (Sum.inr 3845, 8640), (Sum.inr 3850, 8640), (Sum.inr 3866, 8640), (Sum.inr 3868, 8640), (Sum.inr 3869, 8640), (Sum.inr 3871, 8640), (Sum.inr 3872, 8640), (Sum.inr 3876, 8640), (Sum.inr 3877, 8640), (Sum.inr 3881, 8640)]

theorem reindexCheck911 : Integer.Sparse.reindex keyMap MixedData.row911 = numericRow911 := by decide +kernel

theorem numericCheck911 (x : Master → ℝ) : Integer.Sparse.eval numericRow911 x =
    (8640 : ℝ) * reducedSource911 x := by
  norm_num [numericRow911, reducedSource911, Integer.Sparse.eval, Sparse.eval, nodeValue2728, nodeValue2729, nodeValue2732, nodeValue2735, nodeValue2773, nodeValue3558, nodeValue3564, nodeValue3565, nodeValue3583, nodeValue3799, nodeValue3807, nodeValue3811, nodeValue3838, nodeValue3845, nodeValue3850, nodeValue3861, nodeValue3866, nodeValue3868, nodeValue3869, nodeValue3871, nodeValue3872, nodeValue3876, nodeValue3877, nodeValue3881, nodeValue3888, nodeValue3889, nodeValue3976, nodeValue3981, nodeValue3995, nodeValue4003]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
