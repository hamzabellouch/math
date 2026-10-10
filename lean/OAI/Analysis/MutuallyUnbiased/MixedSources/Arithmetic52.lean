import OAI.Analysis.MutuallyUnbiased.MixedData.Source6
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values85
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource832 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2858 x + ((1 : ℝ) * Sparse.eval nodeValue2859 x + ((2 : ℝ) * Sparse.eval nodeValue2864 x + ((1 : ℝ) * Sparse.eval nodeValue3030 x + ((1 : ℝ) * Sparse.eval nodeValue3954 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow832 : Integer.Sparse Master := [(Sum.inr 2858, 1), (Sum.inr 2859, 1), (Sum.inr 2864, 2), (Sum.inr 3030, 1), (Sum.inr 3954, 1), (Sum.inr 4091, -1)]

theorem reindexCheck832 : Integer.Sparse.reindex keyMap MixedData.row832 = numericRow832 := by decide +kernel

theorem numericCheck832 (x : Master → ℝ) : Integer.Sparse.eval numericRow832 x =
    (1 : ℝ) * reducedSource832 x := by
  norm_num [numericRow832, reducedSource832, Integer.Sparse.eval, Sparse.eval, nodeValue2858, nodeValue2859, nodeValue2864, nodeValue3030, nodeValue3954, nodeValue4091]

noncomputable def reducedSource833 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2606 x + ((1 : ℝ) * Sparse.eval nodeValue2607 x + ((1 : ℝ) * Sparse.eval nodeValue2631 x + ((1 : ℝ) * Sparse.eval nodeValue2676 x + ((1 : ℝ) * Sparse.eval nodeValue3524 x + ((1 : ℝ) * Sparse.eval nodeValue3525 x + ((2 : ℝ) * Sparse.eval nodeValue3527 x + ((1 : ℝ) * Sparse.eval nodeValue3566 x + ((2 : ℝ) * Sparse.eval nodeValue3780 x + ((1 : ℝ) * Sparse.eval nodeValue3799 x + ((1 : ℝ) * Sparse.eval nodeValue3800 x + ((2 : ℝ) * Sparse.eval nodeValue3802 x + ((1 : ℝ) * Sparse.eval nodeValue3847 x + ((2 : ℝ) * Sparse.eval nodeValue3850 x + ((2 : ℝ) * Sparse.eval nodeValue3852 x + ((2 : ℝ) * Sparse.eval nodeValue3854 x + ((1 : ℝ) * Sparse.eval nodeValue3878 x + ((2 : ℝ) * Sparse.eval nodeValue3881 x + ((1 : ℝ) * Sparse.eval nodeValue3938 x + ((1 : ℝ) * Sparse.eval nodeValue3976 x + ((2 : ℝ) * Sparse.eval nodeValue3995 x + 0))))))))))))))))))))

def numericRow833 : Integer.Sparse Master := [(Sum.inl 0, -204), (Sum.inl 5, 40), (Sum.inl 2, -95), (Sum.inl 51, -480), (Sum.inl 3, 560), (Sum.inl 13, 240), (Sum.inl 55, -240), (Sum.inl 12, 400), (Sum.inl 27, -60), (Sum.inl 1, -35), (Sum.inr 2606, 8640), (Sum.inr 2607, 4320), (Sum.inr 2631, 4320), (Sum.inr 2676, 4320), (Sum.inr 3524, 4320), (Sum.inr 3527, 8640), (Sum.inr 3566, 4320), (Sum.inr 3780, 8640), (Sum.inr 3799, 4320), (Sum.inr 3800, 4320), (Sum.inr 3802, 8640), (Sum.inr 3850, 8640), (Sum.inr 3854, 8640), (Sum.inr 3878, 4320), (Sum.inr 3881, 8640)]

theorem reindexCheck833 : Integer.Sparse.reindex keyMap MixedData.row833 = numericRow833 := by decide +kernel

theorem numericCheck833 (x : Master → ℝ) : Integer.Sparse.eval numericRow833 x =
    (4320 : ℝ) * reducedSource833 x := by
  norm_num [numericRow833, reducedSource833, Integer.Sparse.eval, Sparse.eval, nodeValue2606, nodeValue2607, nodeValue2631, nodeValue2676, nodeValue3524, nodeValue3525, nodeValue3527, nodeValue3566, nodeValue3780, nodeValue3799, nodeValue3800, nodeValue3802, nodeValue3847, nodeValue3850, nodeValue3852, nodeValue3854, nodeValue3878, nodeValue3881, nodeValue3938, nodeValue3976, nodeValue3995]
  ring

noncomputable def reducedSource834 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2860 x + ((1 : ℝ) * Sparse.eval nodeValue2864 x + ((1 : ℝ) * Sparse.eval nodeValue2874 x + ((1 : ℝ) * Sparse.eval nodeValue3085 x + ((2 : ℝ) * Sparse.eval nodeValue3374 x + ((1 : ℝ) * Sparse.eval nodeValue3378 x + ((1 : ℝ) * Sparse.eval nodeValue3384 x + ((1 : ℝ) * Sparse.eval nodeValue3569 x + ((1 : ℝ) * Sparse.eval nodeValue3758 x + ((1 : ℝ) * Sparse.eval nodeValue3759 x + ((2 : ℝ) * Sparse.eval nodeValue3762 x + ((2 : ℝ) * Sparse.eval nodeValue3788 x + ((1 : ℝ) * Sparse.eval nodeValue3801 x + ((2 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3953 x + ((2 : ℝ) * Sparse.eval nodeValue3958 x + ((2 : ℝ) * Sparse.eval nodeValue3959 x + ((1 : ℝ) * Sparse.eval nodeValue3977 x + ((2 : ℝ) * Sparse.eval nodeValue3982 x + ((1 : ℝ) * Sparse.eval nodeValue4023 x + ((2 : ℝ) * Sparse.eval nodeValue4027 x + 0))))))))))))))))))))

def numericRow834 : Integer.Sparse Master := [(Sum.inl 0, -531), (Sum.inl 5, 120), (Sum.inl 6, -15), (Sum.inl 2, -315), (Sum.inl 7, 240), (Sum.inl 35, 240), (Sum.inl 3, 1680), (Sum.inl 13, 240), (Sum.inl 23, -720), (Sum.inl 54, -720), (Sum.inl 12, 960), (Sum.inl 26, 480), (Sum.inl 4, 480), (Sum.inl 27, -180), (Sum.inl 1, 255), (Sum.inr 2860, 25920), (Sum.inr 2864, 12960), (Sum.inr 2874, 12960), (Sum.inr 3374, 25920), (Sum.inr 3378, 12960), (Sum.inr 3384, 12960), (Sum.inr 3569, 12960), (Sum.inr 3758, 12960), (Sum.inr 3759, 12960), (Sum.inr 3762, 25920), (Sum.inr 3788, 25920), (Sum.inr 3801, 12960), (Sum.inr 3877, 25920), (Sum.inr 3958, 25920), (Sum.inr 3959, 25920)]

theorem reindexCheck834 : Integer.Sparse.reindex keyMap MixedData.row834 = numericRow834 := by decide +kernel

theorem numericCheck834 (x : Master → ℝ) : Integer.Sparse.eval numericRow834 x =
    (12960 : ℝ) * reducedSource834 x := by
  norm_num [numericRow834, reducedSource834, Integer.Sparse.eval, Sparse.eval, nodeValue2860, nodeValue2864, nodeValue2874, nodeValue3085, nodeValue3374, nodeValue3378, nodeValue3384, nodeValue3569, nodeValue3758, nodeValue3759, nodeValue3762, nodeValue3788, nodeValue3801, nodeValue3877, nodeValue3953, nodeValue3958, nodeValue3959, nodeValue3977, nodeValue3982, nodeValue4023, nodeValue4027]
  ring

noncomputable def reducedSource835 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2878 x + ((1 : ℝ) * Sparse.eval nodeValue3703 x + ((1 : ℝ) * Sparse.eval nodeValue3874 x + ((1 : ℝ) * Sparse.eval nodeValue3956 x + ((2 : ℝ) * Sparse.eval nodeValue3961 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow835 : Integer.Sparse Master := [(Sum.inr 2878, 1), (Sum.inr 3703, 1), (Sum.inr 3874, 1), (Sum.inr 3961, 2), (Sum.inr 4092, -1)]

theorem reindexCheck835 : Integer.Sparse.reindex keyMap MixedData.row835 = numericRow835 := by decide +kernel

theorem numericCheck835 (x : Master → ℝ) : Integer.Sparse.eval numericRow835 x =
    (1 : ℝ) * reducedSource835 x := by
  norm_num [numericRow835, reducedSource835, Integer.Sparse.eval, Sparse.eval, nodeValue2878, nodeValue3703, nodeValue3874, nodeValue3956, nodeValue3961, nodeValue4092]

noncomputable def reducedSource836 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2630 x + ((1 : ℝ) * Sparse.eval nodeValue2869 x + ((1 : ℝ) * Sparse.eval nodeValue3697 x + ((1 : ℝ) * Sparse.eval nodeValue3874 x + ((2 : ℝ) * Sparse.eval nodeValue3884 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow836 : Integer.Sparse Master := [(Sum.inr 2630, 1), (Sum.inr 2869, 1), (Sum.inr 3697, 1), (Sum.inr 3874, 1), (Sum.inr 3884, 2), (Sum.inr 4092, -1)]

theorem reindexCheck836 : Integer.Sparse.reindex keyMap MixedData.row836 = numericRow836 := by decide +kernel

theorem numericCheck836 (x : Master → ℝ) : Integer.Sparse.eval numericRow836 x =
    (1 : ℝ) * reducedSource836 x := by
  norm_num [numericRow836, reducedSource836, Integer.Sparse.eval, Sparse.eval, nodeValue2630, nodeValue2869, nodeValue3697, nodeValue3874, nodeValue3884, nodeValue4092]

noncomputable def reducedSource837 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3786 x + ((2 : ℝ) * Sparse.eval nodeValue3788 x + ((1 : ℝ) * Sparse.eval nodeValue3805 x + ((1 : ℝ) * Sparse.eval nodeValue3874 x + ((1 : ℝ) * Sparse.eval nodeValue3956 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow837 : Integer.Sparse Master := [(Sum.inr 3786, 1), (Sum.inr 3788, 2), (Sum.inr 3805, 1), (Sum.inr 3874, 1), (Sum.inr 4092, -1)]

theorem reindexCheck837 : Integer.Sparse.reindex keyMap MixedData.row837 = numericRow837 := by decide +kernel

theorem numericCheck837 (x : Master → ℝ) : Integer.Sparse.eval numericRow837 x =
    (1 : ℝ) * reducedSource837 x := by
  norm_num [numericRow837, reducedSource837, Integer.Sparse.eval, Sparse.eval, nodeValue3786, nodeValue3788, nodeValue3805, nodeValue3874, nodeValue3956, nodeValue4092]

noncomputable def reducedSource838 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2869 x + ((2 : ℝ) * Sparse.eval nodeValue2870 x + ((1 : ℝ) * Sparse.eval nodeValue2878 x + ((1 : ℝ) * Sparse.eval nodeValue3043 x + ((1 : ℝ) * Sparse.eval nodeValue3874 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow838 : Integer.Sparse Master := [(Sum.inr 2869, 1), (Sum.inr 2870, 2), (Sum.inr 2878, 1), (Sum.inr 3043, 1), (Sum.inr 3874, 1), (Sum.inr 4092, -1)]

theorem reindexCheck838 : Integer.Sparse.reindex keyMap MixedData.row838 = numericRow838 := by decide +kernel

theorem numericCheck838 (x : Master → ℝ) : Integer.Sparse.eval numericRow838 x =
    (1 : ℝ) * reducedSource838 x := by
  norm_num [numericRow838, reducedSource838, Integer.Sparse.eval, Sparse.eval, nodeValue2869, nodeValue2870, nodeValue2878, nodeValue3043, nodeValue3874, nodeValue4092]

noncomputable def reducedSource839 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2614 x + ((1 : ℝ) * Sparse.eval nodeValue3043 x + ((1 : ℝ) * Sparse.eval nodeValue3786 x + ((2 : ℝ) * Sparse.eval nodeValue3850 x + ((1 : ℝ) * Sparse.eval nodeValue3874 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow839 : Integer.Sparse Master := [(Sum.inr 2614, 1), (Sum.inr 3043, 1), (Sum.inr 3786, 1), (Sum.inr 3850, 2), (Sum.inr 3874, 1), (Sum.inr 4092, -1)]

theorem reindexCheck839 : Integer.Sparse.reindex keyMap MixedData.row839 = numericRow839 := by decide +kernel

theorem numericCheck839 (x : Master → ℝ) : Integer.Sparse.eval numericRow839 x =
    (1 : ℝ) * reducedSource839 x := by
  norm_num [numericRow839, reducedSource839, Integer.Sparse.eval, Sparse.eval, nodeValue2614, nodeValue3043, nodeValue3786, nodeValue3850, nodeValue3874, nodeValue4092]

noncomputable def reducedSource840 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4792 x + ((1 : ℝ) * Sparse.eval nodeValue4795 x + ((2 : ℝ) * Sparse.eval nodeValue4803 x + ((1 : ℝ) * Sparse.eval nodeValue4885 x + ((1 : ℝ) * Sparse.eval nodeValue5067 x + ((2 : ℝ) * Sparse.eval nodeValue5076 x + ((1 : ℝ) * Sparse.eval nodeValue5251 x + ((1 : ℝ) * Sparse.eval nodeValue5348 x + ((2 : ℝ) * Sparse.eval nodeValue5353 x + ((2 : ℝ) * Sparse.eval nodeValue5354 x + ((2 : ℝ) * Sparse.eval nodeValue5403 x + ((1 : ℝ) * Sparse.eval nodeValue5405 x + ((2 : ℝ) * Sparse.eval nodeValue5406 x + ((2 : ℝ) * Sparse.eval nodeValue5408 x + ((2 : ℝ) * Sparse.eval nodeValue5425 x + ((1 : ℝ) * Sparse.eval nodeValue5429 x + ((2 : ℝ) * Sparse.eval nodeValue5430 x + ((1 : ℝ) * Sparse.eval nodeValue5433 x + ((1 : ℝ) * Sparse.eval nodeValue5437 x + ((1 : ℝ) * Sparse.eval nodeValue5447 x + ((1 : ℝ) * Sparse.eval nodeValue5482 x + 0))))))))))))))))))))

def numericRow840 : Integer.Sparse Master := [(Sum.inl 0, 19), (Sum.inl 2, -25), (Sum.inl 3, -80), (Sum.inl 12, -40), (Sum.inl 4, -80), (Sum.inl 1, 80), (Sum.inr 2483, -2160), (Sum.inr 3477, -2160), (Sum.inr 3692, -2160), (Sum.inr 3769, -2160), (Sum.inr 3789, -2160), (Sum.inr 3800, -1080), (Sum.inr 3801, -2160), (Sum.inr 3805, -1080), (Sum.inr 3810, -2160), (Sum.inr 3812, -2160), (Sum.inr 3899, -2160), (Sum.inr 3901, -1080), (Sum.inr 3909, -1080), (Sum.inr 4025, -1080), (Sum.inr 4046, -1080), (Sum.inr 4792, 4320), (Sum.inr 4795, 4320), (Sum.inr 4803, 8640), (Sum.inr 4885, 4320), (Sum.inr 5067, 4320), (Sum.inr 5251, 4320), (Sum.inr 5348, 4320), (Sum.inr 5353, 8640), (Sum.inr 5425, 8640), (Sum.inr 5429, 4320), (Sum.inr 5430, 8640)]

theorem reindexCheck840 : Integer.Sparse.reindex keyMap MixedData.row840 = numericRow840 := by decide +kernel

theorem numericCheck840 (x : Master → ℝ) : Integer.Sparse.eval numericRow840 x =
    (4320 : ℝ) * reducedSource840 x := by
  norm_num [numericRow840, reducedSource840, Integer.Sparse.eval, Sparse.eval, nodeValue4792, nodeValue4795, nodeValue4803, nodeValue4885, nodeValue5067, nodeValue5076, nodeValue5251, nodeValue5348, nodeValue5353, nodeValue5354, nodeValue5403, nodeValue5405, nodeValue5406, nodeValue5408, nodeValue5425, nodeValue5429, nodeValue5430, nodeValue5433, nodeValue5437, nodeValue5447, nodeValue5482]
  ring

noncomputable def reducedSource841 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2009 x + ((1 : ℝ) * Sparse.eval nodeValue2012 x + ((2 : ℝ) * Sparse.eval nodeValue2021 x + ((1 : ℝ) * Sparse.eval nodeValue2233 x + ((1 : ℝ) * Sparse.eval nodeValue2981 x + ((2 : ℝ) * Sparse.eval nodeValue2986 x + ((1 : ℝ) * Sparse.eval nodeValue3064 x + ((1 : ℝ) * Sparse.eval nodeValue3685 x + ((2 : ℝ) * Sparse.eval nodeValue3691 x + ((2 : ℝ) * Sparse.eval nodeValue3818 x + ((2 : ℝ) * Sparse.eval nodeValue3822 x + ((2 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue3846 x + ((2 : ℝ) * Sparse.eval nodeValue3847 x + ((2 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3899 x + ((1 : ℝ) * Sparse.eval nodeValue3909 x + ((1 : ℝ) * Sparse.eval nodeValue3977 x + ((1 : ℝ) * Sparse.eval nodeValue3992 x + ((1 : ℝ) * Sparse.eval nodeValue4033 x + ((2 : ℝ) * Sparse.eval nodeValue4038 x + 0))))))))))))))))))))

def numericRow841 : Integer.Sparse Master := [(Sum.inl 0, -218), (Sum.inl 5, -160), (Sum.inl 6, 10), (Sum.inl 2, 505), (Sum.inl 7, 640), (Sum.inl 35, 480), (Sum.inl 8, 160), (Sum.inl 51, -960), (Sum.inl 3, 3680), (Sum.inl 13, 1040), (Sum.inl 52, 320), (Sum.inl 23, -960), (Sum.inl 54, -480), (Sum.inl 24, -480), (Sum.inl 55, -960), (Sum.inl 12, 1600), (Sum.inl 25, -480), (Sum.inl 26, 320), (Sum.inl 4, 1440), (Sum.inl 27, 120), (Sum.inl 1, -1315), (Sum.inr 2009, 4320), (Sum.inr 2012, 4320), (Sum.inr 2021, 8640), (Sum.inr 2233, 4320), (Sum.inr 2981, 4320), (Sum.inr 3064, 4320), (Sum.inr 3685, 4320), (Sum.inr 3691, 8640), (Sum.inr 3839, 8640), (Sum.inr 3846, 4320), (Sum.inr 3848, 8640), (Sum.inr 3899, 4320), (Sum.inr 3909, 4320)]

theorem reindexCheck841 : Integer.Sparse.reindex keyMap MixedData.row841 = numericRow841 := by decide +kernel

theorem numericCheck841 (x : Master → ℝ) : Integer.Sparse.eval numericRow841 x =
    (4320 : ℝ) * reducedSource841 x := by
  norm_num [numericRow841, reducedSource841, Integer.Sparse.eval, Sparse.eval, nodeValue2009, nodeValue2012, nodeValue2021, nodeValue2233, nodeValue2981, nodeValue2986, nodeValue3064, nodeValue3685, nodeValue3691, nodeValue3818, nodeValue3822, nodeValue3839, nodeValue3846, nodeValue3847, nodeValue3848, nodeValue3899, nodeValue3909, nodeValue3977, nodeValue3992, nodeValue4033, nodeValue4038]
  ring

noncomputable def reducedSource842 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2195 x + ((1 : ℝ) * Sparse.eval nodeValue2201 x + ((1 : ℝ) * Sparse.eval nodeValue2213 x + ((1 : ℝ) * Sparse.eval nodeValue2252 x + ((1 : ℝ) * Sparse.eval nodeValue3476 x + ((2 : ℝ) * Sparse.eval nodeValue3477 x + ((1 : ℝ) * Sparse.eval nodeValue3539 x + ((2 : ℝ) * Sparse.eval nodeValue3761 x + ((1 : ℝ) * Sparse.eval nodeValue3768 x + ((2 : ℝ) * Sparse.eval nodeValue3769 x + ((1 : ℝ) * Sparse.eval nodeValue3805 x + ((2 : ℝ) * Sparse.eval nodeValue3806 x + ((2 : ℝ) * Sparse.eval nodeValue3810 x + ((2 : ℝ) * Sparse.eval nodeValue3812 x + ((2 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3851 x + ((1 : ℝ) * Sparse.eval nodeValue3855 x + ((2 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3874 x + ((1 : ℝ) * Sparse.eval nodeValue3882 x + ((1 : ℝ) * Sparse.eval nodeValue3980 x + 0))))))))))))))))))))

def numericRow842 : Integer.Sparse Master := [(Sum.inl 0, -61), (Sum.inl 2, 175), (Sum.inl 3, 1520), (Sum.inl 13, 480), (Sum.inl 12, 640), (Sum.inl 4, 800), (Sum.inl 1, -800), (Sum.inr 2195, 8640), (Sum.inr 2201, 4320), (Sum.inr 2213, 4320), (Sum.inr 2252, 4320), (Sum.inr 3476, 4320), (Sum.inr 3477, 8640), (Sum.inr 3539, 4320), (Sum.inr 3761, 8640), (Sum.inr 3768, 4320), (Sum.inr 3769, 8640), (Sum.inr 3805, 4320), (Sum.inr 3810, 8640), (Sum.inr 3812, 8640), (Sum.inr 3840, 8640), (Sum.inr 3871, 8640), (Sum.inr 3874, 4320)]

theorem reindexCheck842 : Integer.Sparse.reindex keyMap MixedData.row842 = numericRow842 := by decide +kernel

theorem numericCheck842 (x : Master → ℝ) : Integer.Sparse.eval numericRow842 x =
    (4320 : ℝ) * reducedSource842 x := by
  norm_num [numericRow842, reducedSource842, Integer.Sparse.eval, Sparse.eval, nodeValue2195, nodeValue2201, nodeValue2213, nodeValue2252, nodeValue3476, nodeValue3477, nodeValue3539, nodeValue3761, nodeValue3768, nodeValue3769, nodeValue3805, nodeValue3806, nodeValue3810, nodeValue3812, nodeValue3840, nodeValue3851, nodeValue3855, nodeValue3871, nodeValue3874, nodeValue3882, nodeValue3980]
  ring

noncomputable def reducedSource843 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5085 x + ((2 : ℝ) * Sparse.eval nodeValue5086 x + ((1 : ℝ) * Sparse.eval nodeValue5098 x + ((2 : ℝ) * Sparse.eval nodeValue5254 x + ((1 : ℝ) * Sparse.eval nodeValue5256 x + ((2 : ℝ) * Sparse.eval nodeValue5265 x + ((1 : ℝ) * Sparse.eval nodeValue5286 x + ((1 : ℝ) * Sparse.eval nodeValue5359 x + ((2 : ℝ) * Sparse.eval nodeValue5360 x + ((1 : ℝ) * Sparse.eval nodeValue5365 x + ((2 : ℝ) * Sparse.eval nodeValue5405 x + ((1 : ℝ) * Sparse.eval nodeValue5406 x + ((2 : ℝ) * Sparse.eval nodeValue5407 x + ((2 : ℝ) * Sparse.eval nodeValue5410 x + ((2 : ℝ) * Sparse.eval nodeValue5411 x + ((2 : ℝ) * Sparse.eval nodeValue5412 x + ((1 : ℝ) * Sparse.eval nodeValue5429 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((2 : ℝ) * Sparse.eval nodeValue5435 x + 0))))))))))))))))))

def numericRow843 : Integer.Sparse Master := [(Sum.inl 0, 84), (Sum.inl 2, 45), (Sum.inl 3, 240), (Sum.inl 12, 160), (Sum.inl 4, 80), (Sum.inl 1, -195), (Sum.inr 2508, -2160), (Sum.inr 3460, -2160), (Sum.inr 3703, -2160), (Sum.inr 3758, -2160), (Sum.inr 3800, -4320), (Sum.inr 3801, -2160), (Sum.inr 3805, -4320), (Sum.inr 3809, -4320), (Sum.inr 3812, -2160), (Sum.inr 3813, -4320), (Sum.inr 3814, -8640), (Sum.inr 3903, -4320), (Sum.inr 3906, -4320), (Sum.inr 5085, 8640), (Sum.inr 5086, 17280), (Sum.inr 5254, 17280), (Sum.inr 5265, 17280), (Sum.inr 5286, 8640), (Sum.inr 5359, 8640), (Sum.inr 5360, 17280), (Sum.inr 5407, 17280), (Sum.inr 5429, 8640)]

theorem reindexCheck843 : Integer.Sparse.reindex keyMap MixedData.row843 = numericRow843 := by decide +kernel

theorem numericCheck843 (x : Master → ℝ) : Integer.Sparse.eval numericRow843 x =
    (8640 : ℝ) * reducedSource843 x := by
  norm_num [numericRow843, reducedSource843, Integer.Sparse.eval, Sparse.eval, nodeValue5085, nodeValue5086, nodeValue5098, nodeValue5254, nodeValue5256, nodeValue5265, nodeValue5286, nodeValue5359, nodeValue5360, nodeValue5365, nodeValue5405, nodeValue5406, nodeValue5407, nodeValue5410, nodeValue5411, nodeValue5412, nodeValue5429, nodeValue5434, nodeValue5435]
  ring

noncomputable def reducedSource844 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2974 x + ((1 : ℝ) * Sparse.eval nodeValue2976 x + ((1 : ℝ) * Sparse.eval nodeValue2996 x + ((1 : ℝ) * Sparse.eval nodeValue3037 x + ((1 : ℝ) * Sparse.eval nodeValue3525 x + ((1 : ℝ) * Sparse.eval nodeValue3526 x + ((2 : ℝ) * Sparse.eval nodeValue3528 x + ((1 : ℝ) * Sparse.eval nodeValue3567 x + ((2 : ℝ) * Sparse.eval nodeValue3780 x + ((1 : ℝ) * Sparse.eval nodeValue3800 x + ((1 : ℝ) * Sparse.eval nodeValue3801 x + ((2 : ℝ) * Sparse.eval nodeValue3803 x + ((1 : ℝ) * Sparse.eval nodeValue3846 x + ((2 : ℝ) * Sparse.eval nodeValue3852 x + ((2 : ℝ) * Sparse.eval nodeValue3853 x + ((2 : ℝ) * Sparse.eval nodeValue3856 x + ((1 : ℝ) * Sparse.eval nodeValue3878 x + ((2 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3938 x + ((1 : ℝ) * Sparse.eval nodeValue3977 x + ((2 : ℝ) * Sparse.eval nodeValue3996 x + 0))))))))))))))))))))

def numericRow844 : Integer.Sparse Master := [(Sum.inl 0, -319), (Sum.inl 5, 60), (Sum.inl 6, -10), (Sum.inl 2, -135), (Sum.inl 35, 80), (Sum.inl 51, -480), (Sum.inl 3, -400), (Sum.inl 13, -400), (Sum.inl 52, 160), (Sum.inl 55, -240), (Sum.inl 12, -400), (Sum.inl 26, 160), (Sum.inl 4, 160), (Sum.inl 27, -60), (Sum.inl 1, 510), (Sum.inl 31, -480), (Sum.inr 2974, 8640), (Sum.inr 2976, 4320), (Sum.inr 3037, 4320), (Sum.inr 3526, 4320), (Sum.inr 3528, 8640), (Sum.inr 3567, 4320), (Sum.inr 3780, 8640), (Sum.inr 3800, 4320), (Sum.inr 3801, 4320), (Sum.inr 3803, 8640), (Sum.inr 3846, 4320), (Sum.inr 3878, 4320)]

theorem reindexCheck844 : Integer.Sparse.reindex keyMap MixedData.row844 = numericRow844 := by decide +kernel

theorem numericCheck844 (x : Master → ℝ) : Integer.Sparse.eval numericRow844 x =
    (4320 : ℝ) * reducedSource844 x := by
  norm_num [numericRow844, reducedSource844, Integer.Sparse.eval, Sparse.eval, nodeValue2974, nodeValue2976, nodeValue2996, nodeValue3037, nodeValue3525, nodeValue3526, nodeValue3528, nodeValue3567, nodeValue3780, nodeValue3800, nodeValue3801, nodeValue3803, nodeValue3846, nodeValue3852, nodeValue3853, nodeValue3856, nodeValue3878, nodeValue3883, nodeValue3938, nodeValue3977, nodeValue3996]
  ring

noncomputable def reducedSource845 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue3016 x + ((1 : ℝ) * Sparse.eval nodeValue3023 x + ((1 : ℝ) * Sparse.eval nodeValue3037 x + ((1 : ℝ) * Sparse.eval nodeValue3085 x + ((1 : ℝ) * Sparse.eval nodeValue3460 x + ((1 : ℝ) * Sparse.eval nodeValue3461 x + ((2 : ℝ) * Sparse.eval nodeValue3464 x + ((1 : ℝ) * Sparse.eval nodeValue3526 x + ((1 : ℝ) * Sparse.eval nodeValue3758 x + ((1 : ℝ) * Sparse.eval nodeValue3759 x + ((2 : ℝ) * Sparse.eval nodeValue3762 x + ((1 : ℝ) * Sparse.eval nodeValue3800 x + ((2 : ℝ) * Sparse.eval nodeValue3803 x + ((2 : ℝ) * Sparse.eval nodeValue3808 x + ((2 : ℝ) * Sparse.eval nodeValue3809 x + ((2 : ℝ) * Sparse.eval nodeValue3814 x + ((1 : ℝ) * Sparse.eval nodeValue3847 x + ((2 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3954 x + ((1 : ℝ) * Sparse.eval nodeValue3977 x + ((2 : ℝ) * Sparse.eval nodeValue3982 x + 0))))))))))))))))))))

def numericRow845 : Integer.Sparse Master := [(Sum.inl 0, -86), (Sum.inl 2, -15), (Sum.inl 3, 240), (Sum.inl 13, 160), (Sum.inl 12, 80), (Sum.inl 4, 80), (Sum.inl 1, 75), (Sum.inr 3016, 4320), (Sum.inr 3023, 2160), (Sum.inr 3037, 2160), (Sum.inr 3460, 2160), (Sum.inr 3461, 2160), (Sum.inr 3464, 4320), (Sum.inr 3526, 2160), (Sum.inr 3758, 2160), (Sum.inr 3759, 2160), (Sum.inr 3762, 4320), (Sum.inr 3800, 2160), (Sum.inr 3803, 4320), (Sum.inr 3809, 4320), (Sum.inr 3814, 4320), (Sum.inr 3954, 2160)]

theorem reindexCheck845 : Integer.Sparse.reindex keyMap MixedData.row845 = numericRow845 := by decide +kernel

theorem numericCheck845 (x : Master → ℝ) : Integer.Sparse.eval numericRow845 x =
    (2160 : ℝ) * reducedSource845 x := by
  norm_num [numericRow845, reducedSource845, Integer.Sparse.eval, Sparse.eval, nodeValue3016, nodeValue3023, nodeValue3037, nodeValue3085, nodeValue3460, nodeValue3461, nodeValue3464, nodeValue3526, nodeValue3758, nodeValue3759, nodeValue3762, nodeValue3800, nodeValue3803, nodeValue3808, nodeValue3809, nodeValue3814, nodeValue3847, nodeValue3853, nodeValue3954, nodeValue3977, nodeValue3982]
  ring

noncomputable def reducedSource846 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2508 x + ((1 : ℝ) * Sparse.eval nodeValue3703 x + ((1 : ℝ) * Sparse.eval nodeValue3805 x + ((1 : ℝ) * Sparse.eval nodeValue3812 x + ((2 : ℝ) * Sparse.eval nodeValue3816 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow846 : Integer.Sparse Master := [(Sum.inr 2508, 1), (Sum.inr 3703, 1), (Sum.inr 3805, 1), (Sum.inr 3812, 1), (Sum.inr 4092, -1)]

theorem reindexCheck846 : Integer.Sparse.reindex keyMap MixedData.row846 = numericRow846 := by decide +kernel

theorem numericCheck846 (x : Master → ℝ) : Integer.Sparse.eval numericRow846 x =
    (1 : ℝ) * reducedSource846 x := by
  norm_num [numericRow846, reducedSource846, Integer.Sparse.eval, Sparse.eval, nodeValue2508, nodeValue3703, nodeValue3805, nodeValue3812, nodeValue3816, nodeValue4092]

noncomputable def reducedSource847 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2534 x + ((1 : ℝ) * Sparse.eval nodeValue2535 x + ((1 : ℝ) * Sparse.eval nodeValue2537 x + ((1 : ℝ) * Sparse.eval nodeValue2587 x + ((1 : ℝ) * Sparse.eval nodeValue2669 x + ((1 : ℝ) * Sparse.eval nodeValue3431 x + ((1 : ℝ) * Sparse.eval nodeValue3434 x + ((1 : ℝ) * Sparse.eval nodeValue3463 x + ((1 : ℝ) * Sparse.eval nodeValue3529 x + ((1 : ℝ) * Sparse.eval nodeValue3531 x + ((1 : ℝ) * Sparse.eval nodeValue3536 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3568 x + ((1 : ℝ) * Sparse.eval nodeValue3743 x + ((1 : ℝ) * Sparse.eval nodeValue3761 x + ((1 : ℝ) * Sparse.eval nodeValue3804 x + ((1 : ℝ) * Sparse.eval nodeValue3805 x + ((1 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3849 x + ((1 : ℝ) * Sparse.eval nodeValue3851 x + ((1 : ℝ) * Sparse.eval nodeValue3857 x + ((1 : ℝ) * Sparse.eval nodeValue3858 x + ((1 : ℝ) * Sparse.eval nodeValue3879 x + ((1 : ℝ) * Sparse.eval nodeValue3880 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3927 x + ((1 : ℝ) * Sparse.eval nodeValue3978 x + ((1 : ℝ) * Sparse.eval nodeValue3994 x + ((1 : ℝ) * Sparse.eval nodeValue3997 x + 0)))))))))))))))))))))))))))))

def numericRow847 : Integer.Sparse Master := [(Sum.inl 0, -156), (Sum.inl 2, 240), (Sum.inl 3, 640), (Sum.inl 12, 160), (Sum.inl 4, 800), (Sum.inl 1, -1060), (Sum.inl 31, -480), (Sum.inr 2534, 8640), (Sum.inr 2535, 8640), (Sum.inr 2537, 8640), (Sum.inr 2587, 8640), (Sum.inr 2669, 8640), (Sum.inr 3431, 8640), (Sum.inr 3434, 8640), (Sum.inr 3463, 8640), (Sum.inr 3529, 8640), (Sum.inr 3536, 8640), (Sum.inr 3540, 8640), (Sum.inr 3568, 8640), (Sum.inr 3743, 8640), (Sum.inr 3761, 8640), (Sum.inr 3804, 8640), (Sum.inr 3805, 8640), (Sum.inr 3840, 8640), (Sum.inr 3848, 8640), (Sum.inr 3849, 8640), (Sum.inr 3857, 8640), (Sum.inr 3879, 8640), (Sum.inr 3880, 8640), (Sum.inr 3884, 8640), (Sum.inr 3927, 8640), (Sum.inr 3978, 8640)]

theorem reindexCheck847 : Integer.Sparse.reindex keyMap MixedData.row847 = numericRow847 := by decide +kernel

theorem numericCheck847 (x : Master → ℝ) : Integer.Sparse.eval numericRow847 x =
    (8640 : ℝ) * reducedSource847 x := by
  norm_num [numericRow847, reducedSource847, Integer.Sparse.eval, Sparse.eval, nodeValue2534, nodeValue2535, nodeValue2537, nodeValue2587, nodeValue2669, nodeValue3431, nodeValue3434, nodeValue3463, nodeValue3529, nodeValue3531, nodeValue3536, nodeValue3540, nodeValue3568, nodeValue3743, nodeValue3761, nodeValue3804, nodeValue3805, nodeValue3840, nodeValue3848, nodeValue3849, nodeValue3851, nodeValue3857, nodeValue3858, nodeValue3879, nodeValue3880, nodeValue3884, nodeValue3927, nodeValue3978, nodeValue3994, nodeValue3997]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
