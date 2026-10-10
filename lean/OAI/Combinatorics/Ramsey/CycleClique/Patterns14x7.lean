import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CachedDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.Certificates027
import OAI.Combinatorics.Ramsey.CycleClique.Certificates028
import OAI.Combinatorics.Ramsey.CycleClique.Certificates029
import OAI.Combinatorics.Ramsey.CycleClique.Certificates030
import OAI.Combinatorics.Ramsey.CycleClique.Certificates031
import OAI.Combinatorics.Ramsey.CycleClique.Certificates032
import OAI.Combinatorics.Ramsey.CycleClique.Certificates033
import OAI.Combinatorics.Ramsey.CycleClique.CliqueBits
import OAI.Combinatorics.Ramsey.CycleClique.CompactDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CompactLabels
import OAI.Combinatorics.Ramsey.CycleClique.EdgeBits
import OAI.Combinatorics.Ramsey.CycleClique.EdgeDecisions
import OAI.Combinatorics.Ramsey.CycleClique.FiniteGraphs
import OAI.Combinatorics.Ramsey.CycleClique.LabelDecisions
import OAI.Combinatorics.Ramsey.CycleClique.MatrixBits
import OAI.Combinatorics.Ramsey.CycleClique.PatternReduction

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_14_7_0 : List (List (List ℕ)) := [[[],[],[],[],[],[],[]],[[],[],[],[],[],[1]],[[],[],[],[],[],[2]],[[],[],[],[],[],[3]],[[],[],[],[],[],[4]],[[],[],[],[],[],[5]],[[],[],[],[],[],[6]],[[],[],[],[],[],[7]],[[],[],[],[],[1,1]],[[],[],[],[],[1,2]],[[],[],[],[],[1,3]],[[],[],[],[],[1,4]],[[],[],[],[],[1,5]],[[],[],[],[],[1,6]],[[],[],[],[],[2,2]],[[],[],[],[],[2,3]]]

theorem patterns_14_7_0_verified : ∀ D ∈ patterns_14_7_0, PatternVerified 14 7 D := by

  simp only [patterns_14_7_0, List.forall_mem_cons]

  exact ⟨⟨certificate_836, certificate_836_valid⟩, ⟨⟨certificate_837, certificate_837_valid⟩, ⟨⟨certificate_838, certificate_838_valid⟩, ⟨⟨certificate_839, certificate_839_valid⟩, ⟨⟨certificate_840, certificate_840_valid⟩, ⟨⟨certificate_841, certificate_841_valid⟩, ⟨⟨certificate_842, certificate_842_valid⟩, ⟨⟨certificate_843, certificate_843_valid⟩, ⟨⟨certificate_844, certificate_844_valid⟩, ⟨⟨certificate_845, certificate_845_valid⟩, ⟨⟨certificate_846, certificate_846_valid⟩, ⟨⟨certificate_847, certificate_847_valid⟩, ⟨⟨certificate_848, certificate_848_valid⟩, ⟨⟨certificate_849, certificate_849_valid⟩, ⟨⟨certificate_850, certificate_850_valid⟩, ⟨⟨certificate_851, certificate_851_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_14_7_1 : List (List (List ℕ)) := [[[],[],[],[],[2,4]],[[],[],[],[],[2,5]],[[],[],[],[],[3,3]],[[],[],[],[],[3,4]],[[],[],[],[1],[1]],[[],[],[],[1],[2]],[[],[],[],[1],[3]],[[],[],[],[1],[4]],[[],[],[],[1],[5]],[[],[],[],[1],[6]],[[],[],[],[1,1,1]],[[],[],[],[1,1,2]],[[],[],[],[1,1,3]],[[],[],[],[1,1,4]],[[],[],[],[1,1,5]],[[],[],[],[1,2,1]]]

theorem patterns_14_7_1_verified : ∀ D ∈ patterns_14_7_1, PatternVerified 14 7 D := by

  simp only [patterns_14_7_1, List.forall_mem_cons]

  exact ⟨⟨certificate_852, certificate_852_valid⟩, ⟨⟨certificate_853, certificate_853_valid⟩, ⟨⟨certificate_854, certificate_854_valid⟩, ⟨⟨certificate_855, certificate_855_valid⟩, ⟨⟨certificate_856, certificate_856_valid⟩, ⟨⟨certificate_857, certificate_857_valid⟩, ⟨⟨certificate_858, certificate_858_valid⟩, ⟨⟨certificate_859, certificate_859_valid⟩, ⟨⟨certificate_860, certificate_860_valid⟩, ⟨⟨certificate_861, certificate_861_valid⟩, ⟨⟨certificate_862, certificate_862_valid⟩, ⟨⟨certificate_863, certificate_863_valid⟩, ⟨⟨certificate_864, certificate_864_valid⟩, ⟨⟨certificate_865, certificate_865_valid⟩, ⟨⟨certificate_866, certificate_866_valid⟩, ⟨⟨certificate_867, certificate_867_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_14_7_2 : List (List (List ℕ)) := [[[],[],[],[1,2,2]],[[],[],[],[1,2,3]],[[],[],[],[1,2,4]],[[],[],[],[1,3,1]],[[],[],[],[1,3,2]],[[],[],[],[1,3,3]],[[],[],[],[1,4,1]],[[],[],[],[1,4,2]],[[],[],[],[1,5,1]],[[],[],[],[2],[2]],[[],[],[],[2],[3]],[[],[],[],[2],[4]],[[],[],[],[2],[5]],[[],[],[],[2,1,2]],[[],[],[],[2,1,3]],[[],[],[],[2,1,4]]]

theorem patterns_14_7_2_verified : ∀ D ∈ patterns_14_7_2, PatternVerified 14 7 D := by

  simp only [patterns_14_7_2, List.forall_mem_cons]

  exact ⟨⟨certificate_868, certificate_868_valid⟩, ⟨⟨certificate_869, certificate_869_valid⟩, ⟨⟨certificate_870, certificate_870_valid⟩, ⟨⟨certificate_871, certificate_871_valid⟩, ⟨⟨certificate_872, certificate_872_valid⟩, ⟨⟨certificate_873, certificate_873_valid⟩, ⟨⟨certificate_874, certificate_874_valid⟩, ⟨⟨certificate_875, certificate_875_valid⟩, ⟨⟨certificate_876, certificate_876_valid⟩, ⟨⟨certificate_877, certificate_877_valid⟩, ⟨⟨certificate_878, certificate_878_valid⟩, ⟨⟨certificate_879, certificate_879_valid⟩, ⟨⟨certificate_880, certificate_880_valid⟩, ⟨⟨certificate_881, certificate_881_valid⟩, ⟨⟨certificate_882, certificate_882_valid⟩, ⟨⟨certificate_883, certificate_883_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_14_7_3 : List (List (List ℕ)) := [[[],[],[],[2,2,2]],[[],[],[],[2,2,3]],[[],[],[],[2,3,2]],[[],[],[],[3],[3]],[[],[],[],[3],[4]],[[],[],[],[3,1,3]],[[],[],[1],[1,1]],[[],[],[1],[1,2]],[[],[],[1],[1,3]],[[],[],[1],[1,4]],[[],[],[1],[1,5]],[[],[],[1],[2,2]],[[],[],[1],[2,3]],[[],[],[1],[2,4]],[[],[],[1],[3,3]],[[],[],[1,1],[2]]]

theorem patterns_14_7_3_verified : ∀ D ∈ patterns_14_7_3, PatternVerified 14 7 D := by

  simp only [patterns_14_7_3, List.forall_mem_cons]

  exact ⟨⟨certificate_884, certificate_884_valid⟩, ⟨⟨certificate_885, certificate_885_valid⟩, ⟨⟨certificate_886, certificate_886_valid⟩, ⟨⟨certificate_887, certificate_887_valid⟩, ⟨⟨certificate_888, certificate_888_valid⟩, ⟨⟨certificate_889, certificate_889_valid⟩, ⟨⟨certificate_890, certificate_890_valid⟩, ⟨⟨certificate_891, certificate_891_valid⟩, ⟨⟨certificate_892, certificate_892_valid⟩, ⟨⟨certificate_893, certificate_893_valid⟩, ⟨⟨certificate_894, certificate_894_valid⟩, ⟨⟨certificate_895, certificate_895_valid⟩, ⟨⟨certificate_896, certificate_896_valid⟩, ⟨⟨certificate_897, certificate_897_valid⟩, ⟨⟨certificate_898, certificate_898_valid⟩, ⟨⟨certificate_899, certificate_899_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_14_7_4 : List (List (List ℕ)) := [[[],[],[1,1],[3]],[[],[],[1,1],[4]],[[],[],[1,1],[5]],[[],[],[1,1,1,1]],[[],[],[1,1,1,2]],[[],[],[1,1,1,3]],[[],[],[1,1,1,4]],[[],[],[1,1,2,1]],[[],[],[1,1,2,2]],[[],[],[1,1,2,3]],[[],[],[1,1,3,1]],[[],[],[1,1,3,2]],[[],[],[1,1,4,1]],[[],[],[1,2],[2]],[[],[],[1,2],[3]],[[],[],[1,2],[4]]]

theorem patterns_14_7_4_verified : ∀ D ∈ patterns_14_7_4, PatternVerified 14 7 D := by

  simp only [patterns_14_7_4, List.forall_mem_cons]

  exact ⟨⟨certificate_900, certificate_900_valid⟩, ⟨⟨certificate_901, certificate_901_valid⟩, ⟨⟨certificate_902, certificate_902_valid⟩, ⟨⟨certificate_903, certificate_903_valid⟩, ⟨⟨certificate_904, certificate_904_valid⟩, ⟨⟨certificate_905, certificate_905_valid⟩, ⟨⟨certificate_906, certificate_906_valid⟩, ⟨⟨certificate_907, certificate_907_valid⟩, ⟨⟨certificate_908, certificate_908_valid⟩, ⟨⟨certificate_909, certificate_909_valid⟩, ⟨⟨certificate_910, certificate_910_valid⟩, ⟨⟨certificate_911, certificate_911_valid⟩, ⟨⟨certificate_912, certificate_912_valid⟩, ⟨⟨certificate_913, certificate_913_valid⟩, ⟨⟨certificate_914, certificate_914_valid⟩, ⟨⟨certificate_915, certificate_915_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_14_7_5 : List (List (List ℕ)) := [[[],[],[1,2,1,2]],[[],[],[1,2,1,3]],[[],[],[1,2,2,1]],[[],[],[1,2,2,2]],[[],[],[1,2,3,1]],[[],[],[1,3],[2]],[[],[],[1,3],[3]],[[],[],[1,3,1,2]],[[],[],[1,4],[2]],[[],[],[2],[2,2]],[[],[],[2],[2,3]],[[],[],[2,1,1,2]],[[],[],[2,1,1,3]],[[],[],[2,1,2,2]],[[],[],[2,2],[3]],[[],[1],[1],[1]]]

theorem patterns_14_7_5_verified : ∀ D ∈ patterns_14_7_5, PatternVerified 14 7 D := by

  simp only [patterns_14_7_5, List.forall_mem_cons]

  exact ⟨⟨certificate_916, certificate_916_valid⟩, ⟨⟨certificate_917, certificate_917_valid⟩, ⟨⟨certificate_918, certificate_918_valid⟩, ⟨⟨certificate_919, certificate_919_valid⟩, ⟨⟨certificate_920, certificate_920_valid⟩, ⟨⟨certificate_921, certificate_921_valid⟩, ⟨⟨certificate_922, certificate_922_valid⟩, ⟨⟨certificate_923, certificate_923_valid⟩, ⟨⟨certificate_924, certificate_924_valid⟩, ⟨⟨certificate_925, certificate_925_valid⟩, ⟨⟨certificate_926, certificate_926_valid⟩, ⟨⟨certificate_927, certificate_927_valid⟩, ⟨⟨certificate_928, certificate_928_valid⟩, ⟨⟨certificate_929, certificate_929_valid⟩, ⟨⟨certificate_930, certificate_930_valid⟩, ⟨⟨certificate_931, certificate_931_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_14_7_6 : List (List (List ℕ)) := [[[],[1],[1],[2]],[[],[1],[1],[3]],[[],[1],[1],[4]],[[],[1],[1],[5]],[[],[1],[1,1,1]],[[],[1],[1,1,2]],[[],[1],[1,1,3]],[[],[1],[1,1,4]],[[],[1],[1,2,1]],[[],[1],[1,2,2]],[[],[1],[1,2,3]],[[],[1],[1,3,1]],[[],[1],[1,3,2]],[[],[1],[1,4,1]],[[],[1],[2],[2]],[[],[1],[2],[3]]]

theorem patterns_14_7_6_verified : ∀ D ∈ patterns_14_7_6, PatternVerified 14 7 D := by

  simp only [patterns_14_7_6, List.forall_mem_cons]

  exact ⟨⟨certificate_932, certificate_932_valid⟩, ⟨⟨certificate_933, certificate_933_valid⟩, ⟨⟨certificate_934, certificate_934_valid⟩, ⟨⟨certificate_935, certificate_935_valid⟩, ⟨⟨certificate_936, certificate_936_valid⟩, ⟨⟨certificate_937, certificate_937_valid⟩, ⟨⟨certificate_938, certificate_938_valid⟩, ⟨⟨certificate_939, certificate_939_valid⟩, ⟨⟨certificate_940, certificate_940_valid⟩, ⟨⟨certificate_941, certificate_941_valid⟩, ⟨⟨certificate_942, certificate_942_valid⟩, ⟨⟨certificate_943, certificate_943_valid⟩, ⟨⟨certificate_944, certificate_944_valid⟩, ⟨⟨certificate_945, certificate_945_valid⟩, ⟨⟨certificate_946, certificate_946_valid⟩, ⟨⟨certificate_947, certificate_947_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_14_7_7 : List (List (List ℕ)) := [[[],[1],[2],[4]],[[],[1],[2,1,2]],[[],[1],[2,1,3]],[[],[1],[2,2,2]],[[],[1],[3],[3]],[[],[1,1],[1,1]],[[],[1,1],[1,2]],[[],[1,1],[1,3]],[[],[1,1],[1,4]],[[],[1,1],[2,2]],[[],[1,1],[2,3]],[[],[1,1,1],[2]],[[],[1,1,1],[3]],[[],[1,1,1],[4]],[[],[1,1,1,1,1]],[[],[1,1,1,1,2]]]

theorem patterns_14_7_7_verified : ∀ D ∈ patterns_14_7_7, PatternVerified 14 7 D := by

  simp only [patterns_14_7_7, List.forall_mem_cons]

  exact ⟨⟨certificate_948, certificate_948_valid⟩, ⟨⟨certificate_949, certificate_949_valid⟩, ⟨⟨certificate_950, certificate_950_valid⟩, ⟨⟨certificate_951, certificate_951_valid⟩, ⟨⟨certificate_952, certificate_952_valid⟩, ⟨⟨certificate_953, certificate_953_valid⟩, ⟨⟨certificate_954, certificate_954_valid⟩, ⟨⟨certificate_955, certificate_955_valid⟩, ⟨⟨certificate_956, certificate_956_valid⟩, ⟨⟨certificate_957, certificate_957_valid⟩, ⟨⟨certificate_958, certificate_958_valid⟩, ⟨⟨certificate_959, certificate_959_valid⟩, ⟨⟨certificate_960, certificate_960_valid⟩, ⟨⟨certificate_961, certificate_961_valid⟩, ⟨⟨certificate_962, certificate_962_valid⟩, ⟨⟨certificate_963, certificate_963_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_14_7_8 : List (List (List ℕ)) := [[[],[1,1,1,1,3]],[[],[1,1,1,2,1]],[[],[1,1,1,2,2]],[[],[1,1,1,3,1]],[[],[1,1,2],[2]],[[],[1,1,2],[3]],[[],[1,1,2,1,1]],[[],[1,1,2,1,2]],[[],[1,1,2,2,1]],[[],[1,1,3],[2]],[[],[1,1,3,1,1]],[[],[1,2],[1,2]],[[],[1,2],[1,3]],[[],[1,2],[2,2]],[[],[1,2,1],[2]],[[],[1,2,1],[3]]]

theorem patterns_14_7_8_verified : ∀ D ∈ patterns_14_7_8, PatternVerified 14 7 D := by

  simp only [patterns_14_7_8, List.forall_mem_cons]

  exact ⟨⟨certificate_964, certificate_964_valid⟩, ⟨⟨certificate_965, certificate_965_valid⟩, ⟨⟨certificate_966, certificate_966_valid⟩, ⟨⟨certificate_967, certificate_967_valid⟩, ⟨⟨certificate_968, certificate_968_valid⟩, ⟨⟨certificate_969, certificate_969_valid⟩, ⟨⟨certificate_970, certificate_970_valid⟩, ⟨⟨certificate_971, certificate_971_valid⟩, ⟨⟨certificate_972, certificate_972_valid⟩, ⟨⟨certificate_973, certificate_973_valid⟩, ⟨⟨certificate_974, certificate_974_valid⟩, ⟨⟨certificate_975, certificate_975_valid⟩, ⟨⟨certificate_976, certificate_976_valid⟩, ⟨⟨certificate_977, certificate_977_valid⟩, ⟨⟨certificate_978, certificate_978_valid⟩, ⟨⟨certificate_979, certificate_979_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_14_7_9 : List (List (List ℕ)) := [[[],[1,2,1,1,2]],[[],[1,2,1,2,1]],[[],[1,2,2],[2]],[[],[1,3,1],[2]],[[],[2],[2],[2]],[[],[2],[2],[3]],[[],[2],[2,1,2]],[[],[2,1,1,1,2]],[[1],[1],[1,1]],[[1],[1],[1,2]],[[1],[1],[1,3]],[[1],[1],[1,4]],[[1],[1],[2,2]],[[1],[1],[2,3]],[[1],[1,1],[2]],[[1],[1,1],[3]]]

theorem patterns_14_7_9_verified : ∀ D ∈ patterns_14_7_9, PatternVerified 14 7 D := by

  simp only [patterns_14_7_9, List.forall_mem_cons]

  exact ⟨⟨certificate_980, certificate_980_valid⟩, ⟨⟨certificate_981, certificate_981_valid⟩, ⟨⟨certificate_982, certificate_982_valid⟩, ⟨⟨certificate_983, certificate_983_valid⟩, ⟨⟨certificate_984, certificate_984_valid⟩, ⟨⟨certificate_985, certificate_985_valid⟩, ⟨⟨certificate_986, certificate_986_valid⟩, ⟨⟨certificate_987, certificate_987_valid⟩, ⟨⟨certificate_988, certificate_988_valid⟩, ⟨⟨certificate_989, certificate_989_valid⟩, ⟨⟨certificate_990, certificate_990_valid⟩, ⟨⟨certificate_991, certificate_991_valid⟩, ⟨⟨certificate_992, certificate_992_valid⟩, ⟨⟨certificate_993, certificate_993_valid⟩, ⟨⟨certificate_994, certificate_994_valid⟩, ⟨⟨certificate_995, certificate_995_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_14_7_10 : List (List (List ℕ)) := [[[1],[1,1],[4]],[[1],[1,1,1,1]],[[1],[1,1,1,2]],[[1],[1,1,1,3]],[[1],[1,1,2,1]],[[1],[1,1,2,2]],[[1],[1,1,3,1]],[[1],[1,2],[2]],[[1],[1,2],[3]],[[1],[1,2,1,2]],[[1],[1,2,2,1]],[[1],[1,3],[2]],[[1],[2],[2,2]],[[1],[2,1,1,2]],[[1,1],[1,1,1]],[[1,1],[1,1,2]]]

theorem patterns_14_7_10_verified : ∀ D ∈ patterns_14_7_10, PatternVerified 14 7 D := by

  simp only [patterns_14_7_10, List.forall_mem_cons]

  exact ⟨⟨certificate_996, certificate_996_valid⟩, ⟨⟨certificate_997, certificate_997_valid⟩, ⟨⟨certificate_998, certificate_998_valid⟩, ⟨⟨certificate_999, certificate_999_valid⟩, ⟨⟨certificate_1000, certificate_1000_valid⟩, ⟨⟨certificate_1001, certificate_1001_valid⟩, ⟨⟨certificate_1002, certificate_1002_valid⟩, ⟨⟨certificate_1003, certificate_1003_valid⟩, ⟨⟨certificate_1004, certificate_1004_valid⟩, ⟨⟨certificate_1005, certificate_1005_valid⟩, ⟨⟨certificate_1006, certificate_1006_valid⟩, ⟨⟨certificate_1007, certificate_1007_valid⟩, ⟨⟨certificate_1008, certificate_1008_valid⟩, ⟨⟨certificate_1009, certificate_1009_valid⟩, ⟨⟨certificate_1010, certificate_1010_valid⟩, ⟨⟨certificate_1011, certificate_1011_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_14_7_11 : List (List (List ℕ)) := [[[1,1],[1,1,3]],[[1,1],[1,2,1]],[[1,1],[1,2,2]],[[1,1],[1,3,1]],[[1,1],[2],[2]],[[1,1],[2],[3]],[[1,1],[2,1,2]],[[1,1,1],[1,2]],[[1,1,1],[1,3]],[[1,1,1],[2,2]],[[1,1,1,1],[2]],[[1,1,1,1],[3]],[[1,1,1,1,1,1]],[[1,1,1,1,1,2]],[[1,1,1,1,2,1]],[[1,1,1,2],[2]]]

theorem patterns_14_7_11_verified : ∀ D ∈ patterns_14_7_11, PatternVerified 14 7 D := by

  simp only [patterns_14_7_11, List.forall_mem_cons]

  exact ⟨⟨certificate_1012, certificate_1012_valid⟩, ⟨⟨certificate_1013, certificate_1013_valid⟩, ⟨⟨certificate_1014, certificate_1014_valid⟩, ⟨⟨certificate_1015, certificate_1015_valid⟩, ⟨⟨certificate_1016, certificate_1016_valid⟩, ⟨⟨certificate_1017, certificate_1017_valid⟩, ⟨⟨certificate_1018, certificate_1018_valid⟩, ⟨⟨certificate_1019, certificate_1019_valid⟩, ⟨⟨certificate_1020, certificate_1020_valid⟩, ⟨⟨certificate_1021, certificate_1021_valid⟩, ⟨⟨certificate_1022, certificate_1022_valid⟩, ⟨⟨certificate_1023, certificate_1023_valid⟩, ⟨⟨certificate_1024, certificate_1024_valid⟩, ⟨⟨certificate_1025, certificate_1025_valid⟩, ⟨⟨certificate_1026, certificate_1026_valid⟩, ⟨⟨certificate_1027, certificate_1027_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_14_7_12 : List (List (List ℕ)) := [[[1,1,1,2,1,1]],[[1,1,2],[1,2]],[[1,1,2,1],[2]],[[1,2],[1,2,1]],[[1,2],[2],[2]]]

theorem patterns_14_7_12_verified : ∀ D ∈ patterns_14_7_12, PatternVerified 14 7 D := by

  simp only [patterns_14_7_12, List.forall_mem_cons]

  exact ⟨⟨certificate_1028, certificate_1028_valid⟩, ⟨⟨certificate_1029, certificate_1029_valid⟩, ⟨⟨certificate_1030, certificate_1030_valid⟩, ⟨⟨certificate_1031, certificate_1031_valid⟩, ⟨⟨certificate_1032, certificate_1032_valid⟩, (by simp)⟩⟩⟩⟩⟩

noncomputable def patterns_14_7 : List (List (List ℕ)) := patterns_14_7_0 ++ (patterns_14_7_1 ++ (patterns_14_7_2 ++ (patterns_14_7_3 ++ (patterns_14_7_4 ++ (patterns_14_7_5 ++ (patterns_14_7_6 ++ (patterns_14_7_7 ++ (patterns_14_7_8 ++ (patterns_14_7_9 ++ (patterns_14_7_10 ++ (patterns_14_7_11 ++ (patterns_14_7_12 ++ ([])))))))))))))

theorem patterns_14_7_verified : ∀ D ∈ patterns_14_7, PatternVerified 14 7 D := by

  simp only [patterns_14_7, List.forall_mem_append]

  exact ⟨patterns_14_7_0_verified, ⟨patterns_14_7_1_verified, ⟨patterns_14_7_2_verified, ⟨patterns_14_7_3_verified, ⟨patterns_14_7_4_verified, ⟨patterns_14_7_5_verified, ⟨patterns_14_7_6_verified, ⟨patterns_14_7_7_verified, ⟨patterns_14_7_8_verified, ⟨patterns_14_7_9_verified, ⟨patterns_14_7_10_verified, ⟨patterns_14_7_11_verified, ⟨patterns_14_7_12_verified, by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_14_7_coverage : patternChoices 7 7 [] = patterns_14_7 := by decide +kernel

theorem finite_patterns_14_7 : ∀ D ∈ patternChoices 7 (14-7) [], PatternVerified 14 7 D := by

  rw [patterns_14_7_coverage]

  exact patterns_14_7_verified

end CycleClique

end OAI
