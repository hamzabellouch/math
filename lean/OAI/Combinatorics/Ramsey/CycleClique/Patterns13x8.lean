import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CachedDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.Certificates025
import OAI.Combinatorics.Ramsey.CycleClique.Certificates026
import OAI.Combinatorics.Ramsey.CycleClique.Certificates027
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

noncomputable def patterns_13_8_0 : List (List (List ℕ)) := [[[],[],[],[],[],[],[],[]],[[],[],[],[],[],[],[1]],[[],[],[],[],[],[],[2]],[[],[],[],[],[],[],[3]],[[],[],[],[],[],[],[4]],[[],[],[],[],[],[],[5]],[[],[],[],[],[],[1,1]],[[],[],[],[],[],[1,2]],[[],[],[],[],[],[1,3]],[[],[],[],[],[],[1,4]],[[],[],[],[],[],[2,2]],[[],[],[],[],[],[2,3]],[[],[],[],[],[1],[1]],[[],[],[],[],[1],[2]],[[],[],[],[],[1],[3]],[[],[],[],[],[1],[4]]]

theorem patterns_13_8_0_verified : ∀ D ∈ patterns_13_8_0, PatternVerified 13 8 D := by

  simp only [patterns_13_8_0, List.forall_mem_cons]

  exact ⟨⟨certificate_781, certificate_781_valid⟩, ⟨⟨certificate_782, certificate_782_valid⟩, ⟨⟨certificate_783, certificate_783_valid⟩, ⟨⟨certificate_784, certificate_784_valid⟩, ⟨⟨certificate_785, certificate_785_valid⟩, ⟨⟨certificate_786, certificate_786_valid⟩, ⟨⟨certificate_787, certificate_787_valid⟩, ⟨⟨certificate_788, certificate_788_valid⟩, ⟨⟨certificate_789, certificate_789_valid⟩, ⟨⟨certificate_790, certificate_790_valid⟩, ⟨⟨certificate_791, certificate_791_valid⟩, ⟨⟨certificate_792, certificate_792_valid⟩, ⟨⟨certificate_793, certificate_793_valid⟩, ⟨⟨certificate_794, certificate_794_valid⟩, ⟨⟨certificate_795, certificate_795_valid⟩, ⟨⟨certificate_796, certificate_796_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_13_8_1 : List (List (List ℕ)) := [[[],[],[],[],[1,1,1]],[[],[],[],[],[1,1,2]],[[],[],[],[],[1,1,3]],[[],[],[],[],[1,2,1]],[[],[],[],[],[1,2,2]],[[],[],[],[],[1,3,1]],[[],[],[],[],[2],[2]],[[],[],[],[],[2],[3]],[[],[],[],[],[2,1,2]],[[],[],[],[1],[1,1]],[[],[],[],[1],[1,2]],[[],[],[],[1],[1,3]],[[],[],[],[1],[2,2]],[[],[],[],[1,1],[2]],[[],[],[],[1,1],[3]],[[],[],[],[1,1,1,1]]]

theorem patterns_13_8_1_verified : ∀ D ∈ patterns_13_8_1, PatternVerified 13 8 D := by

  simp only [patterns_13_8_1, List.forall_mem_cons]

  exact ⟨⟨certificate_797, certificate_797_valid⟩, ⟨⟨certificate_798, certificate_798_valid⟩, ⟨⟨certificate_799, certificate_799_valid⟩, ⟨⟨certificate_800, certificate_800_valid⟩, ⟨⟨certificate_801, certificate_801_valid⟩, ⟨⟨certificate_802, certificate_802_valid⟩, ⟨⟨certificate_803, certificate_803_valid⟩, ⟨⟨certificate_804, certificate_804_valid⟩, ⟨⟨certificate_805, certificate_805_valid⟩, ⟨⟨certificate_806, certificate_806_valid⟩, ⟨⟨certificate_807, certificate_807_valid⟩, ⟨⟨certificate_808, certificate_808_valid⟩, ⟨⟨certificate_809, certificate_809_valid⟩, ⟨⟨certificate_810, certificate_810_valid⟩, ⟨⟨certificate_811, certificate_811_valid⟩, ⟨⟨certificate_812, certificate_812_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_13_8_2 : List (List (List ℕ)) := [[[],[],[],[1,1,1,2]],[[],[],[],[1,1,2,1]],[[],[],[],[1,2],[2]],[[],[],[1],[1],[1]],[[],[],[1],[1],[2]],[[],[],[1],[1],[3]],[[],[],[1],[1,1,1]],[[],[],[1],[1,1,2]],[[],[],[1],[1,2,1]],[[],[],[1],[2],[2]],[[],[],[1,1],[1,1]],[[],[],[1,1],[1,2]],[[],[],[1,1,1],[2]],[[],[],[1,1,1,1,1]],[[],[1],[1],[1,1]],[[],[1],[1],[1,2]]]

theorem patterns_13_8_2_verified : ∀ D ∈ patterns_13_8_2, PatternVerified 13 8 D := by

  simp only [patterns_13_8_2, List.forall_mem_cons]

  exact ⟨⟨certificate_813, certificate_813_valid⟩, ⟨⟨certificate_814, certificate_814_valid⟩, ⟨⟨certificate_815, certificate_815_valid⟩, ⟨⟨certificate_816, certificate_816_valid⟩, ⟨⟨certificate_817, certificate_817_valid⟩, ⟨⟨certificate_818, certificate_818_valid⟩, ⟨⟨certificate_819, certificate_819_valid⟩, ⟨⟨certificate_820, certificate_820_valid⟩, ⟨⟨certificate_821, certificate_821_valid⟩, ⟨⟨certificate_822, certificate_822_valid⟩, ⟨⟨certificate_823, certificate_823_valid⟩, ⟨⟨certificate_824, certificate_824_valid⟩, ⟨⟨certificate_825, certificate_825_valid⟩, ⟨⟨certificate_826, certificate_826_valid⟩, ⟨⟨certificate_827, certificate_827_valid⟩, ⟨⟨certificate_828, certificate_828_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_13_8_3 : List (List (List ℕ)) := [[[],[1],[1,1],[2]],[[],[1],[1,1,1,1]],[[],[1,1],[1,1,1]],[[1],[1],[1],[1]],[[1],[1],[1],[2]],[[1],[1],[1,1,1]],[[1],[1,1],[1,1]]]

theorem patterns_13_8_3_verified : ∀ D ∈ patterns_13_8_3, PatternVerified 13 8 D := by

  simp only [patterns_13_8_3, List.forall_mem_cons]

  exact ⟨⟨certificate_829, certificate_829_valid⟩, ⟨⟨certificate_830, certificate_830_valid⟩, ⟨⟨certificate_831, certificate_831_valid⟩, ⟨⟨certificate_832, certificate_832_valid⟩, ⟨⟨certificate_833, certificate_833_valid⟩, ⟨⟨certificate_834, certificate_834_valid⟩, ⟨⟨certificate_835, certificate_835_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_13_8 : List (List (List ℕ)) := patterns_13_8_0 ++ (patterns_13_8_1 ++ (patterns_13_8_2 ++ (patterns_13_8_3 ++ ([]))))

theorem patterns_13_8_verified : ∀ D ∈ patterns_13_8, PatternVerified 13 8 D := by

  simp only [patterns_13_8, List.forall_mem_append]

  exact ⟨patterns_13_8_0_verified, ⟨patterns_13_8_1_verified, ⟨patterns_13_8_2_verified, ⟨patterns_13_8_3_verified, by simp⟩⟩⟩⟩

theorem patterns_13_8_coverage : patternChoices 8 5 [] = patterns_13_8 := by decide +kernel

theorem finite_patterns_13_8 : ∀ D ∈ patternChoices 8 (13-8) [], PatternVerified 13 8 D := by

  rw [patterns_13_8_coverage]

  exact patterns_13_8_verified

end CycleClique

end OAI
