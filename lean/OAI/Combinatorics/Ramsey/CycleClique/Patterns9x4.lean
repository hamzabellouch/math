import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CachedDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.Certificates003
import OAI.Combinatorics.Ramsey.CycleClique.Certificates004
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

noncomputable def patterns_9_4_0 : List (List (List ℕ)) := [[[],[],[],[]],[[],[],[1]],[[],[],[2]],[[],[],[3]],[[],[],[4]],[[],[],[5]],[[],[1,1]],[[],[1,2]],[[],[1,3]],[[],[1,4]],[[],[2,2]],[[],[2,3]],[[1],[1]],[[1],[2]],[[1],[3]],[[1],[4]]]

theorem patterns_9_4_0_verified : ∀ D ∈ patterns_9_4_0, PatternVerified 9 4 D := by

  simp only [patterns_9_4_0, List.forall_mem_cons]

  exact ⟨⟨certificate_81, certificate_81_valid⟩, ⟨⟨certificate_82, certificate_82_valid⟩, ⟨⟨certificate_83, certificate_83_valid⟩, ⟨⟨certificate_84, certificate_84_valid⟩, ⟨⟨certificate_85, certificate_85_valid⟩, ⟨⟨certificate_86, certificate_86_valid⟩, ⟨⟨certificate_87, certificate_87_valid⟩, ⟨⟨certificate_88, certificate_88_valid⟩, ⟨⟨certificate_89, certificate_89_valid⟩, ⟨⟨certificate_90, certificate_90_valid⟩, ⟨⟨certificate_91, certificate_91_valid⟩, ⟨⟨certificate_92, certificate_92_valid⟩, ⟨⟨certificate_93, certificate_93_valid⟩, ⟨⟨certificate_94, certificate_94_valid⟩, ⟨⟨certificate_95, certificate_95_valid⟩, ⟨⟨certificate_96, certificate_96_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_9_4_1 : List (List (List ℕ)) := [[[1,1,1]],[[1,1,2]],[[1,1,3]],[[1,2,1]],[[1,2,2]],[[1,3,1]],[[2],[2]],[[2],[3]],[[2,1,2]]]

theorem patterns_9_4_1_verified : ∀ D ∈ patterns_9_4_1, PatternVerified 9 4 D := by

  simp only [patterns_9_4_1, List.forall_mem_cons]

  exact ⟨⟨certificate_97, certificate_97_valid⟩, ⟨⟨certificate_98, certificate_98_valid⟩, ⟨⟨certificate_99, certificate_99_valid⟩, ⟨⟨certificate_100, certificate_100_valid⟩, ⟨⟨certificate_101, certificate_101_valid⟩, ⟨⟨certificate_102, certificate_102_valid⟩, ⟨⟨certificate_103, certificate_103_valid⟩, ⟨⟨certificate_104, certificate_104_valid⟩, ⟨⟨certificate_105, certificate_105_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_9_4 : List (List (List ℕ)) := patterns_9_4_0 ++ (patterns_9_4_1 ++ ([]))

theorem patterns_9_4_verified : ∀ D ∈ patterns_9_4, PatternVerified 9 4 D := by

  simp only [patterns_9_4, List.forall_mem_append]

  exact ⟨patterns_9_4_0_verified, ⟨patterns_9_4_1_verified, by simp⟩⟩

theorem patterns_9_4_coverage : patternChoices 4 5 [] = patterns_9_4 := by decide +kernel

theorem finite_patterns_9_4 : ∀ D ∈ patternChoices 4 (9-4) [], PatternVerified 9 4 D := by

  rw [patterns_9_4_coverage]

  exact patterns_9_4_verified

end CycleClique

end OAI
