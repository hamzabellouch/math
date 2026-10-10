import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CachedDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
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

noncomputable def patterns_9_5_0 : List (List (List ℕ)) := [[[],[],[],[],[]],[[],[],[],[1]],[[],[],[],[2]],[[],[],[],[3]],[[],[],[],[4]],[[],[],[1,1]],[[],[],[1,2]],[[],[],[1,3]],[[],[],[2,2]],[[],[1],[1]],[[],[1],[2]],[[],[1],[3]],[[],[1,1,1]],[[],[1,1,2]],[[],[1,2,1]],[[],[2],[2]]]

theorem patterns_9_5_0_verified : ∀ D ∈ patterns_9_5_0, PatternVerified 9 5 D := by

  simp only [patterns_9_5_0, List.forall_mem_cons]

  exact ⟨⟨certificate_106, certificate_106_valid⟩, ⟨⟨certificate_107, certificate_107_valid⟩, ⟨⟨certificate_108, certificate_108_valid⟩, ⟨⟨certificate_109, certificate_109_valid⟩, ⟨⟨certificate_110, certificate_110_valid⟩, ⟨⟨certificate_111, certificate_111_valid⟩, ⟨⟨certificate_112, certificate_112_valid⟩, ⟨⟨certificate_113, certificate_113_valid⟩, ⟨⟨certificate_114, certificate_114_valid⟩, ⟨⟨certificate_115, certificate_115_valid⟩, ⟨⟨certificate_116, certificate_116_valid⟩, ⟨⟨certificate_117, certificate_117_valid⟩, ⟨⟨certificate_118, certificate_118_valid⟩, ⟨⟨certificate_119, certificate_119_valid⟩, ⟨⟨certificate_120, certificate_120_valid⟩, ⟨⟨certificate_121, certificate_121_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_9_5_1 : List (List (List ℕ)) := [[[1],[1,1]],[[1],[1,2]],[[1,1],[2]],[[1,1,1,1]]]

theorem patterns_9_5_1_verified : ∀ D ∈ patterns_9_5_1, PatternVerified 9 5 D := by

  simp only [patterns_9_5_1, List.forall_mem_cons]

  exact ⟨⟨certificate_122, certificate_122_valid⟩, ⟨⟨certificate_123, certificate_123_valid⟩, ⟨⟨certificate_124, certificate_124_valid⟩, ⟨⟨certificate_125, certificate_125_valid⟩, (by simp)⟩⟩⟩⟩

noncomputable def patterns_9_5 : List (List (List ℕ)) := patterns_9_5_0 ++ (patterns_9_5_1 ++ ([]))

theorem patterns_9_5_verified : ∀ D ∈ patterns_9_5, PatternVerified 9 5 D := by

  simp only [patterns_9_5, List.forall_mem_append]

  exact ⟨patterns_9_5_0_verified, ⟨patterns_9_5_1_verified, by simp⟩⟩

theorem patterns_9_5_coverage : patternChoices 5 4 [] = patterns_9_5 := by decide +kernel

theorem finite_patterns_9_5 : ∀ D ∈ patternChoices 5 (9-5) [], PatternVerified 9 5 D := by

  rw [patterns_9_5_coverage]

  exact patterns_9_5_verified

end CycleClique

end OAI
