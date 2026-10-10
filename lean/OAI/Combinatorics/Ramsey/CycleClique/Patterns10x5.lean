import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CachedDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.Certificates005
import OAI.Combinatorics.Ramsey.CycleClique.Certificates006
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

noncomputable def patterns_10_5_0 : List (List (List ℕ)) := [[[],[],[],[],[]],[[],[],[],[1]],[[],[],[],[2]],[[],[],[],[3]],[[],[],[],[4]],[[],[],[],[5]],[[],[],[1,1]],[[],[],[1,2]],[[],[],[1,3]],[[],[],[1,4]],[[],[],[2,2]],[[],[],[2,3]],[[],[1],[1]],[[],[1],[2]],[[],[1],[3]],[[],[1],[4]]]

theorem patterns_10_5_0_verified : ∀ D ∈ patterns_10_5_0, PatternVerified 10 5 D := by

  simp only [patterns_10_5_0, List.forall_mem_cons]

  exact ⟨⟨certificate_144, certificate_144_valid⟩, ⟨⟨certificate_145, certificate_145_valid⟩, ⟨⟨certificate_146, certificate_146_valid⟩, ⟨⟨certificate_147, certificate_147_valid⟩, ⟨⟨certificate_148, certificate_148_valid⟩, ⟨⟨certificate_149, certificate_149_valid⟩, ⟨⟨certificate_150, certificate_150_valid⟩, ⟨⟨certificate_151, certificate_151_valid⟩, ⟨⟨certificate_152, certificate_152_valid⟩, ⟨⟨certificate_153, certificate_153_valid⟩, ⟨⟨certificate_154, certificate_154_valid⟩, ⟨⟨certificate_155, certificate_155_valid⟩, ⟨⟨certificate_156, certificate_156_valid⟩, ⟨⟨certificate_157, certificate_157_valid⟩, ⟨⟨certificate_158, certificate_158_valid⟩, ⟨⟨certificate_159, certificate_159_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_10_5_1 : List (List (List ℕ)) := [[[],[1,1,1]],[[],[1,1,2]],[[],[1,1,3]],[[],[1,2,1]],[[],[1,2,2]],[[],[1,3,1]],[[],[2],[2]],[[],[2],[3]],[[],[2,1,2]],[[1],[1,1]],[[1],[1,2]],[[1],[1,3]],[[1],[2,2]],[[1,1],[2]],[[1,1],[3]],[[1,1,1,1]]]

theorem patterns_10_5_1_verified : ∀ D ∈ patterns_10_5_1, PatternVerified 10 5 D := by

  simp only [patterns_10_5_1, List.forall_mem_cons]

  exact ⟨⟨certificate_160, certificate_160_valid⟩, ⟨⟨certificate_161, certificate_161_valid⟩, ⟨⟨certificate_162, certificate_162_valid⟩, ⟨⟨certificate_163, certificate_163_valid⟩, ⟨⟨certificate_164, certificate_164_valid⟩, ⟨⟨certificate_165, certificate_165_valid⟩, ⟨⟨certificate_166, certificate_166_valid⟩, ⟨⟨certificate_167, certificate_167_valid⟩, ⟨⟨certificate_168, certificate_168_valid⟩, ⟨⟨certificate_169, certificate_169_valid⟩, ⟨⟨certificate_170, certificate_170_valid⟩, ⟨⟨certificate_171, certificate_171_valid⟩, ⟨⟨certificate_172, certificate_172_valid⟩, ⟨⟨certificate_173, certificate_173_valid⟩, ⟨⟨certificate_174, certificate_174_valid⟩, ⟨⟨certificate_175, certificate_175_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_10_5_2 : List (List (List ℕ)) := [[[1,1,1,2]],[[1,1,2,1]],[[1,2],[2]]]

theorem patterns_10_5_2_verified : ∀ D ∈ patterns_10_5_2, PatternVerified 10 5 D := by

  simp only [patterns_10_5_2, List.forall_mem_cons]

  exact ⟨⟨certificate_176, certificate_176_valid⟩, ⟨⟨certificate_177, certificate_177_valid⟩, ⟨⟨certificate_178, certificate_178_valid⟩, (by simp)⟩⟩⟩

noncomputable def patterns_10_5 : List (List (List ℕ)) := patterns_10_5_0 ++ (patterns_10_5_1 ++ (patterns_10_5_2 ++ ([])))

theorem patterns_10_5_verified : ∀ D ∈ patterns_10_5, PatternVerified 10 5 D := by

  simp only [patterns_10_5, List.forall_mem_append]

  exact ⟨patterns_10_5_0_verified, ⟨patterns_10_5_1_verified, ⟨patterns_10_5_2_verified, by simp⟩⟩⟩

theorem patterns_10_5_coverage : patternChoices 5 5 [] = patterns_10_5 := by decide +kernel

theorem finite_patterns_10_5 : ∀ D ∈ patternChoices 5 (10-5) [], PatternVerified 10 5 D := by

  rw [patterns_10_5_coverage]

  exact patterns_10_5_verified

end CycleClique

end OAI
