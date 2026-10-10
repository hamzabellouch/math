import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CachedDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.Certificates006
import OAI.Combinatorics.Ramsey.CycleClique.Certificates007
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

noncomputable def patterns_10_6_0 : List (List (List ℕ)) := [[[],[],[],[],[],[]],[[],[],[],[],[1]],[[],[],[],[],[2]],[[],[],[],[],[3]],[[],[],[],[],[4]],[[],[],[],[1,1]],[[],[],[],[1,2]],[[],[],[],[1,3]],[[],[],[],[2,2]],[[],[],[1],[1]],[[],[],[1],[2]],[[],[],[1],[3]],[[],[],[1,1,1]],[[],[],[1,1,2]],[[],[],[1,2,1]],[[],[],[2],[2]]]

theorem patterns_10_6_0_verified : ∀ D ∈ patterns_10_6_0, PatternVerified 10 6 D := by

  simp only [patterns_10_6_0, List.forall_mem_cons]

  exact ⟨⟨certificate_179, certificate_179_valid⟩, ⟨⟨certificate_180, certificate_180_valid⟩, ⟨⟨certificate_181, certificate_181_valid⟩, ⟨⟨certificate_182, certificate_182_valid⟩, ⟨⟨certificate_183, certificate_183_valid⟩, ⟨⟨certificate_184, certificate_184_valid⟩, ⟨⟨certificate_185, certificate_185_valid⟩, ⟨⟨certificate_186, certificate_186_valid⟩, ⟨⟨certificate_187, certificate_187_valid⟩, ⟨⟨certificate_188, certificate_188_valid⟩, ⟨⟨certificate_189, certificate_189_valid⟩, ⟨⟨certificate_190, certificate_190_valid⟩, ⟨⟨certificate_191, certificate_191_valid⟩, ⟨⟨certificate_192, certificate_192_valid⟩, ⟨⟨certificate_193, certificate_193_valid⟩, ⟨⟨certificate_194, certificate_194_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_10_6_1 : List (List (List ℕ)) := [[[],[1],[1,1]],[[],[1],[1,2]],[[],[1,1],[2]],[[],[1,1,1,1]],[[1],[1],[1]],[[1],[1],[2]],[[1],[1,1,1]],[[1,1],[1,1]]]

theorem patterns_10_6_1_verified : ∀ D ∈ patterns_10_6_1, PatternVerified 10 6 D := by

  simp only [patterns_10_6_1, List.forall_mem_cons]

  exact ⟨⟨certificate_195, certificate_195_valid⟩, ⟨⟨certificate_196, certificate_196_valid⟩, ⟨⟨certificate_197, certificate_197_valid⟩, ⟨⟨certificate_198, certificate_198_valid⟩, ⟨⟨certificate_199, certificate_199_valid⟩, ⟨⟨certificate_200, certificate_200_valid⟩, ⟨⟨certificate_201, certificate_201_valid⟩, ⟨⟨certificate_202, certificate_202_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_10_6 : List (List (List ℕ)) := patterns_10_6_0 ++ (patterns_10_6_1 ++ ([]))

theorem patterns_10_6_verified : ∀ D ∈ patterns_10_6, PatternVerified 10 6 D := by

  simp only [patterns_10_6, List.forall_mem_append]

  exact ⟨patterns_10_6_0_verified, ⟨patterns_10_6_1_verified, by simp⟩⟩

theorem patterns_10_6_coverage : patternChoices 6 4 [] = patterns_10_6 := by decide +kernel

theorem finite_patterns_10_6 : ∀ D ∈ patternChoices 6 (10-6) [], PatternVerified 10 6 D := by

  rw [patterns_10_6_coverage]

  exact patterns_10_6_verified

end CycleClique

end OAI
