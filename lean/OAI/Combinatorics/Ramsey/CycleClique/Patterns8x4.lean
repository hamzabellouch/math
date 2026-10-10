import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CachedDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.Certificates002
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

noncomputable def patterns_8_4_0 : List (List (List ℕ)) := [[[],[],[],[]],[[],[],[1]],[[],[],[2]],[[],[],[3]],[[],[],[4]],[[],[1,1]],[[],[1,2]],[[],[1,3]],[[],[2,2]],[[1],[1]],[[1],[2]],[[1],[3]],[[1,1,1]],[[1,1,2]],[[1,2,1]],[[2],[2]]]

theorem patterns_8_4_0_verified : ∀ D ∈ patterns_8_4_0, PatternVerified 8 4 D := by

  simp only [patterns_8_4_0, List.forall_mem_cons]

  exact ⟨⟨certificate_47, certificate_47_valid⟩, ⟨⟨certificate_48, certificate_48_valid⟩, ⟨⟨certificate_49, certificate_49_valid⟩, ⟨⟨certificate_50, certificate_50_valid⟩, ⟨⟨certificate_51, certificate_51_valid⟩, ⟨⟨certificate_52, certificate_52_valid⟩, ⟨⟨certificate_53, certificate_53_valid⟩, ⟨⟨certificate_54, certificate_54_valid⟩, ⟨⟨certificate_55, certificate_55_valid⟩, ⟨⟨certificate_56, certificate_56_valid⟩, ⟨⟨certificate_57, certificate_57_valid⟩, ⟨⟨certificate_58, certificate_58_valid⟩, ⟨⟨certificate_59, certificate_59_valid⟩, ⟨⟨certificate_60, certificate_60_valid⟩, ⟨⟨certificate_61, certificate_61_valid⟩, ⟨⟨certificate_62, certificate_62_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_8_4 : List (List (List ℕ)) := patterns_8_4_0 ++ ([])

theorem patterns_8_4_verified : ∀ D ∈ patterns_8_4, PatternVerified 8 4 D := by

  simp only [patterns_8_4, List.forall_mem_append]

  exact ⟨patterns_8_4_0_verified, by simp⟩

theorem patterns_8_4_coverage : patternChoices 4 4 [] = patterns_8_4 := by decide +kernel

theorem finite_patterns_8_4 : ∀ D ∈ patternChoices 4 (8-4) [], PatternVerified 8 4 D := by

  rw [patterns_8_4_coverage]

  exact patterns_8_4_verified

end CycleClique

end OAI
