import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CachedDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.Certificates002
import OAI.Combinatorics.Ramsey.CycleClique.Certificates003
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

noncomputable def patterns_8_5_0 : List (List (List ℕ)) := [[[],[],[],[],[]],[[],[],[],[1]],[[],[],[],[2]],[[],[],[],[3]],[[],[],[1,1]],[[],[],[1,2]],[[],[1],[1]],[[],[1],[2]],[[],[1,1,1]],[[1],[1,1]]]

theorem patterns_8_5_0_verified : ∀ D ∈ patterns_8_5_0, PatternVerified 8 5 D := by

  simp only [patterns_8_5_0, List.forall_mem_cons]

  exact ⟨⟨certificate_63, certificate_63_valid⟩, ⟨⟨certificate_64, certificate_64_valid⟩, ⟨⟨certificate_65, certificate_65_valid⟩, ⟨⟨certificate_66, certificate_66_valid⟩, ⟨⟨certificate_67, certificate_67_valid⟩, ⟨⟨certificate_68, certificate_68_valid⟩, ⟨⟨certificate_69, certificate_69_valid⟩, ⟨⟨certificate_70, certificate_70_valid⟩, ⟨⟨certificate_71, certificate_71_valid⟩, ⟨⟨certificate_72, certificate_72_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_8_5 : List (List (List ℕ)) := patterns_8_5_0 ++ ([])

theorem patterns_8_5_verified : ∀ D ∈ patterns_8_5, PatternVerified 8 5 D := by

  simp only [patterns_8_5, List.forall_mem_append]

  exact ⟨patterns_8_5_0_verified, by simp⟩

theorem patterns_8_5_coverage : patternChoices 5 3 [] = patterns_8_5 := by decide +kernel

theorem finite_patterns_8_5 : ∀ D ∈ patternChoices 5 (8-5) [], PatternVerified 8 5 D := by

  rw [patterns_8_5_coverage]

  exact patterns_8_5_verified

end CycleClique

end OAI
