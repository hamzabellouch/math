import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CachedDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.Certificates001
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

noncomputable def patterns_7_4_0 : List (List (List ℕ)) := [[[],[],[],[]],[[],[],[1]],[[],[],[2]],[[],[],[3]],[[],[1,1]],[[],[1,2]],[[1],[1]],[[1],[2]],[[1,1,1]]]

theorem patterns_7_4_0_verified : ∀ D ∈ patterns_7_4_0, PatternVerified 7 4 D := by

  simp only [patterns_7_4_0, List.forall_mem_cons]

  exact ⟨⟨certificate_30, certificate_30_valid⟩, ⟨⟨certificate_31, certificate_31_valid⟩, ⟨⟨certificate_32, certificate_32_valid⟩, ⟨⟨certificate_33, certificate_33_valid⟩, ⟨⟨certificate_34, certificate_34_valid⟩, ⟨⟨certificate_35, certificate_35_valid⟩, ⟨⟨certificate_36, certificate_36_valid⟩, ⟨⟨certificate_37, certificate_37_valid⟩, ⟨⟨certificate_38, certificate_38_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_7_4 : List (List (List ℕ)) := patterns_7_4_0 ++ ([])

theorem patterns_7_4_verified : ∀ D ∈ patterns_7_4, PatternVerified 7 4 D := by

  simp only [patterns_7_4, List.forall_mem_append]

  exact ⟨patterns_7_4_0_verified, by simp⟩

theorem patterns_7_4_coverage : patternChoices 4 3 [] = patterns_7_4 := by decide +kernel

theorem finite_patterns_7_4 : ∀ D ∈ patternChoices 4 (7-4) [], PatternVerified 7 4 D := by

  rw [patterns_7_4_coverage]

  exact patterns_7_4_verified

end CycleClique

end OAI
