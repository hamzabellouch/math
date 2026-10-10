import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CachedDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.Certificates001
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

noncomputable def patterns_6_3_0 : List (List (List ℕ)) := [[[],[],[]],[[],[1]],[[],[2]],[[],[3]],[[1,1]],[[1,2]]]

theorem patterns_6_3_0_verified : ∀ D ∈ patterns_6_3_0, PatternVerified 6 3 D := by

  simp only [patterns_6_3_0, List.forall_mem_cons]

  exact ⟨⟨certificate_7, certificate_7_valid⟩, ⟨⟨certificate_8, certificate_8_valid⟩, ⟨⟨certificate_9, certificate_9_valid⟩, ⟨⟨certificate_10, certificate_10_valid⟩, ⟨⟨certificate_11, certificate_11_valid⟩, ⟨⟨certificate_12, certificate_12_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩

noncomputable def patterns_6_3 : List (List (List ℕ)) := patterns_6_3_0 ++ ([])

theorem patterns_6_3_verified : ∀ D ∈ patterns_6_3, PatternVerified 6 3 D := by

  simp only [patterns_6_3, List.forall_mem_append]

  exact ⟨patterns_6_3_0_verified, by simp⟩

theorem patterns_6_3_coverage : patternChoices 3 3 [] = patterns_6_3 := by decide +kernel

theorem finite_patterns_6_3 : ∀ D ∈ patternChoices 3 (6-3) [], PatternVerified 6 3 D := by

  rw [patterns_6_3_coverage]

  exact patterns_6_3_verified

end CycleClique

end OAI
