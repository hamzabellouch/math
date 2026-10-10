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

noncomputable def patterns_6_4_0 : List (List (List ℕ)) := [[[],[],[],[]],[[],[],[1]],[[],[],[2]],[[],[1,1]],[[1],[1]]]

theorem patterns_6_4_0_verified : ∀ D ∈ patterns_6_4_0, PatternVerified 6 4 D := by

  simp only [patterns_6_4_0, List.forall_mem_cons]

  exact ⟨⟨certificate_13, certificate_13_valid⟩, ⟨⟨certificate_14, certificate_14_valid⟩, ⟨⟨certificate_15, certificate_15_valid⟩, ⟨⟨certificate_16, certificate_16_valid⟩, ⟨⟨certificate_17, certificate_17_valid⟩, (by simp)⟩⟩⟩⟩⟩

noncomputable def patterns_6_4 : List (List (List ℕ)) := patterns_6_4_0 ++ ([])

theorem patterns_6_4_verified : ∀ D ∈ patterns_6_4, PatternVerified 6 4 D := by

  simp only [patterns_6_4, List.forall_mem_append]

  exact ⟨patterns_6_4_0_verified, by simp⟩

theorem patterns_6_4_coverage : patternChoices 4 2 [] = patterns_6_4 := by decide +kernel

theorem finite_patterns_6_4 : ∀ D ∈ patternChoices 4 (6-4) [], PatternVerified 6 4 D := by

  rw [patterns_6_4_coverage]

  exact patterns_6_4_verified

end CycleClique

end OAI
