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

noncomputable def patterns_5_3_0 : List (List (List ℕ)) := [[[],[],[]],[[],[1]],[[],[2]],[[1,1]]]

theorem patterns_5_3_0_verified : ∀ D ∈ patterns_5_3_0, PatternVerified 5 3 D := by

  simp only [patterns_5_3_0, List.forall_mem_cons]

  exact ⟨⟨certificate_0, certificate_0_valid⟩, ⟨⟨certificate_1, certificate_1_valid⟩, ⟨⟨certificate_2, certificate_2_valid⟩, ⟨⟨certificate_3, certificate_3_valid⟩, (by simp)⟩⟩⟩⟩

noncomputable def patterns_5_3 : List (List (List ℕ)) := patterns_5_3_0 ++ ([])

theorem patterns_5_3_verified : ∀ D ∈ patterns_5_3, PatternVerified 5 3 D := by

  simp only [patterns_5_3, List.forall_mem_append]

  exact ⟨patterns_5_3_0_verified, by simp⟩

theorem patterns_5_3_coverage : patternChoices 3 2 [] = patterns_5_3 := by decide +kernel

theorem finite_patterns_5_3 : ∀ D ∈ patternChoices 3 (5-3) [], PatternVerified 5 3 D := by

  rw [patterns_5_3_coverage]

  exact patterns_5_3_verified

end CycleClique

end OAI
