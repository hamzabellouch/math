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

noncomputable def patterns_5_4_0 : List (List (List ℕ)) := [[[],[],[],[]],[[],[],[1]]]

theorem patterns_5_4_0_verified : ∀ D ∈ patterns_5_4_0, PatternVerified 5 4 D := by

  simp only [patterns_5_4_0, List.forall_mem_cons]

  exact ⟨⟨certificate_4, certificate_4_valid⟩, ⟨⟨certificate_5, certificate_5_valid⟩, (by simp)⟩⟩

noncomputable def patterns_5_4 : List (List (List ℕ)) := patterns_5_4_0 ++ ([])

theorem patterns_5_4_verified : ∀ D ∈ patterns_5_4, PatternVerified 5 4 D := by

  simp only [patterns_5_4, List.forall_mem_append]

  exact ⟨patterns_5_4_0_verified, by simp⟩

theorem patterns_5_4_coverage : patternChoices 4 1 [] = patterns_5_4 := by decide +kernel

theorem finite_patterns_5_4 : ∀ D ∈ patternChoices 4 (5-4) [], PatternVerified 5 4 D := by

  rw [patterns_5_4_coverage]

  exact patterns_5_4_verified

end CycleClique

end OAI
