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

noncomputable def patterns_6_5_0 : List (List (List ℕ)) := [[[],[],[],[],[]],[[],[],[],[1]]]

theorem patterns_6_5_0_verified : ∀ D ∈ patterns_6_5_0, PatternVerified 6 5 D := by

  simp only [patterns_6_5_0, List.forall_mem_cons]

  exact ⟨⟨certificate_18, certificate_18_valid⟩, ⟨⟨certificate_19, certificate_19_valid⟩, (by simp)⟩⟩

noncomputable def patterns_6_5 : List (List (List ℕ)) := patterns_6_5_0 ++ ([])

theorem patterns_6_5_verified : ∀ D ∈ patterns_6_5, PatternVerified 6 5 D := by

  simp only [patterns_6_5, List.forall_mem_append]

  exact ⟨patterns_6_5_0_verified, by simp⟩

theorem patterns_6_5_coverage : patternChoices 5 1 [] = patterns_6_5 := by decide +kernel

theorem finite_patterns_6_5 : ∀ D ∈ patternChoices 5 (6-5) [], PatternVerified 6 5 D := by

  rw [patterns_6_5_coverage]

  exact patterns_6_5_verified

end CycleClique

end OAI
