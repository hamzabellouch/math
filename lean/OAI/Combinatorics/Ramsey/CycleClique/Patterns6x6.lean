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

noncomputable def patterns_6_6_0 : List (List (List ℕ)) := [[[],[],[],[],[],[]]]

theorem patterns_6_6_0_verified : ∀ D ∈ patterns_6_6_0, PatternVerified 6 6 D := by

  simp only [patterns_6_6_0, List.forall_mem_cons]

  exact ⟨⟨certificate_20, certificate_20_valid⟩, (by simp)⟩

noncomputable def patterns_6_6 : List (List (List ℕ)) := patterns_6_6_0 ++ ([])

theorem patterns_6_6_verified : ∀ D ∈ patterns_6_6, PatternVerified 6 6 D := by

  simp only [patterns_6_6, List.forall_mem_append]

  exact ⟨patterns_6_6_0_verified, by simp⟩

theorem patterns_6_6_coverage : patternChoices 6 0 [] = patterns_6_6 := by decide +kernel

theorem finite_patterns_6_6 : ∀ D ∈ patternChoices 6 (6-6) [], PatternVerified 6 6 D := by

  rw [patterns_6_6_coverage]

  exact patterns_6_6_verified

end CycleClique

end OAI
