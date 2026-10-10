import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CachedDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
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

noncomputable def patterns_8_8_0 : List (List (List ℕ)) := [[[],[],[],[],[],[],[],[]]]

theorem patterns_8_8_0_verified : ∀ D ∈ patterns_8_8_0, PatternVerified 8 8 D := by

  simp only [patterns_8_8_0, List.forall_mem_cons]

  exact ⟨⟨certificate_80, certificate_80_valid⟩, (by simp)⟩

noncomputable def patterns_8_8 : List (List (List ℕ)) := patterns_8_8_0 ++ ([])

theorem patterns_8_8_verified : ∀ D ∈ patterns_8_8, PatternVerified 8 8 D := by

  simp only [patterns_8_8, List.forall_mem_append]

  exact ⟨patterns_8_8_0_verified, by simp⟩

theorem patterns_8_8_coverage : patternChoices 8 0 [] = patterns_8_8 := by decide +kernel

theorem finite_patterns_8_8 : ∀ D ∈ patternChoices 8 (8-8) [], PatternVerified 8 8 D := by

  rw [patterns_8_8_coverage]

  exact patterns_8_8_verified

end CycleClique

end OAI
