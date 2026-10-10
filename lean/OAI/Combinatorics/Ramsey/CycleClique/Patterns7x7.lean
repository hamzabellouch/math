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

noncomputable def patterns_7_7_0 : List (List (List ℕ)) := [[[],[],[],[],[],[],[]]]

theorem patterns_7_7_0_verified : ∀ D ∈ patterns_7_7_0, PatternVerified 7 7 D := by

  simp only [patterns_7_7_0, List.forall_mem_cons]

  exact ⟨⟨certificate_46, certificate_46_valid⟩, (by simp)⟩

noncomputable def patterns_7_7 : List (List (List ℕ)) := patterns_7_7_0 ++ ([])

theorem patterns_7_7_verified : ∀ D ∈ patterns_7_7, PatternVerified 7 7 D := by

  simp only [patterns_7_7, List.forall_mem_append]

  exact ⟨patterns_7_7_0_verified, by simp⟩

theorem patterns_7_7_coverage : patternChoices 7 0 [] = patterns_7_7 := by decide +kernel

theorem finite_patterns_7_7 : ∀ D ∈ patternChoices 7 (7-7) [], PatternVerified 7 7 D := by

  rw [patterns_7_7_coverage]

  exact patterns_7_7_verified

end CycleClique

end OAI
