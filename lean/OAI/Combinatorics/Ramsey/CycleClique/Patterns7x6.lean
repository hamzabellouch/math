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

noncomputable def patterns_7_6_0 : List (List (List ℕ)) := [[[],[],[],[],[],[]],[[],[],[],[],[1]]]

theorem patterns_7_6_0_verified : ∀ D ∈ patterns_7_6_0, PatternVerified 7 6 D := by

  simp only [patterns_7_6_0, List.forall_mem_cons]

  exact ⟨⟨certificate_44, certificate_44_valid⟩, ⟨⟨certificate_45, certificate_45_valid⟩, (by simp)⟩⟩

noncomputable def patterns_7_6 : List (List (List ℕ)) := patterns_7_6_0 ++ ([])

theorem patterns_7_6_verified : ∀ D ∈ patterns_7_6, PatternVerified 7 6 D := by

  simp only [patterns_7_6, List.forall_mem_append]

  exact ⟨patterns_7_6_0_verified, by simp⟩

theorem patterns_7_6_coverage : patternChoices 6 1 [] = patterns_7_6 := by decide +kernel

theorem finite_patterns_7_6 : ∀ D ∈ patternChoices 6 (7-6) [], PatternVerified 7 6 D := by

  rw [patterns_7_6_coverage]

  exact patterns_7_6_verified

end CycleClique

end OAI
