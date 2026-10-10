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

noncomputable def patterns_8_7_0 : List (List (List ℕ)) := [[[],[],[],[],[],[],[]],[[],[],[],[],[],[1]]]

theorem patterns_8_7_0_verified : ∀ D ∈ patterns_8_7_0, PatternVerified 8 7 D := by

  simp only [patterns_8_7_0, List.forall_mem_cons]

  exact ⟨⟨certificate_78, certificate_78_valid⟩, ⟨⟨certificate_79, certificate_79_valid⟩, (by simp)⟩⟩

noncomputable def patterns_8_7 : List (List (List ℕ)) := patterns_8_7_0 ++ ([])

theorem patterns_8_7_verified : ∀ D ∈ patterns_8_7, PatternVerified 8 7 D := by

  simp only [patterns_8_7, List.forall_mem_append]

  exact ⟨patterns_8_7_0_verified, by simp⟩

theorem patterns_8_7_coverage : patternChoices 7 1 [] = patterns_8_7 := by decide +kernel

theorem finite_patterns_8_7 : ∀ D ∈ patternChoices 7 (8-7) [], PatternVerified 8 7 D := by

  rw [patterns_8_7_coverage]

  exact patterns_8_7_verified

end CycleClique

end OAI
