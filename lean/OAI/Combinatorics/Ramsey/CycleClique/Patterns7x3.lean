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

noncomputable def patterns_7_3_0 : List (List (List ℕ)) := [[[],[],[]],[[],[1]],[[],[2]],[[],[3]],[[],[4]],[[1,1]],[[1,2]],[[1,3]],[[2,2]]]

theorem patterns_7_3_0_verified : ∀ D ∈ patterns_7_3_0, PatternVerified 7 3 D := by

  simp only [patterns_7_3_0, List.forall_mem_cons]

  exact ⟨⟨certificate_21, certificate_21_valid⟩, ⟨⟨certificate_22, certificate_22_valid⟩, ⟨⟨certificate_23, certificate_23_valid⟩, ⟨⟨certificate_24, certificate_24_valid⟩, ⟨⟨certificate_25, certificate_25_valid⟩, ⟨⟨certificate_26, certificate_26_valid⟩, ⟨⟨certificate_27, certificate_27_valid⟩, ⟨⟨certificate_28, certificate_28_valid⟩, ⟨⟨certificate_29, certificate_29_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_7_3 : List (List (List ℕ)) := patterns_7_3_0 ++ ([])

theorem patterns_7_3_verified : ∀ D ∈ patterns_7_3, PatternVerified 7 3 D := by

  simp only [patterns_7_3, List.forall_mem_append]

  exact ⟨patterns_7_3_0_verified, by simp⟩

theorem patterns_7_3_coverage : patternChoices 3 4 [] = patterns_7_3 := by decide +kernel

theorem finite_patterns_7_3 : ∀ D ∈ patternChoices 3 (7-3) [], PatternVerified 7 3 D := by

  rw [patterns_7_3_coverage]

  exact patterns_7_3_verified

end CycleClique

end OAI
