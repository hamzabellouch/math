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

noncomputable def patterns_7_5_0 : List (List (List ℕ)) := [[[],[],[],[],[]],[[],[],[],[1]],[[],[],[],[2]],[[],[],[1,1]],[[],[1],[1]]]

theorem patterns_7_5_0_verified : ∀ D ∈ patterns_7_5_0, PatternVerified 7 5 D := by

  simp only [patterns_7_5_0, List.forall_mem_cons]

  exact ⟨⟨certificate_39, certificate_39_valid⟩, ⟨⟨certificate_40, certificate_40_valid⟩, ⟨⟨certificate_41, certificate_41_valid⟩, ⟨⟨certificate_42, certificate_42_valid⟩, ⟨⟨certificate_43, certificate_43_valid⟩, (by simp)⟩⟩⟩⟩⟩

noncomputable def patterns_7_5 : List (List (List ℕ)) := patterns_7_5_0 ++ ([])

theorem patterns_7_5_verified : ∀ D ∈ patterns_7_5, PatternVerified 7 5 D := by

  simp only [patterns_7_5, List.forall_mem_append]

  exact ⟨patterns_7_5_0_verified, by simp⟩

theorem patterns_7_5_coverage : patternChoices 5 2 [] = patterns_7_5 := by decide +kernel

theorem finite_patterns_7_5 : ∀ D ∈ patternChoices 5 (7-5) [], PatternVerified 7 5 D := by

  rw [patterns_7_5_coverage]

  exact patterns_7_5_verified

end CycleClique

end OAI
