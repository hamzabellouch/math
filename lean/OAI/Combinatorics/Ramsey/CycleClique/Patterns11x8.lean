import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CachedDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.Certificates011
import OAI.Combinatorics.Ramsey.CycleClique.Certificates012
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

noncomputable def patterns_11_8_0 : List (List (List ℕ)) := [[[],[],[],[],[],[],[],[]],[[],[],[],[],[],[],[1]],[[],[],[],[],[],[],[2]],[[],[],[],[],[],[],[3]],[[],[],[],[],[],[1,1]],[[],[],[],[],[],[1,2]],[[],[],[],[],[1],[1]],[[],[],[],[],[1],[2]],[[],[],[],[],[1,1,1]],[[],[],[],[1],[1,1]],[[],[],[1],[1],[1]]]

theorem patterns_11_8_0_verified : ∀ D ∈ patterns_11_8_0, PatternVerified 11 8 D := by

  simp only [patterns_11_8_0, List.forall_mem_cons]

  exact ⟨⟨certificate_350, certificate_350_valid⟩, ⟨⟨certificate_351, certificate_351_valid⟩, ⟨⟨certificate_352, certificate_352_valid⟩, ⟨⟨certificate_353, certificate_353_valid⟩, ⟨⟨certificate_354, certificate_354_valid⟩, ⟨⟨certificate_355, certificate_355_valid⟩, ⟨⟨certificate_356, certificate_356_valid⟩, ⟨⟨certificate_357, certificate_357_valid⟩, ⟨⟨certificate_358, certificate_358_valid⟩, ⟨⟨certificate_359, certificate_359_valid⟩, ⟨⟨certificate_360, certificate_360_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_11_8 : List (List (List ℕ)) := patterns_11_8_0 ++ ([])

theorem patterns_11_8_verified : ∀ D ∈ patterns_11_8, PatternVerified 11 8 D := by

  simp only [patterns_11_8, List.forall_mem_append]

  exact ⟨patterns_11_8_0_verified, by simp⟩

theorem patterns_11_8_coverage : patternChoices 8 3 [] = patterns_11_8 := by decide +kernel

theorem finite_patterns_11_8 : ∀ D ∈ patternChoices 8 (11-8) [], PatternVerified 11 8 D := by

  rw [patterns_11_8_coverage]

  exact patterns_11_8_verified

end CycleClique

end OAI
