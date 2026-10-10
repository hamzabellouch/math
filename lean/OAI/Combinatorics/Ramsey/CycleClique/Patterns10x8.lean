import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CachedDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.Certificates007
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

noncomputable def patterns_10_8_0 : List (List (List ℕ)) := [[[],[],[],[],[],[],[],[]],[[],[],[],[],[],[],[1]],[[],[],[],[],[],[],[2]],[[],[],[],[],[],[1,1]],[[],[],[],[],[1],[1]]]

theorem patterns_10_8_0_verified : ∀ D ∈ patterns_10_8_0, PatternVerified 10 8 D := by

  simp only [patterns_10_8_0, List.forall_mem_cons]

  exact ⟨⟨certificate_214, certificate_214_valid⟩, ⟨⟨certificate_215, certificate_215_valid⟩, ⟨⟨certificate_216, certificate_216_valid⟩, ⟨⟨certificate_217, certificate_217_valid⟩, ⟨⟨certificate_218, certificate_218_valid⟩, (by simp)⟩⟩⟩⟩⟩

noncomputable def patterns_10_8 : List (List (List ℕ)) := patterns_10_8_0 ++ ([])

theorem patterns_10_8_verified : ∀ D ∈ patterns_10_8, PatternVerified 10 8 D := by

  simp only [patterns_10_8, List.forall_mem_append]

  exact ⟨patterns_10_8_0_verified, by simp⟩

theorem patterns_10_8_coverage : patternChoices 8 2 [] = patterns_10_8 := by decide +kernel

theorem finite_patterns_10_8 : ∀ D ∈ patternChoices 8 (10-8) [], PatternVerified 10 8 D := by

  rw [patterns_10_8_coverage]

  exact patterns_10_8_verified

end CycleClique

end OAI
