import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CachedDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.Certificates005
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

noncomputable def patterns_9_8_0 : List (List (List ℕ)) := [[[],[],[],[],[],[],[],[]],[[],[],[],[],[],[],[1]]]

theorem patterns_9_8_0_verified : ∀ D ∈ patterns_9_8_0, PatternVerified 9 8 D := by

  simp only [patterns_9_8_0, List.forall_mem_cons]

  exact ⟨⟨certificate_142, certificate_142_valid⟩, ⟨⟨certificate_143, certificate_143_valid⟩, (by simp)⟩⟩

noncomputable def patterns_9_8 : List (List (List ℕ)) := patterns_9_8_0 ++ ([])

theorem patterns_9_8_verified : ∀ D ∈ patterns_9_8, PatternVerified 9 8 D := by

  simp only [patterns_9_8, List.forall_mem_append]

  exact ⟨patterns_9_8_0_verified, by simp⟩

theorem patterns_9_8_coverage : patternChoices 8 1 [] = patterns_9_8 := by decide +kernel

theorem finite_patterns_9_8 : ∀ D ∈ patternChoices 8 (9-8) [], PatternVerified 9 8 D := by

  rw [patterns_9_8_coverage]

  exact patterns_9_8_verified

end CycleClique

end OAI
