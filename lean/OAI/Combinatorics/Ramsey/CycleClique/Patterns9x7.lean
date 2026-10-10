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

noncomputable def patterns_9_7_0 : List (List (List ℕ)) := [[[],[],[],[],[],[],[]],[[],[],[],[],[],[1]],[[],[],[],[],[],[2]],[[],[],[],[],[1,1]],[[],[],[],[1],[1]]]

theorem patterns_9_7_0_verified : ∀ D ∈ patterns_9_7_0, PatternVerified 9 7 D := by

  simp only [patterns_9_7_0, List.forall_mem_cons]

  exact ⟨⟨certificate_137, certificate_137_valid⟩, ⟨⟨certificate_138, certificate_138_valid⟩, ⟨⟨certificate_139, certificate_139_valid⟩, ⟨⟨certificate_140, certificate_140_valid⟩, ⟨⟨certificate_141, certificate_141_valid⟩, (by simp)⟩⟩⟩⟩⟩

noncomputable def patterns_9_7 : List (List (List ℕ)) := patterns_9_7_0 ++ ([])

theorem patterns_9_7_verified : ∀ D ∈ patterns_9_7, PatternVerified 9 7 D := by

  simp only [patterns_9_7, List.forall_mem_append]

  exact ⟨patterns_9_7_0_verified, by simp⟩

theorem patterns_9_7_coverage : patternChoices 7 2 [] = patterns_9_7 := by decide +kernel

theorem finite_patterns_9_7 : ∀ D ∈ patternChoices 7 (9-7) [], PatternVerified 9 7 D := by

  rw [patterns_9_7_coverage]

  exact patterns_9_7_verified

end CycleClique

end OAI
