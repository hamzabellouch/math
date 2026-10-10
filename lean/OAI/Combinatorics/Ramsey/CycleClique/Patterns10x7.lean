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

noncomputable def patterns_10_7_0 : List (List (List ℕ)) := [[[],[],[],[],[],[],[]],[[],[],[],[],[],[1]],[[],[],[],[],[],[2]],[[],[],[],[],[],[3]],[[],[],[],[],[1,1]],[[],[],[],[],[1,2]],[[],[],[],[1],[1]],[[],[],[],[1],[2]],[[],[],[],[1,1,1]],[[],[],[1],[1,1]],[[],[1],[1],[1]]]

theorem patterns_10_7_0_verified : ∀ D ∈ patterns_10_7_0, PatternVerified 10 7 D := by

  simp only [patterns_10_7_0, List.forall_mem_cons]

  exact ⟨⟨certificate_203, certificate_203_valid⟩, ⟨⟨certificate_204, certificate_204_valid⟩, ⟨⟨certificate_205, certificate_205_valid⟩, ⟨⟨certificate_206, certificate_206_valid⟩, ⟨⟨certificate_207, certificate_207_valid⟩, ⟨⟨certificate_208, certificate_208_valid⟩, ⟨⟨certificate_209, certificate_209_valid⟩, ⟨⟨certificate_210, certificate_210_valid⟩, ⟨⟨certificate_211, certificate_211_valid⟩, ⟨⟨certificate_212, certificate_212_valid⟩, ⟨⟨certificate_213, certificate_213_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_10_7 : List (List (List ℕ)) := patterns_10_7_0 ++ ([])

theorem patterns_10_7_verified : ∀ D ∈ patterns_10_7, PatternVerified 10 7 D := by

  simp only [patterns_10_7, List.forall_mem_append]

  exact ⟨patterns_10_7_0_verified, by simp⟩

theorem patterns_10_7_coverage : patternChoices 7 3 [] = patterns_10_7 := by decide +kernel

theorem finite_patterns_10_7 : ∀ D ∈ patternChoices 7 (10-7) [], PatternVerified 10 7 D := by

  rw [patterns_10_7_coverage]

  exact patterns_10_7_verified

end CycleClique

end OAI
