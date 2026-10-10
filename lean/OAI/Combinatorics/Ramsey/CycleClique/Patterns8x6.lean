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

noncomputable def patterns_8_6_0 : List (List (List ℕ)) := [[[],[],[],[],[],[]],[[],[],[],[],[1]],[[],[],[],[],[2]],[[],[],[],[1,1]],[[],[],[1],[1]]]

theorem patterns_8_6_0_verified : ∀ D ∈ patterns_8_6_0, PatternVerified 8 6 D := by

  simp only [patterns_8_6_0, List.forall_mem_cons]

  exact ⟨⟨certificate_73, certificate_73_valid⟩, ⟨⟨certificate_74, certificate_74_valid⟩, ⟨⟨certificate_75, certificate_75_valid⟩, ⟨⟨certificate_76, certificate_76_valid⟩, ⟨⟨certificate_77, certificate_77_valid⟩, (by simp)⟩⟩⟩⟩⟩

noncomputable def patterns_8_6 : List (List (List ℕ)) := patterns_8_6_0 ++ ([])

theorem patterns_8_6_verified : ∀ D ∈ patterns_8_6, PatternVerified 8 6 D := by

  simp only [patterns_8_6, List.forall_mem_append]

  exact ⟨patterns_8_6_0_verified, by simp⟩

theorem patterns_8_6_coverage : patternChoices 6 2 [] = patterns_8_6 := by decide +kernel

theorem finite_patterns_8_6 : ∀ D ∈ patternChoices 6 (8-6) [], PatternVerified 8 6 D := by

  rw [patterns_8_6_coverage]

  exact patterns_8_6_verified

end CycleClique

end OAI
