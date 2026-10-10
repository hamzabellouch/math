import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CachedDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.Certificates004
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

noncomputable def patterns_9_6_0 : List (List (List ℕ)) := [[[],[],[],[],[],[]],[[],[],[],[],[1]],[[],[],[],[],[2]],[[],[],[],[],[3]],[[],[],[],[1,1]],[[],[],[],[1,2]],[[],[],[1],[1]],[[],[],[1],[2]],[[],[],[1,1,1]],[[],[1],[1,1]],[[1],[1],[1]]]

theorem patterns_9_6_0_verified : ∀ D ∈ patterns_9_6_0, PatternVerified 9 6 D := by

  simp only [patterns_9_6_0, List.forall_mem_cons]

  exact ⟨⟨certificate_126, certificate_126_valid⟩, ⟨⟨certificate_127, certificate_127_valid⟩, ⟨⟨certificate_128, certificate_128_valid⟩, ⟨⟨certificate_129, certificate_129_valid⟩, ⟨⟨certificate_130, certificate_130_valid⟩, ⟨⟨certificate_131, certificate_131_valid⟩, ⟨⟨certificate_132, certificate_132_valid⟩, ⟨⟨certificate_133, certificate_133_valid⟩, ⟨⟨certificate_134, certificate_134_valid⟩, ⟨⟨certificate_135, certificate_135_valid⟩, ⟨⟨certificate_136, certificate_136_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_9_6 : List (List (List ℕ)) := patterns_9_6_0 ++ ([])

theorem patterns_9_6_verified : ∀ D ∈ patterns_9_6, PatternVerified 9 6 D := by

  simp only [patterns_9_6, List.forall_mem_append]

  exact ⟨patterns_9_6_0_verified, by simp⟩

theorem patterns_9_6_coverage : patternChoices 6 3 [] = patterns_9_6 := by decide +kernel

theorem finite_patterns_9_6 : ∀ D ∈ patternChoices 6 (9-6) [], PatternVerified 9 6 D := by

  rw [patterns_9_6_coverage]

  exact patterns_9_6_verified

end CycleClique

end OAI
