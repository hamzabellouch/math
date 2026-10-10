import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CachedDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.Certificates016
import OAI.Combinatorics.Ramsey.CycleClique.Certificates017
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

noncomputable def patterns_12_8_0 : List (List (List ℕ)) := [[[],[],[],[],[],[],[],[]],[[],[],[],[],[],[],[1]],[[],[],[],[],[],[],[2]],[[],[],[],[],[],[],[3]],[[],[],[],[],[],[],[4]],[[],[],[],[],[],[1,1]],[[],[],[],[],[],[1,2]],[[],[],[],[],[],[1,3]],[[],[],[],[],[],[2,2]],[[],[],[],[],[1],[1]],[[],[],[],[],[1],[2]],[[],[],[],[],[1],[3]],[[],[],[],[],[1,1,1]],[[],[],[],[],[1,1,2]],[[],[],[],[],[1,2,1]],[[],[],[],[],[2],[2]]]

theorem patterns_12_8_0_verified : ∀ D ∈ patterns_12_8_0, PatternVerified 12 8 D := by

  simp only [patterns_12_8_0, List.forall_mem_cons]

  exact ⟨⟨certificate_499, certificate_499_valid⟩, ⟨⟨certificate_500, certificate_500_valid⟩, ⟨⟨certificate_501, certificate_501_valid⟩, ⟨⟨certificate_502, certificate_502_valid⟩, ⟨⟨certificate_503, certificate_503_valid⟩, ⟨⟨certificate_504, certificate_504_valid⟩, ⟨⟨certificate_505, certificate_505_valid⟩, ⟨⟨certificate_506, certificate_506_valid⟩, ⟨⟨certificate_507, certificate_507_valid⟩, ⟨⟨certificate_508, certificate_508_valid⟩, ⟨⟨certificate_509, certificate_509_valid⟩, ⟨⟨certificate_510, certificate_510_valid⟩, ⟨⟨certificate_511, certificate_511_valid⟩, ⟨⟨certificate_512, certificate_512_valid⟩, ⟨⟨certificate_513, certificate_513_valid⟩, ⟨⟨certificate_514, certificate_514_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_12_8_1 : List (List (List ℕ)) := [[[],[],[],[1],[1,1]],[[],[],[],[1],[1,2]],[[],[],[],[1,1],[2]],[[],[],[],[1,1,1,1]],[[],[],[1],[1],[1]],[[],[],[1],[1],[2]],[[],[],[1],[1,1,1]],[[],[],[1,1],[1,1]],[[],[1],[1],[1,1]],[[1],[1],[1],[1]]]

theorem patterns_12_8_1_verified : ∀ D ∈ patterns_12_8_1, PatternVerified 12 8 D := by

  simp only [patterns_12_8_1, List.forall_mem_cons]

  exact ⟨⟨certificate_515, certificate_515_valid⟩, ⟨⟨certificate_516, certificate_516_valid⟩, ⟨⟨certificate_517, certificate_517_valid⟩, ⟨⟨certificate_518, certificate_518_valid⟩, ⟨⟨certificate_519, certificate_519_valid⟩, ⟨⟨certificate_520, certificate_520_valid⟩, ⟨⟨certificate_521, certificate_521_valid⟩, ⟨⟨certificate_522, certificate_522_valid⟩, ⟨⟨certificate_523, certificate_523_valid⟩, ⟨⟨certificate_524, certificate_524_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_12_8 : List (List (List ℕ)) := patterns_12_8_0 ++ (patterns_12_8_1 ++ ([]))

theorem patterns_12_8_verified : ∀ D ∈ patterns_12_8, PatternVerified 12 8 D := by

  simp only [patterns_12_8, List.forall_mem_append]

  exact ⟨patterns_12_8_0_verified, ⟨patterns_12_8_1_verified, by simp⟩⟩

theorem patterns_12_8_coverage : patternChoices 8 4 [] = patterns_12_8 := by decide +kernel

theorem finite_patterns_12_8 : ∀ D ∈ patternChoices 8 (12-8) [], PatternVerified 12 8 D := by

  rw [patterns_12_8_coverage]

  exact patterns_12_8_verified

end CycleClique

end OAI
