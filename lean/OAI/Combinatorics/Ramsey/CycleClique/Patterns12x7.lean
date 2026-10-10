import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CachedDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.Certificates015
import OAI.Combinatorics.Ramsey.CycleClique.Certificates016
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

noncomputable def patterns_12_7_0 : List (List (List ℕ)) := [[[],[],[],[],[],[],[]],[[],[],[],[],[],[1]],[[],[],[],[],[],[2]],[[],[],[],[],[],[3]],[[],[],[],[],[],[4]],[[],[],[],[],[],[5]],[[],[],[],[],[1,1]],[[],[],[],[],[1,2]],[[],[],[],[],[1,3]],[[],[],[],[],[1,4]],[[],[],[],[],[2,2]],[[],[],[],[],[2,3]],[[],[],[],[1],[1]],[[],[],[],[1],[2]],[[],[],[],[1],[3]],[[],[],[],[1],[4]]]

theorem patterns_12_7_0_verified : ∀ D ∈ patterns_12_7_0, PatternVerified 12 7 D := by

  simp only [patterns_12_7_0, List.forall_mem_cons]

  exact ⟨⟨certificate_448, certificate_448_valid⟩, ⟨⟨certificate_449, certificate_449_valid⟩, ⟨⟨certificate_450, certificate_450_valid⟩, ⟨⟨certificate_451, certificate_451_valid⟩, ⟨⟨certificate_452, certificate_452_valid⟩, ⟨⟨certificate_453, certificate_453_valid⟩, ⟨⟨certificate_454, certificate_454_valid⟩, ⟨⟨certificate_455, certificate_455_valid⟩, ⟨⟨certificate_456, certificate_456_valid⟩, ⟨⟨certificate_457, certificate_457_valid⟩, ⟨⟨certificate_458, certificate_458_valid⟩, ⟨⟨certificate_459, certificate_459_valid⟩, ⟨⟨certificate_460, certificate_460_valid⟩, ⟨⟨certificate_461, certificate_461_valid⟩, ⟨⟨certificate_462, certificate_462_valid⟩, ⟨⟨certificate_463, certificate_463_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_12_7_1 : List (List (List ℕ)) := [[[],[],[],[1,1,1]],[[],[],[],[1,1,2]],[[],[],[],[1,1,3]],[[],[],[],[1,2,1]],[[],[],[],[1,2,2]],[[],[],[],[1,3,1]],[[],[],[],[2],[2]],[[],[],[],[2],[3]],[[],[],[],[2,1,2]],[[],[],[1],[1,1]],[[],[],[1],[1,2]],[[],[],[1],[1,3]],[[],[],[1],[2,2]],[[],[],[1,1],[2]],[[],[],[1,1],[3]],[[],[],[1,1,1,1]]]

theorem patterns_12_7_1_verified : ∀ D ∈ patterns_12_7_1, PatternVerified 12 7 D := by

  simp only [patterns_12_7_1, List.forall_mem_cons]

  exact ⟨⟨certificate_464, certificate_464_valid⟩, ⟨⟨certificate_465, certificate_465_valid⟩, ⟨⟨certificate_466, certificate_466_valid⟩, ⟨⟨certificate_467, certificate_467_valid⟩, ⟨⟨certificate_468, certificate_468_valid⟩, ⟨⟨certificate_469, certificate_469_valid⟩, ⟨⟨certificate_470, certificate_470_valid⟩, ⟨⟨certificate_471, certificate_471_valid⟩, ⟨⟨certificate_472, certificate_472_valid⟩, ⟨⟨certificate_473, certificate_473_valid⟩, ⟨⟨certificate_474, certificate_474_valid⟩, ⟨⟨certificate_475, certificate_475_valid⟩, ⟨⟨certificate_476, certificate_476_valid⟩, ⟨⟨certificate_477, certificate_477_valid⟩, ⟨⟨certificate_478, certificate_478_valid⟩, ⟨⟨certificate_479, certificate_479_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_12_7_2 : List (List (List ℕ)) := [[[],[],[1,1,1,2]],[[],[],[1,1,2,1]],[[],[],[1,2],[2]],[[],[1],[1],[1]],[[],[1],[1],[2]],[[],[1],[1],[3]],[[],[1],[1,1,1]],[[],[1],[1,1,2]],[[],[1],[1,2,1]],[[],[1],[2],[2]],[[],[1,1],[1,1]],[[],[1,1],[1,2]],[[],[1,1,1],[2]],[[],[1,1,1,1,1]],[[1],[1],[1,1]],[[1],[1],[1,2]]]

theorem patterns_12_7_2_verified : ∀ D ∈ patterns_12_7_2, PatternVerified 12 7 D := by

  simp only [patterns_12_7_2, List.forall_mem_cons]

  exact ⟨⟨certificate_480, certificate_480_valid⟩, ⟨⟨certificate_481, certificate_481_valid⟩, ⟨⟨certificate_482, certificate_482_valid⟩, ⟨⟨certificate_483, certificate_483_valid⟩, ⟨⟨certificate_484, certificate_484_valid⟩, ⟨⟨certificate_485, certificate_485_valid⟩, ⟨⟨certificate_486, certificate_486_valid⟩, ⟨⟨certificate_487, certificate_487_valid⟩, ⟨⟨certificate_488, certificate_488_valid⟩, ⟨⟨certificate_489, certificate_489_valid⟩, ⟨⟨certificate_490, certificate_490_valid⟩, ⟨⟨certificate_491, certificate_491_valid⟩, ⟨⟨certificate_492, certificate_492_valid⟩, ⟨⟨certificate_493, certificate_493_valid⟩, ⟨⟨certificate_494, certificate_494_valid⟩, ⟨⟨certificate_495, certificate_495_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_12_7_3 : List (List (List ℕ)) := [[[1],[1,1],[2]],[[1],[1,1,1,1]],[[1,1],[1,1,1]]]

theorem patterns_12_7_3_verified : ∀ D ∈ patterns_12_7_3, PatternVerified 12 7 D := by

  simp only [patterns_12_7_3, List.forall_mem_cons]

  exact ⟨⟨certificate_496, certificate_496_valid⟩, ⟨⟨certificate_497, certificate_497_valid⟩, ⟨⟨certificate_498, certificate_498_valid⟩, (by simp)⟩⟩⟩

noncomputable def patterns_12_7 : List (List (List ℕ)) := patterns_12_7_0 ++ (patterns_12_7_1 ++ (patterns_12_7_2 ++ (patterns_12_7_3 ++ ([]))))

theorem patterns_12_7_verified : ∀ D ∈ patterns_12_7, PatternVerified 12 7 D := by

  simp only [patterns_12_7, List.forall_mem_append]

  exact ⟨patterns_12_7_0_verified, ⟨patterns_12_7_1_verified, ⟨patterns_12_7_2_verified, ⟨patterns_12_7_3_verified, by simp⟩⟩⟩⟩

theorem patterns_12_7_coverage : patternChoices 7 5 [] = patterns_12_7 := by decide +kernel

theorem finite_patterns_12_7 : ∀ D ∈ patternChoices 7 (12-7) [], PatternVerified 12 7 D := by

  rw [patterns_12_7_coverage]

  exact patterns_12_7_verified

end CycleClique

end OAI
