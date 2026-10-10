import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CachedDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.Certificates011
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

noncomputable def patterns_11_7_0 : List (List (List ℕ)) := [[[],[],[],[],[],[],[]],[[],[],[],[],[],[1]],[[],[],[],[],[],[2]],[[],[],[],[],[],[3]],[[],[],[],[],[],[4]],[[],[],[],[],[1,1]],[[],[],[],[],[1,2]],[[],[],[],[],[1,3]],[[],[],[],[],[2,2]],[[],[],[],[1],[1]],[[],[],[],[1],[2]],[[],[],[],[1],[3]],[[],[],[],[1,1,1]],[[],[],[],[1,1,2]],[[],[],[],[1,2,1]],[[],[],[],[2],[2]]]

theorem patterns_11_7_0_verified : ∀ D ∈ patterns_11_7_0, PatternVerified 11 7 D := by

  simp only [patterns_11_7_0, List.forall_mem_cons]

  exact ⟨⟨certificate_325, certificate_325_valid⟩, ⟨⟨certificate_326, certificate_326_valid⟩, ⟨⟨certificate_327, certificate_327_valid⟩, ⟨⟨certificate_328, certificate_328_valid⟩, ⟨⟨certificate_329, certificate_329_valid⟩, ⟨⟨certificate_330, certificate_330_valid⟩, ⟨⟨certificate_331, certificate_331_valid⟩, ⟨⟨certificate_332, certificate_332_valid⟩, ⟨⟨certificate_333, certificate_333_valid⟩, ⟨⟨certificate_334, certificate_334_valid⟩, ⟨⟨certificate_335, certificate_335_valid⟩, ⟨⟨certificate_336, certificate_336_valid⟩, ⟨⟨certificate_337, certificate_337_valid⟩, ⟨⟨certificate_338, certificate_338_valid⟩, ⟨⟨certificate_339, certificate_339_valid⟩, ⟨⟨certificate_340, certificate_340_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_11_7_1 : List (List (List ℕ)) := [[[],[],[1],[1,1]],[[],[],[1],[1,2]],[[],[],[1,1],[2]],[[],[],[1,1,1,1]],[[],[1],[1],[1]],[[],[1],[1],[2]],[[],[1],[1,1,1]],[[],[1,1],[1,1]],[[1],[1],[1,1]]]

theorem patterns_11_7_1_verified : ∀ D ∈ patterns_11_7_1, PatternVerified 11 7 D := by

  simp only [patterns_11_7_1, List.forall_mem_cons]

  exact ⟨⟨certificate_341, certificate_341_valid⟩, ⟨⟨certificate_342, certificate_342_valid⟩, ⟨⟨certificate_343, certificate_343_valid⟩, ⟨⟨certificate_344, certificate_344_valid⟩, ⟨⟨certificate_345, certificate_345_valid⟩, ⟨⟨certificate_346, certificate_346_valid⟩, ⟨⟨certificate_347, certificate_347_valid⟩, ⟨⟨certificate_348, certificate_348_valid⟩, ⟨⟨certificate_349, certificate_349_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_11_7 : List (List (List ℕ)) := patterns_11_7_0 ++ (patterns_11_7_1 ++ ([]))

theorem patterns_11_7_verified : ∀ D ∈ patterns_11_7, PatternVerified 11 7 D := by

  simp only [patterns_11_7, List.forall_mem_append]

  exact ⟨patterns_11_7_0_verified, ⟨patterns_11_7_1_verified, by simp⟩⟩

theorem patterns_11_7_coverage : patternChoices 7 4 [] = patterns_11_7 := by decide +kernel

theorem finite_patterns_11_7 : ∀ D ∈ patternChoices 7 (11-7) [], PatternVerified 11 7 D := by

  rw [patterns_11_7_coverage]

  exact patterns_11_7_verified

end CycleClique

end OAI
