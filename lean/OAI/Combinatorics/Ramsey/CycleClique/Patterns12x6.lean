import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CachedDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.Certificates012
import OAI.Combinatorics.Ramsey.CycleClique.Certificates013
import OAI.Combinatorics.Ramsey.CycleClique.Certificates014
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

noncomputable def patterns_12_6_0 : List (List (List ℕ)) := [[[],[],[],[],[],[]],[[],[],[],[],[1]],[[],[],[],[],[2]],[[],[],[],[],[3]],[[],[],[],[],[4]],[[],[],[],[],[5]],[[],[],[],[],[6]],[[],[],[],[1,1]],[[],[],[],[1,2]],[[],[],[],[1,3]],[[],[],[],[1,4]],[[],[],[],[1,5]],[[],[],[],[2,2]],[[],[],[],[2,3]],[[],[],[],[2,4]],[[],[],[],[3,3]]]

theorem patterns_12_6_0_verified : ∀ D ∈ patterns_12_6_0, PatternVerified 12 6 D := by

  simp only [patterns_12_6_0, List.forall_mem_cons]

  exact ⟨⟨certificate_361, certificate_361_valid⟩, ⟨⟨certificate_362, certificate_362_valid⟩, ⟨⟨certificate_363, certificate_363_valid⟩, ⟨⟨certificate_364, certificate_364_valid⟩, ⟨⟨certificate_365, certificate_365_valid⟩, ⟨⟨certificate_366, certificate_366_valid⟩, ⟨⟨certificate_367, certificate_367_valid⟩, ⟨⟨certificate_368, certificate_368_valid⟩, ⟨⟨certificate_369, certificate_369_valid⟩, ⟨⟨certificate_370, certificate_370_valid⟩, ⟨⟨certificate_371, certificate_371_valid⟩, ⟨⟨certificate_372, certificate_372_valid⟩, ⟨⟨certificate_373, certificate_373_valid⟩, ⟨⟨certificate_374, certificate_374_valid⟩, ⟨⟨certificate_375, certificate_375_valid⟩, ⟨⟨certificate_376, certificate_376_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_12_6_1 : List (List (List ℕ)) := [[[],[],[1],[1]],[[],[],[1],[2]],[[],[],[1],[3]],[[],[],[1],[4]],[[],[],[1],[5]],[[],[],[1,1,1]],[[],[],[1,1,2]],[[],[],[1,1,3]],[[],[],[1,1,4]],[[],[],[1,2,1]],[[],[],[1,2,2]],[[],[],[1,2,3]],[[],[],[1,3,1]],[[],[],[1,3,2]],[[],[],[1,4,1]],[[],[],[2],[2]]]

theorem patterns_12_6_1_verified : ∀ D ∈ patterns_12_6_1, PatternVerified 12 6 D := by

  simp only [patterns_12_6_1, List.forall_mem_cons]

  exact ⟨⟨certificate_377, certificate_377_valid⟩, ⟨⟨certificate_378, certificate_378_valid⟩, ⟨⟨certificate_379, certificate_379_valid⟩, ⟨⟨certificate_380, certificate_380_valid⟩, ⟨⟨certificate_381, certificate_381_valid⟩, ⟨⟨certificate_382, certificate_382_valid⟩, ⟨⟨certificate_383, certificate_383_valid⟩, ⟨⟨certificate_384, certificate_384_valid⟩, ⟨⟨certificate_385, certificate_385_valid⟩, ⟨⟨certificate_386, certificate_386_valid⟩, ⟨⟨certificate_387, certificate_387_valid⟩, ⟨⟨certificate_388, certificate_388_valid⟩, ⟨⟨certificate_389, certificate_389_valid⟩, ⟨⟨certificate_390, certificate_390_valid⟩, ⟨⟨certificate_391, certificate_391_valid⟩, ⟨⟨certificate_392, certificate_392_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_12_6_2 : List (List (List ℕ)) := [[[],[],[2],[3]],[[],[],[2],[4]],[[],[],[2,1,2]],[[],[],[2,1,3]],[[],[],[2,2,2]],[[],[],[3],[3]],[[],[1],[1,1]],[[],[1],[1,2]],[[],[1],[1,3]],[[],[1],[1,4]],[[],[1],[2,2]],[[],[1],[2,3]],[[],[1,1],[2]],[[],[1,1],[3]],[[],[1,1],[4]],[[],[1,1,1,1]]]

theorem patterns_12_6_2_verified : ∀ D ∈ patterns_12_6_2, PatternVerified 12 6 D := by

  simp only [patterns_12_6_2, List.forall_mem_cons]

  exact ⟨⟨certificate_393, certificate_393_valid⟩, ⟨⟨certificate_394, certificate_394_valid⟩, ⟨⟨certificate_395, certificate_395_valid⟩, ⟨⟨certificate_396, certificate_396_valid⟩, ⟨⟨certificate_397, certificate_397_valid⟩, ⟨⟨certificate_398, certificate_398_valid⟩, ⟨⟨certificate_399, certificate_399_valid⟩, ⟨⟨certificate_400, certificate_400_valid⟩, ⟨⟨certificate_401, certificate_401_valid⟩, ⟨⟨certificate_402, certificate_402_valid⟩, ⟨⟨certificate_403, certificate_403_valid⟩, ⟨⟨certificate_404, certificate_404_valid⟩, ⟨⟨certificate_405, certificate_405_valid⟩, ⟨⟨certificate_406, certificate_406_valid⟩, ⟨⟨certificate_407, certificate_407_valid⟩, ⟨⟨certificate_408, certificate_408_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_12_6_3 : List (List (List ℕ)) := [[[],[1,1,1,2]],[[],[1,1,1,3]],[[],[1,1,2,1]],[[],[1,1,2,2]],[[],[1,1,3,1]],[[],[1,2],[2]],[[],[1,2],[3]],[[],[1,2,1,2]],[[],[1,2,2,1]],[[],[1,3],[2]],[[],[2],[2,2]],[[],[2,1,1,2]],[[1],[1],[1]],[[1],[1],[2]],[[1],[1],[3]],[[1],[1],[4]]]

theorem patterns_12_6_3_verified : ∀ D ∈ patterns_12_6_3, PatternVerified 12 6 D := by

  simp only [patterns_12_6_3, List.forall_mem_cons]

  exact ⟨⟨certificate_409, certificate_409_valid⟩, ⟨⟨certificate_410, certificate_410_valid⟩, ⟨⟨certificate_411, certificate_411_valid⟩, ⟨⟨certificate_412, certificate_412_valid⟩, ⟨⟨certificate_413, certificate_413_valid⟩, ⟨⟨certificate_414, certificate_414_valid⟩, ⟨⟨certificate_415, certificate_415_valid⟩, ⟨⟨certificate_416, certificate_416_valid⟩, ⟨⟨certificate_417, certificate_417_valid⟩, ⟨⟨certificate_418, certificate_418_valid⟩, ⟨⟨certificate_419, certificate_419_valid⟩, ⟨⟨certificate_420, certificate_420_valid⟩, ⟨⟨certificate_421, certificate_421_valid⟩, ⟨⟨certificate_422, certificate_422_valid⟩, ⟨⟨certificate_423, certificate_423_valid⟩, ⟨⟨certificate_424, certificate_424_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_12_6_4 : List (List (List ℕ)) := [[[1],[1,1,1]],[[1],[1,1,2]],[[1],[1,1,3]],[[1],[1,2,1]],[[1],[1,2,2]],[[1],[1,3,1]],[[1],[2],[2]],[[1],[2],[3]],[[1],[2,1,2]],[[1,1],[1,1]],[[1,1],[1,2]],[[1,1],[1,3]],[[1,1],[2,2]],[[1,1,1],[2]],[[1,1,1],[3]],[[1,1,1,1,1]]]

theorem patterns_12_6_4_verified : ∀ D ∈ patterns_12_6_4, PatternVerified 12 6 D := by

  simp only [patterns_12_6_4, List.forall_mem_cons]

  exact ⟨⟨certificate_425, certificate_425_valid⟩, ⟨⟨certificate_426, certificate_426_valid⟩, ⟨⟨certificate_427, certificate_427_valid⟩, ⟨⟨certificate_428, certificate_428_valid⟩, ⟨⟨certificate_429, certificate_429_valid⟩, ⟨⟨certificate_430, certificate_430_valid⟩, ⟨⟨certificate_431, certificate_431_valid⟩, ⟨⟨certificate_432, certificate_432_valid⟩, ⟨⟨certificate_433, certificate_433_valid⟩, ⟨⟨certificate_434, certificate_434_valid⟩, ⟨⟨certificate_435, certificate_435_valid⟩, ⟨⟨certificate_436, certificate_436_valid⟩, ⟨⟨certificate_437, certificate_437_valid⟩, ⟨⟨certificate_438, certificate_438_valid⟩, ⟨⟨certificate_439, certificate_439_valid⟩, ⟨⟨certificate_440, certificate_440_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_12_6_5 : List (List (List ℕ)) := [[[1,1,1,1,2]],[[1,1,1,2,1]],[[1,1,2],[2]],[[1,1,2,1,1]],[[1,2],[1,2]],[[1,2,1],[2]],[[2],[2],[2]]]

theorem patterns_12_6_5_verified : ∀ D ∈ patterns_12_6_5, PatternVerified 12 6 D := by

  simp only [patterns_12_6_5, List.forall_mem_cons]

  exact ⟨⟨certificate_441, certificate_441_valid⟩, ⟨⟨certificate_442, certificate_442_valid⟩, ⟨⟨certificate_443, certificate_443_valid⟩, ⟨⟨certificate_444, certificate_444_valid⟩, ⟨⟨certificate_445, certificate_445_valid⟩, ⟨⟨certificate_446, certificate_446_valid⟩, ⟨⟨certificate_447, certificate_447_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_12_6 : List (List (List ℕ)) := patterns_12_6_0 ++ (patterns_12_6_1 ++ (patterns_12_6_2 ++ (patterns_12_6_3 ++ (patterns_12_6_4 ++ (patterns_12_6_5 ++ ([]))))))

theorem patterns_12_6_verified : ∀ D ∈ patterns_12_6, PatternVerified 12 6 D := by

  simp only [patterns_12_6, List.forall_mem_append]

  exact ⟨patterns_12_6_0_verified, ⟨patterns_12_6_1_verified, ⟨patterns_12_6_2_verified, ⟨patterns_12_6_3_verified, ⟨patterns_12_6_4_verified, ⟨patterns_12_6_5_verified, by simp⟩⟩⟩⟩⟩⟩

theorem patterns_12_6_coverage : patternChoices 6 6 [] = patterns_12_6 := by decide +kernel

theorem finite_patterns_12_6 : ∀ D ∈ patternChoices 6 (12-6) [], PatternVerified 12 6 D := by

  rw [patterns_12_6_coverage]

  exact patterns_12_6_verified

end CycleClique

end OAI
