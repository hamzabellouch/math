import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CachedDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.Certificates009
import OAI.Combinatorics.Ramsey.CycleClique.Certificates010
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

noncomputable def patterns_11_6_0 : List (List (List ℕ)) := [[[],[],[],[],[],[]],[[],[],[],[],[1]],[[],[],[],[],[2]],[[],[],[],[],[3]],[[],[],[],[],[4]],[[],[],[],[],[5]],[[],[],[],[1,1]],[[],[],[],[1,2]],[[],[],[],[1,3]],[[],[],[],[1,4]],[[],[],[],[2,2]],[[],[],[],[2,3]],[[],[],[1],[1]],[[],[],[1],[2]],[[],[],[1],[3]],[[],[],[1],[4]]]

theorem patterns_11_6_0_verified : ∀ D ∈ patterns_11_6_0, PatternVerified 11 6 D := by

  simp only [patterns_11_6_0, List.forall_mem_cons]

  exact ⟨⟨certificate_279, certificate_279_valid⟩, ⟨⟨certificate_280, certificate_280_valid⟩, ⟨⟨certificate_281, certificate_281_valid⟩, ⟨⟨certificate_282, certificate_282_valid⟩, ⟨⟨certificate_283, certificate_283_valid⟩, ⟨⟨certificate_284, certificate_284_valid⟩, ⟨⟨certificate_285, certificate_285_valid⟩, ⟨⟨certificate_286, certificate_286_valid⟩, ⟨⟨certificate_287, certificate_287_valid⟩, ⟨⟨certificate_288, certificate_288_valid⟩, ⟨⟨certificate_289, certificate_289_valid⟩, ⟨⟨certificate_290, certificate_290_valid⟩, ⟨⟨certificate_291, certificate_291_valid⟩, ⟨⟨certificate_292, certificate_292_valid⟩, ⟨⟨certificate_293, certificate_293_valid⟩, ⟨⟨certificate_294, certificate_294_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_11_6_1 : List (List (List ℕ)) := [[[],[],[1,1,1]],[[],[],[1,1,2]],[[],[],[1,1,3]],[[],[],[1,2,1]],[[],[],[1,2,2]],[[],[],[1,3,1]],[[],[],[2],[2]],[[],[],[2],[3]],[[],[],[2,1,2]],[[],[1],[1,1]],[[],[1],[1,2]],[[],[1],[1,3]],[[],[1],[2,2]],[[],[1,1],[2]],[[],[1,1],[3]],[[],[1,1,1,1]]]

theorem patterns_11_6_1_verified : ∀ D ∈ patterns_11_6_1, PatternVerified 11 6 D := by

  simp only [patterns_11_6_1, List.forall_mem_cons]

  exact ⟨⟨certificate_295, certificate_295_valid⟩, ⟨⟨certificate_296, certificate_296_valid⟩, ⟨⟨certificate_297, certificate_297_valid⟩, ⟨⟨certificate_298, certificate_298_valid⟩, ⟨⟨certificate_299, certificate_299_valid⟩, ⟨⟨certificate_300, certificate_300_valid⟩, ⟨⟨certificate_301, certificate_301_valid⟩, ⟨⟨certificate_302, certificate_302_valid⟩, ⟨⟨certificate_303, certificate_303_valid⟩, ⟨⟨certificate_304, certificate_304_valid⟩, ⟨⟨certificate_305, certificate_305_valid⟩, ⟨⟨certificate_306, certificate_306_valid⟩, ⟨⟨certificate_307, certificate_307_valid⟩, ⟨⟨certificate_308, certificate_308_valid⟩, ⟨⟨certificate_309, certificate_309_valid⟩, ⟨⟨certificate_310, certificate_310_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_11_6_2 : List (List (List ℕ)) := [[[],[1,1,1,2]],[[],[1,1,2,1]],[[],[1,2],[2]],[[1],[1],[1]],[[1],[1],[2]],[[1],[1],[3]],[[1],[1,1,1]],[[1],[1,1,2]],[[1],[1,2,1]],[[1],[2],[2]],[[1,1],[1,1]],[[1,1],[1,2]],[[1,1,1],[2]],[[1,1,1,1,1]]]

theorem patterns_11_6_2_verified : ∀ D ∈ patterns_11_6_2, PatternVerified 11 6 D := by

  simp only [patterns_11_6_2, List.forall_mem_cons]

  exact ⟨⟨certificate_311, certificate_311_valid⟩, ⟨⟨certificate_312, certificate_312_valid⟩, ⟨⟨certificate_313, certificate_313_valid⟩, ⟨⟨certificate_314, certificate_314_valid⟩, ⟨⟨certificate_315, certificate_315_valid⟩, ⟨⟨certificate_316, certificate_316_valid⟩, ⟨⟨certificate_317, certificate_317_valid⟩, ⟨⟨certificate_318, certificate_318_valid⟩, ⟨⟨certificate_319, certificate_319_valid⟩, ⟨⟨certificate_320, certificate_320_valid⟩, ⟨⟨certificate_321, certificate_321_valid⟩, ⟨⟨certificate_322, certificate_322_valid⟩, ⟨⟨certificate_323, certificate_323_valid⟩, ⟨⟨certificate_324, certificate_324_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_11_6 : List (List (List ℕ)) := patterns_11_6_0 ++ (patterns_11_6_1 ++ (patterns_11_6_2 ++ ([])))

theorem patterns_11_6_verified : ∀ D ∈ patterns_11_6, PatternVerified 11 6 D := by

  simp only [patterns_11_6, List.forall_mem_append]

  exact ⟨patterns_11_6_0_verified, ⟨patterns_11_6_1_verified, ⟨patterns_11_6_2_verified, by simp⟩⟩⟩

theorem patterns_11_6_coverage : patternChoices 6 5 [] = patterns_11_6 := by decide +kernel

theorem finite_patterns_11_6 : ∀ D ∈ patternChoices 6 (11-6) [], PatternVerified 11 6 D := by

  rw [patterns_11_6_coverage]

  exact patterns_11_6_verified

end CycleClique

end OAI
