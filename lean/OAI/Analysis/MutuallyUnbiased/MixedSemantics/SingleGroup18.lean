import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleRules
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical160
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical240
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical241
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound8

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue296 : Sparse (Fin 909) := [(0, (17 / 864)), (1, (-5 / 216)), (2, (-25 / 288)), (3, (-10 / 27)), (4, (-5 / 54)), (5, (5 / 216)), (6, (5 / 216)), (7, (-5 / 27)), (8, (-5 / 54)), (9, (-5 / 108)), (12, (-5 / 54)), (13, (-5 / 54)), (26, (-5 / 54)), (27, (5 / 72)), (33, (5 / 18)), (35, (-5 / 27)), (51, (5 / 18)), (52, (-5 / 27)), (59, (5 / 18)), (68, (5 / 36)), (81, (5 / 18)), (256, (5 / 18)), (486, (-5 / 9))]

theorem singlePair296 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node296 node296Labels = Sparse.eval singlePairValue296 (familyPairVector B) := by
  have hp := single_label_three B hB node296
  have hl : node296Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node296 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node296 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node296 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node296 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node296 (EqualityPatterns.family3.label 1) = PairSemantics.raw5130 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node296 PairSemantics.raw5130; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5130 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node296 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node296 (EqualityPatterns.family3.label 2) = PairSemantics.raw7697 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node296 PairSemantics.raw7697; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7697 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node296 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value382 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node296 (EqualityPatterns.family3.label 3) = PairSemantics.raw855 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node296 PairSemantics.raw855; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical855 hH).trans (PairSemantics.sound382 hH)
  have hm4 : familyPairMoment B (groupedColumns node296 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1851 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node296 (EqualityPatterns.family3.label 4) = PairSemantics.raw622 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node296 PairSemantics.raw622; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical622 hH).trans (PairSemantics.sound1851 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue296, PairSemantics.value0, PairSemantics.value46, PairSemantics.value232, PairSemantics.value382, PairSemantics.value1851, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue297 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 432)), (2, (-5 / 144)), (3, (-25 / 54)), (6, (5 / 216)), (7, (-5 / 18)), (9, (-5 / 108)), (12, (-5 / 54)), (13, (-5 / 54)), (23, (5 / 18)), (25, (5 / 18)), (26, (-5 / 54)), (27, (5 / 72)), (35, (-5 / 54)), (51, (5 / 9)), (52, (-5 / 54)), (54, (5 / 9)), (64, (5 / 9)), (68, (5 / 36)), (123, (5 / 18)), (124, (5 / 18)), (125, (5 / 18)), (259, (5 / 18)), (260, (5 / 18))]

theorem singlePair297 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node297 node297Labels = Sparse.eval singlePairValue297 (familyPairVector B) := by
  have hp := single_label_three B hB node297
  have hl : node297Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node297 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node297 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node297 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node297 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node297 (EqualityPatterns.family3.label 1) = PairSemantics.raw5134 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node297 PairSemantics.raw5134; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5134 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node297 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node297 (EqualityPatterns.family3.label 2) = PairSemantics.raw7694 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node297 PairSemantics.raw7694; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7694 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node297 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value382 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node297 (EqualityPatterns.family3.label 3) = PairSemantics.raw855 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node297 PairSemantics.raw855; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical855 hH).trans (PairSemantics.sound382 hH)
  have hm4 : familyPairMoment B (groupedColumns node297 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1852 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node297 (EqualityPatterns.family3.label 4) = PairSemantics.raw623 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node297 PairSemantics.raw623; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical623 hH).trans (PairSemantics.sound1852 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue297, PairSemantics.value0, PairSemantics.value46, PairSemantics.value382, PairSemantics.value1852, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue298 : Sparse (Fin 909) := [(0, (5 / 288)), (1, (5 / 432)), (2, (-35 / 864)), (3, (-5 / 27)), (5, (-5 / 216)), (6, (5 / 216)), (9, (-5 / 108)), (12, (-5 / 54)), (13, (-5 / 54)), (31, (5 / 18)), (33, (5 / 18)), (51, (5 / 9)), (52, (-5 / 54)), (59, (5 / 18)), (68, (5 / 36)), (123, (5 / 18)), (124, (5 / 18)), (126, (5 / 18)), (259, (5 / 18)), (262, (5 / 18))]

theorem singlePair298 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node298 node298Labels = Sparse.eval singlePairValue298 (familyPairVector B) := by
  have hp := single_label_three B hB node298
  have hl : node298Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node298 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node298 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node298 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node298 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node298 (EqualityPatterns.family3.label 1) = PairSemantics.raw5138 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node298 PairSemantics.raw5138; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5138 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node298 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node298 (EqualityPatterns.family3.label 2) = PairSemantics.raw7692 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node298 PairSemantics.raw7692; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7692 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node298 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value382 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node298 (EqualityPatterns.family3.label 3) = PairSemantics.raw855 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node298 PairSemantics.raw855; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical855 hH).trans (PairSemantics.sound382 hH)
  have hm4 : familyPairMoment B (groupedColumns node298 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1855 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node298 (EqualityPatterns.family3.label 4) = PairSemantics.raw624 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node298 PairSemantics.raw624; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical624 hH).trans (PairSemantics.sound1855 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue298, PairSemantics.value0, PairSemantics.value46, PairSemantics.value232, PairSemantics.value382, PairSemantics.value1855, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue299 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (5 / 48)), (2, (-25 / 432)), (3, (-10 / 27)), (5, (5 / 27)), (6, (-5 / 216)), (12, (-5 / 54)), (13, (-10 / 27)), (52, (-10 / 27)), (128, (-5 / 54))]

theorem singlePair299 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node299 node299Labels = Sparse.eval singlePairValue299 (familyPairVector B) := by
  have hp := single_label_three B hB node299
  have hl : node299Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node299 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node299 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node299 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node299 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node299 (EqualityPatterns.family3.label 1) = PairSemantics.raw5138 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node299 PairSemantics.raw5138; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5138 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node299 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node299 (EqualityPatterns.family3.label 2) = PairSemantics.raw7696 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node299 PairSemantics.raw7696; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7696 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node299 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node299 (EqualityPatterns.family3.label 3) = PairSemantics.raw857 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node299 PairSemantics.raw857; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical857 hH).trans (PairSemantics.sound24 hH)
  have hm4 : familyPairMoment B (groupedColumns node299 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1854 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node299 (EqualityPatterns.family3.label 4) = PairSemantics.raw625 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node299 PairSemantics.raw625; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical625 hH).trans (PairSemantics.sound1854 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue299, PairSemantics.value0, PairSemantics.value24, PairSemantics.value232, PairSemantics.value1854, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue300 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (65 / 864)), (2, (-65 / 432)), (3, (-5 / 9)), (5, (5 / 54)), (7, (-10 / 27)), (8, (-10 / 27)), (12, (-5 / 54)), (13, (-5 / 54)), (26, (-5 / 54)), (33, (5 / 18)), (35, (-5 / 54)), (51, (5 / 9)), (59, (5 / 18))]

theorem singlePair300 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node300 node300Labels = Sparse.eval singlePairValue300 (familyPairVector B) := by
  have hp := single_label_three B hB node300
  have hl : node300Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node300 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node300 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node300 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node300 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node300 (EqualityPatterns.family3.label 1) = PairSemantics.raw5138 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node300 PairSemantics.raw5138; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5138 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node300 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node300 (EqualityPatterns.family3.label 2) = PairSemantics.raw7697 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node300 PairSemantics.raw7697; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7697 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node300 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node300 (EqualityPatterns.family3.label 3) = PairSemantics.raw858 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node300 PairSemantics.raw858; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical858 hH).trans (PairSemantics.sound25 hH)
  have hm4 : familyPairMoment B (groupedColumns node300 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1856 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node300 (EqualityPatterns.family3.label 4) = PairSemantics.raw626 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node300 PairSemantics.raw626; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical626 hH).trans (PairSemantics.sound1856 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue300, PairSemantics.value0, PairSemantics.value25, PairSemantics.value232, PairSemantics.value1856, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue301 : Sparse (Fin 909) := [(0, (37 / 864)), (1, (-5 / 864)), (2, (5 / 54)), (3, (-10 / 27)), (5, (25 / 216)), (6, (-5 / 216)), (7, (-5 / 27)), (26, (-5 / 27)), (35, (-5 / 54))]

theorem singlePair301 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node301 node301Labels = Sparse.eval singlePairValue301 (familyPairVector B) := by
  have hp := single_label_three B hB node301
  have hl : node301Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node301 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node301 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node301 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node301 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node301 (EqualityPatterns.family3.label 1) = PairSemantics.raw5134 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node301 PairSemantics.raw5134; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5134 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node301 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node301 (EqualityPatterns.family3.label 2) = PairSemantics.raw7704 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node301 PairSemantics.raw7704; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7704 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node301 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node301 (EqualityPatterns.family3.label 3) = PairSemantics.raw859 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node301 PairSemantics.raw859; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical859 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node301 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2467 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node301 (EqualityPatterns.family3.label 4) = PairSemantics.raw627 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node301 PairSemantics.raw627; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical627 hH).trans (PairSemantics.sound2467 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue301, PairSemantics.value0, PairSemantics.value46, PairSemantics.value65, PairSemantics.value118, PairSemantics.value2467, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue302 : Sparse (Fin 909) := [(0, (23 / 864)), (1, (5 / 48)), (2, (-35 / 432)), (3, (-5 / 27)), (5, (5 / 36)), (6, (-5 / 288)), (8, (-5 / 27)), (52, (-5 / 54))]

theorem singlePair302 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node302 node302Labels = Sparse.eval singlePairValue302 (familyPairVector B) := by
  have hp := single_label_three B hB node302
  have hl : node302Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node302 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node302 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node302 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node302 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node302 (EqualityPatterns.family3.label 1) = PairSemantics.raw5135 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node302 PairSemantics.raw5135; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5135 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node302 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node302 (EqualityPatterns.family3.label 2) = PairSemantics.raw7702 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node302 PairSemantics.raw7702; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7702 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node302 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node302 (EqualityPatterns.family3.label 3) = PairSemantics.raw859 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node302 PairSemantics.raw859; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical859 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node302 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2466 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node302 (EqualityPatterns.family3.label 4) = PairSemantics.raw628 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node302 PairSemantics.raw628; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical628 hH).trans (PairSemantics.sound2466 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue302, PairSemantics.value0, PairSemantics.value65, PairSemantics.value118, PairSemantics.value232, PairSemantics.value2466, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue303 : Sparse (Fin 909) := [(0, (17 / 432)), (1, (-5 / 216)), (2, (-5 / 144)), (5, (-5 / 108)), (6, (5 / 216))]

theorem singlePair303 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node303 node303Labels = Sparse.eval singlePairValue303 (familyPairVector B) := by
  have hp := single_label_three B hB node303
  have hl : node303Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node303 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node303 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node303 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node303 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node303 (EqualityPatterns.family3.label 1) = PairSemantics.raw5136 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node303 PairSemantics.raw5136; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5136 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node303 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node303 (EqualityPatterns.family3.label 2) = PairSemantics.raw7703 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node303 PairSemantics.raw7703; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7703 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node303 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node303 (EqualityPatterns.family3.label 3) = PairSemantics.raw860 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node303 PairSemantics.raw860; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical860 hH).trans (PairSemantics.sound24 hH)
  have hm4 : familyPairMoment B (groupedColumns node303 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value862 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node303 (EqualityPatterns.family3.label 4) = PairSemantics.raw629 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node303 PairSemantics.raw629; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical629 hH).trans (PairSemantics.sound862 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue303, PairSemantics.value0, PairSemantics.value24, PairSemantics.value46, PairSemantics.value65, PairSemantics.value862, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue304 : Sparse (Fin 909) := [(0, (19 / 864)), (1, (5 / 144)), (2, (-5 / 96)), (3, (-5 / 18)), (4, (-5 / 27)), (5, (5 / 54)), (6, (-5 / 432)), (7, (-5 / 27)), (26, (-5 / 27)), (35, (-5 / 27)), (52, (-5 / 27))]

theorem singlePair304 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node304 node304Labels = Sparse.eval singlePairValue304 (familyPairVector B) := by
  have hp := single_label_three B hB node304
  have hl : node304Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node304 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node304 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node304 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node304 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node304 (EqualityPatterns.family3.label 1) = PairSemantics.raw5140 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node304 PairSemantics.raw5140; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5140 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node304 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node304 (EqualityPatterns.family3.label 2) = PairSemantics.raw7698 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node304 PairSemantics.raw7698; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7698 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node304 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node304 (EqualityPatterns.family3.label 3) = PairSemantics.raw859 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node304 PairSemantics.raw859; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical859 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node304 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2128 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node304 (EqualityPatterns.family3.label 4) = PairSemantics.raw630 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node304 PairSemantics.raw630; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical630 hH).trans (PairSemantics.sound2128 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue304, PairSemantics.value0, PairSemantics.value11, PairSemantics.value118, PairSemantics.value232, PairSemantics.value2128, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue305 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 432)), (2, (-5 / 288)), (3, (5 / 54)), (5, (-5 / 108)), (6, (5 / 288)), (52, (5 / 54))]

theorem singlePair305 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node305 node305Labels = Sparse.eval singlePairValue305 (familyPairVector B) := by
  have hp := single_label_three B hB node305
  have hl : node305Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node305 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node305 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node305 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node305 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node305 (EqualityPatterns.family3.label 1) = PairSemantics.raw5139 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node305 PairSemantics.raw5139; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5139 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node305 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node305 (EqualityPatterns.family3.label 2) = PairSemantics.raw7699 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node305 PairSemantics.raw7699; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7699 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node305 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node305 (EqualityPatterns.family3.label 3) = PairSemantics.raw860 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node305 PairSemantics.raw860; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical860 hH).trans (PairSemantics.sound24 hH)
  have hm4 : familyPairMoment B (groupedColumns node305 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value559 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node305 (EqualityPatterns.family3.label 4) = PairSemantics.raw631 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node305 PairSemantics.raw631; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical631 hH).trans (PairSemantics.sound559 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue305, PairSemantics.value0, PairSemantics.value11, PairSemantics.value24, PairSemantics.value232, PairSemantics.value559, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue306 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (-5 / 72)), (2, (55 / 864)), (3, (5 / 18)), (5, (-5 / 72)), (7, (5 / 27)), (26, (5 / 54)), (35, (5 / 54))]

theorem singlePair306 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node306 node306Labels = Sparse.eval singlePairValue306 (familyPairVector B) := by
  have hp := single_label_three B hB node306
  have hl : node306Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node306 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node306 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node306 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node306 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node306 (EqualityPatterns.family3.label 1) = PairSemantics.raw5136 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node306 PairSemantics.raw5136; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5136 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node306 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node306 (EqualityPatterns.family3.label 2) = PairSemantics.raw7706 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node306 PairSemantics.raw7706; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7706 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node306 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node306 (EqualityPatterns.family3.label 3) = PairSemantics.raw861 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node306 PairSemantics.raw861; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical861 hH).trans (PairSemantics.sound25 hH)
  have hm4 : familyPairMoment B (groupedColumns node306 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value645 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node306 (EqualityPatterns.family3.label 4) = PairSemantics.raw632 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node306 PairSemantics.raw632; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical632 hH).trans (PairSemantics.sound645 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue306, PairSemantics.value0, PairSemantics.value11, PairSemantics.value25, PairSemantics.value46, PairSemantics.value645, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue307 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (25 / 216)), (2, (5 / 72)), (5, (-5 / 54)), (8, (5 / 27))]

theorem singlePair307 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node307 node307Labels = Sparse.eval singlePairValue307 (familyPairVector B) := by
  have hp := single_label_three B hB node307
  have hl : node307Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node307 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node307 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node307 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node307 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node307 (EqualityPatterns.family3.label 1) = PairSemantics.raw5139 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node307 PairSemantics.raw5139; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5139 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node307 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node307 (EqualityPatterns.family3.label 2) = PairSemantics.raw7703 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node307 PairSemantics.raw7703; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7703 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node307 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node307 (EqualityPatterns.family3.label 3) = PairSemantics.raw861 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node307 PairSemantics.raw861; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical861 hH).trans (PairSemantics.sound25 hH)
  have hm4 : familyPairMoment B (groupedColumns node307 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value866 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node307 (EqualityPatterns.family3.label 4) = PairSemantics.raw633 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node307 PairSemantics.raw633; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical633 hH).trans (PairSemantics.sound866 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue307, PairSemantics.value0, PairSemantics.value25, PairSemantics.value65, PairSemantics.value232, PairSemantics.value866, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue308 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 432)), (2, (5 / 216)), (3, (5 / 27)), (6, (5 / 432)), (12, (5 / 54)), (13, (10 / 27)), (52, (5 / 27)), (128, (5 / 54))]

theorem singlePair308 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node308 node308Labels = Sparse.eval singlePairValue308 (familyPairVector B) := by
  have hp := single_label_three B hB node308
  have hl : node308Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node308 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node308 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node308 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node308 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node308 (EqualityPatterns.family3.label 1) = PairSemantics.raw5147 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node308 PairSemantics.raw5147; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5147 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node308 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node308 (EqualityPatterns.family3.label 2) = PairSemantics.raw7693 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node308 PairSemantics.raw7693; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7693 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node308 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node308 (EqualityPatterns.family3.label 3) = PairSemantics.raw860 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node308 PairSemantics.raw860; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical860 hH).trans (PairSemantics.sound24 hH)
  have hm4 : familyPairMoment B (groupedColumns node308 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value527 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node308 (EqualityPatterns.family3.label 4) = PairSemantics.raw634 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node308 PairSemantics.raw634; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical634 hH).trans (PairSemantics.sound527 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue308, PairSemantics.value0, PairSemantics.value24, PairSemantics.value46, PairSemantics.value527, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue309 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 216)), (2, (5 / 108)), (3, (5 / 54)), (5, (-5 / 108)), (12, (5 / 54)), (13, (5 / 54)), (33, (-5 / 18)), (51, (-5 / 18)), (59, (-5 / 18))]

theorem singlePair309 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node309 node309Labels = Sparse.eval singlePairValue309 (familyPairVector B) := by
  have hp := single_label_three B hB node309
  have hl : node309Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node309 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node309 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node309 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node309 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node309 (EqualityPatterns.family3.label 1) = PairSemantics.raw5147 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node309 PairSemantics.raw5147; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5147 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node309 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node309 (EqualityPatterns.family3.label 2) = PairSemantics.raw7695 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node309 PairSemantics.raw7695; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7695 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node309 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node309 (EqualityPatterns.family3.label 3) = PairSemantics.raw861 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node309 PairSemantics.raw861; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical861 hH).trans (PairSemantics.sound25 hH)
  have hm4 : familyPairMoment B (groupedColumns node309 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value529 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node309 (EqualityPatterns.family3.label 4) = PairSemantics.raw635 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node309 PairSemantics.raw635; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical635 hH).trans (PairSemantics.sound529 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue309, PairSemantics.value0, PairSemantics.value25, PairSemantics.value46, PairSemantics.value529, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue310 : Sparse (Fin 909) := [(0, (37 / 864)), (1, (-25 / 288)), (2, (-5 / 54)), (3, (-10 / 27)), (4, (-5 / 27)), (5, (-5 / 216)), (6, (5 / 432)), (26, (-5 / 27)), (35, (-5 / 54)), (52, (-5 / 27))]

theorem singlePair310 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node310 node310Labels = Sparse.eval singlePairValue310 (familyPairVector B) := by
  have hp := single_label_three B hB node310
  have hl : node310Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node310 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node310 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node310 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node310 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node310 (EqualityPatterns.family3.label 1) = PairSemantics.raw5123 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node310 PairSemantics.raw5123; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5123 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node310 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node310 (EqualityPatterns.family3.label 2) = PairSemantics.raw7715 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node310 PairSemantics.raw7715; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7715 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node310 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value383 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node310 (EqualityPatterns.family3.label 3) = PairSemantics.raw866 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node310 PairSemantics.raw866; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical866 hH).trans (PairSemantics.sound383 hH)
  have hm4 : familyPairMoment B (groupedColumns node310 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2471 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node310 (EqualityPatterns.family3.label 4) = PairSemantics.raw636 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node310 PairSemantics.raw636; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical636 hH).trans (PairSemantics.sound2471 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue310, PairSemantics.value0, PairSemantics.value46, PairSemantics.value65, PairSemantics.value383, PairSemantics.value2471, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue311 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-55 / 864)), (2, (-65 / 864)), (3, (5 / 54)), (5, (5 / 216)), (26, (5 / 27)), (35, (5 / 54))]

theorem singlePair311 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node311 node311Labels = Sparse.eval singlePairValue311 (familyPairVector B) := by
  have hp := single_label_three B hB node311
  have hl : node311Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node311 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node311 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node311 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node311 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node311 (EqualityPatterns.family3.label 1) = PairSemantics.raw5125 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node311 PairSemantics.raw5125; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5125 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node311 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node311 (EqualityPatterns.family3.label 2) = PairSemantics.raw7714 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node311 PairSemantics.raw7714; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7714 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node311 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node311 (EqualityPatterns.family3.label 3) = PairSemantics.raw867 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node311 PairSemantics.raw867; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical867 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node311 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value876 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node311 (EqualityPatterns.family3.label 4) = PairSemantics.raw637 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node311 PairSemantics.raw637; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical637 hH).trans (PairSemantics.sound876 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue311, PairSemantics.value0, PairSemantics.value10, PairSemantics.value65, PairSemantics.value118, PairSemantics.value876, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
