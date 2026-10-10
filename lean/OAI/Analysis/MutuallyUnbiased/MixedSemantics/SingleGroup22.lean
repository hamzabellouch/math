import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleRules
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical159
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical160
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical241
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical242
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound5

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue360 : Sparse (Fin 909) := [(0, (17 / 432)), (1, (25 / 288)), (2, (35 / 288)), (3, (-10 / 9)), (4, (-5 / 9)), (5, (-5 / 72)), (12, (-5 / 18)), (13, (-5 / 27)), (26, (-5 / 9)), (27, (5 / 24)), (35, (-5 / 18)), (55, (5 / 6))]

theorem singlePair360 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node360 node360Labels = Sparse.eval singlePairValue360 (familyPairVector B) := by
  have hp := single_label_three B hB node360
  have hl : node360Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node360 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node360 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node360 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node360 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value716 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node360 (EqualityPatterns.family3.label 1) = PairSemantics.raw5109 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node360 PairSemantics.raw5109; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5109 hH).trans (PairSemantics.sound716 hH)
  have hm2 : familyPairMoment B (groupedColumns node360 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node360 (EqualityPatterns.family3.label 2) = PairSemantics.raw7755 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node360 PairSemantics.raw7755; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7755 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node360 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node360 (EqualityPatterns.family3.label 3) = PairSemantics.raw883 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node360 PairSemantics.raw883; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical883 hH).trans (PairSemantics.sound26 hH)
  have hm4 : familyPairMoment B (groupedColumns node360 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2141 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node360 (EqualityPatterns.family3.label 4) = PairSemantics.raw696 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node360 PairSemantics.raw696; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical696 hH).trans (PairSemantics.sound2141 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue360, PairSemantics.value0, PairSemantics.value11, PairSemantics.value26, PairSemantics.value716, PairSemantics.value2141, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue361 : Sparse (Fin 909) := [(0, (31 / 864)), (1, (-25 / 288)), (2, (-5 / 72)), (3, (5 / 27)), (5, (5 / 216)), (12, (5 / 54)), (13, (5 / 54)), (26, (5 / 54)), (27, (-5 / 72)), (35, (5 / 54)), (55, (-5 / 18))]

theorem singlePair361 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node361 node361Labels = Sparse.eval singlePairValue361 (familyPairVector B) := by
  have hp := single_label_three B hB node361
  have hl : node361Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node361 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node361 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node361 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node361 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value231 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node361 (EqualityPatterns.family3.label 1) = PairSemantics.raw5110 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node361 PairSemantics.raw5110; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5110 hH).trans (PairSemantics.sound231 hH)
  have hm2 : familyPairMoment B (groupedColumns node361 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node361 (EqualityPatterns.family3.label 2) = PairSemantics.raw7754 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node361 PairSemantics.raw7754; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7754 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node361 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node361 (EqualityPatterns.family3.label 3) = PairSemantics.raw884 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node361 PairSemantics.raw884; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical884 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node361 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value669 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node361 (EqualityPatterns.family3.label 4) = PairSemantics.raw697 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node361 PairSemantics.raw697; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical697 hH).trans (PairSemantics.sound669 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue361, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value231, PairSemantics.value669, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue362 : Sparse (Fin 909) := [(0, (17 / 864)), (1, (5 / 144)), (2, (-5 / 96)), (3, (5 / 54)), (5, (5 / 216)), (27, (-5 / 72)), (33, (-5 / 18)), (55, (-5 / 18)), (64, (-5 / 18))]

theorem singlePair362 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node362 node362Labels = Sparse.eval singlePairValue362 (familyPairVector B) := by
  have hp := single_label_three B hB node362
  have hl : node362Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node362 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node362 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node362 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node362 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value231 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node362 (EqualityPatterns.family3.label 1) = PairSemantics.raw5111 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node362 PairSemantics.raw5111; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5111 hH).trans (PairSemantics.sound231 hH)
  have hm2 : familyPairMoment B (groupedColumns node362 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node362 (EqualityPatterns.family3.label 2) = PairSemantics.raw7751 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node362 PairSemantics.raw7751; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7751 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node362 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node362 (EqualityPatterns.family3.label 3) = PairSemantics.raw884 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node362 PairSemantics.raw884; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical884 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node362 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value356 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node362 (EqualityPatterns.family3.label 4) = PairSemantics.raw698 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node362 PairSemantics.raw698; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical698 hH).trans (PairSemantics.sound356 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue362, PairSemantics.value0, PairSemantics.value10, PairSemantics.value231, PairSemantics.value232, PairSemantics.value356, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue363 : Sparse (Fin 909) := [(0, (25 / 864)), (1, (5 / 144)), (2, (-5 / 864)), (3, (-35 / 54)), (4, (-5 / 27)), (5, (5 / 216)), (7, (-5 / 54)), (12, (-5 / 54)), (13, (-5 / 54)), (23, (5 / 18)), (25, (5 / 9)), (26, (-10 / 27)), (27, (-5 / 72)), (33, (5 / 9)), (34, (-5 / 27)), (35, (-5 / 54)), (55, (5 / 18)), (63, (5 / 9)), (64, (5 / 9)), (65, (5 / 18)), (67, (-5 / 54))]

theorem singlePair363 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node363 node363Labels = Sparse.eval singlePairValue363 (familyPairVector B) := by
  have hp := single_label_three B hB node363
  have hl : node363Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node363 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node363 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node363 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node363 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value231 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node363 (EqualityPatterns.family3.label 1) = PairSemantics.raw5113 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node363 PairSemantics.raw5113; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5113 hH).trans (PairSemantics.sound231 hH)
  have hm2 : familyPairMoment B (groupedColumns node363 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node363 (EqualityPatterns.family3.label 2) = PairSemantics.raw7748 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node363 PairSemantics.raw7748; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7748 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node363 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node363 (EqualityPatterns.family3.label 3) = PairSemantics.raw883 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node363 PairSemantics.raw883; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical883 hH).trans (PairSemantics.sound26 hH)
  have hm4 : familyPairMoment B (groupedColumns node363 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1420 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node363 (EqualityPatterns.family3.label 4) = PairSemantics.raw700 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node363 PairSemantics.raw700; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical700 hH).trans (PairSemantics.sound1420 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue363, PairSemantics.value0, PairSemantics.value26, PairSemantics.value46, PairSemantics.value231, PairSemantics.value1420, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue364 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-25 / 432)), (2, (-5 / 216)), (23, (-5 / 18)), (27, (5 / 36)), (55, (-5 / 18)), (63, (-5 / 18)), (65, (-5 / 18))]

theorem singlePair364 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node364 node364Labels = Sparse.eval singlePairValue364 (familyPairVector B) := by
  have hp := single_label_three B hB node364
  have hl : node364Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node364 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node364 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node364 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node364 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value45 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node364 (EqualityPatterns.family3.label 1) = PairSemantics.raw5114 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node364 PairSemantics.raw5114; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5114 hH).trans (PairSemantics.sound45 hH)
  have hm2 : familyPairMoment B (groupedColumns node364 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node364 (EqualityPatterns.family3.label 2) = PairSemantics.raw7747 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node364 PairSemantics.raw7747; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7747 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node364 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node364 (EqualityPatterns.family3.label 3) = PairSemantics.raw884 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node364 PairSemantics.raw884; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical884 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node364 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value357 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node364 (EqualityPatterns.family3.label 4) = PairSemantics.raw701 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node364 PairSemantics.raw701; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical701 hH).trans (PairSemantics.sound357 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue364, PairSemantics.value0, PairSemantics.value10, PairSemantics.value45, PairSemantics.value46, PairSemantics.value357, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue365 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 108)), (2, (-5 / 108)), (5, (5 / 216)), (25, (-5 / 18)), (27, (-5 / 72)), (33, (-5 / 18)), (63, (-5 / 18)), (64, (-5 / 18))]

theorem singlePair365 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node365 node365Labels = Sparse.eval singlePairValue365 (familyPairVector B) := by
  have hp := single_label_three B hB node365
  have hl : node365Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node365 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node365 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node365 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node365 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value231 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node365 (EqualityPatterns.family3.label 1) = PairSemantics.raw5115 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node365 PairSemantics.raw5115; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5115 hH).trans (PairSemantics.sound231 hH)
  have hm2 : familyPairMoment B (groupedColumns node365 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node365 (EqualityPatterns.family3.label 2) = PairSemantics.raw7745 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node365 PairSemantics.raw7745; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7745 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node365 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node365 (EqualityPatterns.family3.label 3) = PairSemantics.raw884 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node365 PairSemantics.raw884; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical884 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node365 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value358 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node365 (EqualityPatterns.family3.label 4) = PairSemantics.raw702 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node365 PairSemantics.raw702; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical702 hH).trans (PairSemantics.sound358 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue365, PairSemantics.value0, PairSemantics.value10, PairSemantics.value46, PairSemantics.value231, PairSemantics.value358, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue366 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 216)), (2, (65 / 432)), (27, (5 / 36)), (63, (5 / 9))]

theorem singlePair366 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node366 node366Labels = Sparse.eval singlePairValue366 (familyPairVector B) := by
  have hp := single_label_three B hB node366
  have hl : node366Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node366 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node366 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node366 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node366 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value45 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node366 (EqualityPatterns.family3.label 1) = PairSemantics.raw5116 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node366 PairSemantics.raw5116; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5116 hH).trans (PairSemantics.sound45 hH)
  have hm2 : familyPairMoment B (groupedColumns node366 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node366 (EqualityPatterns.family3.label 2) = PairSemantics.raw7746 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node366 PairSemantics.raw7746; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7746 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node366 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node366 (EqualityPatterns.family3.label 3) = PairSemantics.raw887 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node366 PairSemantics.raw887; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical887 hH).trans (PairSemantics.sound3 hH)
  have hm4 : familyPairMoment B (groupedColumns node366 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value101 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node366 (EqualityPatterns.family3.label 4) = PairSemantics.raw704 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node366 PairSemantics.raw704; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical704 hH).trans (PairSemantics.sound101 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue366, PairSemantics.value0, PairSemantics.value3, PairSemantics.value45, PairSemantics.value46, PairSemantics.value101, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue367 : Sparse (Fin 909) := [(0, (7 / 432)), (1, (5 / 72)), (2, (5 / 432)), (24, (-5 / 18)), (27, (5 / 36)), (55, (-5 / 9)), (66, (-5 / 18))]

theorem singlePair367 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node367 node367Labels = Sparse.eval singlePairValue367 (familyPairVector B) := by
  have hp := single_label_three B hB node367
  have hl : node367Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node367 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node367 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node367 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node367 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value45 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node367 (EqualityPatterns.family3.label 1) = PairSemantics.raw5106 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node367 PairSemantics.raw5106; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5106 hH).trans (PairSemantics.sound45 hH)
  have hm2 : familyPairMoment B (groupedColumns node367 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node367 (EqualityPatterns.family3.label 2) = PairSemantics.raw7760 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node367 PairSemantics.raw7760; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7760 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node367 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node367 (EqualityPatterns.family3.label 3) = PairSemantics.raw893 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node367 PairSemantics.raw893; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical893 hH).trans (PairSemantics.sound26 hH)
  have hm4 : familyPairMoment B (groupedColumns node367 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value361 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node367 (EqualityPatterns.family3.label 4) = PairSemantics.raw707 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node367 PairSemantics.raw707; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical707 hH).trans (PairSemantics.sound361 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue367, PairSemantics.value0, PairSemantics.value26, PairSemantics.value45, PairSemantics.value232, PairSemantics.value361, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue368 : Sparse (Fin 909) := [(0, (29 / 864)), (1, (-5 / 864)), (3, (5 / 18)), (4, (5 / 27)), (5, (5 / 216)), (26, (5 / 27)), (27, (-5 / 72)), (35, (5 / 54)), (55, (-5 / 18))]

theorem singlePair368 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node368 node368Labels = Sparse.eval singlePairValue368 (familyPairVector B) := by
  have hp := single_label_three B hB node368
  have hl : node368Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node368 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node368 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node368 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node368 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value231 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node368 (EqualityPatterns.family3.label 1) = PairSemantics.raw5110 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node368 PairSemantics.raw5110; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5110 hH).trans (PairSemantics.sound231 hH)
  have hm2 : familyPairMoment B (groupedColumns node368 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node368 (EqualityPatterns.family3.label 2) = PairSemantics.raw7758 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node368 PairSemantics.raw7758; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7758 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node368 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node368 (EqualityPatterns.family3.label 3) = PairSemantics.raw893 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node368 PairSemantics.raw893; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical893 hH).trans (PairSemantics.sound26 hH)
  have hm4 : familyPairMoment B (groupedColumns node368 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value666 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node368 (EqualityPatterns.family3.label 4) = PairSemantics.raw710 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node368 PairSemantics.raw710; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical710 hH).trans (PairSemantics.sound666 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue368, PairSemantics.value0, PairSemantics.value11, PairSemantics.value26, PairSemantics.value231, PairSemantics.value666, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue369 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 72)), (2, (-5 / 144)), (27, (5 / 36)), (55, (5 / 9))]

theorem singlePair369 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node369 node369Labels = Sparse.eval singlePairValue369 (familyPairVector B) := by
  have hp := single_label_three B hB node369
  have hl : node369Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node369 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node369 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node369 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node369 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value45 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node369 (EqualityPatterns.family3.label 1) = PairSemantics.raw5116 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node369 PairSemantics.raw5116; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5116 hH).trans (PairSemantics.sound45 hH)
  have hm2 : familyPairMoment B (groupedColumns node369 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node369 (EqualityPatterns.family3.label 2) = PairSemantics.raw7753 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node369 PairSemantics.raw7753; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7753 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node369 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node369 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node369 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node369 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value212 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node369 (EqualityPatterns.family3.label 4) = PairSemantics.raw713 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node369 PairSemantics.raw713; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical713 hH).trans (PairSemantics.sound212 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue369, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value45, PairSemantics.value212, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue370 : Sparse (Fin 909) := [(0, (25 / 432)), (1, (-25 / 432)), (2, (-5 / 108)), (3, (-10 / 27)), (5, (-5 / 216)), (12, (-5 / 54)), (13, (-5 / 54)), (26, (-5 / 27)), (27, (5 / 72)), (35, (-5 / 54)), (55, (5 / 18))]

theorem singlePair370 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node370 node370Labels = Sparse.eval singlePairValue370 (familyPairVector B) := by
  have hp := single_label_three B hB node370
  have hl : node370Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node370 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node370 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node370 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node370 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value717 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node370 (EqualityPatterns.family3.label 1) = PairSemantics.raw5120 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node370 PairSemantics.raw5120; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5120 hH).trans (PairSemantics.sound717 hH)
  have hm2 : familyPairMoment B (groupedColumns node370 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node370 (EqualityPatterns.family3.label 2) = PairSemantics.raw7741 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node370 PairSemantics.raw7741; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7741 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node370 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node370 (EqualityPatterns.family3.label 3) = PairSemantics.raw879 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node370 PairSemantics.raw879; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical879 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node370 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2793 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node370 (EqualityPatterns.family3.label 4) = PairSemantics.raw720 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node370 PairSemantics.raw720; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical720 hH).trans (PairSemantics.sound2793 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue370, PairSemantics.value0, PairSemantics.value10, PairSemantics.value65, PairSemantics.value717, PairSemantics.value2793, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue371 : Sparse (Fin 909) := [(0, (35 / 864)), (1, (205 / 864)), (2, (5 / 108)), (3, (-35 / 54)), (4, (-10 / 27)), (5, (-5 / 216)), (26, (-10 / 27)), (27, (5 / 72)), (35, (-5 / 54)), (55, (5 / 18))]

theorem singlePair371 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node371 node371Labels = Sparse.eval singlePairValue371 (familyPairVector B) := by
  have hp := single_label_three B hB node371
  have hl : node371Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node371 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node371 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node371 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node371 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value717 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node371 (EqualityPatterns.family3.label 1) = PairSemantics.raw5120 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node371 PairSemantics.raw5120; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5120 hH).trans (PairSemantics.sound717 hH)
  have hm2 : familyPairMoment B (groupedColumns node371 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node371 (EqualityPatterns.family3.label 2) = PairSemantics.raw7743 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node371 PairSemantics.raw7743; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7743 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node371 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node371 (EqualityPatterns.family3.label 3) = PairSemantics.raw883 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node371 PairSemantics.raw883; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical883 hH).trans (PairSemantics.sound26 hH)
  have hm4 : familyPairMoment B (groupedColumns node371 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2671 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node371 (EqualityPatterns.family3.label 4) = PairSemantics.raw721 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node371 PairSemantics.raw721; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical721 hH).trans (PairSemantics.sound2671 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue371, PairSemantics.value0, PairSemantics.value26, PairSemantics.value65, PairSemantics.value717, PairSemantics.value2671, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue372 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-5 / 216)), (2, (-25 / 432)), (3, (5 / 54)), (27, (-5 / 72)), (55, (-5 / 18))]

theorem singlePair372 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node372 node372Labels = Sparse.eval singlePairValue372 (familyPairVector B) := by
  have hp := single_label_three B hB node372
  have hl : node372Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node372 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node372 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node372 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node372 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value231 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node372 (EqualityPatterns.family3.label 1) = PairSemantics.raw5122 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node372 PairSemantics.raw5122; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5122 hH).trans (PairSemantics.sound231 hH)
  have hm2 : familyPairMoment B (groupedColumns node372 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node372 (EqualityPatterns.family3.label 2) = PairSemantics.raw7740 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node372 PairSemantics.raw7740; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7740 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node372 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node372 (EqualityPatterns.family3.label 3) = PairSemantics.raw884 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node372 PairSemantics.raw884; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical884 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node372 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1143 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node372 (EqualityPatterns.family3.label 4) = PairSemantics.raw722 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node372 PairSemantics.raw722; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical722 hH).trans (PairSemantics.sound1143 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue372, PairSemantics.value0, PairSemantics.value10, PairSemantics.value65, PairSemantics.value231, PairSemantics.value1143, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue373 : Sparse (Fin 909) := [(0, (11 / 864)), (1, (5 / 96)), (2, (-5 / 108)), (3, (-5 / 18)), (12, (-5 / 27)), (13, (-25 / 54)), (26, (-5 / 27)), (34, (-5 / 27))]

theorem singlePair373 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node373 node373Labels = Sparse.eval singlePairValue373 (familyPairVector B) := by
  have hp := single_label_three B hB node373
  have hl : node373Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node373 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node373 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node373 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node373 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node373 (EqualityPatterns.family3.label 1) = PairSemantics.raw5140 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node373 PairSemantics.raw5140; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5140 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node373 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node373 (EqualityPatterns.family3.label 2) = PairSemantics.raw7726 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node373 PairSemantics.raw7726; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7726 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node373 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node373 (EqualityPatterns.family3.label 3) = PairSemantics.raw879 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node373 PairSemantics.raw879; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical879 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node373 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1428 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node373 (EqualityPatterns.family3.label 4) = PairSemantics.raw727 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node373 PairSemantics.raw727; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical727 hH).trans (PairSemantics.sound1428 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue373, PairSemantics.value0, PairSemantics.value10, PairSemantics.value232, PairSemantics.value1428, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue374 : Sparse (Fin 909) := [(0, (1 / 108)), (1, (5 / 144)), (2, (5 / 144)), (13, (5 / 27))]

theorem singlePair374 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node374 node374Labels = Sparse.eval singlePairValue374 (familyPairVector B) := by
  have hp := single_label_three B hB node374
  have hl : node374Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node374 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node374 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node374 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node374 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node374 (EqualityPatterns.family3.label 1) = PairSemantics.raw5139 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node374 PairSemantics.raw5139; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5139 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node374 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node374 (EqualityPatterns.family3.label 2) = PairSemantics.raw7728 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node374 PairSemantics.raw7728; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7728 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node374 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node374 (EqualityPatterns.family3.label 3) = PairSemantics.raw881 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node374 PairSemantics.raw881; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical881 hH).trans (PairSemantics.sound3 hH)
  have hm4 : familyPairMoment B (groupedColumns node374 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value364 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node374 (EqualityPatterns.family3.label 4) = PairSemantics.raw728 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node374 PairSemantics.raw728; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical728 hH).trans (PairSemantics.sound364 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue374, PairSemantics.value0, PairSemantics.value3, PairSemantics.value232, PairSemantics.value364, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue375 : Sparse (Fin 909) := [(0, (-1 / 108)), (1, (-35 / 864)), (2, (25 / 864)), (3, (-20 / 27)), (4, (-10 / 27)), (13, (-5 / 54)), (26, (-5 / 9)), (34, (-5 / 27))]

theorem singlePair375 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node375 node375Labels = Sparse.eval singlePairValue375 (familyPairVector B) := by
  have hp := single_label_three B hB node375
  have hl : node375Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node375 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node375 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node375 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node375 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node375 (EqualityPatterns.family3.label 1) = PairSemantics.raw5134 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node375 PairSemantics.raw5134; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5134 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node375 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value1323 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node375 (EqualityPatterns.family3.label 2) = PairSemantics.raw7734 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node375 PairSemantics.raw7734; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7734 hH).trans (PairSemantics.sound1323 hH)
  have hm3 : familyPairMoment B (groupedColumns node375 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node375 (EqualityPatterns.family3.label 3) = PairSemantics.raw883 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node375 PairSemantics.raw883; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical883 hH).trans (PairSemantics.sound26 hH)
  have hm4 : familyPairMoment B (groupedColumns node375 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1430 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node375 (EqualityPatterns.family3.label 4) = PairSemantics.raw730 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node375 PairSemantics.raw730; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical730 hH).trans (PairSemantics.sound1430 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue375, PairSemantics.value0, PairSemantics.value26, PairSemantics.value46, PairSemantics.value1323, PairSemantics.value1430, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
