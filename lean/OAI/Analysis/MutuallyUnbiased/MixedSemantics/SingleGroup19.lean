import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleRules
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical160
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical161
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical239
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical240
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical241
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound8

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue312 : Sparse (Fin 909) := [(0, (11 / 288)), (1, (5 / 432)), (2, (35 / 432)), (3, (5 / 27)), (6, (-5 / 864)), (52, (5 / 54))]

theorem singlePair312 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node312 node312Labels = Sparse.eval singlePairValue312 (familyPairVector B) := by
  have hp := single_label_three B hB node312
  have hl : node312Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node312 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node312 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node312 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node312 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node312 (EqualityPatterns.family3.label 1) = PairSemantics.raw5131 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node312 PairSemantics.raw5131; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5131 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node312 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node312 (EqualityPatterns.family3.label 2) = PairSemantics.raw7712 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node312 PairSemantics.raw7712; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7712 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node312 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node312 (EqualityPatterns.family3.label 3) = PairSemantics.raw867 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node312 PairSemantics.raw867; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical867 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node312 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value870 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node312 (EqualityPatterns.family3.label 4) = PairSemantics.raw638 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node312 PairSemantics.raw638; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical638 hH).trans (PairSemantics.sound870 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue312, PairSemantics.value0, PairSemantics.value46, PairSemantics.value65, PairSemantics.value118, PairSemantics.value870, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue313 : Sparse (Fin 909) := [(0, (23 / 864)), (1, (-5 / 108)), (2, (-5 / 432)), (3, (5 / 18)), (5, (5 / 216)), (6, (-5 / 864)), (12, (5 / 54)), (13, (5 / 18)), (26, (5 / 54)), (34, (5 / 27)), (35, (5 / 54)), (60, (5 / 54))]

theorem singlePair313 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node313 node313Labels = Sparse.eval singlePairValue313 (familyPairVector B) := by
  have hp := single_label_three B hB node313
  have hl : node313Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node313 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node313 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node313 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node313 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node313 (EqualityPatterns.family3.label 1) = PairSemantics.raw5133 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node313 PairSemantics.raw5133; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5133 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node313 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node313 (EqualityPatterns.family3.label 2) = PairSemantics.raw7710 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node313 PairSemantics.raw7710; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7710 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node313 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node313 (EqualityPatterns.family3.label 3) = PairSemantics.raw867 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node313 PairSemantics.raw867; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical867 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node313 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value378 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node313 (EqualityPatterns.family3.label 4) = PairSemantics.raw639 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node313 PairSemantics.raw639; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical639 hH).trans (PairSemantics.sound378 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue313, PairSemantics.value0, PairSemantics.value10, PairSemantics.value46, PairSemantics.value118, PairSemantics.value378, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue314 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-5 / 96)), (2, (5 / 144)), (4, (5 / 54)), (5, (5 / 216)), (6, (-5 / 864)), (26, (5 / 54)), (35, (5 / 54)), (52, (5 / 54))]

theorem singlePair314 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node314 node314Labels = Sparse.eval singlePairValue314 (familyPairVector B) := by
  have hp := single_label_three B hB node314
  have hl : node314Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node314 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node314 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node314 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node314 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node314 (EqualityPatterns.family3.label 1) = PairSemantics.raw5142 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node314 PairSemantics.raw5142; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5142 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node314 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node314 (EqualityPatterns.family3.label 2) = PairSemantics.raw7707 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node314 PairSemantics.raw7707; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7707 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node314 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node314 (EqualityPatterns.family3.label 3) = PairSemantics.raw867 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node314 PairSemantics.raw867; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical867 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node314 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value658 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node314 (EqualityPatterns.family3.label 4) = PairSemantics.raw640 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node314 PairSemantics.raw640; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical640 hH).trans (PairSemantics.sound658 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue314, PairSemantics.value0, PairSemantics.value11, PairSemantics.value46, PairSemantics.value118, PairSemantics.value658, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue315 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-5 / 72)), (2, (-5 / 144)), (3, (-5 / 27)), (6, (5 / 432)), (52, (-5 / 27))]

theorem singlePair315 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node315 node315Labels = Sparse.eval singlePairValue315 (familyPairVector B) := by
  have hp := single_label_three B hB node315
  have hl : node315Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node315 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node315 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node315 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node315 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node315 (EqualityPatterns.family3.label 1) = PairSemantics.raw5149 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node315 PairSemantics.raw5149; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5149 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node315 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node315 (EqualityPatterns.family3.label 2) = PairSemantics.raw7705 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node315 PairSemantics.raw7705; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7705 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node315 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node315 (EqualityPatterns.family3.label 3) = PairSemantics.raw869 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node315 PairSemantics.raw869; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical869 hH).trans (PairSemantics.sound24 hH)
  have hm4 : familyPairMoment B (groupedColumns node315 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value180 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node315 (EqualityPatterns.family3.label 4) = PairSemantics.raw641 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node315 PairSemantics.raw641; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical641 hH).trans (PairSemantics.sound180 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue315, PairSemantics.value0, PairSemantics.value11, PairSemantics.value24, PairSemantics.value46, PairSemantics.value180, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue316 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 108)), (2, (-5 / 432)), (3, (-5 / 27)), (5, (-5 / 108)), (26, (-5 / 27)), (35, (-5 / 27))]

theorem singlePair316 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node316 node316Labels = Sparse.eval singlePairValue316 (familyPairVector B) := by
  have hp := single_label_three B hB node316
  have hl : node316Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node316 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node316 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node316 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node316 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node316 (EqualityPatterns.family3.label 1) = PairSemantics.raw5132 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node316 PairSemantics.raw5132; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5132 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node316 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node316 (EqualityPatterns.family3.label 2) = PairSemantics.raw7716 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node316 PairSemantics.raw7716; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7716 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node316 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node316 (EqualityPatterns.family3.label 3) = PairSemantics.raw872 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node316 PairSemantics.raw872; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical872 hH).trans (PairSemantics.sound25 hH)
  have hm4 : familyPairMoment B (groupedColumns node316 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value209 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node316 (EqualityPatterns.family3.label 4) = PairSemantics.raw642 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node316 PairSemantics.raw642; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical642 hH).trans (PairSemantics.sound209 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue316, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value25, PairSemantics.value209, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue317 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (35 / 288)), (2, (-5 / 288)), (3, (-5 / 54)), (5, (5 / 216)), (6, (5 / 216)), (7, (-5 / 54)), (9, (-5 / 108)), (12, (-5 / 54)), (13, (-5 / 54)), (23, (5 / 18)), (27, (5 / 72)), (35, (-5 / 27)), (68, (5 / 36)), (69, (-5 / 54)), (70, (-5 / 54)), (124, (5 / 18)), (125, (5 / 18))]

theorem singlePair317 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node317 node317Labels = Sparse.eval singlePairValue317 (familyPairVector B) := by
  have hp := single_label_three B hB node317
  have hl : node317Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node317 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node317 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node317 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node317 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node317 (EqualityPatterns.family3.label 1) = PairSemantics.raw5163 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node317 PairSemantics.raw5163; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5163 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node317 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node317 (EqualityPatterns.family3.label 2) = PairSemantics.raw7660 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node317 PairSemantics.raw7660; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7660 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node317 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value382 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node317 (EqualityPatterns.family3.label 3) = PairSemantics.raw855 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node317 PairSemantics.raw855; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical855 hH).trans (PairSemantics.sound382 hH)
  have hm4 : familyPairMoment B (groupedColumns node317 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1874 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node317 (EqualityPatterns.family3.label 4) = PairSemantics.raw644 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node317 PairSemantics.raw644; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical644 hH).trans (PairSemantics.sound1874 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue317, PairSemantics.value0, PairSemantics.value4, PairSemantics.value232, PairSemantics.value382, PairSemantics.value1874, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue318 : Sparse (Fin 909) := [(0, (23 / 864)), (2, (-145 / 864)), (3, (-5 / 18)), (5, (5 / 36)), (6, (5 / 216)), (7, (-10 / 27)), (8, (-10 / 27)), (9, (-5 / 108)), (51, (5 / 9)), (68, (5 / 36)), (69, (-5 / 54)), (71, (-5 / 54)), (124, (5 / 18)), (126, (5 / 18))]

theorem singlePair318 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node318 node318Labels = Sparse.eval singlePairValue318 (familyPairVector B) := by
  have hp := single_label_three B hB node318
  have hl : node318Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node318 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node318 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node318 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node318 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node318 (EqualityPatterns.family3.label 1) = PairSemantics.raw5166 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node318 PairSemantics.raw5166; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5166 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node318 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node318 (EqualityPatterns.family3.label 2) = PairSemantics.raw7655 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node318 PairSemantics.raw7655; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7655 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node318 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value382 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node318 (EqualityPatterns.family3.label 3) = PairSemantics.raw855 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node318 PairSemantics.raw855; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical855 hH).trans (PairSemantics.sound382 hH)
  have hm4 : familyPairMoment B (groupedColumns node318 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1877 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node318 (EqualityPatterns.family3.label 4) = PairSemantics.raw645 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node318 PairSemantics.raw645; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical645 hH).trans (PairSemantics.sound1877 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue318, PairSemantics.value0, PairSemantics.value11, PairSemantics.value232, PairSemantics.value382, PairSemantics.value1877, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue319 : Sparse (Fin 909) := [(0, (1 / 72)), (1, (35 / 432)), (2, (-5 / 108)), (3, (-10 / 27)), (5, (5 / 54)), (6, (-5 / 432)), (13, (-10 / 27)), (35, (-5 / 27)), (52, (-10 / 27))]

theorem singlePair319 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node319 node319Labels = Sparse.eval singlePairValue319 (familyPairVector B) := by
  have hp := single_label_three B hB node319
  have hl : node319Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node319 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node319 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node319 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node319 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node319 (EqualityPatterns.family3.label 1) = PairSemantics.raw5156 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node319 PairSemantics.raw5156; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5156 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node319 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node319 (EqualityPatterns.family3.label 2) = PairSemantics.raw7673 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node319 PairSemantics.raw7673; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7673 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node319 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node319 (EqualityPatterns.family3.label 3) = PairSemantics.raw857 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node319 PairSemantics.raw857; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical857 hH).trans (PairSemantics.sound24 hH)
  have hm4 : familyPairMoment B (groupedColumns node319 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1861 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node319 (EqualityPatterns.family3.label 4) = PairSemantics.raw646 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node319 PairSemantics.raw646; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical646 hH).trans (PairSemantics.sound1861 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue319, PairSemantics.value0, PairSemantics.value24, PairSemantics.value232, PairSemantics.value1861, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue320 : Sparse (Fin 909) := [(0, (37 / 864)), (1, (-5 / 144)), (2, (5 / 216)), (3, (-10 / 27)), (4, (-5 / 54)), (5, (25 / 216)), (6, (-5 / 288)), (7, (-5 / 27)), (8, (-5 / 54)), (26, (-5 / 27)), (35, (-5 / 54))]

theorem singlePair320 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node320 node320Labels = Sparse.eval singlePairValue320 (familyPairVector B) := by
  have hp := single_label_three B hB node320
  have hl : node320Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node320 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node320 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node320 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node320 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node320 (EqualityPatterns.family3.label 1) = PairSemantics.raw5153 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node320 PairSemantics.raw5153; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5153 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node320 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node320 (EqualityPatterns.family3.label 2) = PairSemantics.raw7680 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node320 PairSemantics.raw7680; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7680 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node320 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node320 (EqualityPatterns.family3.label 3) = PairSemantics.raw859 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node320 PairSemantics.raw859; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical859 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node320 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2463 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node320 (EqualityPatterns.family3.label 4) = PairSemantics.raw647 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node320 PairSemantics.raw647; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical647 hH).trans (PairSemantics.sound2463 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue320, PairSemantics.value0, PairSemantics.value46, PairSemantics.value65, PairSemantics.value118, PairSemantics.value2463, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue321 : Sparse (Fin 909) := [(0, (19 / 864)), (1, (85 / 432)), (2, (-25 / 432)), (3, (-5 / 27)), (5, (5 / 36)), (6, (-5 / 288)), (7, (-5 / 54)), (8, (-5 / 27))]

theorem singlePair321 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node321 node321Labels = Sparse.eval singlePairValue321 (familyPairVector B) := by
  have hp := single_label_three B hB node321
  have hl : node321Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node321 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node321 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node321 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node321 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node321 (EqualityPatterns.family3.label 1) = PairSemantics.raw5156 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node321 PairSemantics.raw5156; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5156 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node321 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node321 (EqualityPatterns.family3.label 2) = PairSemantics.raw7676 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node321 PairSemantics.raw7676; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7676 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node321 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node321 (EqualityPatterns.family3.label 3) = PairSemantics.raw859 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node321 PairSemantics.raw859; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical859 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node321 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2462 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node321 (EqualityPatterns.family3.label 4) = PairSemantics.raw648 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node321 PairSemantics.raw648; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical648 hH).trans (PairSemantics.sound2462 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue321, PairSemantics.value0, PairSemantics.value65, PairSemantics.value118, PairSemantics.value232, PairSemantics.value2462, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue322 : Sparse (Fin 909) := [(0, (1 / 48)), (1, (65 / 864)), (2, (-25 / 432)), (3, (-35 / 54)), (4, (-5 / 27)), (5, (5 / 108)), (6, (-5 / 864)), (7, (-5 / 27)), (12, (-5 / 27)), (13, (-25 / 54)), (26, (-10 / 27)), (34, (-5 / 27)), (35, (-10 / 27)), (52, (-5 / 27)), (67, (-5 / 54))]

theorem singlePair322 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node322 node322Labels = Sparse.eval singlePairValue322 (familyPairVector B) := by
  have hp := single_label_three B hB node322
  have hl : node322Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node322 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node322 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node322 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node322 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node322 (EqualityPatterns.family3.label 1) = PairSemantics.raw5158 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node322 PairSemantics.raw5158; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5158 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node322 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node322 (EqualityPatterns.family3.label 2) = PairSemantics.raw7675 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node322 PairSemantics.raw7675; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7675 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node322 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node322 (EqualityPatterns.family3.label 3) = PairSemantics.raw859 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node322 PairSemantics.raw859; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical859 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node322 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1860 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node322 (EqualityPatterns.family3.label 4) = PairSemantics.raw649 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node322 PairSemantics.raw649; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical649 hH).trans (PairSemantics.sound1860 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue322, PairSemantics.value0, PairSemantics.value46, PairSemantics.value118, PairSemantics.value232, PairSemantics.value1860, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue323 : Sparse (Fin 909) := [(0, (13 / 864)), (1, (65 / 864)), (2, (5 / 216)), (3, (5 / 27)), (5, (-5 / 216)), (6, (5 / 432)), (13, (5 / 27)), (35, (5 / 54)), (52, (5 / 27))]

theorem singlePair323 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node323 node323Labels = Sparse.eval singlePairValue323 (familyPairVector B) := by
  have hp := single_label_three B hB node323
  have hl : node323Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node323 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node323 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node323 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node323 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node323 (EqualityPatterns.family3.label 1) = PairSemantics.raw5159 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node323 PairSemantics.raw5159; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5159 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node323 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node323 (EqualityPatterns.family3.label 2) = PairSemantics.raw7674 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node323 PairSemantics.raw7674; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7674 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node323 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node323 (EqualityPatterns.family3.label 3) = PairSemantics.raw860 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node323 PairSemantics.raw860; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical860 hH).trans (PairSemantics.sound24 hH)
  have hm4 : familyPairMoment B (groupedColumns node323 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value531 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node323 (EqualityPatterns.family3.label 4) = PairSemantics.raw650 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node323 PairSemantics.raw650; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical650 hH).trans (PairSemantics.sound531 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue323, PairSemantics.value0, PairSemantics.value24, PairSemantics.value46, PairSemantics.value232, PairSemantics.value531, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue324 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (5 / 432)), (2, (-5 / 144)), (3, (5 / 27)), (5, (-5 / 108)), (7, (5 / 54)), (13, (5 / 54)), (26, (5 / 27)), (34, (5 / 54)), (35, (5 / 27)), (67, (5 / 54))]

theorem singlePair324 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node324 node324Labels = Sparse.eval singlePairValue324 (familyPairVector B) := by
  have hp := single_label_three B hB node324
  have hl : node324Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node324 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node324 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node324 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node324 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node324 (EqualityPatterns.family3.label 1) = PairSemantics.raw5154 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node324 PairSemantics.raw5154; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5154 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node324 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node324 (EqualityPatterns.family3.label 2) = PairSemantics.raw7682 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node324 PairSemantics.raw7682; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7682 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node324 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node324 (EqualityPatterns.family3.label 3) = PairSemantics.raw861 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node324 PairSemantics.raw861; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical861 hH).trans (PairSemantics.sound25 hH)
  have hm4 : familyPairMoment B (groupedColumns node324 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value355 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node324 (EqualityPatterns.family3.label 4) = PairSemantics.raw651 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node324 PairSemantics.raw651; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical651 hH).trans (PairSemantics.sound355 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue324, PairSemantics.value0, PairSemantics.value10, PairSemantics.value25, PairSemantics.value232, PairSemantics.value355, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue325 : Sparse (Fin 909) := [(0, (11 / 288)), (1, (5 / 432)), (2, (55 / 864)), (3, (5 / 54)), (5, (-5 / 54)), (7, (5 / 54)), (8, (5 / 54))]

theorem singlePair325 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node325 node325Labels = Sparse.eval singlePairValue325 (familyPairVector B) := by
  have hp := single_label_three B hB node325
  have hl : node325Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node325 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node325 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node325 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node325 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node325 (EqualityPatterns.family3.label 1) = PairSemantics.raw5157 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node325 PairSemantics.raw5157; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5157 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node325 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node325 (EqualityPatterns.family3.label 2) = PairSemantics.raw7679 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node325 PairSemantics.raw7679; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7679 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node325 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node325 (EqualityPatterns.family3.label 3) = PairSemantics.raw861 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node325 PairSemantics.raw861; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical861 hH).trans (PairSemantics.sound25 hH)
  have hm4 : familyPairMoment B (groupedColumns node325 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value863 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node325 (EqualityPatterns.family3.label 4) = PairSemantics.raw652 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node325 PairSemantics.raw652; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical652 hH).trans (PairSemantics.sound863 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue325, PairSemantics.value0, PairSemantics.value25, PairSemantics.value46, PairSemantics.value65, PairSemantics.value863, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue326 : Sparse (Fin 909) := [(0, (23 / 864)), (1, (35 / 432)), (2, (-65 / 864)), (3, (-10 / 27)), (5, (5 / 54)), (6, (-5 / 432)), (7, (-5 / 27)), (8, (-5 / 54)), (12, (-5 / 27)), (13, (-5 / 27)), (35, (-5 / 54)), (51, (5 / 18)), (52, (-5 / 54))]

theorem singlePair326 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node326 node326Labels = Sparse.eval singlePairValue326 (familyPairVector B) := by
  have hp := single_label_three B hB node326
  have hl : node326Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node326 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node326 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node326 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node326 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node326 (EqualityPatterns.family3.label 1) = PairSemantics.raw5176 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node326 PairSemantics.raw5176; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5176 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node326 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node326 (EqualityPatterns.family3.label 2) = PairSemantics.raw7657 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node326 PairSemantics.raw7657; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7657 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node326 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node326 (EqualityPatterns.family3.label 3) = PairSemantics.raw859 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node326 PairSemantics.raw859; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical859 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node326 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1885 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node326 (EqualityPatterns.family3.label 4) = PairSemantics.raw653 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node326 PairSemantics.raw653; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical653 hH).trans (PairSemantics.sound1885 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue326, PairSemantics.value0, PairSemantics.value11, PairSemantics.value118, PairSemantics.value232, PairSemantics.value1885, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue327 : Sparse (Fin 909) := [(0, (17 / 864)), (1, (35 / 288)), (3, (-55 / 54)), (4, (-5 / 27)), (5, (5 / 108)), (6, (-5 / 432)), (7, (-5 / 54)), (13, (-10 / 27)), (26, (-20 / 27)), (34, (-25 / 54)), (35, (-5 / 18)), (52, (-5 / 54)), (64, (5 / 18)), (67, (-5 / 27))]

theorem singlePair327 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node327 node327Labels = Sparse.eval singlePairValue327 (familyPairVector B) := by
  have hp := single_label_three B hB node327
  have hl : node327Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node327 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node327 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node327 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node327 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node327 (EqualityPatterns.family3.label 1) = PairSemantics.raw5181 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node327 PairSemantics.raw5181; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5181 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node327 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node327 (EqualityPatterns.family3.label 2) = PairSemantics.raw7653 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node327 PairSemantics.raw7653; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7653 hH).trans (PairSemantics.sound26 hH)
  have hm3 : familyPairMoment B (groupedColumns node327 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node327 (EqualityPatterns.family3.label 3) = PairSemantics.raw859 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node327 PairSemantics.raw859; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical859 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node327 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1425 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node327 (EqualityPatterns.family3.label 4) = PairSemantics.raw654 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node327 PairSemantics.raw654; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical654 hH).trans (PairSemantics.sound1425 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue327, PairSemantics.value0, PairSemantics.value26, PairSemantics.value118, PairSemantics.value232, PairSemantics.value1425, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
