import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleRules
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical160
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical161
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical238
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical240
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
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

def singlePairValue280 : Sparse (Fin 909) := [(0, (19 / 864)), (1, (5 / 144)), (2, (5 / 72)), (3, (-10 / 27)), (4, (-5 / 54)), (5, (-5 / 36)), (6, (5 / 288)), (7, (-5 / 54)), (9, (-5 / 216)), (12, (-5 / 54)), (23, (5 / 18)), (25, (5 / 18)), (26, (-5 / 27)), (27, (5 / 24)), (35, (-5 / 54)), (51, (5 / 18)), (54, (5 / 18)), (55, (5 / 18)), (64, (5 / 18)), (68, (25 / 72)), (123, (5 / 18)), (124, (5 / 18)), (125, (5 / 18)), (259, (5 / 18)), (266, (5 / 18)), (487, (-5 / 9))]

theorem singlePair280 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node280 node280Labels = Sparse.eval singlePairValue280 (familyPairVector B) := by
  have hp := single_label_three B hB node280
  have hl : node280Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node280 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node280 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node280 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node280 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node280 (EqualityPatterns.family3.label 1) = PairSemantics.raw5153 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node280 PairSemantics.raw5153; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5153 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node280 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node280 (EqualityPatterns.family3.label 2) = PairSemantics.raw7641 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node280 PairSemantics.raw7641; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7641 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node280 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value380 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node280 (EqualityPatterns.family3.label 3) = PairSemantics.raw847 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node280 PairSemantics.raw847; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical847 hH).trans (PairSemantics.sound380 hH)
  have hm4 : familyPairMoment B (groupedColumns node280 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1864 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node280 (EqualityPatterns.family3.label 4) = PairSemantics.raw606 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node280 PairSemantics.raw606; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical606 hH).trans (PairSemantics.sound1864 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue280, PairSemantics.value0, PairSemantics.value46, PairSemantics.value380, PairSemantics.value1864, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue281 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-55 / 864)), (2, (5 / 288)), (5, (5 / 108)), (6, (-5 / 432)), (9, (5 / 216)), (51, (-5 / 18)), (68, (-5 / 72)), (123, (-5 / 18)), (124, (-5 / 18)), (259, (-5 / 18))]

theorem singlePair281 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node281 node281Labels = Sparse.eval singlePairValue281 (familyPairVector B) := by
  have hp := single_label_three B hB node281
  have hl : node281Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node281 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node281 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node281 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node281 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node281 (EqualityPatterns.family3.label 1) = PairSemantics.raw5157 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node281 PairSemantics.raw5157; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5157 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node281 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node281 (EqualityPatterns.family3.label 2) = PairSemantics.raw7638 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node281 PairSemantics.raw7638; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7638 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node281 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value116 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node281 (EqualityPatterns.family3.label 3) = PairSemantics.raw848 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node281 PairSemantics.raw848; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical848 hH).trans (PairSemantics.sound116 hH)
  have hm4 : familyPairMoment B (groupedColumns node281 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value528 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node281 (EqualityPatterns.family3.label 4) = PairSemantics.raw607 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node281 PairSemantics.raw607; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical607 hH).trans (PairSemantics.sound528 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue281, PairSemantics.value0, PairSemantics.value46, PairSemantics.value116, PairSemantics.value528, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue282 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-25 / 432)), (2, (5 / 432)), (5, (5 / 216)), (27, (-5 / 72)), (68, (-5 / 36)), (487, (5 / 9))]

theorem singlePair282 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node282 node282Labels = Sparse.eval singlePairValue282 (familyPairVector B) := by
  have hp := single_label_three B hB node282
  have hl : node282Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node282 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node282 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node282 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node282 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node282 (EqualityPatterns.family3.label 1) = PairSemantics.raw5157 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node282 PairSemantics.raw5157; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5157 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node282 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node282 (EqualityPatterns.family3.label 2) = PairSemantics.raw7640 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node282 PairSemantics.raw7640; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7640 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node282 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value117 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node282 (EqualityPatterns.family3.label 3) = PairSemantics.raw849 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node282 PairSemantics.raw849; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical849 hH).trans (PairSemantics.sound117 hH)
  have hm4 : familyPairMoment B (groupedColumns node282 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value534 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node282 (EqualityPatterns.family3.label 4) = PairSemantics.raw608 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node282 PairSemantics.raw608; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical608 hH).trans (PairSemantics.sound534 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue282, PairSemantics.value0, PairSemantics.value46, PairSemantics.value117, PairSemantics.value534, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue283 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (55 / 864)), (2, (-25 / 432)), (3, (-5 / 18)), (4, (-5 / 54)), (5, (-5 / 72)), (6, (5 / 288)), (7, (-5 / 27)), (8, (-5 / 27)), (9, (-5 / 216)), (24, (5 / 9)), (27, (5 / 36)), (51, (5 / 18)), (52, (-5 / 54)), (68, (25 / 72)), (69, (-5 / 54)), (124, (5 / 18)), (126, (10 / 9))]

theorem singlePair283 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node283 node283Labels = Sparse.eval singlePairValue283 (familyPairVector B) := by
  have hp := single_label_three B hB node283
  have hl : node283Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node283 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node283 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node283 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node283 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node283 (EqualityPatterns.family3.label 1) = PairSemantics.raw5164 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node283 PairSemantics.raw5164; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5164 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node283 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node283 (EqualityPatterns.family3.label 2) = PairSemantics.raw7633 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node283 PairSemantics.raw7633; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7633 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node283 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value380 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node283 (EqualityPatterns.family3.label 3) = PairSemantics.raw847 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node283 PairSemantics.raw847; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical847 hH).trans (PairSemantics.sound380 hH)
  have hm4 : familyPairMoment B (groupedColumns node283 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1871 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node283 (EqualityPatterns.family3.label 4) = PairSemantics.raw609 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node283 PairSemantics.raw609; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical609 hH).trans (PairSemantics.sound1871 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue283, PairSemantics.value0, PairSemantics.value11, PairSemantics.value232, PairSemantics.value380, PairSemantics.value1871, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue284 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (95 / 864)), (2, (-5 / 288)), (3, (5 / 54)), (6, (-5 / 432)), (7, (5 / 27)), (9, (5 / 216)), (68, (-5 / 72)), (69, (5 / 54)), (124, (-5 / 18))]

theorem singlePair284 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node284 node284Labels = Sparse.eval singlePairValue284 (familyPairVector B) := by
  have hp := single_label_three B hB node284
  have hl : node284Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node284 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node284 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node284 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node284 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node284 (EqualityPatterns.family3.label 1) = PairSemantics.raw5165 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node284 PairSemantics.raw5165; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5165 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node284 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node284 (EqualityPatterns.family3.label 2) = PairSemantics.raw7634 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node284 PairSemantics.raw7634; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7634 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node284 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value116 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node284 (EqualityPatterns.family3.label 3) = PairSemantics.raw848 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node284 PairSemantics.raw848; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical848 hH).trans (PairSemantics.sound116 hH)
  have hm4 : familyPairMoment B (groupedColumns node284 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value541 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node284 (EqualityPatterns.family3.label 4) = PairSemantics.raw610 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node284 PairSemantics.raw610; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical610 hH).trans (PairSemantics.sound541 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue284, PairSemantics.value0, PairSemantics.value4, PairSemantics.value116, PairSemantics.value232, PairSemantics.value541, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue285 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (-25 / 432)), (2, (35 / 864)), (3, (5 / 54)), (6, (-5 / 432)), (7, (5 / 54)), (9, (5 / 216)), (52, (5 / 54)), (68, (-5 / 72)), (69, (5 / 54)), (126, (-5 / 18))]

theorem singlePair285 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node285 node285Labels = Sparse.eval singlePairValue285 (familyPairVector B) := by
  have hp := single_label_three B hB node285
  have hl : node285Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node285 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node285 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node285 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node285 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node285 (EqualityPatterns.family3.label 1) = PairSemantics.raw5167 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node285 PairSemantics.raw5167; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5167 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node285 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node285 (EqualityPatterns.family3.label 2) = PairSemantics.raw7631 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node285 PairSemantics.raw7631; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7631 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node285 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value116 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node285 (EqualityPatterns.family3.label 3) = PairSemantics.raw848 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node285 PairSemantics.raw848; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical848 hH).trans (PairSemantics.sound116 hH)
  have hm4 : familyPairMoment B (groupedColumns node285 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value544 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node285 (EqualityPatterns.family3.label 4) = PairSemantics.raw611 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node285 PairSemantics.raw611; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical611 hH).trans (PairSemantics.sound544 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue285, PairSemantics.value0, PairSemantics.value11, PairSemantics.value46, PairSemantics.value116, PairSemantics.value544, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue286 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (25 / 288)), (2, (5 / 864)), (3, (5 / 54)), (5, (5 / 216)), (7, (5 / 54)), (23, (-5 / 18)), (27, (-5 / 72)), (68, (-5 / 36)), (124, (-5 / 18)), (125, (-5 / 18))]

theorem singlePair286 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node286 node286Labels = Sparse.eval singlePairValue286 (familyPairVector B) := by
  have hp := single_label_three B hB node286
  have hl : node286Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node286 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node286 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node286 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node286 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node286 (EqualityPatterns.family3.label 1) = PairSemantics.raw5165 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node286 PairSemantics.raw5165; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5165 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node286 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node286 (EqualityPatterns.family3.label 2) = PairSemantics.raw7637 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node286 PairSemantics.raw7637; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7637 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node286 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value117 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node286 (EqualityPatterns.family3.label 3) = PairSemantics.raw849 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node286 PairSemantics.raw849; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical849 hH).trans (PairSemantics.sound117 hH)
  have hm4 : familyPairMoment B (groupedColumns node286 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value542 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node286 (EqualityPatterns.family3.label 4) = PairSemantics.raw612 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node286 PairSemantics.raw612; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical612 hH).trans (PairSemantics.sound542 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue286, PairSemantics.value0, PairSemantics.value4, PairSemantics.value46, PairSemantics.value117, PairSemantics.value542, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue287 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 432)), (2, (-5 / 432)), (5, (5 / 216)), (8, (5 / 54)), (24, (-5 / 18)), (27, (-5 / 72)), (68, (-5 / 36)), (126, (-5 / 9))]

theorem singlePair287 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node287 node287Labels = Sparse.eval singlePairValue287 (familyPairVector B) := by
  have hp := single_label_three B hB node287
  have hl : node287Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node287 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node287 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node287 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node287 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node287 (EqualityPatterns.family3.label 1) = PairSemantics.raw5167 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node287 PairSemantics.raw5167; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5167 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node287 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node287 (EqualityPatterns.family3.label 2) = PairSemantics.raw7634 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node287 PairSemantics.raw7634; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7634 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node287 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value117 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node287 (EqualityPatterns.family3.label 3) = PairSemantics.raw849 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node287 PairSemantics.raw849; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical849 hH).trans (PairSemantics.sound117 hH)
  have hm4 : familyPairMoment B (groupedColumns node287 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value545 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node287 (EqualityPatterns.family3.label 4) = PairSemantics.raw613 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node287 PairSemantics.raw613; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical613 hH).trans (PairSemantics.sound545 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue287, PairSemantics.value0, PairSemantics.value11, PairSemantics.value117, PairSemantics.value232, PairSemantics.value545, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue288 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 72)), (2, (-5 / 144)), (5, (5 / 216)), (27, (-5 / 72)), (55, (-5 / 18)), (64, (-5 / 18)), (68, (-5 / 36)), (125, (-5 / 18)), (266, (-5 / 18))]

theorem singlePair288 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node288 node288Labels = Sparse.eval singlePairValue288 (familyPairVector B) := by
  have hp := single_label_three B hB node288
  have hl : node288Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node288 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node288 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node288 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node288 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node288 (EqualityPatterns.family3.label 1) = PairSemantics.raw5173 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node288 PairSemantics.raw5173; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5173 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node288 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node288 (EqualityPatterns.family3.label 2) = PairSemantics.raw7628 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node288 PairSemantics.raw7628; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7628 hH).trans (PairSemantics.sound10 hH)
  have hm3 : familyPairMoment B (groupedColumns node288 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value117 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node288 (EqualityPatterns.family3.label 3) = PairSemantics.raw849 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node288 PairSemantics.raw849; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical849 hH).trans (PairSemantics.sound117 hH)
  have hm4 : familyPairMoment B (groupedColumns node288 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value353 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node288 (EqualityPatterns.family3.label 4) = PairSemantics.raw614 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node288 PairSemantics.raw614; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical614 hH).trans (PairSemantics.sound353 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue288, PairSemantics.value0, PairSemantics.value10, PairSemantics.value46, PairSemantics.value117, PairSemantics.value353, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue289 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (-35 / 432)), (2, (5 / 864)), (5, (5 / 216)), (51, (-5 / 18)), (68, (-5 / 36)), (124, (-5 / 18)), (126, (-5 / 18))]

theorem singlePair289 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node289 node289Labels = Sparse.eval singlePairValue289 (familyPairVector B) := by
  have hp := single_label_three B hB node289
  have hl : node289Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node289 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node289 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node289 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node289 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node289 (EqualityPatterns.family3.label 1) = PairSemantics.raw5175 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node289 PairSemantics.raw5175; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5175 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node289 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node289 (EqualityPatterns.family3.label 2) = PairSemantics.raw7626 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node289 PairSemantics.raw7626; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7626 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node289 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value117 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node289 (EqualityPatterns.family3.label 3) = PairSemantics.raw849 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node289 PairSemantics.raw849; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical849 hH).trans (PairSemantics.sound117 hH)
  have hm4 : familyPairMoment B (groupedColumns node289 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value547 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node289 (EqualityPatterns.family3.label 4) = PairSemantics.raw615 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node289 PairSemantics.raw615; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical615 hH).trans (PairSemantics.sound547 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue289, PairSemantics.value0, PairSemantics.value11, PairSemantics.value46, PairSemantics.value117, PairSemantics.value547, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue290 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (25 / 216)), (2, (5 / 432)), (68, (5 / 36)), (124, (5 / 9))]

theorem singlePair290 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node290 node290Labels = Sparse.eval singlePairValue290 (familyPairVector B) := by
  have hp := single_label_three B hB node290
  have hl : node290Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node290 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node290 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node290 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node290 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node290 (EqualityPatterns.family3.label 1) = PairSemantics.raw5169 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node290 PairSemantics.raw5169; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5169 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node290 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node290 (EqualityPatterns.family3.label 2) = PairSemantics.raw7639 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node290 PairSemantics.raw7639; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7639 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node290 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value23 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node290 (EqualityPatterns.family3.label 3) = PairSemantics.raw852 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node290 PairSemantics.raw852; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical852 hH).trans (PairSemantics.sound23 hH)
  have hm4 : familyPairMoment B (groupedColumns node290 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value162 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node290 (EqualityPatterns.family3.label 4) = PairSemantics.raw616 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node290 PairSemantics.raw616; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical616 hH).trans (PairSemantics.sound162 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue290, PairSemantics.value0, PairSemantics.value4, PairSemantics.value23, PairSemantics.value46, PairSemantics.value162, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue291 : Sparse (Fin 909) := [(0, (37 / 864)), (1, (-5 / 108)), (2, (5 / 216)), (5, (5 / 108)), (6, (-5 / 108)), (8, (-5 / 27)), (9, (-5 / 216)), (58, (5 / 864)), (68, (5 / 72)), (71, (-5 / 27)), (236, (5 / 18))]

theorem singlePair291 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node291 node291Labels = Sparse.eval singlePairValue291 (familyPairVector B) := by
  have hp := single_label_three B hB node291
  have hl : node291Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node291 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node291 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node291 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node291 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node291 (EqualityPatterns.family3.label 1) = PairSemantics.raw5123 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node291 PairSemantics.raw5123; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5123 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node291 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node291 (EqualityPatterns.family3.label 2) = PairSemantics.raw7702 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node291 PairSemantics.raw7702; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7702 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node291 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value381 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node291 (EqualityPatterns.family3.label 3) = PairSemantics.raw854 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node291 PairSemantics.raw854; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical854 hH).trans (PairSemantics.sound381 hH)
  have hm4 : familyPairMoment B (groupedColumns node291 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2458 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node291 (EqualityPatterns.family3.label 4) = PairSemantics.raw617 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node291 PairSemantics.raw617; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical617 hH).trans (PairSemantics.sound2458 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue291, PairSemantics.value0, PairSemantics.value46, PairSemantics.value65, PairSemantics.value381, PairSemantics.value2458, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue292 : Sparse (Fin 909) := [(0, (17 / 864)), (1, (-5 / 108)), (2, (-65 / 864)), (3, (-10 / 27)), (6, (-25 / 864)), (7, (-5 / 54)), (9, (-5 / 108)), (12, (-5 / 54)), (13, (-10 / 27)), (35, (-5 / 27)), (51, (5 / 18)), (52, (-10 / 27)), (58, (5 / 864)), (68, (5 / 72)), (69, (-5 / 54)), (126, (5 / 18)), (128, (-5 / 54)), (262, (5 / 18)), (495, (-5 / 54))]

theorem singlePair292 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node292 node292Labels = Sparse.eval singlePairValue292 (familyPairVector B) := by
  have hp := single_label_three B hB node292
  have hl : node292Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node292 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node292 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node292 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node292 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node292 (EqualityPatterns.family3.label 1) = PairSemantics.raw5124 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node292 PairSemantics.raw5124; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5124 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node292 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node292 (EqualityPatterns.family3.label 2) = PairSemantics.raw7701 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node292 PairSemantics.raw7701; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7701 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node292 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value381 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node292 (EqualityPatterns.family3.label 3) = PairSemantics.raw854 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node292 PairSemantics.raw854; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical854 hH).trans (PairSemantics.sound381 hH)
  have hm4 : familyPairMoment B (groupedColumns node292 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1850 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node292 (EqualityPatterns.family3.label 4) = PairSemantics.raw618 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node292 PairSemantics.raw618; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical618 hH).trans (PairSemantics.sound1850 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue292, PairSemantics.value0, PairSemantics.value46, PairSemantics.value232, PairSemantics.value381, PairSemantics.value1850, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue293 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-55 / 864)), (2, (-25 / 432)), (3, (-5 / 27)), (5, (5 / 54)), (6, (5 / 288)), (7, (-5 / 27)), (8, (-5 / 27)), (9, (-5 / 108)), (52, (-5 / 54)), (68, (5 / 36)), (69, (-5 / 54)), (71, (-5 / 54)), (126, (5 / 18)), (236, (5 / 18))]

theorem singlePair293 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node293 node293Labels = Sparse.eval singlePairValue293 (familyPairVector B) := by
  have hp := single_label_three B hB node293
  have hl : node293Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node293 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node293 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node293 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node293 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node293 (EqualityPatterns.family3.label 1) = PairSemantics.raw5123 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node293 PairSemantics.raw5123; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5123 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node293 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node293 (EqualityPatterns.family3.label 2) = PairSemantics.raw7704 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node293 PairSemantics.raw7704; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7704 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node293 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value382 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node293 (EqualityPatterns.family3.label 3) = PairSemantics.raw855 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node293 PairSemantics.raw855; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical855 hH).trans (PairSemantics.sound382 hH)
  have hm4 : familyPairMoment B (groupedColumns node293 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2460 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node293 (EqualityPatterns.family3.label 4) = PairSemantics.raw619 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node293 PairSemantics.raw619; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical619 hH).trans (PairSemantics.sound2460 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue293, PairSemantics.value0, PairSemantics.value46, PairSemantics.value65, PairSemantics.value382, PairSemantics.value2460, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue294 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (5 / 288)), (2, (-5 / 108)), (3, (-5 / 27)), (6, (-35 / 864)), (7, (-5 / 54)), (8, (-5 / 27)), (9, (-5 / 216)), (52, (-5 / 27)), (58, (5 / 864)), (68, (5 / 72)), (69, (-5 / 54)), (71, (-5 / 54)), (126, (5 / 18))]

theorem singlePair294 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node294 node294Labels = Sparse.eval singlePairValue294 (familyPairVector B) := by
  have hp := single_label_three B hB node294
  have hl : node294Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node294 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node294 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node294 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node294 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node294 (EqualityPatterns.family3.label 1) = PairSemantics.raw5127 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node294 PairSemantics.raw5127; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5127 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node294 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node294 (EqualityPatterns.family3.label 2) = PairSemantics.raw7698 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node294 PairSemantics.raw7698; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7698 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node294 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value381 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node294 (EqualityPatterns.family3.label 3) = PairSemantics.raw854 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node294 PairSemantics.raw854; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical854 hH).trans (PairSemantics.sound381 hH)
  have hm4 : familyPairMoment B (groupedColumns node294 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1876 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node294 (EqualityPatterns.family3.label 4) = PairSemantics.raw620 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node294 PairSemantics.raw620; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical620 hH).trans (PairSemantics.sound1876 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue294, PairSemantics.value0, PairSemantics.value11, PairSemantics.value232, PairSemantics.value381, PairSemantics.value1876, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue295 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (-5 / 216)), (2, (-5 / 144)), (3, (-25 / 54)), (4, (-5 / 54)), (5, (5 / 108)), (6, (5 / 288)), (7, (-5 / 18)), (9, (-5 / 108)), (24, (5 / 18)), (26, (-5 / 27)), (27, (5 / 72)), (35, (-5 / 18)), (52, (-5 / 54)), (68, (5 / 36)), (69, (-5 / 54)), (70, (-5 / 54)), (126, (5 / 18)), (197, (5 / 18))]

theorem singlePair295 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node295 node295Labels = Sparse.eval singlePairValue295 (familyPairVector B) := by
  have hp := single_label_three B hB node295
  have hl : node295Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node295 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node295 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node295 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node295 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node295 (EqualityPatterns.family3.label 1) = PairSemantics.raw5126 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node295 PairSemantics.raw5126; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5126 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node295 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node295 (EqualityPatterns.family3.label 2) = PairSemantics.raw7700 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node295 PairSemantics.raw7700; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7700 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node295 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value382 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node295 (EqualityPatterns.family3.label 3) = PairSemantics.raw855 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node295 PairSemantics.raw855; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical855 hH).trans (PairSemantics.sound382 hH)
  have hm4 : familyPairMoment B (groupedColumns node295 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2114 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node295 (EqualityPatterns.family3.label 4) = PairSemantics.raw621 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node295 PairSemantics.raw621; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical621 hH).trans (PairSemantics.sound2114 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue295, PairSemantics.value0, PairSemantics.value11, PairSemantics.value46, PairSemantics.value382, PairSemantics.value2114, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
