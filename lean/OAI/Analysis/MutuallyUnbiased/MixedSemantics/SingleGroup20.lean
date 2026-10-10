import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleRules
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical161
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical239
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical240
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound8

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue328 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 288)), (2, (55 / 864)), (3, (5 / 27)), (5, (-5 / 108)), (7, (5 / 54)), (26, (5 / 27)), (34, (5 / 54)), (35, (5 / 54)), (64, (-5 / 18)), (67, (5 / 54))]

theorem singlePair328 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node328 node328Labels = Sparse.eval singlePairValue328 (familyPairVector B) := by
  have hp := single_label_three B hB node328
  have hl : node328Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node328 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node328 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node328 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node328 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node328 (EqualityPatterns.family3.label 1) = PairSemantics.raw5173 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node328 PairSemantics.raw5173; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5173 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node328 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node328 (EqualityPatterns.family3.label 2) = PairSemantics.raw7664 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node328 PairSemantics.raw7664; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7664 hH).trans (PairSemantics.sound26 hH)
  have hm3 : familyPairMoment B (groupedColumns node328 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node328 (EqualityPatterns.family3.label 3) = PairSemantics.raw861 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node328 PairSemantics.raw861; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical861 hH).trans (PairSemantics.sound25 hH)
  have hm4 : familyPairMoment B (groupedColumns node328 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value360 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node328 (EqualityPatterns.family3.label 4) = PairSemantics.raw655 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node328 PairSemantics.raw655; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical655 hH).trans (PairSemantics.sound360 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue328, PairSemantics.value0, PairSemantics.value25, PairSemantics.value26, PairSemantics.value46, PairSemantics.value360, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue329 : Sparse (Fin 909) := [(0, (19 / 864)), (1, (25 / 864)), (2, (5 / 108)), (3, (5 / 54)), (5, (-5 / 72)), (7, (5 / 54)), (8, (5 / 54)), (51, (-5 / 18))]

theorem singlePair329 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node329 node329Labels = Sparse.eval singlePairValue329 (familyPairVector B) := by
  have hp := single_label_three B hB node329
  have hl : node329Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node329 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node329 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node329 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node329 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node329 (EqualityPatterns.family3.label 1) = PairSemantics.raw5175 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node329 PairSemantics.raw5175; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5175 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node329 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node329 (EqualityPatterns.family3.label 2) = PairSemantics.raw7661 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node329 PairSemantics.raw7661; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7661 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node329 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node329 (EqualityPatterns.family3.label 3) = PairSemantics.raw861 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node329 PairSemantics.raw861; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical861 hH).trans (PairSemantics.sound25 hH)
  have hm4 : familyPairMoment B (groupedColumns node329 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value561 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node329 (EqualityPatterns.family3.label 4) = PairSemantics.raw656 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node329 PairSemantics.raw656; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical656 hH).trans (PairSemantics.sound561 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue329, PairSemantics.value0, PairSemantics.value11, PairSemantics.value25, PairSemantics.value232, PairSemantics.value561, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue330 : Sparse (Fin 909) := [(0, (23 / 864)), (1, (-5 / 864)), (2, (-55 / 864)), (3, (-5 / 6)), (4, (-5 / 18)), (5, (-5 / 72)), (6, (5 / 288)), (7, (-5 / 54)), (12, (-5 / 54)), (13, (-5 / 54)), (26, (-25 / 54)), (33, (5 / 18)), (34, (-5 / 27)), (35, (-5 / 27)), (67, (-5 / 54)), (81, (5 / 18))]

theorem singlePair330 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node330 node330Labels = Sparse.eval singlePairValue330 (familyPairVector B) := by
  have hp := single_label_three B hB node330
  have hl : node330Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node330 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node330 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node330 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node330 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node330 (EqualityPatterns.family3.label 1) = PairSemantics.raw5153 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node330 PairSemantics.raw5153; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5153 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node330 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node330 (EqualityPatterns.family3.label 2) = PairSemantics.raw7689 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node330 PairSemantics.raw7689; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7689 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node330 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value383 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node330 (EqualityPatterns.family3.label 3) = PairSemantics.raw866 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node330 PairSemantics.raw866; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical866 hH).trans (PairSemantics.sound383 hH)
  have hm4 : familyPairMoment B (groupedColumns node330 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1866 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node330 (EqualityPatterns.family3.label 4) = PairSemantics.raw657 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node330 PairSemantics.raw657; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical657 hH).trans (PairSemantics.sound1866 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue330, PairSemantics.value0, PairSemantics.value46, PairSemantics.value232, PairSemantics.value383, PairSemantics.value1866, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue331 : Sparse (Fin 909) := [(0, (17 / 864)), (1, (25 / 216)), (2, (-25 / 216)), (3, (-10 / 9)), (4, (-5 / 9)), (5, (-5 / 108)), (6, (5 / 288)), (7, (-5 / 18)), (26, (-5 / 9)), (35, (-5 / 27))]

theorem singlePair331 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node331 node331Labels = Sparse.eval singlePairValue331 (familyPairVector B) := by
  have hp := single_label_three B hB node331
  have hl : node331Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node331 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node331 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node331 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node331 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node331 (EqualityPatterns.family3.label 1) = PairSemantics.raw5156 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node331 PairSemantics.raw5156; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5156 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node331 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node331 (EqualityPatterns.family3.label 2) = PairSemantics.raw7687 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node331 PairSemantics.raw7687; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7687 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node331 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value383 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node331 (EqualityPatterns.family3.label 3) = PairSemantics.raw866 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node331 PairSemantics.raw866; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical866 hH).trans (PairSemantics.sound383 hH)
  have hm4 : familyPairMoment B (groupedColumns node331 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2303 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node331 (EqualityPatterns.family3.label 4) = PairSemantics.raw658 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node331 PairSemantics.raw658; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical658 hH).trans (PairSemantics.sound2303 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue331, PairSemantics.value0, PairSemantics.value11, PairSemantics.value232, PairSemantics.value383, PairSemantics.value2303, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue332 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-5 / 54)), (2, (5 / 288)), (3, (5 / 18)), (4, (5 / 54)), (5, (5 / 216)), (6, (-5 / 864)), (7, (5 / 54)), (26, (5 / 27)), (35, (5 / 54))]

theorem singlePair332 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node332 node332Labels = Sparse.eval singlePairValue332 (familyPairVector B) := by
  have hp := single_label_three B hB node332
  have hl : node332Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node332 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node332 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node332 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node332 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node332 (EqualityPatterns.family3.label 1) = PairSemantics.raw5157 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node332 PairSemantics.raw5157; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5157 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node332 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node332 (EqualityPatterns.family3.label 2) = PairSemantics.raw7686 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node332 PairSemantics.raw7686; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7686 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node332 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node332 (EqualityPatterns.family3.label 3) = PairSemantics.raw867 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node332 PairSemantics.raw867; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical867 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node332 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value702 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node332 (EqualityPatterns.family3.label 4) = PairSemantics.raw659 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node332 PairSemantics.raw659; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical659 hH).trans (PairSemantics.sound702 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue332, PairSemantics.value0, PairSemantics.value11, PairSemantics.value46, PairSemantics.value118, PairSemantics.value702, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue333 : Sparse (Fin 909) := [(0, (7 / 432)), (1, (5 / 108)), (2, (25 / 864)), (3, (5 / 27)), (4, (5 / 54)), (5, (5 / 216)), (6, (-5 / 864)), (26, (5 / 54)), (33, (-5 / 18)), (81, (-5 / 18))]

theorem singlePair333 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node333 node333Labels = Sparse.eval singlePairValue333 (familyPairVector B) := by
  have hp := single_label_three B hB node333
  have hl : node333Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node333 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node333 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node333 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node333 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node333 (EqualityPatterns.family3.label 1) = PairSemantics.raw5159 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node333 PairSemantics.raw5159; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5159 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node333 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node333 (EqualityPatterns.family3.label 2) = PairSemantics.raw7684 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node333 PairSemantics.raw7684; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7684 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node333 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node333 (EqualityPatterns.family3.label 3) = PairSemantics.raw867 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node333 PairSemantics.raw867; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical867 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node333 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value535 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node333 (EqualityPatterns.family3.label 4) = PairSemantics.raw660 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node333 PairSemantics.raw660; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical660 hH).trans (PairSemantics.sound535 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue333, PairSemantics.value0, PairSemantics.value46, PairSemantics.value118, PairSemantics.value232, PairSemantics.value535, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue334 : Sparse (Fin 909) := [(0, (49 / 864)), (1, (-35 / 432)), (2, (-55 / 432)), (3, (-5 / 27)), (6, (5 / 288)), (7, (-5 / 54)), (8, (-5 / 27))]

theorem singlePair334 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node334 node334Labels = Sparse.eval singlePairValue334 (familyPairVector B) := by
  have hp := single_label_three B hB node334
  have hl : node334Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node334 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node334 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node334 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node334 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node334 (EqualityPatterns.family3.label 1) = PairSemantics.raw5164 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node334 PairSemantics.raw5164; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5164 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node334 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node334 (EqualityPatterns.family3.label 2) = PairSemantics.raw7680 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node334 PairSemantics.raw7680; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7680 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node334 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value383 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node334 (EqualityPatterns.family3.label 3) = PairSemantics.raw866 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node334 PairSemantics.raw866; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical866 hH).trans (PairSemantics.sound383 hH)
  have hm4 : familyPairMoment B (groupedColumns node334 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1884 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node334 (EqualityPatterns.family3.label 4) = PairSemantics.raw662 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node334 PairSemantics.raw662; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical662 hH).trans (PairSemantics.sound1884 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue334, PairSemantics.value0, PairSemantics.value11, PairSemantics.value65, PairSemantics.value383, PairSemantics.value1884, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue335 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (95 / 432)), (2, (-5 / 864)), (3, (5 / 54)), (6, (-5 / 864)), (7, (5 / 54))]

theorem singlePair335 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node335 node335Labels = Sparse.eval singlePairValue335 (familyPairVector B) := by
  have hp := single_label_three B hB node335
  have hl : node335Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node335 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node335 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node335 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node335 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node335 (EqualityPatterns.family3.label 1) = PairSemantics.raw5165 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node335 PairSemantics.raw5165; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5165 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node335 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node335 (EqualityPatterns.family3.label 2) = PairSemantics.raw7679 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node335 PairSemantics.raw7679; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7679 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node335 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node335 (EqualityPatterns.family3.label 3) = PairSemantics.raw867 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node335 PairSemantics.raw867; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical867 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node335 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value555 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node335 (EqualityPatterns.family3.label 4) = PairSemantics.raw663 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node335 PairSemantics.raw663; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical663 hH).trans (PairSemantics.sound555 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue335, PairSemantics.value0, PairSemantics.value4, PairSemantics.value65, PairSemantics.value118, PairSemantics.value555, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue336 : Sparse (Fin 909) := [(0, (47 / 864)), (1, (-5 / 216)), (2, (5 / 144)), (6, (-5 / 864)), (8, (5 / 54))]

theorem singlePair336 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node336 node336Labels = Sparse.eval singlePairValue336 (familyPairVector B) := by
  have hp := single_label_three B hB node336
  have hl : node336Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node336 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node336 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node336 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node336 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node336 (EqualityPatterns.family3.label 1) = PairSemantics.raw5167 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node336 PairSemantics.raw5167; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5167 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node336 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node336 (EqualityPatterns.family3.label 2) = PairSemantics.raw7677 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node336 PairSemantics.raw7677; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7677 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node336 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node336 (EqualityPatterns.family3.label 3) = PairSemantics.raw867 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node336 PairSemantics.raw867; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical867 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node336 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value560 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node336 (EqualityPatterns.family3.label 4) = PairSemantics.raw664 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node336 PairSemantics.raw664; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical664 hH).trans (PairSemantics.sound560 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue336, PairSemantics.value0, PairSemantics.value11, PairSemantics.value65, PairSemantics.value118, PairSemantics.value560, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue337 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (65 / 432)), (2, (5 / 864)), (5, (5 / 216)), (6, (-5 / 864)), (7, (5 / 54)), (12, (5 / 54)), (13, (5 / 54)), (35, (5 / 54))]

theorem singlePair337 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node337 node337Labels = Sparse.eval singlePairValue337 (familyPairVector B) := by
  have hp := single_label_three B hB node337
  have hl : node337Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node337 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node337 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node337 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node337 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node337 (EqualityPatterns.family3.label 1) = PairSemantics.raw5170 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node337 PairSemantics.raw5170; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5170 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node337 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node337 (EqualityPatterns.family3.label 2) = PairSemantics.raw7674 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node337 PairSemantics.raw7674; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7674 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node337 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node337 (EqualityPatterns.family3.label 3) = PairSemantics.raw867 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node337 PairSemantics.raw867; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical867 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node337 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value556 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node337 (EqualityPatterns.family3.label 4) = PairSemantics.raw665 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node337 PairSemantics.raw665; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical665 hH).trans (PairSemantics.sound556 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue337, PairSemantics.value0, PairSemantics.value4, PairSemantics.value118, PairSemantics.value232, PairSemantics.value556, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue338 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (25 / 108)), (5, (5 / 108)), (6, (5 / 432))]

theorem singlePair338 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node338 node338Labels = Sparse.eval singlePairValue338 (familyPairVector B) := by
  have hp := single_label_three B hB node338
  have hl : node338Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node338 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node338 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node338 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node338 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node338 (EqualityPatterns.family3.label 1) = PairSemantics.raw5169 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node338 PairSemantics.raw5169; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5169 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node338 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node338 (EqualityPatterns.family3.label 2) = PairSemantics.raw7678 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node338 PairSemantics.raw7678; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7678 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node338 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node338 (EqualityPatterns.family3.label 3) = PairSemantics.raw869 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node338 PairSemantics.raw869; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical869 hH).trans (PairSemantics.sound24 hH)
  have hm4 : familyPairMoment B (groupedColumns node338 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value168 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node338 (EqualityPatterns.family3.label 4) = PairSemantics.raw666 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node338 PairSemantics.raw666; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical666 hH).trans (PairSemantics.sound168 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue338, PairSemantics.value0, PairSemantics.value4, PairSemantics.value24, PairSemantics.value65, PairSemantics.value168, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue339 : Sparse (Fin 909) := [(0, (37 / 864)), (1, (-35 / 432)), (2, (25 / 432)), (3, (5 / 27)), (6, (-5 / 864)), (7, (5 / 54))]

theorem singlePair339 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node339 node339Labels = Sparse.eval singlePairValue339 (familyPairVector B) := by
  have hp := single_label_three B hB node339
  have hl : node339Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node339 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node339 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node339 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node339 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node339 (EqualityPatterns.family3.label 1) = PairSemantics.raw5179 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node339 PairSemantics.raw5179; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5179 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node339 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node339 (EqualityPatterns.family3.label 2) = PairSemantics.raw7669 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node339 PairSemantics.raw7669; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7669 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node339 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node339 (EqualityPatterns.family3.label 3) = PairSemantics.raw867 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node339 PairSemantics.raw867; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical867 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node339 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value562 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node339 (EqualityPatterns.family3.label 4) = PairSemantics.raw667 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node339 PairSemantics.raw667; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical667 hH).trans (PairSemantics.sound562 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue339, PairSemantics.value0, PairSemantics.value11, PairSemantics.value118, PairSemantics.value562, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue340 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (5 / 216)), (2, (5 / 108)), (3, (5 / 18)), (4, (5 / 54)), (5, (5 / 216)), (6, (-5 / 864)), (13, (5 / 54)), (26, (5 / 18)), (34, (5 / 27)), (35, (5 / 54)), (67, (5 / 54))]

theorem singlePair340 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node340 node340Labels = Sparse.eval singlePairValue340 (familyPairVector B) := by
  have hp := single_label_three B hB node340
  have hl : node340Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node340 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node340 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node340 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node340 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node340 (EqualityPatterns.family3.label 1) = PairSemantics.raw5182 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node340 PairSemantics.raw5182; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5182 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node340 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node340 (EqualityPatterns.family3.label 2) = PairSemantics.raw7666 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node340 PairSemantics.raw7666; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7666 hH).trans (PairSemantics.sound26 hH)
  have hm3 : familyPairMoment B (groupedColumns node340 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node340 (EqualityPatterns.family3.label 3) = PairSemantics.raw867 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node340 PairSemantics.raw867; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical867 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node340 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value371 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node340 (EqualityPatterns.family3.label 4) = PairSemantics.raw668 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node340 PairSemantics.raw668; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical668 hH).trans (PairSemantics.sound371 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue340, PairSemantics.value0, PairSemantics.value26, PairSemantics.value46, PairSemantics.value118, PairSemantics.value371, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue341 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-25 / 216)), (2, (-5 / 72)), (5, (5 / 108)), (6, (5 / 432))]

theorem singlePair341 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node341 node341Labels = Sparse.eval singlePairValue341 (familyPairVector B) := by
  have hp := single_label_three B hB node341
  have hl : node341Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node341 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node341 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node341 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node341 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node341 (EqualityPatterns.family3.label 1) = PairSemantics.raw5177 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node341 PairSemantics.raw5177; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5177 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node341 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node341 (EqualityPatterns.family3.label 2) = PairSemantics.raw7671 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node341 PairSemantics.raw7671; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7671 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node341 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node341 (EqualityPatterns.family3.label 3) = PairSemantics.raw869 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node341 PairSemantics.raw869; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical869 hH).trans (PairSemantics.sound24 hH)
  have hm4 : familyPairMoment B (groupedColumns node341 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value174 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node341 (EqualityPatterns.family3.label 4) = PairSemantics.raw669 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node341 PairSemantics.raw669; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical669 hH).trans (PairSemantics.sound174 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue341, PairSemantics.value0, PairSemantics.value11, PairSemantics.value24, PairSemantics.value174, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue342 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 216)), (2, (5 / 432)), (5, (-5 / 108)), (26, (-5 / 27)), (34, (-5 / 27)), (67, (-5 / 27))]

theorem singlePair342 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node342 node342Labels = Sparse.eval singlePairValue342 (familyPairVector B) := by
  have hp := single_label_three B hB node342
  have hl : node342Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node342 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node342 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node342 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node342 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node342 (EqualityPatterns.family3.label 1) = PairSemantics.raw5161 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node342 PairSemantics.raw5161; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5161 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node342 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node342 (EqualityPatterns.family3.label 2) = PairSemantics.raw7690 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node342 PairSemantics.raw7690; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7690 hH).trans (PairSemantics.sound26 hH)
  have hm3 : familyPairMoment B (groupedColumns node342 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node342 (EqualityPatterns.family3.label 3) = PairSemantics.raw872 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node342 PairSemantics.raw872; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical872 hH).trans (PairSemantics.sound25 hH)
  have hm4 : familyPairMoment B (groupedColumns node342 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value108 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node342 (EqualityPatterns.family3.label 4) = PairSemantics.raw670 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node342 PairSemantics.raw670; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical670 hH).trans (PairSemantics.sound108 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue342, PairSemantics.value0, PairSemantics.value10, PairSemantics.value25, PairSemantics.value26, PairSemantics.value108, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue343 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (35 / 216)), (2, (5 / 432)), (3, (-5 / 27)), (5, (-5 / 108)), (7, (-5 / 27))]

theorem singlePair343 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node343 node343Labels = Sparse.eval singlePairValue343 (familyPairVector B) := by
  have hp := single_label_three B hB node343
  have hl : node343Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node343 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node343 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node343 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node343 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node343 (EqualityPatterns.family3.label 1) = PairSemantics.raw5169 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node343 PairSemantics.raw5169; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5169 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node343 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node343 (EqualityPatterns.family3.label 2) = PairSemantics.raw7685 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node343 PairSemantics.raw7685; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7685 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node343 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node343 (EqualityPatterns.family3.label 3) = PairSemantics.raw872 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node343 PairSemantics.raw872; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical872 hH).trans (PairSemantics.sound25 hH)
  have hm4 : familyPairMoment B (groupedColumns node343 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value169 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node343 (EqualityPatterns.family3.label 4) = PairSemantics.raw671 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node343 PairSemantics.raw671; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical671 hH).trans (PairSemantics.sound169 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue343, PairSemantics.value0, PairSemantics.value4, PairSemantics.value11, PairSemantics.value25, PairSemantics.value169, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
