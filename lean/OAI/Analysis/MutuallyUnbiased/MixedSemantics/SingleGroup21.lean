import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleRules
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical159
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical161
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical162
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical238
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical239
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical242
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound8

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue344 : Sparse (Fin 909) := [(0, (1 / 18)), (1, (-5 / 108)), (5, (-5 / 108)), (8, (-5 / 27))]

theorem singlePair344 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node344 node344Labels = Sparse.eval singlePairValue344 (familyPairVector B) := by
  have hp := single_label_three B hB node344
  have hl : node344Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node344 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node344 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node344 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node344 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node344 (EqualityPatterns.family3.label 1) = PairSemantics.raw5177 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node344 PairSemantics.raw5177; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5177 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node344 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node344 (EqualityPatterns.family3.label 2) = PairSemantics.raw7678 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node344 PairSemantics.raw7678; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7678 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node344 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node344 (EqualityPatterns.family3.label 3) = PairSemantics.raw872 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node344 PairSemantics.raw872; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical872 hH).trans (PairSemantics.sound25 hH)
  have hm4 : familyPairMoment B (groupedColumns node344 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value175 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node344 (EqualityPatterns.family3.label 4) = PairSemantics.raw672 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node344 PairSemantics.raw672; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical672 hH).trans (PairSemantics.sound175 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue344, PairSemantics.value0, PairSemantics.value11, PairSemantics.value25, PairSemantics.value65, PairSemantics.value175, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue345 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (5 / 96)), (2, (-95 / 864)), (3, (-25 / 27)), (5, (5 / 108)), (6, (-5 / 864)), (7, (-5 / 54)), (12, (-10 / 27)), (13, (-35 / 54)), (34, (-5 / 54)), (35, (-5 / 54)), (51, (5 / 9)), (52, (-5 / 18)), (54, (5 / 18)), (64, (5 / 18))]

theorem singlePair345 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node345 node345Labels = Sparse.eval singlePairValue345 (familyPairVector B) := by
  have hp := single_label_three B hB node345
  have hl : node345Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node345 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node345 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node345 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node345 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node345 (EqualityPatterns.family3.label 1) = PairSemantics.raw5191 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node345 PairSemantics.raw5191; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5191 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node345 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node345 (EqualityPatterns.family3.label 2) = PairSemantics.raw7629 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node345 PairSemantics.raw7629; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7629 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node345 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node345 (EqualityPatterns.family3.label 3) = PairSemantics.raw859 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node345 PairSemantics.raw859; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical859 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node345 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1863 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node345 (EqualityPatterns.family3.label 4) = PairSemantics.raw673 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node345 PairSemantics.raw673; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical673 hH).trans (PairSemantics.sound1863 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue345, PairSemantics.value0, PairSemantics.value46, PairSemantics.value118, PairSemantics.value232, PairSemantics.value1863, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue346 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-35 / 864)), (2, (5 / 96)), (3, (5 / 54)), (5, (-5 / 108)), (7, (5 / 54)), (51, (-5 / 18)), (54, (-5 / 18)), (64, (-5 / 18))]

theorem singlePair346 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node346 node346Labels = Sparse.eval singlePairValue346 (familyPairVector B) := by
  have hp := single_label_three B hB node346
  have hl : node346Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node346 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node346 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node346 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node346 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node346 (EqualityPatterns.family3.label 1) = PairSemantics.raw5189 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node346 PairSemantics.raw5189; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5189 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node346 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node346 (EqualityPatterns.family3.label 2) = PairSemantics.raw7637 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node346 PairSemantics.raw7637; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7637 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node346 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node346 (EqualityPatterns.family3.label 3) = PairSemantics.raw861 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node346 PairSemantics.raw861; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical861 hH).trans (PairSemantics.sound25 hH)
  have hm4 : familyPairMoment B (groupedColumns node346 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value533 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node346 (EqualityPatterns.family3.label 4) = PairSemantics.raw674 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node346 PairSemantics.raw674; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical674 hH).trans (PairSemantics.sound533 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue346, PairSemantics.value0, PairSemantics.value25, PairSemantics.value46, PairSemantics.value533, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue347 : Sparse (Fin 909) := [(0, (7 / 288)), (2, (-5 / 54)), (3, (-35 / 54)), (4, (-5 / 27)), (5, (-5 / 72)), (6, (5 / 288)), (12, (-5 / 27)), (13, (-5 / 27)), (25, (5 / 18)), (26, (-5 / 27)), (31, (5 / 9)), (33, (5 / 9)), (34, (-5 / 54)), (51, (5 / 9)), (52, (-5 / 54)), (64, (5 / 18)), (123, (5 / 9))]

theorem singlePair347 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node347 node347Labels = Sparse.eval singlePairValue347 (familyPairVector B) := by
  have hp := single_label_three B hB node347
  have hl : node347Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node347 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node347 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node347 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node347 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node347 (EqualityPatterns.family3.label 1) = PairSemantics.raw5188 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node347 PairSemantics.raw5188; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5188 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node347 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node347 (EqualityPatterns.family3.label 2) = PairSemantics.raw7641 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node347 PairSemantics.raw7641; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7641 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node347 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value383 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node347 (EqualityPatterns.family3.label 3) = PairSemantics.raw866 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node347 PairSemantics.raw866; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical866 hH).trans (PairSemantics.sound383 hH)
  have hm4 : familyPairMoment B (groupedColumns node347 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1868 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node347 (EqualityPatterns.family3.label 4) = PairSemantics.raw675 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node347 PairSemantics.raw675; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical675 hH).trans (PairSemantics.sound1868 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue347, PairSemantics.value0, PairSemantics.value46, PairSemantics.value232, PairSemantics.value383, PairSemantics.value1868, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue348 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (-5 / 96)), (2, (35 / 864)), (3, (5 / 54)), (5, (5 / 216)), (6, (-5 / 864)), (25, (-5 / 18)), (26, (5 / 54)), (64, (-5 / 18)), (123, (-5 / 18))]

theorem singlePair348 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node348 node348Labels = Sparse.eval singlePairValue348 (familyPairVector B) := by
  have hp := single_label_three B hB node348
  have hl : node348Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node348 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node348 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node348 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node348 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node348 (EqualityPatterns.family3.label 1) = PairSemantics.raw5189 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node348 PairSemantics.raw5189; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5189 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node348 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node348 (EqualityPatterns.family3.label 2) = PairSemantics.raw7640 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node348 PairSemantics.raw7640; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7640 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node348 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node348 (EqualityPatterns.family3.label 3) = PairSemantics.raw867 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node348 PairSemantics.raw867; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical867 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node348 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value536 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node348 (EqualityPatterns.family3.label 4) = PairSemantics.raw676 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node348 PairSemantics.raw676; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical676 hH).trans (PairSemantics.sound536 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue348, PairSemantics.value0, PairSemantics.value46, PairSemantics.value118, PairSemantics.value536, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue349 : Sparse (Fin 909) := [(0, (5 / 288)), (1, (5 / 216)), (2, (5 / 432)), (5, (5 / 216)), (6, (-5 / 864)), (31, (-5 / 18)), (33, (-5 / 18)), (51, (-5 / 18)), (123, (-5 / 18))]

theorem singlePair349 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node349 node349Labels = Sparse.eval singlePairValue349 (familyPairVector B) := by
  have hp := single_label_three B hB node349
  have hl : node349Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node349 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node349 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node349 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node349 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node349 (EqualityPatterns.family3.label 1) = PairSemantics.raw5190 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node349 PairSemantics.raw5190; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5190 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node349 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node349 (EqualityPatterns.family3.label 2) = PairSemantics.raw7638 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node349 PairSemantics.raw7638; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7638 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node349 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node349 (EqualityPatterns.family3.label 3) = PairSemantics.raw867 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node349 PairSemantics.raw867; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical867 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node349 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value539 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node349 (EqualityPatterns.family3.label 4) = PairSemantics.raw677 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node349 PairSemantics.raw677; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical677 hH).trans (PairSemantics.sound539 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue349, PairSemantics.value0, PairSemantics.value46, PairSemantics.value118, PairSemantics.value232, PairSemantics.value539, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue350 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 144)), (6, (5 / 432)), (123, (5 / 9))]

theorem singlePair350 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node350 node350Labels = Sparse.eval singlePairValue350 (familyPairVector B) := by
  have hp := single_label_three B hB node350
  have hl : node350Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node350 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node350 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node350 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node350 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node350 (EqualityPatterns.family3.label 1) = PairSemantics.raw5192 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node350 PairSemantics.raw5192; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5192 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node350 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node350 (EqualityPatterns.family3.label 2) = PairSemantics.raw7639 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node350 PairSemantics.raw7639; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7639 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node350 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node350 (EqualityPatterns.family3.label 3) = PairSemantics.raw869 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node350 PairSemantics.raw869; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical869 hH).trans (PairSemantics.sound24 hH)
  have hm4 : familyPairMoment B (groupedColumns node350 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value159 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node350 (EqualityPatterns.family3.label 4) = PairSemantics.raw678 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node350 PairSemantics.raw678; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical678 hH).trans (PairSemantics.sound159 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue350, PairSemantics.value0, PairSemantics.value24, PairSemantics.value46, PairSemantics.value159, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue351 : Sparse (Fin 909) := [(0, (25 / 864)), (1, (5 / 144)), (2, (-25 / 144)), (3, (-5 / 6)), (4, (-5 / 18)), (5, (-5 / 72)), (6, (5 / 288)), (12, (-5 / 18)), (13, (-5 / 27)), (51, (5 / 6)), (52, (-5 / 18))]

theorem singlePair351 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node351 node351Labels = Sparse.eval singlePairValue351 (familyPairVector B) := by
  have hp := single_label_three B hB node351
  have hl : node351Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node351 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node351 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node351 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node351 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node351 (EqualityPatterns.family3.label 1) = PairSemantics.raw5195 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node351 PairSemantics.raw5195; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5195 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node351 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node351 (EqualityPatterns.family3.label 2) = PairSemantics.raw7635 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node351 PairSemantics.raw7635; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7635 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node351 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value383 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node351 (EqualityPatterns.family3.label 3) = PairSemantics.raw866 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node351 PairSemantics.raw866; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical866 hH).trans (PairSemantics.sound383 hH)
  have hm4 : familyPairMoment B (groupedColumns node351 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1890 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node351 (EqualityPatterns.family3.label 4) = PairSemantics.raw679 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node351 PairSemantics.raw679; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical679 hH).trans (PairSemantics.sound1890 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue351, PairSemantics.value0, PairSemantics.value11, PairSemantics.value232, PairSemantics.value383, PairSemantics.value1890, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue352 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 432)), (2, (25 / 864)), (3, (5 / 27)), (4, (5 / 54)), (5, (5 / 216)), (6, (-5 / 864)), (51, (-5 / 18)), (52, (5 / 54))]

theorem singlePair352 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node352 node352Labels = Sparse.eval singlePairValue352 (familyPairVector B) := by
  have hp := single_label_three B hB node352
  have hl : node352Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node352 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node352 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node352 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node352 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node352 (EqualityPatterns.family3.label 1) = PairSemantics.raw5196 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node352 PairSemantics.raw5196; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5196 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node352 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node352 (EqualityPatterns.family3.label 2) = PairSemantics.raw7634 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node352 PairSemantics.raw7634; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7634 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node352 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node352 (EqualityPatterns.family3.label 3) = PairSemantics.raw867 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node352 PairSemantics.raw867; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical867 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node352 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value569 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node352 (EqualityPatterns.family3.label 4) = PairSemantics.raw680 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node352 PairSemantics.raw680; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical680 hH).trans (PairSemantics.sound569 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue352, PairSemantics.value0, PairSemantics.value11, PairSemantics.value118, PairSemantics.value232, PairSemantics.value569, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue353 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (-25 / 432)), (2, (5 / 108)), (3, (5 / 27)), (5, (5 / 216)), (6, (-5 / 864)), (12, (5 / 54)), (13, (5 / 54)), (51, (-5 / 18)), (52, (5 / 54))]

theorem singlePair353 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node353 node353Labels = Sparse.eval singlePairValue353 (familyPairVector B) := by
  have hp := single_label_three B hB node353
  have hl : node353Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node353 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node353 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node353 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node353 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node353 (EqualityPatterns.family3.label 1) = PairSemantics.raw5198 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node353 PairSemantics.raw5198; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5198 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node353 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node353 (EqualityPatterns.family3.label 2) = PairSemantics.raw7631 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node353 PairSemantics.raw7631; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7631 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node353 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node353 (EqualityPatterns.family3.label 3) = PairSemantics.raw867 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node353 PairSemantics.raw867; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical867 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node353 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value572 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node353 (EqualityPatterns.family3.label 4) = PairSemantics.raw681 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node353 PairSemantics.raw681; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical681 hH).trans (PairSemantics.sound572 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue353, PairSemantics.value0, PairSemantics.value11, PairSemantics.value46, PairSemantics.value118, PairSemantics.value572, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue354 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 144)), (5, (-5 / 108)), (64, (5 / 9))]

theorem singlePair354 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node354 node354Labels = Sparse.eval singlePairValue354 (familyPairVector B) := by
  have hp := single_label_three B hB node354
  have hl : node354Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node354 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node354 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node354 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node354 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node354 (EqualityPatterns.family3.label 1) = PairSemantics.raw5192 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node354 PairSemantics.raw5192; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5192 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node354 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node354 (EqualityPatterns.family3.label 2) = PairSemantics.raw7643 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node354 PairSemantics.raw7643; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7643 hH).trans (PairSemantics.sound10 hH)
  have hm3 : familyPairMoment B (groupedColumns node354 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node354 (EqualityPatterns.family3.label 3) = PairSemantics.raw872 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node354 PairSemantics.raw872; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical872 hH).trans (PairSemantics.sound25 hH)
  have hm4 : familyPairMoment B (groupedColumns node354 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value103 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node354 (EqualityPatterns.family3.label 4) = PairSemantics.raw682 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node354 PairSemantics.raw682; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical682 hH).trans (PairSemantics.sound103 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue354, PairSemantics.value0, PairSemantics.value10, PairSemantics.value25, PairSemantics.value46, PairSemantics.value103, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue355 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-5 / 144)), (2, (5 / 144)), (5, (-5 / 108)), (51, (5 / 9))]

theorem singlePair355 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node355 node355Labels = Sparse.eval singlePairValue355 (familyPairVector B) := by
  have hp := single_label_three B hB node355
  have hl : node355Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node355 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node355 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node355 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node355 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node355 (EqualityPatterns.family3.label 1) = PairSemantics.raw5197 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node355 PairSemantics.raw5197; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5197 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node355 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node355 (EqualityPatterns.family3.label 2) = PairSemantics.raw7639 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node355 PairSemantics.raw7639; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7639 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node355 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node355 (EqualityPatterns.family3.label 3) = PairSemantics.raw872 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node355 PairSemantics.raw872; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical872 hH).trans (PairSemantics.sound25 hH)
  have hm4 : familyPairMoment B (groupedColumns node355 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value184 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node355 (EqualityPatterns.family3.label 4) = PairSemantics.raw683 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node355 PairSemantics.raw683; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical683 hH).trans (PairSemantics.sound184 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue355, PairSemantics.value0, PairSemantics.value11, PairSemantics.value25, PairSemantics.value46, PairSemantics.value184, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue356 : Sparse (Fin 909) := [(0, (19 / 864)), (1, (-25 / 864)), (2, (25 / 432)), (3, (-5 / 27)), (5, (-5 / 54)), (12, (-5 / 54)), (13, (-5 / 54)), (23, (5 / 9)), (25, (5 / 18)), (26, (-5 / 54)), (27, (5 / 36)), (33, (5 / 18)), (35, (-5 / 54)), (54, (5 / 9)), (55, (5 / 9)), (63, (5 / 9)), (64, (5 / 18)), (65, (5 / 9)), (68, (5 / 18)), (125, (5 / 18)), (196, (5 / 18)), (264, (5 / 18)), (266, (5 / 18))]

theorem singlePair356 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node356 node356Labels = Sparse.eval singlePairValue356 (familyPairVector B) := by
  have hp := single_label_three B hB node356
  have hl : node356Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node356 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node356 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node356 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node356 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value715 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node356 (EqualityPatterns.family3.label 1) = PairSemantics.raw5103 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node356 PairSemantics.raw5103; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5103 hH).trans (PairSemantics.sound715 hH)
  have hm2 : familyPairMoment B (groupedColumns node356 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node356 (EqualityPatterns.family3.label 2) = PairSemantics.raw7759 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node356 PairSemantics.raw7759; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7759 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node356 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node356 (EqualityPatterns.family3.label 3) = PairSemantics.raw879 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node356 PairSemantics.raw879; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical879 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node356 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1415 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node356 (EqualityPatterns.family3.label 4) = PairSemantics.raw689 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node356 PairSemantics.raw689; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical689 hH).trans (PairSemantics.sound1415 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue356, PairSemantics.value0, PairSemantics.value10, PairSemantics.value46, PairSemantics.value715, PairSemantics.value1415, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue357 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 96)), (2, (-25 / 864)), (3, (-20 / 27)), (5, (5 / 216)), (7, (-5 / 54)), (12, (-5 / 18)), (13, (-5 / 9)), (23, (5 / 18)), (26, (-10 / 27)), (27, (-5 / 72)), (34, (-5 / 27)), (35, (-5 / 18)), (55, (5 / 9)), (63, (5 / 18)), (65, (5 / 18)), (67, (-5 / 54))]

theorem singlePair357 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node357 node357Labels = Sparse.eval singlePairValue357 (familyPairVector B) := by
  have hp := single_label_three B hB node357
  have hl : node357Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node357 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node357 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node357 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node357 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value231 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node357 (EqualityPatterns.family3.label 1) = PairSemantics.raw5108 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node357 PairSemantics.raw5108; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5108 hH).trans (PairSemantics.sound231 hH)
  have hm2 : familyPairMoment B (groupedColumns node357 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node357 (EqualityPatterns.family3.label 2) = PairSemantics.raw7752 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node357 PairSemantics.raw7752; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7752 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node357 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node357 (EqualityPatterns.family3.label 3) = PairSemantics.raw879 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node357 PairSemantics.raw879; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical879 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node357 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1417 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node357 (EqualityPatterns.family3.label 4) = PairSemantics.raw691 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node357 PairSemantics.raw691; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical691 hH).trans (PairSemantics.sound1417 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue357, PairSemantics.value0, PairSemantics.value10, PairSemantics.value231, PairSemantics.value232, PairSemantics.value1417, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue358 : Sparse (Fin 909) := [(0, (31 / 864)), (1, (-35 / 432)), (2, (5 / 864)), (3, (-5 / 9)), (5, (-5 / 72)), (12, (-5 / 27)), (13, (-5 / 18)), (25, (5 / 18)), (26, (-5 / 54)), (27, (5 / 24)), (33, (5 / 6)), (35, (-5 / 54)), (55, (5 / 9)), (63, (5 / 18)), (64, (5 / 9))]

theorem singlePair358 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node358 node358Labels = Sparse.eval singlePairValue358 (familyPairVector B) := by
  have hp := single_label_three B hB node358
  have hl : node358Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node358 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node358 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node358 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node358 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value716 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node358 (EqualityPatterns.family3.label 1) = PairSemantics.raw5109 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node358 PairSemantics.raw5109; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5109 hH).trans (PairSemantics.sound716 hH)
  have hm2 : familyPairMoment B (groupedColumns node358 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node358 (EqualityPatterns.family3.label 2) = PairSemantics.raw7750 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node358 PairSemantics.raw7750; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7750 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node358 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node358 (EqualityPatterns.family3.label 3) = PairSemantics.raw879 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node358 PairSemantics.raw879; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical879 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node358 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1418 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node358 (EqualityPatterns.family3.label 4) = PairSemantics.raw692 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node358 PairSemantics.raw692; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical692 hH).trans (PairSemantics.sound1418 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue358, PairSemantics.value0, PairSemantics.value10, PairSemantics.value232, PairSemantics.value716, PairSemantics.value1418, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue359 : Sparse (Fin 909) := [(0, (1 / 48)), (1, (145 / 864)), (2, (-25 / 864)), (3, (-25 / 27)), (4, (-10 / 27)), (5, (5 / 216)), (7, (-5 / 54)), (12, (-5 / 54)), (13, (-5 / 54)), (24, (5 / 18)), (26, (-5 / 9)), (27, (-5 / 72)), (33, (5 / 18)), (34, (-5 / 27)), (35, (-5 / 27)), (55, (5 / 6)), (64, (5 / 18)), (66, (5 / 18)), (67, (-5 / 54))]

theorem singlePair359 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node359 node359Labels = Sparse.eval singlePairValue359 (familyPairVector B) := by
  have hp := single_label_three B hB node359
  have hl : node359Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node359 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node359 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node359 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node359 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value231 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node359 (EqualityPatterns.family3.label 1) = PairSemantics.raw5107 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node359 PairSemantics.raw5107; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5107 hH).trans (PairSemantics.sound231 hH)
  have hm2 : familyPairMoment B (groupedColumns node359 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node359 (EqualityPatterns.family3.label 2) = PairSemantics.raw7756 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node359 PairSemantics.raw7756; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7756 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node359 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node359 (EqualityPatterns.family3.label 3) = PairSemantics.raw883 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node359 PairSemantics.raw883; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical883 hH).trans (PairSemantics.sound26 hH)
  have hm4 : familyPairMoment B (groupedColumns node359 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1419 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node359 (EqualityPatterns.family3.label 4) = PairSemantics.raw694 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node359 PairSemantics.raw694; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical694 hH).trans (PairSemantics.sound1419 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue359, PairSemantics.value0, PairSemantics.value26, PairSemantics.value231, PairSemantics.value232, PairSemantics.value1419, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
