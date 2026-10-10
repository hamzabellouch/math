import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleRules
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical280
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical281
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical282
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound5

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue232 : Sparse (Fin 909) := [(0, (47 / 864)), (1, (-35 / 288)), (2, (-25 / 216)), (3, (-10 / 27)), (5, (-5 / 216)), (6, (5 / 432)), (12, (-5 / 54)), (13, (-10 / 27)), (35, (-5 / 54)), (52, (-5 / 27))]

theorem singlePair232 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node232 node232Labels = Sparse.eval singlePairValue232 (familyPairVector B) := by
  have hp := single_label_three B hB node232
  have hl : node232Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node232 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node232 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node232 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node232 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node232 (EqualityPatterns.family3.label 1) = PairSemantics.raw879 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node232 PairSemantics.raw879; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical879 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node232 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node232 (EqualityPatterns.family3.label 2) = PairSemantics.raw9031 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node232 PairSemantics.raw9031; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9031 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node232 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value383 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node232 (EqualityPatterns.family3.label 3) = PairSemantics.raw866 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node232 PairSemantics.raw866; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical866 hH).trans (PairSemantics.sound383 hH)
  have hm4 : familyPairMoment B (groupedColumns node232 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2790 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node232 (EqualityPatterns.family3.label 4) = PairSemantics.raw437 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node232 PairSemantics.raw437; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical437 hH).trans (PairSemantics.sound2790 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue232, PairSemantics.value0, PairSemantics.value10, PairSemantics.value65, PairSemantics.value383, PairSemantics.value2790, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue233 : Sparse (Fin 909) := [(0, (13 / 288)), (1, (5 / 432)), (2, (185 / 864)), (5, (5 / 216)), (13, (5 / 54)), (35, (5 / 54))]

theorem singlePair233 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node233 node233Labels = Sparse.eval singlePairValue233 (familyPairVector B) := by
  have hp := single_label_three B hB node233
  have hl : node233Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node233 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node233 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node233 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node233 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node233 (EqualityPatterns.family3.label 1) = PairSemantics.raw881 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node233 PairSemantics.raw881; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical881 hH).trans (PairSemantics.sound3 hH)
  have hm2 : familyPairMoment B (groupedColumns node233 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node233 (EqualityPatterns.family3.label 2) = PairSemantics.raw9030 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node233 PairSemantics.raw9030; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9030 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node233 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node233 (EqualityPatterns.family3.label 3) = PairSemantics.raw867 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node233 PairSemantics.raw867; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical867 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node233 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1287 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node233 (EqualityPatterns.family3.label 4) = PairSemantics.raw438 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node233 PairSemantics.raw438; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical438 hH).trans (PairSemantics.sound1287 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue233, PairSemantics.value0, PairSemantics.value3, PairSemantics.value65, PairSemantics.value118, PairSemantics.value1287, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue234 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-5 / 288)), (2, (-5 / 144)), (3, (5 / 54)), (6, (-5 / 864)), (13, (5 / 54)), (52, (5 / 54))]

theorem singlePair234 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node234 node234Labels = Sparse.eval singlePairValue234 (familyPairVector B) := by
  have hp := single_label_three B hB node234
  have hl : node234Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node234 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node234 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node234 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node234 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node234 (EqualityPatterns.family3.label 1) = PairSemantics.raw886 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node234 PairSemantics.raw886; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical886 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node234 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node234 (EqualityPatterns.family3.label 2) = PairSemantics.raw9025 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node234 PairSemantics.raw9025; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9025 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node234 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node234 (EqualityPatterns.family3.label 3) = PairSemantics.raw867 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node234 PairSemantics.raw867; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical867 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node234 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1138 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node234 (EqualityPatterns.family3.label 4) = PairSemantics.raw439 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node234 PairSemantics.raw439; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical439 hH).trans (PairSemantics.sound1138 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue234, PairSemantics.value0, PairSemantics.value10, PairSemantics.value65, PairSemantics.value118, PairSemantics.value1138, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue235 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 108)), (2, (-5 / 288)), (3, (5 / 27)), (5, (5 / 216)), (6, (-5 / 864)), (12, (5 / 54)), (13, (5 / 18)), (35, (5 / 54)), (52, (5 / 54))]

theorem singlePair235 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node235 node235Labels = Sparse.eval singlePairValue235 (familyPairVector B) := by
  have hp := single_label_three B hB node235
  have hl : node235Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node235 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node235 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node235 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node235 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node235 (EqualityPatterns.family3.label 1) = PairSemantics.raw896 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node235 PairSemantics.raw896; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical896 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node235 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node235 (EqualityPatterns.family3.label 2) = PairSemantics.raw9018 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node235 PairSemantics.raw9018; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9018 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node235 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node235 (EqualityPatterns.family3.label 3) = PairSemantics.raw867 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node235 PairSemantics.raw867; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical867 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node235 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value662 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node235 (EqualityPatterns.family3.label 4) = PairSemantics.raw440 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node235 PairSemantics.raw440; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical440 hH).trans (PairSemantics.sound662 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue235, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value118, PairSemantics.value662, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue236 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-35 / 432)), (2, (-35 / 432)), (6, (5 / 432)), (13, (-5 / 27)), (52, (-5 / 27))]

theorem singlePair236 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node236 node236Labels = Sparse.eval singlePairValue236 (familyPairVector B) := by
  have hp := single_label_three B hB node236
  have hl : node236Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node236 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node236 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node236 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node236 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node236 (EqualityPatterns.family3.label 1) = PairSemantics.raw898 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node236 PairSemantics.raw898; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical898 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node236 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node236 (EqualityPatterns.family3.label 2) = PairSemantics.raw9013 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node236 PairSemantics.raw9013; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9013 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node236 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node236 (EqualityPatterns.family3.label 3) = PairSemantics.raw869 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node236 PairSemantics.raw869; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical869 hH).trans (PairSemantics.sound24 hH)
  have hm4 : familyPairMoment B (groupedColumns node236 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value187 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node236 (EqualityPatterns.family3.label 4) = PairSemantics.raw441 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node236 PairSemantics.raw441; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical441 hH).trans (PairSemantics.sound187 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue236, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value24, PairSemantics.value187, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue237 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 216)), (2, (85 / 432)), (5, (-5 / 108)), (13, (-5 / 27)), (35, (-5 / 27))]

theorem singlePair237 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node237 node237Labels = Sparse.eval singlePairValue237 (familyPairVector B) := by
  have hp := single_label_three B hB node237
  have hl : node237Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node237 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node237 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node237 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node237 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node237 (EqualityPatterns.family3.label 1) = PairSemantics.raw887 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node237 PairSemantics.raw887; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical887 hH).trans (PairSemantics.sound3 hH)
  have hm2 : familyPairMoment B (groupedColumns node237 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node237 (EqualityPatterns.family3.label 2) = PairSemantics.raw9032 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node237 PairSemantics.raw9032; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9032 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node237 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node237 (EqualityPatterns.family3.label 3) = PairSemantics.raw872 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node237 PairSemantics.raw872; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical872 hH).trans (PairSemantics.sound25 hH)
  have hm4 : familyPairMoment B (groupedColumns node237 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value214 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node237 (EqualityPatterns.family3.label 4) = PairSemantics.raw442 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node237 PairSemantics.raw442; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical442 hH).trans (PairSemantics.sound214 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue237, PairSemantics.value0, PairSemantics.value3, PairSemantics.value11, PairSemantics.value25, PairSemantics.value214, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue238 : Sparse (Fin 909) := [(0, (25 / 864)), (1, (35 / 864)), (2, (5 / 288)), (3, (-20 / 27)), (4, (-5 / 54)), (5, (5 / 216)), (6, (-5 / 864)), (12, (-10 / 27)), (13, (-25 / 27)), (26, (-5 / 54)), (32, (-5 / 54)), (33, (5 / 18)), (34, (-5 / 54)), (35, (-5 / 27)), (51, (5 / 18)), (52, (-5 / 54)), (54, (5 / 9)), (56, (5 / 18)), (60, (-5 / 54)), (61, (5 / 18)), (62, (5 / 18))]

theorem singlePair238 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node238 node238Labels = Sparse.eval singlePairValue238 (familyPairVector B) := by
  have hp := single_label_three B hB node238
  have hl : node238Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node238 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node238 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node238 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node238 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node238 (EqualityPatterns.family3.label 1) = PairSemantics.raw913 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node238 PairSemantics.raw913; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical913 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node238 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node238 (EqualityPatterns.family3.label 2) = PairSemantics.raw8960 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node238 PairSemantics.raw8960; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8960 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node238 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node238 (EqualityPatterns.family3.label 3) = PairSemantics.raw859 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node238 PairSemantics.raw859; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical859 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node238 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1413 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node238 (EqualityPatterns.family3.label 4) = PairSemantics.raw443 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node238 PairSemantics.raw443; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical443 hH).trans (PairSemantics.sound1413 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue238, PairSemantics.value0, PairSemantics.value26, PairSemantics.value46, PairSemantics.value118, PairSemantics.value1413, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue239 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (35 / 864)), (2, (5 / 864)), (3, (5 / 27)), (6, (5 / 432)), (13, (5 / 27)), (26, (5 / 54)), (34, (5 / 54)), (35, (5 / 27)), (52, (5 / 54)), (60, (5 / 54))]

theorem singlePair239 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node239 node239Labels = Sparse.eval singlePairValue239 (familyPairVector B) := by
  have hp := single_label_three B hB node239
  have hl : node239Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node239 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node239 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node239 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node239 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node239 (EqualityPatterns.family3.label 1) = PairSemantics.raw912 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node239 PairSemantics.raw912; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical912 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node239 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node239 (EqualityPatterns.family3.label 2) = PairSemantics.raw8962 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node239 PairSemantics.raw8962; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8962 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node239 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node239 (EqualityPatterns.family3.label 3) = PairSemantics.raw860 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node239 PairSemantics.raw860; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical860 hH).trans (PairSemantics.sound24 hH)
  have hm4 : familyPairMoment B (groupedColumns node239 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value349 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node239 (EqualityPatterns.family3.label 4) = PairSemantics.raw444 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node239 PairSemantics.raw444; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical444 hH).trans (PairSemantics.sound349 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue239, PairSemantics.value0, PairSemantics.value24, PairSemantics.value26, PairSemantics.value46, PairSemantics.value349, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue240 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 144)), (2, (25 / 432)), (5, (-5 / 108)), (51, (-5 / 18)), (54, (-5 / 18)), (56, (-5 / 18)), (61, (-5 / 18))]

theorem singlePair240 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node240 node240Labels = Sparse.eval singlePairValue240 (familyPairVector B) := by
  have hp := single_label_three B hB node240
  have hl : node240Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node240 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node240 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node240 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node240 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node240 (EqualityPatterns.family3.label 1) = PairSemantics.raw912 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node240 PairSemantics.raw912; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical912 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node240 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node240 (EqualityPatterns.family3.label 2) = PairSemantics.raw8964 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node240 PairSemantics.raw8964; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8964 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node240 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node240 (EqualityPatterns.family3.label 3) = PairSemantics.raw861 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node240 PairSemantics.raw861; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical861 hH).trans (PairSemantics.sound25 hH)
  have hm4 : familyPairMoment B (groupedColumns node240 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value351 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node240 (EqualityPatterns.family3.label 4) = PairSemantics.raw445 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node240 PairSemantics.raw445; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical445 hH).trans (PairSemantics.sound351 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue240, PairSemantics.value0, PairSemantics.value25, PairSemantics.value26, PairSemantics.value46, PairSemantics.value351, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue241 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (35 / 216)), (2, (-5 / 108)), (6, (5 / 216)), (226, (5 / 9))]

theorem singlePair241 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node241 node241Labels = Sparse.eval singlePairValue241 (familyPairVector B) := by
  have hp := single_label_three B hB node241
  have hl : node241Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node241 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node241 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node241 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node241 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node241 (EqualityPatterns.family3.label 1) = PairSemantics.raw903 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node241 PairSemantics.raw903; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical903 hH).trans (PairSemantics.sound24 hH)
  have hm2 : familyPairMoment B (groupedColumns node241 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node241 (EqualityPatterns.family3.label 2) = PairSemantics.raw8987 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node241 PairSemantics.raw8987; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8987 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node241 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node241 (EqualityPatterns.family3.label 3) = PairSemantics.raw869 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node241 PairSemantics.raw869; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical869 hH).trans (PairSemantics.sound24 hH)
  have hm4 : familyPairMoment B (groupedColumns node241 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value220 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node241 (EqualityPatterns.family3.label 4) = PairSemantics.raw446 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node241 PairSemantics.raw446; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical446 hH).trans (PairSemantics.sound220 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue241, PairSemantics.value0, PairSemantics.value4, PairSemantics.value24, PairSemantics.value220, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue242 : Sparse (Fin 909) := [(0, (29 / 864)), (1, (-65 / 864)), (2, (-85 / 864)), (3, (-5 / 9)), (5, (-5 / 72)), (6, (5 / 288)), (13, (-5 / 18)), (26, (-5 / 18)), (33, (5 / 6)), (35, (-5 / 54)), (54, (5 / 6)), (62, (5 / 9))]

theorem singlePair242 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node242 node242Labels = Sparse.eval singlePairValue242 (familyPairVector B) := by
  have hp := single_label_three B hB node242
  have hl : node242Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node242 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node242 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node242 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node242 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node242 (EqualityPatterns.family3.label 1) = PairSemantics.raw904 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node242 PairSemantics.raw904; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical904 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node242 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node242 (EqualityPatterns.family3.label 2) = PairSemantics.raw8983 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node242 PairSemantics.raw8983; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8983 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node242 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value383 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node242 (EqualityPatterns.family3.label 3) = PairSemantics.raw866 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node242 PairSemantics.raw866; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical866 hH).trans (PairSemantics.sound383 hH)
  have hm4 : familyPairMoment B (groupedColumns node242 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1409 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node242 (EqualityPatterns.family3.label 4) = PairSemantics.raw447 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node242 PairSemantics.raw447; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical447 hH).trans (PairSemantics.sound1409 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue242, PairSemantics.value0, PairSemantics.value10, PairSemantics.value232, PairSemantics.value383, PairSemantics.value1409, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue243 : Sparse (Fin 909) := [(0, (11 / 288)), (1, (5 / 288)), (2, (5 / 288)), (3, (-5 / 6)), (4, (-10 / 27)), (5, (-5 / 72)), (6, (5 / 288)), (12, (-5 / 27)), (13, (-25 / 54)), (26, (-10 / 27)), (35, (-5 / 18)), (54, (5 / 18)), (56, (5 / 9))]

theorem singlePair243 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node243 node243Labels = Sparse.eval singlePairValue243 (familyPairVector B) := by
  have hp := single_label_three B hB node243
  have hl : node243Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node243 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node243 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node243 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node243 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node243 (EqualityPatterns.family3.label 1) = PairSemantics.raw905 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node243 PairSemantics.raw905; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical905 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node243 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node243 (EqualityPatterns.family3.label 2) = PairSemantics.raw8982 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node243 PairSemantics.raw8982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8982 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node243 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value383 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node243 (EqualityPatterns.family3.label 3) = PairSemantics.raw866 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node243 PairSemantics.raw866; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical866 hH).trans (PairSemantics.sound383 hH)
  have hm4 : familyPairMoment B (groupedColumns node243 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2297 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node243 (EqualityPatterns.family3.label 4) = PairSemantics.raw448 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node243 PairSemantics.raw448; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical448 hH).trans (PairSemantics.sound2297 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue243, PairSemantics.value0, PairSemantics.value11, PairSemantics.value26, PairSemantics.value383, PairSemantics.value2297, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue244 : Sparse (Fin 909) := [(0, (31 / 864)), (1, (-5 / 48)), (2, (-5 / 72)), (3, (5 / 54)), (5, (5 / 216)), (6, (-5 / 864)), (26, (5 / 27)), (35, (5 / 54)), (54, (-5 / 18))]

theorem singlePair244 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node244 node244Labels = Sparse.eval singlePairValue244 (familyPairVector B) := by
  have hp := single_label_three B hB node244
  have hl : node244Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node244 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node244 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node244 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node244 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node244 (EqualityPatterns.family3.label 1) = PairSemantics.raw906 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node244 PairSemantics.raw906; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical906 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node244 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node244 (EqualityPatterns.family3.label 2) = PairSemantics.raw8981 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node244 PairSemantics.raw8981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8981 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node244 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node244 (EqualityPatterns.family3.label 3) = PairSemantics.raw867 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node244 PairSemantics.raw867; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical867 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node244 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value699 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node244 (EqualityPatterns.family3.label 4) = PairSemantics.raw449 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node244 PairSemantics.raw449; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical449 hH).trans (PairSemantics.sound699 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue244, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value118, PairSemantics.value699, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue245 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (5 / 432)), (2, (25 / 864)), (3, (5 / 27)), (4, (5 / 54)), (5, (5 / 216)), (6, (-5 / 864)), (13, (5 / 54)), (26, (5 / 54)), (35, (5 / 54)), (56, (-5 / 18))]

theorem singlePair245 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node245 node245Labels = Sparse.eval singlePairValue245 (familyPairVector B) := by
  have hp := single_label_three B hB node245
  have hl : node245Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node245 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node245 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node245 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node245 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node245 (EqualityPatterns.family3.label 1) = PairSemantics.raw907 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node245 PairSemantics.raw907; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical907 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node245 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node245 (EqualityPatterns.family3.label 2) = PairSemantics.raw8978 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node245 PairSemantics.raw8978; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8978 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node245 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node245 (EqualityPatterns.family3.label 3) = PairSemantics.raw867 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node245 PairSemantics.raw867; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical867 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node245 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value697 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node245 (EqualityPatterns.family3.label 4) = PairSemantics.raw450 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node245 PairSemantics.raw450; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical450 hH).trans (PairSemantics.sound697 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue245, PairSemantics.value0, PairSemantics.value11, PairSemantics.value26, PairSemantics.value118, PairSemantics.value697, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue246 : Sparse (Fin 909) := [(0, (23 / 864)), (1, (-5 / 144)), (3, (5 / 54)), (5, (5 / 216)), (6, (-5 / 864)), (13, (5 / 54)), (33, (-5 / 18)), (54, (-5 / 18)), (62, (-5 / 18))]

theorem singlePair246 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node246 node246Labels = Sparse.eval singlePairValue246 (familyPairVector B) := by
  have hp := single_label_three B hB node246
  have hl : node246Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node246 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node246 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node246 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node246 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node246 (EqualityPatterns.family3.label 1) = PairSemantics.raw910 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node246 PairSemantics.raw910; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical910 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node246 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node246 (EqualityPatterns.family3.label 2) = PairSemantics.raw8974 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node246 PairSemantics.raw8974; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8974 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node246 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node246 (EqualityPatterns.family3.label 3) = PairSemantics.raw867 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node246 PairSemantics.raw867; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical867 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node246 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value345 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node246 (EqualityPatterns.family3.label 4) = PairSemantics.raw451 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node246 PairSemantics.raw451; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical451 hH).trans (PairSemantics.sound345 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue246, PairSemantics.value0, PairSemantics.value10, PairSemantics.value46, PairSemantics.value118, PairSemantics.value345, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue247 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 72)), (2, (-5 / 216)), (6, (5 / 432)), (26, (-5 / 27)), (35, (-5 / 27))]

theorem singlePair247 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node247 node247Labels = Sparse.eval singlePairValue247 (familyPairVector B) := by
  have hp := single_label_three B hB node247
  have hl : node247Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node247 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node247 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node247 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node247 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node247 (EqualityPatterns.family3.label 1) = PairSemantics.raw909 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node247 PairSemantics.raw909; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical909 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node247 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node247 (EqualityPatterns.family3.label 2) = PairSemantics.raw8979 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node247 PairSemantics.raw8979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8979 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node247 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node247 (EqualityPatterns.family3.label 3) = PairSemantics.raw869 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node247 PairSemantics.raw869; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical869 hH).trans (PairSemantics.sound24 hH)
  have hm4 : familyPairMoment B (groupedColumns node247 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value222 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node247 (EqualityPatterns.family3.label 4) = PairSemantics.raw452 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node247 PairSemantics.raw452; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical452 hH).trans (PairSemantics.sound222 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue247, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value24, PairSemantics.value222, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
