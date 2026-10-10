import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleRules
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical160
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical161
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical162
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound6

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue24 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (5 / 288)), (2, (-35 / 864)), (5, (5 / 216)), (6, (-5 / 288)), (9, (25 / 216)), (52, (5 / 27)), (58, (-5 / 864)), (69, (5 / 27)), (71, (5 / 54)), (256, (-5 / 18)), (495, (5 / 54))]

theorem singlePair24 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node24 node24Labels = Sparse.eval singlePairValue24 (familyPairVector B) := by
  have hp := single_label_three B hB node24
  have hl : node24Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node24 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node24 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node24 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node24 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node24 (EqualityPatterns.family3.label 1) = PairSemantics.raw886 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node24 PairSemantics.raw886; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical886 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node24 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node24 (EqualityPatterns.family3.label 2) = PairSemantics.raw5203 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node24 PairSemantics.raw5203; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5203 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node24 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value66 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node24 (EqualityPatterns.family3.label 3) = PairSemantics.raw43 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node24 PairSemantics.raw43; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical43 hH).trans (PairSemantics.sound66 hH)
  have hm4 : familyPairMoment B (groupedColumns node24 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value298 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node24 (EqualityPatterns.family3.label 4) = PairSemantics.raw16 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node24 PairSemantics.raw16; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical16 hH).trans (PairSemantics.sound298 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue24, PairSemantics.value0, PairSemantics.value10, PairSemantics.value66, PairSemantics.value232, PairSemantics.value298, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue25 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 144)), (2, (25 / 144)), (58, (5 / 432)), (70, (-5 / 27))]

theorem singlePair25 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node25 node25Labels = Sparse.eval singlePairValue25 (familyPairVector B) := by
  have hp := single_label_three B hB node25
  have hl : node25Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node25 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node25 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node25 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node25 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node25 (EqualityPatterns.family3.label 1) = PairSemantics.raw887 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node25 PairSemantics.raw887; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical887 hH).trans (PairSemantics.sound3 hH)
  have hm2 : familyPairMoment B (groupedColumns node25 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node25 (EqualityPatterns.family3.label 2) = PairSemantics.raw5204 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node25 PairSemantics.raw5204; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5204 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node25 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value12 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node25 (EqualityPatterns.family3.label 3) = PairSemantics.raw45 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node25 PairSemantics.raw45; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical45 hH).trans (PairSemantics.sound12 hH)
  have hm4 : familyPairMoment B (groupedColumns node25 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value129 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node25 (EqualityPatterns.family3.label 4) = PairSemantics.raw17 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node25 PairSemantics.raw17; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical17 hH).trans (PairSemantics.sound129 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue25, PairSemantics.value0, PairSemantics.value3, PairSemantics.value11, PairSemantics.value12, PairSemantics.value129, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue26 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (5 / 216)), (2, (5 / 144)), (6, (-5 / 432)), (8, (5 / 27)), (9, (5 / 54)), (58, (-5 / 864)), (69, (5 / 54)), (71, (10 / 27))]

theorem singlePair26 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node26 node26Labels = Sparse.eval singlePairValue26 (familyPairVector B) := by
  have hp := single_label_three B hB node26
  have hl : node26Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node26 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node26 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node26 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node26 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node26 (EqualityPatterns.family3.label 1) = PairSemantics.raw893 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node26 PairSemantics.raw893; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical893 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node26 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node26 (EqualityPatterns.family3.label 2) = PairSemantics.raw5196 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node26 PairSemantics.raw5196; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5196 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node26 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value66 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node26 (EqualityPatterns.family3.label 3) = PairSemantics.raw43 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node26 PairSemantics.raw43; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical43 hH).trans (PairSemantics.sound66 hH)
  have hm4 : familyPairMoment B (groupedColumns node26 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value387 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node26 (EqualityPatterns.family3.label 4) = PairSemantics.raw18 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node26 PairSemantics.raw18; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical18 hH).trans (PairSemantics.sound387 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue26, PairSemantics.value0, PairSemantics.value11, PairSemantics.value26, PairSemantics.value66, PairSemantics.value387, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue27 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-55 / 864)), (2, (-35 / 864)), (3, (5 / 54)), (5, (5 / 72)), (6, (-5 / 288)), (7, (5 / 54)), (9, (25 / 216)), (35, (5 / 27)), (52, (5 / 54)), (58, (-5 / 864)), (69, (5 / 54)), (70, (5 / 54)), (256, (-5 / 18)), (257, (5 / 54)), (495, (5 / 54))]

theorem singlePair27 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node27 node27Labels = Sparse.eval singlePairValue27 (familyPairVector B) := by
  have hp := single_label_three B hB node27
  have hl : node27Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node27 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node27 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node27 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node27 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node27 (EqualityPatterns.family3.label 1) = PairSemantics.raw896 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node27 PairSemantics.raw896; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical896 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node27 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node27 (EqualityPatterns.family3.label 2) = PairSemantics.raw5194 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node27 PairSemantics.raw5194; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5194 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node27 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value66 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node27 (EqualityPatterns.family3.label 3) = PairSemantics.raw43 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node27 PairSemantics.raw43; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical43 hH).trans (PairSemantics.sound66 hH)
  have hm4 : familyPairMoment B (groupedColumns node27 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value300 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node27 (EqualityPatterns.family3.label 4) = PairSemantics.raw19 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node27 PairSemantics.raw19; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical19 hH).trans (PairSemantics.sound300 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue27, PairSemantics.value0, PairSemantics.value10, PairSemantics.value46, PairSemantics.value66, PairSemantics.value300, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue28 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-35 / 432)), (2, (-5 / 108)), (5, (5 / 108)), (6, (5 / 432)), (58, (5 / 432)), (71, (-5 / 27))]

theorem singlePair28 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node28 node28Labels = Sparse.eval singlePairValue28 (familyPairVector B) := by
  have hp := single_label_three B hB node28
  have hl : node28Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node28 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node28 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node28 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node28 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node28 (EqualityPatterns.family3.label 1) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node28 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node28 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node28 (EqualityPatterns.family3.label 2) = PairSemantics.raw5197 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node28 PairSemantics.raw5197; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5197 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node28 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value12 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node28 (EqualityPatterns.family3.label 3) = PairSemantics.raw45 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node28 PairSemantics.raw45; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical45 hH).trans (PairSemantics.sound12 hH)
  have hm4 : familyPairMoment B (groupedColumns node28 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value123 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node28 (EqualityPatterns.family3.label 4) = PairSemantics.raw20 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node28 PairSemantics.raw20; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical20 hH).trans (PairSemantics.sound123 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue28, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value12, PairSemantics.value123, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue29 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 216)), (2, (65 / 432)), (5, (-5 / 108)), (9, (-5 / 54)), (35, (-5 / 27)), (70, (-5 / 27)), (257, (-5 / 27))]

theorem singlePair29 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node29 node29Labels = Sparse.eval singlePairValue29 (familyPairVector B) := by
  have hp := single_label_three B hB node29
  have hl : node29Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node29 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node29 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node29 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node29 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node29 (EqualityPatterns.family3.label 1) = PairSemantics.raw887 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node29 PairSemantics.raw887; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical887 hH).trans (PairSemantics.sound3 hH)
  have hm2 : familyPairMoment B (groupedColumns node29 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node29 (EqualityPatterns.family3.label 2) = PairSemantics.raw5208 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node29 PairSemantics.raw5208; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5208 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node29 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value13 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node29 (EqualityPatterns.family3.label 3) = PairSemantics.raw47 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node29 PairSemantics.raw47; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical47 hH).trans (PairSemantics.sound13 hH)
  have hm4 : familyPairMoment B (groupedColumns node29 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value70 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node29 (EqualityPatterns.family3.label 4) = PairSemantics.raw21 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node29 PairSemantics.raw21; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical21 hH).trans (PairSemantics.sound70 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue29, PairSemantics.value0, PairSemantics.value3, PairSemantics.value13, PairSemantics.value46, PairSemantics.value70, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue30 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-35 / 432)), (2, (-5 / 108)), (9, (-5 / 54)), (69, (-5 / 27)), (71, (-5 / 27))]

theorem singlePair30 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node30 node30Labels = Sparse.eval singlePairValue30 (familyPairVector B) := by
  have hp := single_label_three B hB node30
  have hl : node30Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node30 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node30 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node30 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node30 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node30 (EqualityPatterns.family3.label 1) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node30 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node30 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node30 (EqualityPatterns.family3.label 2) = PairSemantics.raw5204 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node30 PairSemantics.raw5204; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5204 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node30 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value13 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node30 (EqualityPatterns.family3.label 3) = PairSemantics.raw47 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node30 PairSemantics.raw47; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical47 hH).trans (PairSemantics.sound13 hH)
  have hm4 : familyPairMoment B (groupedColumns node30 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value127 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node30 (EqualityPatterns.family3.label 4) = PairSemantics.raw22 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node30 PairSemantics.raw22; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical22 hH).trans (PairSemantics.sound127 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue30, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value13, PairSemantics.value127, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue31 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (35 / 216)), (2, (5 / 216)), (5, (5 / 54)), (6, (5 / 216)), (58, (5 / 432)), (69, (-5 / 27))]

theorem singlePair31 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node31 node31Labels = Sparse.eval singlePairValue31 (familyPairVector B) := by
  have hp := single_label_three B hB node31
  have hl : node31Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node31 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node31 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node31 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node31 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node31 (EqualityPatterns.family3.label 1) = PairSemantics.raw914 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node31 PairSemantics.raw914; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical914 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node31 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node31 (EqualityPatterns.family3.label 2) = PairSemantics.raw5169 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node31 PairSemantics.raw5169; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5169 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node31 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value12 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node31 (EqualityPatterns.family3.label 3) = PairSemantics.raw45 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node31 PairSemantics.raw45; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical45 hH).trans (PairSemantics.sound12 hH)
  have hm4 : familyPairMoment B (groupedColumns node31 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value119 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node31 (EqualityPatterns.family3.label 4) = PairSemantics.raw23 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node31 PairSemantics.raw23; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical23 hH).trans (PairSemantics.sound119 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue31, PairSemantics.value0, PairSemantics.value4, PairSemantics.value12, PairSemantics.value26, PairSemantics.value119, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue32 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 72)), (2, (-25 / 432)), (6, (5 / 216)), (9, (-5 / 108)), (35, (-5 / 27)), (58, (5 / 432)), (257, (-5 / 27)), (495, (-5 / 27))]

theorem singlePair32 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node32 node32Labels = Sparse.eval singlePairValue32 (familyPairVector B) := by
  have hp := single_label_three B hB node32
  have hl : node32Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node32 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node32 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node32 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node32 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node32 (EqualityPatterns.family3.label 1) = PairSemantics.raw918 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node32 PairSemantics.raw918; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical918 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node32 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node32 (EqualityPatterns.family3.label 2) = PairSemantics.raw5161 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node32 PairSemantics.raw5161; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5161 hH).trans (PairSemantics.sound10 hH)
  have hm3 : familyPairMoment B (groupedColumns node32 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value12 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node32 (EqualityPatterns.family3.label 3) = PairSemantics.raw45 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node32 PairSemantics.raw45; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical45 hH).trans (PairSemantics.sound12 hH)
  have hm4 : familyPairMoment B (groupedColumns node32 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value76 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node32 (EqualityPatterns.family3.label 4) = PairSemantics.raw24 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node32 PairSemantics.raw24; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical24 hH).trans (PairSemantics.sound76 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue32, PairSemantics.value0, PairSemantics.value10, PairSemantics.value12, PairSemantics.value76, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue33 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 48)), (2, (-5 / 144)), (5, (-5 / 108)), (7, (-5 / 27)), (9, (-5 / 54)), (69, (-5 / 27)), (70, (-5 / 27))]

theorem singlePair33 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node33 node33Labels = Sparse.eval singlePairValue33 (familyPairVector B) := by
  have hp := single_label_three B hB node33
  have hl : node33Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node33 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node33 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node33 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node33 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node33 (EqualityPatterns.family3.label 1) = PairSemantics.raw909 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node33 PairSemantics.raw909; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical909 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node33 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node33 (EqualityPatterns.family3.label 2) = PairSemantics.raw5185 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node33 PairSemantics.raw5185; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5185 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node33 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value13 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node33 (EqualityPatterns.family3.label 3) = PairSemantics.raw47 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node33 PairSemantics.raw47; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical47 hH).trans (PairSemantics.sound13 hH)
  have hm4 : familyPairMoment B (groupedColumns node33 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value120 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node33 (EqualityPatterns.family3.label 4) = PairSemantics.raw25 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node33 PairSemantics.raw25; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical25 hH).trans (PairSemantics.sound120 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue33, PairSemantics.value0, PairSemantics.value4, PairSemantics.value10, PairSemantics.value13, PairSemantics.value120, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue34 : Sparse (Fin 909) := [(0, (7 / 216)), (2, (5 / 216)), (5, (-5 / 108)), (8, (-5 / 27)), (9, (-5 / 54)), (71, (-10 / 27))]

theorem singlePair34 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node34 node34Labels = Sparse.eval singlePairValue34 (familyPairVector B) := by
  have hp := single_label_three B hB node34
  have hl : node34Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node34 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node34 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node34 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node34 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node34 (EqualityPatterns.family3.label 1) = PairSemantics.raw914 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node34 PairSemantics.raw914; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical914 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node34 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node34 (EqualityPatterns.family3.label 2) = PairSemantics.raw5177 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node34 PairSemantics.raw5177; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5177 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node34 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value13 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node34 (EqualityPatterns.family3.label 3) = PairSemantics.raw47 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node34 PairSemantics.raw47; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical47 hH).trans (PairSemantics.sound13 hH)
  have hm4 : familyPairMoment B (groupedColumns node34 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value124 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node34 (EqualityPatterns.family3.label 4) = PairSemantics.raw26 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node34 PairSemantics.raw26; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical26 hH).trans (PairSemantics.sound124 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue34, PairSemantics.value0, PairSemantics.value11, PairSemantics.value13, PairSemantics.value26, PairSemantics.value124, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue35 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 48)), (2, (-5 / 144)), (5, (-5 / 36)), (6, (-5 / 144)), (9, (-5 / 36)), (58, (-5 / 144))]

theorem singlePair35 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node35 node35Labels = Sparse.eval singlePairValue35 (familyPairVector B) := by
  have hp := single_label_three B hB node35
  have hl : node35Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node35 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node35 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node35 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node35 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node35 (EqualityPatterns.family3.label 1) = PairSemantics.raw917 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node35 PairSemantics.raw917; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical917 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node35 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node35 (EqualityPatterns.family3.label 2) = PairSemantics.raw5183 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node35 PairSemantics.raw5183; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5183 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node35 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value6 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node35 (EqualityPatterns.family3.label 3) = PairSemantics.raw48 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node35 PairSemantics.raw48; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical48 hH).trans (PairSemantics.sound6 hH)
  have hm4 : familyPairMoment B (groupedColumns node35 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value48 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node35 (EqualityPatterns.family3.label 4) = PairSemantics.raw27 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node35 PairSemantics.raw27; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical27 hH).trans (PairSemantics.sound48 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue35, PairSemantics.value0, PairSemantics.value4, PairSemantics.value6, PairSemantics.value10, PairSemantics.value48, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue36 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-25 / 432)), (2, (-5 / 216)), (5, (-5 / 108)), (9, (-5 / 54)), (256, (5 / 9))]

theorem singlePair36 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node36 node36Labels = Sparse.eval singlePairValue36 (familyPairVector B) := by
  have hp := single_label_three B hB node36
  have hl : node36Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node36 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node36 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node36 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node36 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node36 (EqualityPatterns.family3.label 1) = PairSemantics.raw922 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node36 PairSemantics.raw922; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical922 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node36 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node36 (EqualityPatterns.family3.label 2) = PairSemantics.raw5149 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node36 PairSemantics.raw5149; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5149 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node36 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value13 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node36 (EqualityPatterns.family3.label 3) = PairSemantics.raw47 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node36 PairSemantics.raw47; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical47 hH).trans (PairSemantics.sound13 hH)
  have hm4 : familyPairMoment B (groupedColumns node36 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value74 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node36 (EqualityPatterns.family3.label 4) = PairSemantics.raw28 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node36 PairSemantics.raw28; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical28 hH).trans (PairSemantics.sound74 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue36, PairSemantics.value0, PairSemantics.value10, PairSemantics.value13, PairSemantics.value46, PairSemantics.value74, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue37 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 72)), (2, (-5 / 72)), (6, (-5 / 144)), (58, (-5 / 144)), (495, (5 / 9))]

theorem singlePair37 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node37 node37Labels = Sparse.eval singlePairValue37 (familyPairVector B) := by
  have hp := single_label_three B hB node37
  have hl : node37Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node37 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node37 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node37 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node37 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node37 (EqualityPatterns.family3.label 1) = PairSemantics.raw924 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node37 PairSemantics.raw924; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical924 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node37 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node37 (EqualityPatterns.family3.label 2) = PairSemantics.raw5151 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node37 PairSemantics.raw5151; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5151 hH).trans (PairSemantics.sound10 hH)
  have hm3 : familyPairMoment B (groupedColumns node37 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value6 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node37 (EqualityPatterns.family3.label 3) = PairSemantics.raw48 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node37 PairSemantics.raw48; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical48 hH).trans (PairSemantics.sound6 hH)
  have hm4 : familyPairMoment B (groupedColumns node37 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value39 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node37 (EqualityPatterns.family3.label 4) = PairSemantics.raw29 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node37 PairSemantics.raw29; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical29 hH).trans (PairSemantics.sound39 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue37, PairSemantics.value0, PairSemantics.value6, PairSemantics.value10, PairSemantics.value39, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue38 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 36)), (2, (5 / 36)), (9, (5 / 36)), (70, (5 / 9))]

theorem singlePair38 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node38 node38Labels = Sparse.eval singlePairValue38 (familyPairVector B) := by
  have hp := single_label_three B hB node38
  have hl : node38Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node38 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node38 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node38 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node38 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node38 (EqualityPatterns.family3.label 1) = PairSemantics.raw900 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node38 PairSemantics.raw900; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical900 hH).trans (PairSemantics.sound3 hH)
  have hm2 : familyPairMoment B (groupedColumns node38 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node38 (EqualityPatterns.family3.label 2) = PairSemantics.raw5214 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node38 PairSemantics.raw5214; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5214 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node38 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value7 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node38 (EqualityPatterns.family3.label 3) = PairSemantics.raw51 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node38 PairSemantics.raw51; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical51 hH).trans (PairSemantics.sound7 hH)
  have hm4 : familyPairMoment B (groupedColumns node38 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value28 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node38 (EqualityPatterns.family3.label 4) = PairSemantics.raw30 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node38 PairSemantics.raw30; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical30 hH).trans (PairSemantics.sound28 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue38, PairSemantics.value0, PairSemantics.value3, PairSemantics.value4, PairSemantics.value7, PairSemantics.value28, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue39 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 72)), (2, (-5 / 144)), (9, (5 / 36)), (71, (5 / 9))]

theorem singlePair39 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node39 node39Labels = Sparse.eval singlePairValue39 (familyPairVector B) := by
  have hp := single_label_three B hB node39
  have hl : node39Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node39 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node39 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node39 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node39 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node39 (EqualityPatterns.family3.label 1) = PairSemantics.raw917 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node39 PairSemantics.raw917; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical917 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node39 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node39 (EqualityPatterns.family3.label 2) = PairSemantics.raw5199 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node39 PairSemantics.raw5199; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5199 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node39 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value7 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node39 (EqualityPatterns.family3.label 3) = PairSemantics.raw51 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node39 PairSemantics.raw51; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical51 hH).trans (PairSemantics.sound7 hH)
  have hm4 : familyPairMoment B (groupedColumns node39 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value30 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node39 (EqualityPatterns.family3.label 4) = PairSemantics.raw31 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node39 PairSemantics.raw31; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical31 hH).trans (PairSemantics.sound30 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue39, PairSemantics.value0, PairSemantics.value7, PairSemantics.value10, PairSemantics.value11, PairSemantics.value30, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
