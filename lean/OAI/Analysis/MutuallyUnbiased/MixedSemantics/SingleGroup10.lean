import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleRules
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical279
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical280
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound9

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue168 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-25 / 432)), (2, (-5 / 216)), (68, (5 / 36)), (124, (-5 / 18)), (196, (-5 / 18)), (197, (-5 / 18)), (266, (-5 / 18))]

theorem singlePair168 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node168 node168Labels = Sparse.eval singlePairValue168 (familyPairVector B) := by
  have hp := single_label_three B hB node168
  have hl : node168Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node168 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node168 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node168 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node168 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node168 (EqualityPatterns.family3.label 1) = PairSemantics.raw891 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node168 PairSemantics.raw891; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical891 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node168 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node168 (EqualityPatterns.family3.label 2) = PairSemantics.raw8964 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node168 PairSemantics.raw8964; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8964 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node168 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value23 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node168 (EqualityPatterns.family3.label 3) = PairSemantics.raw846 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node168 PairSemantics.raw846; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical846 hH).trans (PairSemantics.sound23 hH)
  have hm4 : familyPairMoment B (groupedColumns node168 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value328 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node168 (EqualityPatterns.family3.label 4) = PairSemantics.raw373 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node168 PairSemantics.raw373; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical373 hH).trans (PairSemantics.sound328 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue168, PairSemantics.value0, PairSemantics.value10, PairSemantics.value23, PairSemantics.value46, PairSemantics.value328, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue169 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 432)), (2, (5 / 144)), (68, (5 / 36)), (125, (-5 / 18)), (126, (-5 / 18)), (197, (-5 / 18)), (268, (-5 / 18))]

theorem singlePair169 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node169 node169Labels = Sparse.eval singlePairValue169 (familyPairVector B) := by
  have hp := single_label_three B hB node169
  have hl : node169Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node169 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node169 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node169 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node169 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node169 (EqualityPatterns.family3.label 1) = PairSemantics.raw893 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node169 PairSemantics.raw893; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical893 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node169 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node169 (EqualityPatterns.family3.label 2) = PairSemantics.raw8962 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node169 PairSemantics.raw8962; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8962 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node169 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value23 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node169 (EqualityPatterns.family3.label 3) = PairSemantics.raw846 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node169 PairSemantics.raw846; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical846 hH).trans (PairSemantics.sound23 hH)
  have hm4 : familyPairMoment B (groupedColumns node169 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value332 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node169 (EqualityPatterns.family3.label 4) = PairSemantics.raw374 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node169 PairSemantics.raw374; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical374 hH).trans (PairSemantics.sound332 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue169, PairSemantics.value0, PairSemantics.value23, PairSemantics.value26, PairSemantics.value46, PairSemantics.value332, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue170 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 72)), (2, (-5 / 72)), (68, (5 / 36)), (125, (-5 / 9)), (264, (-5 / 9))]

theorem singlePair170 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node170 node170Labels = Sparse.eval singlePairValue170 (familyPairVector B) := by
  have hp := single_label_three B hB node170
  have hl : node170Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node170 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node170 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node170 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node170 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node170 (EqualityPatterns.family3.label 1) = PairSemantics.raw896 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node170 PairSemantics.raw896; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical896 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node170 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node170 (EqualityPatterns.family3.label 2) = PairSemantics.raw8959 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node170 PairSemantics.raw8959; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8959 hH).trans (PairSemantics.sound10 hH)
  have hm3 : familyPairMoment B (groupedColumns node170 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value23 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node170 (EqualityPatterns.family3.label 3) = PairSemantics.raw846 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node170 PairSemantics.raw846; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical846 hH).trans (PairSemantics.sound23 hH)
  have hm4 : familyPairMoment B (groupedColumns node170 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value330 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node170 (EqualityPatterns.family3.label 4) = PairSemantics.raw375 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node170 PairSemantics.raw375; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical375 hH).trans (PairSemantics.sound330 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue170, PairSemantics.value0, PairSemantics.value10, PairSemantics.value23, PairSemantics.value330, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue171 : Sparse (Fin 909) := [(0, (29 / 864)), (1, (-25 / 864)), (2, (25 / 864)), (3, (-5 / 18)), (5, (-5 / 54)), (6, (5 / 864)), (7, (-5 / 54)), (9, (-5 / 216)), (12, (-5 / 54)), (13, (-5 / 54)), (23, (5 / 18)), (26, (-5 / 27)), (27, (5 / 24)), (35, (-5 / 18)), (54, (5 / 18)), (55, (5 / 9)), (68, (25 / 72)), (70, (-5 / 54)), (125, (5 / 9)), (196, (5 / 18)), (197, (5 / 9))]

theorem singlePair171 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node171 node171Labels = Sparse.eval singlePairValue171 (familyPairVector B) := by
  have hp := single_label_three B hB node171
  have hl : node171Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node171 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node171 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node171 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node171 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node171 (EqualityPatterns.family3.label 1) = PairSemantics.raw879 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node171 PairSemantics.raw879; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical879 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node171 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node171 (EqualityPatterns.family3.label 2) = PairSemantics.raw8982 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node171 PairSemantics.raw8982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8982 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node171 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value380 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node171 (EqualityPatterns.family3.label 3) = PairSemantics.raw847 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node171 PairSemantics.raw847; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical847 hH).trans (PairSemantics.sound380 hH)
  have hm4 : familyPairMoment B (groupedColumns node171 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2111 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node171 (EqualityPatterns.family3.label 4) = PairSemantics.raw376 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node171 PairSemantics.raw376; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical376 hH).trans (PairSemantics.sound2111 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue171, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value380, PairSemantics.value2111, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue172 : Sparse (Fin 909) := [(0, (5 / 288)), (1, (-5 / 864)), (2, (-5 / 288)), (3, (-5 / 27)), (5, (-5 / 54)), (6, (5 / 288)), (9, (-5 / 216)), (13, (-5 / 27)), (27, (5 / 24)), (33, (5 / 18)), (52, (-5 / 27)), (55, (5 / 9)), (64, (5 / 9)), (68, (25 / 72)), (125, (5 / 9)), (197, (5 / 18)), (260, (5 / 18)), (263, (-5 / 9))]

theorem singlePair172 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node172 node172Labels = Sparse.eval singlePairValue172 (familyPairVector B) := by
  have hp := single_label_three B hB node172
  have hl : node172Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node172 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node172 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node172 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node172 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node172 (EqualityPatterns.family3.label 1) = PairSemantics.raw880 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node172 PairSemantics.raw880; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical880 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node172 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node172 (EqualityPatterns.family3.label 2) = PairSemantics.raw8980 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node172 PairSemantics.raw8980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8980 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node172 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value380 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node172 (EqualityPatterns.family3.label 3) = PairSemantics.raw847 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node172 PairSemantics.raw847; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical847 hH).trans (PairSemantics.sound380 hH)
  have hm4 : familyPairMoment B (groupedColumns node172 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1393 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node172 (EqualityPatterns.family3.label 4) = PairSemantics.raw377 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node172 PairSemantics.raw377; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical377 hH).trans (PairSemantics.sound1393 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue172, PairSemantics.value0, PairSemantics.value10, PairSemantics.value232, PairSemantics.value380, PairSemantics.value1393, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue173 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-35 / 864)), (2, (5 / 32)), (5, (5 / 108)), (9, (5 / 216)), (13, (5 / 54)), (35, (5 / 27)), (68, (-5 / 72)), (70, (5 / 54)), (196, (-5 / 18))]

theorem singlePair173 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node173 node173Labels = Sparse.eval singlePairValue173 (familyPairVector B) := by
  have hp := single_label_three B hB node173
  have hl : node173Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node173 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node173 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node173 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node173 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node173 (EqualityPatterns.family3.label 1) = PairSemantics.raw881 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node173 PairSemantics.raw881; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical881 hH).trans (PairSemantics.sound3 hH)
  have hm2 : familyPairMoment B (groupedColumns node173 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node173 (EqualityPatterns.family3.label 2) = PairSemantics.raw8981 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node173 PairSemantics.raw8981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8981 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node173 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value116 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node173 (EqualityPatterns.family3.label 3) = PairSemantics.raw848 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node173 PairSemantics.raw848; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical848 hH).trans (PairSemantics.sound116 hH)
  have hm4 : familyPairMoment B (groupedColumns node173 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value636 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node173 (EqualityPatterns.family3.label 4) = PairSemantics.raw378 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node173 PairSemantics.raw378; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical378 hH).trans (PairSemantics.sound636 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue173, PairSemantics.value0, PairSemantics.value3, PairSemantics.value11, PairSemantics.value116, PairSemantics.value636, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue174 : Sparse (Fin 909) := [(0, (25 / 864)), (1, (85 / 864)), (2, (5 / 54)), (3, (-25 / 54)), (4, (-5 / 27)), (5, (-25 / 216)), (6, (5 / 432)), (7, (-5 / 27)), (9, (-5 / 216)), (13, (-5 / 54)), (24, (5 / 9)), (26, (-5 / 27)), (27, (5 / 24)), (35, (-5 / 18)), (55, (5 / 18)), (56, (5 / 9)), (68, (25 / 72)), (70, (-5 / 54)), (125, (5 / 18)), (197, (10 / 9))]

theorem singlePair174 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node174 node174Labels = Sparse.eval singlePairValue174 (familyPairVector B) := by
  have hp := single_label_three B hB node174
  have hl : node174Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node174 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node174 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node174 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node174 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node174 (EqualityPatterns.family3.label 1) = PairSemantics.raw883 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node174 PairSemantics.raw883; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical883 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node174 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node174 (EqualityPatterns.family3.label 2) = PairSemantics.raw8977 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node174 PairSemantics.raw8977; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8977 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node174 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value380 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node174 (EqualityPatterns.family3.label 3) = PairSemantics.raw847 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node174 PairSemantics.raw847; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical847 hH).trans (PairSemantics.sound380 hH)
  have hm4 : familyPairMoment B (groupedColumns node174 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2110 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node174 (EqualityPatterns.family3.label 4) = PairSemantics.raw379 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node174 PairSemantics.raw379; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical379 hH).trans (PairSemantics.sound2110 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue174, PairSemantics.value0, PairSemantics.value11, PairSemantics.value26, PairSemantics.value380, PairSemantics.value2110, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue175 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-85 / 864)), (2, (-5 / 72)), (3, (5 / 54)), (5, (5 / 108)), (6, (-5 / 864)), (7, (5 / 54)), (9, (5 / 216)), (26, (5 / 54)), (35, (5 / 27)), (68, (-5 / 72)), (70, (5 / 54)), (197, (-5 / 18))]

theorem singlePair175 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node175 node175Labels = Sparse.eval singlePairValue175 (familyPairVector B) := by
  have hp := single_label_three B hB node175
  have hl : node175Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node175 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node175 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node175 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node175 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node175 (EqualityPatterns.family3.label 1) = PairSemantics.raw884 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node175 PairSemantics.raw884; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical884 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node175 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node175 (EqualityPatterns.family3.label 2) = PairSemantics.raw8978 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node175 PairSemantics.raw8978; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8978 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node175 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value116 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node175 (EqualityPatterns.family3.label 3) = PairSemantics.raw848 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node175 PairSemantics.raw848; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical848 hH).trans (PairSemantics.sound116 hH)
  have hm4 : familyPairMoment B (groupedColumns node175 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value633 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node175 (EqualityPatterns.family3.label 4) = PairSemantics.raw380 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node175 PairSemantics.raw380; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical380 hH).trans (PairSemantics.sound633 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue175, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value116, PairSemantics.value633, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue176 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-55 / 864)), (2, (-5 / 288)), (5, (5 / 108)), (6, (-5 / 432)), (9, (5 / 216)), (13, (5 / 54)), (52, (5 / 54)), (64, (-5 / 18)), (68, (-5 / 72)), (125, (-5 / 18)), (260, (-5 / 18))]

theorem singlePair176 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node176 node176Labels = Sparse.eval singlePairValue176 (familyPairVector B) := by
  have hp := single_label_three B hB node176
  have hl : node176Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node176 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node176 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node176 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node176 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node176 (EqualityPatterns.family3.label 1) = PairSemantics.raw886 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node176 PairSemantics.raw886; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical886 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node176 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node176 (EqualityPatterns.family3.label 2) = PairSemantics.raw8974 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node176 PairSemantics.raw8974; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8974 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node176 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value116 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node176 (EqualityPatterns.family3.label 3) = PairSemantics.raw848 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node176 PairSemantics.raw848; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical848 hH).trans (PairSemantics.sound116 hH)
  have hm4 : familyPairMoment B (groupedColumns node176 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value327 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node176 (EqualityPatterns.family3.label 4) = PairSemantics.raw381 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node176 PairSemantics.raw381; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical381 hH).trans (PairSemantics.sound327 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue176, PairSemantics.value0, PairSemantics.value10, PairSemantics.value46, PairSemantics.value116, PairSemantics.value327, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue177 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-25 / 864)), (2, (35 / 288)), (5, (5 / 216)), (13, (5 / 54)), (27, (-5 / 72)), (35, (5 / 54)), (63, (-5 / 18)), (68, (-5 / 36)), (196, (-5 / 18)), (264, (-5 / 18))]

theorem singlePair177 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node177 node177Labels = Sparse.eval singlePairValue177 (familyPairVector B) := by
  have hp := single_label_three B hB node177
  have hl : node177Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node177 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node177 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node177 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node177 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node177 (EqualityPatterns.family3.label 1) = PairSemantics.raw881 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node177 PairSemantics.raw881; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical881 hH).trans (PairSemantics.sound3 hH)
  have hm2 : familyPairMoment B (groupedColumns node177 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node177 (EqualityPatterns.family3.label 2) = PairSemantics.raw8984 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node177 PairSemantics.raw8984; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8984 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node177 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value117 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node177 (EqualityPatterns.family3.label 3) = PairSemantics.raw849 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node177 PairSemantics.raw849; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical849 hH).trans (PairSemantics.sound117 hH)
  have hm4 : familyPairMoment B (groupedColumns node177 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value325 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node177 (EqualityPatterns.family3.label 4) = PairSemantics.raw382 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node177 PairSemantics.raw382; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical382 hH).trans (PairSemantics.sound325 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue177, PairSemantics.value0, PairSemantics.value3, PairSemantics.value46, PairSemantics.value117, PairSemantics.value325, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue178 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-25 / 288)), (2, (-5 / 96)), (27, (-5 / 72)), (55, (-5 / 18)), (68, (-5 / 36)), (125, (-5 / 18)), (197, (-5 / 18))]

theorem singlePair178 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node178 node178Labels = Sparse.eval singlePairValue178 (familyPairVector B) := by
  have hp := single_label_three B hB node178
  have hl : node178Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node178 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node178 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node178 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node178 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node178 (EqualityPatterns.family3.label 1) = PairSemantics.raw884 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node178 PairSemantics.raw884; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical884 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node178 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node178 (EqualityPatterns.family3.label 2) = PairSemantics.raw8981 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node178 PairSemantics.raw8981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8981 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node178 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value117 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node178 (EqualityPatterns.family3.label 3) = PairSemantics.raw849 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node178 PairSemantics.raw849; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical849 hH).trans (PairSemantics.sound117 hH)
  have hm4 : familyPairMoment B (groupedColumns node178 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value635 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node178 (EqualityPatterns.family3.label 4) = PairSemantics.raw383 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node178 PairSemantics.raw383; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical383 hH).trans (PairSemantics.sound635 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue178, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value117, PairSemantics.value635, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue179 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (175 / 864)), (2, (5 / 108)), (3, (-5 / 9)), (5, (-5 / 36)), (6, (5 / 288)), (7, (-5 / 18)), (9, (-5 / 216)), (12, (-5 / 18)), (13, (-10 / 27)), (23, (5 / 6)), (27, (5 / 24)), (35, (-5 / 18)), (54, (5 / 6)), (68, (25 / 72)), (70, (-5 / 54)), (125, (5 / 6)), (196, (5 / 9))]

theorem singlePair179 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node179 node179Labels = Sparse.eval singlePairValue179 (familyPairVector B) := by
  have hp := single_label_three B hB node179
  have hl : node179Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node179 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node179 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node179 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node179 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node179 (EqualityPatterns.family3.label 1) = PairSemantics.raw894 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node179 PairSemantics.raw894; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical894 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node179 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node179 (EqualityPatterns.family3.label 2) = PairSemantics.raw8968 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node179 PairSemantics.raw8968; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8968 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node179 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value380 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node179 (EqualityPatterns.family3.label 3) = PairSemantics.raw847 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node179 PairSemantics.raw847; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical847 hH).trans (PairSemantics.sound380 hH)
  have hm4 : familyPairMoment B (groupedColumns node179 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2109 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node179 (EqualityPatterns.family3.label 4) = PairSemantics.raw384 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node179 PairSemantics.raw384; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical384 hH).trans (PairSemantics.sound2109 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue179, PairSemantics.value0, PairSemantics.value4, PairSemantics.value26, PairSemantics.value380, PairSemantics.value2109, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue180 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 36)), (2, (5 / 216)), (3, (5 / 27)), (5, (5 / 108)), (6, (-5 / 432)), (7, (5 / 27)), (9, (5 / 216)), (13, (5 / 54)), (35, (5 / 27)), (68, (-5 / 72)), (70, (5 / 54)), (125, (-5 / 18))]

theorem singlePair180 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node180 node180Labels = Sparse.eval singlePairValue180 (familyPairVector B) := by
  have hp := single_label_three B hB node180
  have hl : node180Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node180 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node180 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node180 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node180 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node180 (EqualityPatterns.family3.label 1) = PairSemantics.raw893 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node180 PairSemantics.raw893; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical893 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node180 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node180 (EqualityPatterns.family3.label 2) = PairSemantics.raw8969 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node180 PairSemantics.raw8969; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8969 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node180 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value116 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node180 (EqualityPatterns.family3.label 3) = PairSemantics.raw848 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node180 PairSemantics.raw848; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical848 hH).trans (PairSemantics.sound116 hH)
  have hm4 : familyPairMoment B (groupedColumns node180 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value551 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node180 (EqualityPatterns.family3.label 4) = PairSemantics.raw385 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node180 PairSemantics.raw385; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical385 hH).trans (PairSemantics.sound551 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue180, PairSemantics.value0, PairSemantics.value4, PairSemantics.value26, PairSemantics.value116, PairSemantics.value551, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue181 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-25 / 288)), (2, (-65 / 864)), (5, (5 / 108)), (6, (-5 / 432)), (9, (5 / 216)), (54, (-5 / 18)), (62, (-5 / 18)), (68, (-5 / 72)), (260, (-5 / 18)), (264, (-5 / 18))]

theorem singlePair181 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node181 node181Labels = Sparse.eval singlePairValue181 (familyPairVector B) := by
  have hp := single_label_three B hB node181
  have hl : node181Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node181 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node181 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node181 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node181 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node181 (EqualityPatterns.family3.label 1) = PairSemantics.raw896 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node181 PairSemantics.raw896; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical896 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node181 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node181 (EqualityPatterns.family3.label 2) = PairSemantics.raw8967 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node181 PairSemantics.raw8967; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8967 hH).trans (PairSemantics.sound10 hH)
  have hm3 : familyPairMoment B (groupedColumns node181 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value116 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node181 (EqualityPatterns.family3.label 3) = PairSemantics.raw848 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node181 PairSemantics.raw848; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical848 hH).trans (PairSemantics.sound116 hH)
  have hm4 : familyPairMoment B (groupedColumns node181 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value331 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node181 (EqualityPatterns.family3.label 4) = PairSemantics.raw386 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node181 PairSemantics.raw386; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical386 hH).trans (PairSemantics.sound331 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue181, PairSemantics.value0, PairSemantics.value10, PairSemantics.value116, PairSemantics.value331, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue182 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 54)), (2, (-5 / 108)), (5, (5 / 216)), (23, (-5 / 18)), (27, (-5 / 72)), (54, (-5 / 18)), (68, (-5 / 36)), (125, (-5 / 18)), (196, (-5 / 18))]

theorem singlePair182 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node182 node182Labels = Sparse.eval singlePairValue182 (familyPairVector B) := by
  have hp := single_label_three B hB node182
  have hl : node182Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node182 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node182 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node182 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node182 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node182 (EqualityPatterns.family3.label 1) = PairSemantics.raw891 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node182 PairSemantics.raw891; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical891 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node182 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node182 (EqualityPatterns.family3.label 2) = PairSemantics.raw8973 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node182 PairSemantics.raw8973; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8973 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node182 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value117 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node182 (EqualityPatterns.family3.label 3) = PairSemantics.raw849 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node182 PairSemantics.raw849; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical849 hH).trans (PairSemantics.sound117 hH)
  have hm4 : familyPairMoment B (groupedColumns node182 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value631 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node182 (EqualityPatterns.family3.label 4) = PairSemantics.raw387 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node182 PairSemantics.raw387; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical387 hH).trans (PairSemantics.sound631 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue182, PairSemantics.value0, PairSemantics.value4, PairSemantics.value10, PairSemantics.value117, PairSemantics.value631, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue183 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-5 / 432)), (2, (5 / 432)), (5, (5 / 216)), (24, (-5 / 18)), (27, (-5 / 72)), (56, (-5 / 18)), (68, (-5 / 36)), (197, (-5 / 9))]

theorem singlePair183 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node183 node183Labels = Sparse.eval singlePairValue183 (familyPairVector B) := by
  have hp := single_label_three B hB node183
  have hl : node183Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node183 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node183 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node183 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node183 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node183 (EqualityPatterns.family3.label 1) = PairSemantics.raw893 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node183 PairSemantics.raw893; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical893 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node183 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node183 (EqualityPatterns.family3.label 2) = PairSemantics.raw8971 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node183 PairSemantics.raw8971; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8971 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node183 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value117 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node183 (EqualityPatterns.family3.label 3) = PairSemantics.raw849 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node183 PairSemantics.raw849; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical849 hH).trans (PairSemantics.sound117 hH)
  have hm4 : familyPairMoment B (groupedColumns node183 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value634 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node183 (EqualityPatterns.family3.label 4) = PairSemantics.raw388 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node183 PairSemantics.raw388; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical388 hH).trans (PairSemantics.sound634 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue183, PairSemantics.value0, PairSemantics.value11, PairSemantics.value26, PairSemantics.value117, PairSemantics.value634, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
