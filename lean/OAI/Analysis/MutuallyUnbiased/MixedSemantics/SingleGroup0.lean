import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleRules
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical160
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical162
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound6

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue8 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (-5 / 864)), (2, (-5 / 72)), (5, (25 / 72)), (6, (-5 / 72)), (7, (-5 / 9)), (9, (25 / 108)), (35, (-5 / 18)), (58, (-5 / 864)), (69, (-5 / 6)), (70, (-20 / 27)), (71, (-5 / 9)), (257, (-5 / 27))]

theorem singlePair8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node8 node8Labels = Sparse.eval singlePairValue8 (familyPairVector B) := by
  have hp := single_label_three B hB node8
  have hl : node8Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node8 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node8 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node8 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node8 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node8 (EqualityPatterns.family3.label 1) = PairSemantics.raw904 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node8 PairSemantics.raw904; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical904 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node8 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node8 (EqualityPatterns.family3.label 2) = PairSemantics.raw5140 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node8 PairSemantics.raw5140; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5140 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node8 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value66 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node8 (EqualityPatterns.family3.label 3) = PairSemantics.raw36 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node8 PairSemantics.raw36; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical36 hH).trans (PairSemantics.sound66 hH)
  have hm4 : familyPairMoment B (groupedColumns node8 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1379 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node8 (EqualityPatterns.family3.label 4) = PairSemantics.raw0 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node8 PairSemantics.raw0; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical0 hH).trans (PairSemantics.sound1379 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue8, PairSemantics.value0, PairSemantics.value10, PairSemantics.value66, PairSemantics.value232, PairSemantics.value1379, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue9 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (5 / 288)), (2, (-5 / 288)), (5, (-5 / 54)), (6, (5 / 108)), (9, (-5 / 36)), (58, (5 / 432)), (69, (5 / 54)), (70, (5 / 54)), (71, (5 / 27))]

theorem singlePair9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node9 node9Labels = Sparse.eval singlePairValue9 (familyPairVector B) := by
  have hp := single_label_three B hB node9
  have hl : node9Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node9 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node9 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node9 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node9 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node9 (EqualityPatterns.family3.label 1) = PairSemantics.raw906 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node9 PairSemantics.raw906; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical906 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node9 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node9 (EqualityPatterns.family3.label 2) = PairSemantics.raw5139 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node9 PairSemantics.raw5139; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5139 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node9 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value12 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node9 (EqualityPatterns.family3.label 3) = PairSemantics.raw37 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node9 PairSemantics.raw37; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical37 hH).trans (PairSemantics.sound12 hH)
  have hm4 : familyPairMoment B (groupedColumns node9 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value297 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node9 (EqualityPatterns.family3.label 4) = PairSemantics.raw1 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node9 PairSemantics.raw1; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical1 hH).trans (PairSemantics.sound297 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue9, PairSemantics.value0, PairSemantics.value10, PairSemantics.value12, PairSemantics.value232, PairSemantics.value297, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue10 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (-5 / 288)), (2, (-35 / 864)), (3, (-5 / 27)), (5, (5 / 18)), (6, (-5 / 144)), (7, (-5 / 9)), (8, (-5 / 27)), (9, (5 / 27)), (35, (-10 / 27)), (52, (-5 / 27)), (58, (-5 / 864)), (69, (-20 / 27)), (70, (-25 / 54)), (71, (-5 / 9)), (256, (5 / 9)), (257, (-5 / 27)), (495, (-5 / 27))]

theorem singlePair10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node10 node10Labels = Sparse.eval singlePairValue10 (familyPairVector B) := by
  have hp := single_label_three B hB node10
  have hl : node10Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node10 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node10 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node10 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node10 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node10 (EqualityPatterns.family3.label 1) = PairSemantics.raw908 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node10 PairSemantics.raw908; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical908 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node10 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node10 (EqualityPatterns.family3.label 2) = PairSemantics.raw5134 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node10 PairSemantics.raw5134; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5134 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node10 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value66 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node10 (EqualityPatterns.family3.label 3) = PairSemantics.raw36 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node10 PairSemantics.raw36; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical36 hH).trans (PairSemantics.sound66 hH)
  have hm4 : familyPairMoment B (groupedColumns node10 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1382 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node10 (EqualityPatterns.family3.label 4) = PairSemantics.raw2 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node10 PairSemantics.raw2; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical2 hH).trans (PairSemantics.sound1382 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue10, PairSemantics.value0, PairSemantics.value26, PairSemantics.value46, PairSemantics.value66, PairSemantics.value1382, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue11 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (25 / 864)), (2, (65 / 864)), (5, (-5 / 54)), (6, (5 / 144)), (9, (-25 / 216)), (52, (5 / 54)), (58, (5 / 432)), (69, (5 / 27)), (71, (5 / 27)), (495, (5 / 54))]

theorem singlePair11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node11 node11Labels = Sparse.eval singlePairValue11 (familyPairVector B) := by
  have hp := single_label_three B hB node11
  have hl : node11Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node11 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node11 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node11 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node11 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node11 (EqualityPatterns.family3.label 1) = PairSemantics.raw907 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node11 PairSemantics.raw907; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical907 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node11 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node11 (EqualityPatterns.family3.label 2) = PairSemantics.raw5136 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node11 PairSemantics.raw5136; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5136 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node11 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value12 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node11 (EqualityPatterns.family3.label 3) = PairSemantics.raw37 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node11 PairSemantics.raw37; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical37 hH).trans (PairSemantics.sound12 hH)
  have hm4 : familyPairMoment B (groupedColumns node11 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value301 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node11 (EqualityPatterns.family3.label 4) = PairSemantics.raw3 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node11 PairSemantics.raw3; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3 hH).trans (PairSemantics.sound301 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue11, PairSemantics.value0, PairSemantics.value12, PairSemantics.value26, PairSemantics.value46, PairSemantics.value301, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue12 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 96)), (2, (-5 / 288)), (5, (-5 / 72)), (7, (5 / 27)), (9, (-5 / 54)), (35, (5 / 54)), (69, (5 / 18)), (70, (5 / 18)), (71, (5 / 54)), (257, (5 / 54))]

theorem singlePair12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node12 node12Labels = Sparse.eval singlePairValue12 (familyPairVector B) := by
  have hp := single_label_three B hB node12
  have hl : node12Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node12 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node12 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node12 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node12 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node12 (EqualityPatterns.family3.label 1) = PairSemantics.raw906 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node12 PairSemantics.raw906; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical906 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node12 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node12 (EqualityPatterns.family3.label 2) = PairSemantics.raw5142 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node12 PairSemantics.raw5142; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5142 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node12 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value13 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node12 (EqualityPatterns.family3.label 3) = PairSemantics.raw38 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node12 PairSemantics.raw38; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical38 hH).trans (PairSemantics.sound13 hH)
  have hm4 : familyPairMoment B (groupedColumns node12 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value299 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node12 (EqualityPatterns.family3.label 4) = PairSemantics.raw4 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node12 PairSemantics.raw4; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4 hH).trans (PairSemantics.sound299 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue12, PairSemantics.value0, PairSemantics.value10, PairSemantics.value13, PairSemantics.value46, PairSemantics.value299, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue13 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-25 / 432)), (2, (-5 / 144)), (5, (5 / 54)), (6, (-5 / 108)), (9, (5 / 36)), (58, (-5 / 144))]

theorem singlePair13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node13 node13Labels = Sparse.eval singlePairValue13 (familyPairVector B) := by
  have hp := single_label_three B hB node13
  have hl : node13Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node13 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node13 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node13 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node13 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node13 (EqualityPatterns.family3.label 1) = PairSemantics.raw909 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node13 PairSemantics.raw909; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical909 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node13 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node13 (EqualityPatterns.family3.label 2) = PairSemantics.raw5141 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node13 PairSemantics.raw5141; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5141 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node13 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value6 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node13 (EqualityPatterns.family3.label 3) = PairSemantics.raw39 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node13 PairSemantics.raw39; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical39 hH).trans (PairSemantics.sound6 hH)
  have hm4 : familyPairMoment B (groupedColumns node13 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value71 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node13 (EqualityPatterns.family3.label 4) = PairSemantics.raw5 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node13 PairSemantics.raw5; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5 hH).trans (PairSemantics.sound71 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue13, PairSemantics.value0, PairSemantics.value6, PairSemantics.value10, PairSemantics.value46, PairSemantics.value71, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue14 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 864)), (2, (-5 / 864)), (5, (-5 / 108)), (6, (5 / 144)), (9, (-5 / 54)), (35, (5 / 27)), (58, (5 / 432)), (69, (5 / 54)), (70, (5 / 54)), (257, (5 / 27)), (495, (5 / 27))]

theorem singlePair14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node14 node14Labels = Sparse.eval singlePairValue14 (familyPairVector B) := by
  have hp := single_label_three B hB node14
  have hl : node14Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node14 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node14 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node14 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node14 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node14 (EqualityPatterns.family3.label 1) = PairSemantics.raw915 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node14 PairSemantics.raw915; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical915 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node14 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node14 (EqualityPatterns.family3.label 2) = PairSemantics.raw5125 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node14 PairSemantics.raw5125; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5125 hH).trans (PairSemantics.sound10 hH)
  have hm3 : familyPairMoment B (groupedColumns node14 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value12 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node14 (EqualityPatterns.family3.label 3) = PairSemantics.raw37 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node14 PairSemantics.raw37; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical37 hH).trans (PairSemantics.sound12 hH)
  have hm4 : familyPairMoment B (groupedColumns node14 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value304 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node14 (EqualityPatterns.family3.label 4) = PairSemantics.raw6 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node14 PairSemantics.raw6; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical6 hH).trans (PairSemantics.sound304 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue14, PairSemantics.value0, PairSemantics.value10, PairSemantics.value12, PairSemantics.value26, PairSemantics.value304, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue15 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 288)), (2, (35 / 864)), (5, (-5 / 72)), (7, (5 / 54)), (8, (5 / 54)), (9, (-5 / 54)), (69, (5 / 27)), (70, (5 / 54)), (71, (5 / 18)), (256, (-5 / 18))]

theorem singlePair15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node15 node15Labels = Sparse.eval singlePairValue15 (familyPairVector B) := by
  have hp := single_label_three B hB node15
  have hl : node15Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node15 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node15 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node15 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node15 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node15 (EqualityPatterns.family3.label 1) = PairSemantics.raw912 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node15 PairSemantics.raw912; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical912 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node15 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node15 (EqualityPatterns.family3.label 2) = PairSemantics.raw5131 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node15 PairSemantics.raw5131; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5131 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node15 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value13 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node15 (EqualityPatterns.family3.label 3) = PairSemantics.raw38 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node15 PairSemantics.raw38; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical38 hH).trans (PairSemantics.sound13 hH)
  have hm4 : familyPairMoment B (groupedColumns node15 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value303 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node15 (EqualityPatterns.family3.label 4) = PairSemantics.raw7 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node15 PairSemantics.raw7; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7 hH).trans (PairSemantics.sound303 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue15, PairSemantics.value0, PairSemantics.value13, PairSemantics.value26, PairSemantics.value46, PairSemantics.value303, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue16 : Sparse (Fin 909) := [(0, (11 / 432)), (2, (-5 / 216)), (5, (5 / 108)), (6, (-5 / 108)), (9, (5 / 54)), (58, (-5 / 144)), (495, (-5 / 27))]

theorem singlePair16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node16 node16Labels = Sparse.eval singlePairValue16 (familyPairVector B) := by
  have hp := single_label_three B hB node16
  have hl : node16Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node16 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node16 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node16 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node16 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node16 (EqualityPatterns.family3.label 1) = PairSemantics.raw914 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node16 PairSemantics.raw914; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical914 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node16 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node16 (EqualityPatterns.family3.label 2) = PairSemantics.raw5132 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node16 PairSemantics.raw5132; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5132 hH).trans (PairSemantics.sound10 hH)
  have hm3 : familyPairMoment B (groupedColumns node16 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value6 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node16 (EqualityPatterns.family3.label 3) = PairSemantics.raw39 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node16 PairSemantics.raw39; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical39 hH).trans (PairSemantics.sound6 hH)
  have hm4 : familyPairMoment B (groupedColumns node16 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value77 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node16 (EqualityPatterns.family3.label 4) = PairSemantics.raw8 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node16 PairSemantics.raw8; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8 hH).trans (PairSemantics.sound77 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue16, PairSemantics.value0, PairSemantics.value6, PairSemantics.value10, PairSemantics.value26, PairSemantics.value77, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue17 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-25 / 432)), (2, (-5 / 216)), (9, (5 / 36)), (69, (-5 / 27)), (70, (-5 / 27)), (71, (-5 / 27))]

theorem singlePair17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node17 node17Labels = Sparse.eval singlePairValue17 (familyPairVector B) := by
  have hp := single_label_three B hB node17
  have hl : node17Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node17 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node17 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node17 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node17 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node17 (EqualityPatterns.family3.label 1) = PairSemantics.raw909 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node17 PairSemantics.raw909; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical909 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node17 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node17 (EqualityPatterns.family3.label 2) = PairSemantics.raw5149 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node17 PairSemantics.raw5149; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5149 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node17 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value7 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node17 (EqualityPatterns.family3.label 3) = PairSemantics.raw40 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node17 PairSemantics.raw40; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical40 hH).trans (PairSemantics.sound7 hH)
  have hm4 : familyPairMoment B (groupedColumns node17 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value73 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node17 (EqualityPatterns.family3.label 4) = PairSemantics.raw9 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node17 PairSemantics.raw9; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9 hH).trans (PairSemantics.sound73 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue17, PairSemantics.value0, PairSemantics.value7, PairSemantics.value10, PairSemantics.value46, PairSemantics.value73, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue18 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 432)), (2, (5 / 144)), (9, (5 / 36)), (69, (-5 / 27)), (71, (-10 / 27))]

theorem singlePair18 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node18 node18Labels = Sparse.eval singlePairValue18 (familyPairVector B) := by
  have hp := single_label_three B hB node18
  have hl : node18Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node18 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node18 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node18 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node18 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node18 (EqualityPatterns.family3.label 1) = PairSemantics.raw914 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node18 PairSemantics.raw914; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical914 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node18 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node18 (EqualityPatterns.family3.label 2) = PairSemantics.raw5141 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node18 PairSemantics.raw5141; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5141 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node18 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value7 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node18 (EqualityPatterns.family3.label 3) = PairSemantics.raw40 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node18 PairSemantics.raw40; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical40 hH).trans (PairSemantics.sound7 hH)
  have hm4 : familyPairMoment B (groupedColumns node18 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value78 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node18 (EqualityPatterns.family3.label 4) = PairSemantics.raw10 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node18 PairSemantics.raw10; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical10 hH).trans (PairSemantics.sound78 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue18, PairSemantics.value0, PairSemantics.value7, PairSemantics.value26, PairSemantics.value46, PairSemantics.value78, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue19 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 72)), (2, (-5 / 72)), (9, (5 / 36)), (69, (-5 / 27)), (70, (-5 / 27)), (257, (-5 / 27))]

theorem singlePair19 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node19 node19Labels = Sparse.eval singlePairValue19 (familyPairVector B) := by
  have hp := single_label_three B hB node19
  have hl : node19Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node19 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node19 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node19 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node19 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node19 (EqualityPatterns.family3.label 1) = PairSemantics.raw918 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node19 PairSemantics.raw918; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical918 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node19 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node19 (EqualityPatterns.family3.label 2) = PairSemantics.raw5132 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node19 PairSemantics.raw5132; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5132 hH).trans (PairSemantics.sound10 hH)
  have hm3 : familyPairMoment B (groupedColumns node19 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value7 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node19 (EqualityPatterns.family3.label 3) = PairSemantics.raw40 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node19 PairSemantics.raw40; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical40 hH).trans (PairSemantics.sound7 hH)
  have hm4 : familyPairMoment B (groupedColumns node19 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value75 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node19 (EqualityPatterns.family3.label 4) = PairSemantics.raw11 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node19 PairSemantics.raw11; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical11 hH).trans (PairSemantics.sound75 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue19, PairSemantics.value0, PairSemantics.value7, PairSemantics.value10, PairSemantics.value75, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue20 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 72)), (2, (-5 / 72)), (9, (-5 / 18)), (58, (5 / 36))]

theorem singlePair20 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node20 node20Labels = Sparse.eval singlePairValue20 (familyPairVector B) := by
  have hp := single_label_three B hB node20
  have hl : node20Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node20 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node20 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node20 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node20 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node20 (EqualityPatterns.family3.label 1) = PairSemantics.raw917 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node20 PairSemantics.raw917; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical917 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node20 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node20 (EqualityPatterns.family3.label 2) = PairSemantics.raw5151 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node20 PairSemantics.raw5151; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5151 hH).trans (PairSemantics.sound10 hH)
  have hm3 : familyPairMoment B (groupedColumns node20 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value1 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node20 (EqualityPatterns.family3.label 3) = PairSemantics.raw41 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node20 PairSemantics.raw41; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical41 hH).trans (PairSemantics.sound1 hH)
  have hm4 : familyPairMoment B (groupedColumns node20 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value60 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node20 (EqualityPatterns.family3.label 4) = PairSemantics.raw12 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node20 PairSemantics.raw12; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical12 hH).trans (PairSemantics.sound60 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue20, PairSemantics.value0, PairSemantics.value1, PairSemantics.value10, PairSemantics.value60, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue21 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (25 / 864)), (2, (25 / 864)), (3, (-5 / 18)), (5, (-5 / 27)), (6, (5 / 72)), (7, (-5 / 18)), (9, (-95 / 216)), (35, (-25 / 54)), (52, (-5 / 9)), (58, (5 / 216)), (69, (-5 / 9)), (70, (-5 / 18)), (71, (-5 / 18)), (256, (5 / 6)), (257, (-5 / 27)), (495, (-5 / 18))]

theorem singlePair21 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node21 node21Labels = Sparse.eval singlePairValue21 (familyPairVector B) := by
  have hp := single_label_three B hB node21
  have hl : node21Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node21 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node21 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node21 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node21 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node21 (EqualityPatterns.family3.label 1) = PairSemantics.raw879 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node21 PairSemantics.raw879; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical879 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node21 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node21 (EqualityPatterns.family3.label 2) = PairSemantics.raw5207 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node21 PairSemantics.raw5207; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5207 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node21 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value295 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node21 (EqualityPatterns.family3.label 3) = PairSemantics.raw42 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node21 PairSemantics.raw42; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical42 hH).trans (PairSemantics.sound295 hH)
  have hm4 : familyPairMoment B (groupedColumns node21 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1380 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node21 (EqualityPatterns.family3.label 4) = PairSemantics.raw13 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node21 PairSemantics.raw13; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical13 hH).trans (PairSemantics.sound1380 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue21, PairSemantics.value0, PairSemantics.value10, PairSemantics.value232, PairSemantics.value295, PairSemantics.value1380, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue22 : Sparse (Fin 909) := [(0, (29 / 864)), (1, (-5 / 216)), (2, (5 / 432)), (6, (5 / 96)), (7, (-5 / 18)), (8, (-5 / 9)), (9, (-10 / 27)), (58, (5 / 216)), (69, (-5 / 9)), (70, (-5 / 27)), (71, (-10 / 9))]

theorem singlePair22 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node22 node22Labels = Sparse.eval singlePairValue22 (familyPairVector B) := by
  have hp := single_label_three B hB node22
  have hl : node22Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node22 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node22 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node22 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node22 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node22 (EqualityPatterns.family3.label 1) = PairSemantics.raw883 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node22 PairSemantics.raw883; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical883 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node22 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node22 (EqualityPatterns.family3.label 2) = PairSemantics.raw5206 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node22 PairSemantics.raw5206; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5206 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node22 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value295 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node22 (EqualityPatterns.family3.label 3) = PairSemantics.raw42 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node22 PairSemantics.raw42; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical42 hH).trans (PairSemantics.sound295 hH)
  have hm4 : familyPairMoment B (groupedColumns node22 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1438 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node22 (EqualityPatterns.family3.label 4) = PairSemantics.raw14 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node22 PairSemantics.raw14; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical14 hH).trans (PairSemantics.sound1438 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue22, PairSemantics.value0, PairSemantics.value11, PairSemantics.value26, PairSemantics.value295, PairSemantics.value1438, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue23 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-65 / 864)), (2, (-35 / 864)), (6, (-5 / 864)), (7, (5 / 54)), (9, (5 / 54)), (58, (-5 / 864)), (69, (5 / 27)), (70, (5 / 54)), (71, (5 / 27))]

theorem singlePair23 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node23 node23Labels = Sparse.eval singlePairValue23 (familyPairVector B) := by
  have hp := single_label_three B hB node23
  have hl : node23Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node23 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node23 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node23 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node23 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node23 (EqualityPatterns.family3.label 1) = PairSemantics.raw884 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node23 PairSemantics.raw884; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical884 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node23 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node23 (EqualityPatterns.family3.label 2) = PairSemantics.raw5205 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node23 PairSemantics.raw5205; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5205 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node23 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value66 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node23 (EqualityPatterns.family3.label 3) = PairSemantics.raw43 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node23 PairSemantics.raw43; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical43 hH).trans (PairSemantics.sound66 hH)
  have hm4 : familyPairMoment B (groupedColumns node23 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value389 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node23 (EqualityPatterns.family3.label 4) = PairSemantics.raw15 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node23 PairSemantics.raw15; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical15 hH).trans (PairSemantics.sound389 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue23, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value66, PairSemantics.value389, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
