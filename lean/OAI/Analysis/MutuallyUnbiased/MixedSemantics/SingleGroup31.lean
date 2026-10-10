import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleRules
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical129
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical151
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical152
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical159
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical160
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical161
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical162
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical238
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical239
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical240
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical241
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical280
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound41

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue507 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 12)), (12, (5 / 9))]

theorem singlePair507 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node507 node507Labels = Sparse.eval singlePairValue507 (familyPairVector B) := by
  have hp := single_label_three B hB node507
  have hl : node507Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node507 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node507 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node507 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node507 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node507 (EqualityPatterns.family3.label 1) = PairSemantics.raw5214 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node507 PairSemantics.raw5214; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5214 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node507 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node507 (EqualityPatterns.family3.label 2) = PairSemantics.raw8985 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node507 PairSemantics.raw8985; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8985 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node507 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node507 (EqualityPatterns.family3.label 3) = PairSemantics.raw5183 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node507 PairSemantics.raw5183; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5183 hH).trans (PairSemantics.sound4 hH)
  have hm4 : familyPairMoment B (groupedColumns node507 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value41 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node507 (EqualityPatterns.family3.label 4) = PairSemantics.raw4141 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node507 PairSemantics.raw4141; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4141 hH).trans (PairSemantics.sound41 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue507, PairSemantics.value0, PairSemantics.value4, PairSemantics.value41, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue508 : Sparse (Fin 909) := [(0, (13 / 216)), (1, (5 / 216)), (5, (-5 / 72)), (8, (-5 / 18)), (24, (5 / 18)), (27, (5 / 24)), (30, (5 / 9))]

theorem singlePair508 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node508 node508Labels = Sparse.eval singlePairValue508 (familyPairVector B) := by
  have hp := single_label_three B hB node508
  have hl : node508Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node508 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node508 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node508 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node508 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node508 (EqualityPatterns.family3.label 1) = PairSemantics.raw7668 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node508 PairSemantics.raw7668; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7668 hH).trans (PairSemantics.sound65 hH)
  have hm2 : familyPairMoment B (groupedColumns node508 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node508 (EqualityPatterns.family3.label 2) = PairSemantics.raw7680 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node508 PairSemantics.raw7680; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7680 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node508 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value716 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node508 (EqualityPatterns.family3.label 3) = PairSemantics.raw5109 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node508 PairSemantics.raw5109; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5109 hH).trans (PairSemantics.sound716 hH)
  have hm4 : familyPairMoment B (groupedColumns node508 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2651 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node508 (EqualityPatterns.family3.label 4) = PairSemantics.raw4859 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node508 PairSemantics.raw4859; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4859 hH).trans (PairSemantics.sound2651 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue508, PairSemantics.value0, PairSemantics.value65, PairSemantics.value716, PairSemantics.value2651, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue509 : Sparse (Fin 909) := [(0, (2 / 27)), (1, (5 / 108)), (5, (5 / 216)), (8, (5 / 54)), (27, (-5 / 72)), (30, (-5 / 18))]

theorem singlePair509 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node509 node509Labels = Sparse.eval singlePairValue509 (familyPairVector B) := by
  have hp := single_label_three B hB node509
  have hl : node509Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node509 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node509 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node509 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node509 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node509 (EqualityPatterns.family3.label 1) = PairSemantics.raw7670 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node509 PairSemantics.raw7670; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7670 hH).trans (PairSemantics.sound65 hH)
  have hm2 : familyPairMoment B (groupedColumns node509 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node509 (EqualityPatterns.family3.label 2) = PairSemantics.raw7677 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node509 PairSemantics.raw7677; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7677 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node509 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value231 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node509 (EqualityPatterns.family3.label 3) = PairSemantics.raw5110 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node509 PairSemantics.raw5110; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5110 hH).trans (PairSemantics.sound231 hH)
  have hm4 : familyPairMoment B (groupedColumns node509 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1130 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node509 (EqualityPatterns.family3.label 4) = PairSemantics.raw4860 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node509 PairSemantics.raw4860; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4860 hH).trans (PairSemantics.sound1130 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue509, PairSemantics.value0, PairSemantics.value65, PairSemantics.value231, PairSemantics.value1130, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue510 : Sparse (Fin 909) := [(0, (13 / 216)), (1, (5 / 216)), (27, (5 / 36)), (30, (5 / 9))]

theorem singlePair510 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node510 node510Labels = Sparse.eval singlePairValue510 (familyPairVector B) := by
  have hp := single_label_three B hB node510
  have hl : node510Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node510 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node510 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node510 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node510 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node510 (EqualityPatterns.family3.label 1) = PairSemantics.raw7678 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node510 PairSemantics.raw7678; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7678 hH).trans (PairSemantics.sound65 hH)
  have hm2 : familyPairMoment B (groupedColumns node510 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node510 (EqualityPatterns.family3.label 2) = PairSemantics.raw7678 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node510 PairSemantics.raw7678; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7678 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node510 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value45 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node510 (EqualityPatterns.family3.label 3) = PairSemantics.raw5116 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node510 PairSemantics.raw5116; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5116 hH).trans (PairSemantics.sound45 hH)
  have hm4 : familyPairMoment B (groupedColumns node510 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value275 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node510 (EqualityPatterns.family3.label 4) = PairSemantics.raw4861 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node510 PairSemantics.raw4861; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4861 hH).trans (PairSemantics.sound275 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue510, PairSemantics.value0, PairSemantics.value45, PairSemantics.value65, PairSemantics.value275, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue511 : Sparse (Fin 909) := [(0, (7 / 432)), (1, (35 / 144)), (2, (-115 / 864)), (3, (-10 / 27)), (4, (-5 / 18)), (5, (-5 / 216)), (6, (5 / 864)), (31, (5 / 9)), (51, (5 / 18)), (52, (-5 / 54))]

theorem singlePair511 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node511 node511Labels = Sparse.eval singlePairValue511 (familyPairVector B) := by
  have hp := single_label_three B hB node511
  have hl : node511Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node511 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node511 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node511 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node511 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node511 (EqualityPatterns.family3.label 1) = PairSemantics.raw7625 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node511 PairSemantics.raw7625; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7625 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node511 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node511 (EqualityPatterns.family3.label 2) = PairSemantics.raw7729 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node511 PairSemantics.raw7729; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7729 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node511 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value717 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node511 (EqualityPatterns.family3.label 3) = PairSemantics.raw5120 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node511 PairSemantics.raw5120; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5120 hH).trans (PairSemantics.sound717 hH)
  have hm4 : familyPairMoment B (groupedColumns node511 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2659 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node511 (EqualityPatterns.family3.label 4) = PairSemantics.raw4865 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node511 PairSemantics.raw4865; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4865 hH).trans (PairSemantics.sound2659 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue511, PairSemantics.value0, PairSemantics.value65, PairSemantics.value232, PairSemantics.value717, PairSemantics.value2659, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue512 : Sparse (Fin 909) := [(0, (-7 / 216)), (1, (65 / 432)), (2, (-25 / 432)), (3, (-35 / 54)), (4, (-10 / 27)), (12, (-5 / 27)), (25, (5 / 18)), (26, (-5 / 54)), (31, (5 / 9)), (33, (5 / 18))]

theorem singlePair512 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node512 node512Labels = Sparse.eval singlePairValue512 (familyPairVector B) := by
  have hp := single_label_three B hB node512
  have hl : node512Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node512 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node512 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node512 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node512 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node512 (EqualityPatterns.family3.label 1) = PairSemantics.raw7633 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node512 PairSemantics.raw7633; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7633 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node512 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value1323 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node512 (EqualityPatterns.family3.label 2) = PairSemantics.raw7727 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node512 PairSemantics.raw7727; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7727 hH).trans (PairSemantics.sound1323 hH)
  have hm3 : familyPairMoment B (groupedColumns node512 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node512 (EqualityPatterns.family3.label 3) = PairSemantics.raw5123 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node512 PairSemantics.raw5123; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5123 hH).trans (PairSemantics.sound46 hH)
  have hm4 : familyPairMoment B (groupedColumns node512 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2295 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node512 (EqualityPatterns.family3.label 4) = PairSemantics.raw4866 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node512 PairSemantics.raw4866; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4866 hH).trans (PairSemantics.sound2295 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue512, PairSemantics.value0, PairSemantics.value46, PairSemantics.value232, PairSemantics.value1323, PairSemantics.value2295, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue513 : Sparse (Fin 909) := [(1, (10 / 27)), (2, (-5 / 54)), (3, (-10 / 27)), (4, (-10 / 27)), (12, (-5 / 54)), (31, (5 / 9))]

theorem singlePair513 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node513 node513Labels = Sparse.eval singlePairValue513 (familyPairVector B) := by
  have hp := single_label_three B hB node513
  have hl : node513Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node513 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node513 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node513 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node513 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node513 (EqualityPatterns.family3.label 1) = PairSemantics.raw7630 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node513 PairSemantics.raw7630; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7630 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node513 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node513 (EqualityPatterns.family3.label 2) = PairSemantics.raw7733 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node513 PairSemantics.raw7733; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7733 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node513 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node513 (EqualityPatterns.family3.label 3) = PairSemantics.raw5127 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node513 PairSemantics.raw5127; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5127 hH).trans (PairSemantics.sound232 hH)
  have hm4 : familyPairMoment B (groupedColumns node513 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2667 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node513 (EqualityPatterns.family3.label 4) = PairSemantics.raw4867 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node513 PairSemantics.raw4867; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4867 hH).trans (PairSemantics.sound2667 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue513, PairSemantics.value0, PairSemantics.value65, PairSemantics.value232, PairSemantics.value2667, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue514 : Sparse (Fin 909) := [(0, (31 / 864)), (1, (-5 / 216)), (2, (5 / 288)), (3, (5 / 54)), (4, (5 / 54)), (31, (-5 / 18))]

theorem singlePair514 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node514 node514Labels = Sparse.eval singlePairValue514 (familyPairVector B) := by
  have hp := single_label_three B hB node514
  have hl : node514Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node514 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node514 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node514 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node514 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node514 (EqualityPatterns.family3.label 1) = PairSemantics.raw7634 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node514 PairSemantics.raw7634; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7634 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node514 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node514 (EqualityPatterns.family3.label 2) = PairSemantics.raw7730 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node514 PairSemantics.raw7730; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7730 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node514 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node514 (EqualityPatterns.family3.label 3) = PairSemantics.raw5128 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node514 PairSemantics.raw5128; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5128 hH).trans (PairSemantics.sound46 hH)
  have hm4 : familyPairMoment B (groupedColumns node514 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1141 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node514 (EqualityPatterns.family3.label 4) = PairSemantics.raw4869 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node514 PairSemantics.raw4869; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4869 hH).trans (PairSemantics.sound1141 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue514, PairSemantics.value0, PairSemantics.value46, PairSemantics.value65, PairSemantics.value232, PairSemantics.value1141, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue515 : Sparse (Fin 909) := []

theorem singlePair515 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node515 node515Labels = Sparse.eval singlePairValue515 (familyPairVector B) := by
  have hp := single_label_three B hB node515
  have hl : node515Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node515 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node515 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node515 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node515 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node515 (EqualityPatterns.family3.label 1) = PairSemantics.raw7634 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node515 PairSemantics.raw7634; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7634 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node515 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value5 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node515 (EqualityPatterns.family3.label 2) = PairSemantics.raw7737 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node515 PairSemantics.raw7737; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7737 hH).trans (PairSemantics.sound5 hH)
  have hm3 : familyPairMoment B (groupedColumns node515 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node515 (EqualityPatterns.family3.label 3) = PairSemantics.raw5139 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node515 PairSemantics.raw5139; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5139 hH).trans (PairSemantics.sound232 hH)
  have hm4 : familyPairMoment B (groupedColumns node515 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1153 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node515 (EqualityPatterns.family3.label 4) = PairSemantics.raw4877 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node515 PairSemantics.raw4877; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4877 hH).trans (PairSemantics.sound1153 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue515, PairSemantics.value0, PairSemantics.value5, PairSemantics.value232, PairSemantics.value1153, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue516 : Sparse (Fin 909) := [(0, (17 / 432)), (1, (-5 / 144)), (2, (5 / 216)), (31, (5 / 9))]

theorem singlePair516 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node516 node516Labels = Sparse.eval singlePairValue516 (familyPairVector B) := by
  have hp := single_label_three B hB node516
  have hl : node516Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node516 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node516 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node516 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node516 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node516 (EqualityPatterns.family3.label 1) = PairSemantics.raw7639 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node516 PairSemantics.raw7639; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7639 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node516 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node516 (EqualityPatterns.family3.label 2) = PairSemantics.raw7731 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node516 PairSemantics.raw7731; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7731 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node516 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node516 (EqualityPatterns.family3.label 3) = PairSemantics.raw5141 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node516 PairSemantics.raw5141; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5141 hH).trans (PairSemantics.sound46 hH)
  have hm4 : familyPairMoment B (groupedColumns node516 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value276 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node516 (EqualityPatterns.family3.label 4) = PairSemantics.raw4878 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node516 PairSemantics.raw4878; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4878 hH).trans (PairSemantics.sound276 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue516, PairSemantics.value0, PairSemantics.value46, PairSemantics.value65, PairSemantics.value276, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue517 : Sparse (Fin 909) := [(0, (17 / 288)), (1, (25 / 216)), (2, (-5 / 72)), (5, (-5 / 216)), (6, (5 / 864)), (8, (-5 / 27)), (27, (5 / 72)), (30, (5 / 18))]

theorem singlePair517 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node517 node517Labels = Sparse.eval singlePairValue517 (familyPairVector B) := by
  have hp := single_label_three B hB node517
  have hl : node517Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node517 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node517 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node517 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node517 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node517 (EqualityPatterns.family3.label 1) = PairSemantics.raw7668 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node517 PairSemantics.raw7668; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7668 hH).trans (PairSemantics.sound65 hH)
  have hm2 : familyPairMoment B (groupedColumns node517 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node517 (EqualityPatterns.family3.label 2) = PairSemantics.raw7702 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node517 PairSemantics.raw7702; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7702 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node517 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value717 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node517 (EqualityPatterns.family3.label 3) = PairSemantics.raw5120 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node517 PairSemantics.raw5120; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5120 hH).trans (PairSemantics.sound717 hH)
  have hm4 : familyPairMoment B (groupedColumns node517 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2655 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node517 (EqualityPatterns.family3.label 4) = PairSemantics.raw4880 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node517 PairSemantics.raw4880; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4880 hH).trans (PairSemantics.sound2655 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue517, PairSemantics.value0, PairSemantics.value65, PairSemantics.value717, PairSemantics.value2655, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue518 : Sparse (Fin 909) := [(0, (-13 / 864)), (1, (-5 / 864)), (2, (-5 / 432)), (3, (-5 / 27)), (4, (-5 / 27)), (31, (5 / 18))]

theorem singlePair518 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node518 node518Labels = Sparse.eval singlePairValue518 (familyPairVector B) := by
  have hp := single_label_three B hB node518
  have hl : node518Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node518 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node518 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node518 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node518 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value1323 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node518 (EqualityPatterns.family3.label 1) = PairSemantics.raw7658 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node518 PairSemantics.raw7658; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7658 hH).trans (PairSemantics.sound1323 hH)
  have hm2 : familyPairMoment B (groupedColumns node518 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node518 (EqualityPatterns.family3.label 2) = PairSemantics.raw7711 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node518 PairSemantics.raw7711; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7711 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node518 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node518 (EqualityPatterns.family3.label 3) = PairSemantics.raw5123 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node518 PairSemantics.raw5123; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5123 hH).trans (PairSemantics.sound46 hH)
  have hm4 : familyPairMoment B (groupedColumns node518 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2665 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node518 (EqualityPatterns.family3.label 4) = PairSemantics.raw4881 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node518 PairSemantics.raw4881; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4881 hH).trans (PairSemantics.sound2665 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue518, PairSemantics.value0, PairSemantics.value46, PairSemantics.value65, PairSemantics.value1323, PairSemantics.value2665, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue519 : Sparse (Fin 909) := [(0, (1 / 864)), (1, (245 / 864)), (2, (-25 / 432)), (3, (-10 / 27)), (4, (-5 / 18)), (26, (-5 / 54)), (31, (5 / 18))]

theorem singlePair519 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node519 node519Labels = Sparse.eval singlePairValue519 (familyPairVector B) := by
  have hp := single_label_three B hB node519
  have hl : node519Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node519 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node519 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node519 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node519 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node519 (EqualityPatterns.family3.label 1) = PairSemantics.raw7654 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node519 PairSemantics.raw7654; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7654 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node519 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node519 (EqualityPatterns.family3.label 2) = PairSemantics.raw7715 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node519 PairSemantics.raw7715; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7715 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node519 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node519 (EqualityPatterns.family3.label 3) = PairSemantics.raw5127 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node519 PairSemantics.raw5127; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5127 hH).trans (PairSemantics.sound232 hH)
  have hm4 : familyPairMoment B (groupedColumns node519 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2669 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node519 (EqualityPatterns.family3.label 4) = PairSemantics.raw4882 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node519 PairSemantics.raw4882; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4882 hH).trans (PairSemantics.sound2669 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue519, PairSemantics.value0, PairSemantics.value65, PairSemantics.value232, PairSemantics.value2669, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue520 : Sparse (Fin 909) := [(0, (47 / 864)), (1, (115 / 432)), (2, (-55 / 864)), (3, (-5 / 54)), (4, (-5 / 27))]

theorem singlePair520 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node520 node520Labels = Sparse.eval singlePairValue520 (familyPairVector B) := by
  have hp := single_label_three B hB node520
  have hl : node520Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node520 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node520 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node520 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node520 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node520 (EqualityPatterns.family3.label 1) = PairSemantics.raw7676 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node520 PairSemantics.raw7676; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7676 hH).trans (PairSemantics.sound65 hH)
  have hm2 : familyPairMoment B (groupedColumns node520 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node520 (EqualityPatterns.family3.label 2) = PairSemantics.raw7704 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node520 PairSemantics.raw7704; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7704 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node520 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node520 (EqualityPatterns.family3.label 3) = PairSemantics.raw5127 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node520 PairSemantics.raw5127; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5127 hH).trans (PairSemantics.sound232 hH)
  have hm4 : familyPairMoment B (groupedColumns node520 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2660 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node520 (EqualityPatterns.family3.label 4) = PairSemantics.raw4884 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node520 PairSemantics.raw4884; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4884 hH).trans (PairSemantics.sound2660 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue520, PairSemantics.value0, PairSemantics.value65, PairSemantics.value232, PairSemantics.value2660, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue521 : Sparse (Fin 909) := [(0, (11 / 144)), (1, (-5 / 72)), (2, (5 / 144))]

theorem singlePair521 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node521 node521Labels = Sparse.eval singlePairValue521 (familyPairVector B) := by
  have hp := single_label_three B hB node521
  have hl : node521Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node521 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node521 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node521 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node521 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node521 (EqualityPatterns.family3.label 1) = PairSemantics.raw7677 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node521 PairSemantics.raw7677; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7677 hH).trans (PairSemantics.sound65 hH)
  have hm2 : familyPairMoment B (groupedColumns node521 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node521 (EqualityPatterns.family3.label 2) = PairSemantics.raw7703 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node521 PairSemantics.raw7703; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7703 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node521 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node521 (EqualityPatterns.family3.label 3) = PairSemantics.raw5128 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node521 PairSemantics.raw5128; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5128 hH).trans (PairSemantics.sound46 hH)
  have hm4 : familyPairMoment B (groupedColumns node521 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1135 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node521 (EqualityPatterns.family3.label 4) = PairSemantics.raw4885 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node521 PairSemantics.raw4885; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4885 hH).trans (PairSemantics.sound1135 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue521, PairSemantics.value0, PairSemantics.value46, PairSemantics.value65, PairSemantics.value1135, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue522 : Sparse (Fin 909) := [(0, (5 / 288)), (1, (5 / 864)), (2, (-5 / 216)), (3, (5 / 27)), (26, (5 / 54))]

theorem singlePair522 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node522 node522Labels = Sparse.eval singlePairValue522 (familyPairVector B) := by
  have hp := single_label_three B hB node522
  have hl : node522Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node522 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node522 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node522 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node522 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node522 (EqualityPatterns.family3.label 1) = PairSemantics.raw7659 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node522 PairSemantics.raw7659; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7659 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node522 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node522 (EqualityPatterns.family3.label 2) = PairSemantics.raw7717 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node522 PairSemantics.raw7717; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7717 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node522 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node522 (EqualityPatterns.family3.label 3) = PairSemantics.raw5139 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node522 PairSemantics.raw5139; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5139 hH).trans (PairSemantics.sound232 hH)
  have hm4 : familyPairMoment B (groupedColumns node522 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value710 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node522 (EqualityPatterns.family3.label 4) = PairSemantics.raw4887 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node522 PairSemantics.raw4887; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4887 hH).trans (PairSemantics.sound710 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue522, PairSemantics.value0, PairSemantics.value11, PairSemantics.value232, PairSemantics.value710, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
