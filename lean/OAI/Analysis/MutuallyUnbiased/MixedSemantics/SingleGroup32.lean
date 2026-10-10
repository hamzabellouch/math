import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleRules
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical152
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical154
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical155
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical160
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical161
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical162
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical230
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical231
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical239
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical240
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical241
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical242
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical282
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound36
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound43

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue523 : Sparse (Fin 909) := [(0, (49 / 864)), (1, (-25 / 432)), (2, (-5 / 864)), (3, (5 / 54)), (4, (5 / 27))]

theorem singlePair523 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node523 node523Labels = Sparse.eval singlePairValue523 (familyPairVector B) := by
  have hp := single_label_three B hB node523
  have hl : node523Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node523 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node523 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node523 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node523 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node523 (EqualityPatterns.family3.label 1) = PairSemantics.raw7669 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node523 PairSemantics.raw7669; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7669 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node523 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node523 (EqualityPatterns.family3.label 2) = PairSemantics.raw7714 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node523 PairSemantics.raw7714; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7714 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node523 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node523 (EqualityPatterns.family3.label 3) = PairSemantics.raw5139 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node523 PairSemantics.raw5139; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5139 hH).trans (PairSemantics.sound232 hH)
  have hm4 : familyPairMoment B (groupedColumns node523 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value709 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node523 (EqualityPatterns.family3.label 4) = PairSemantics.raw4888 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node523 PairSemantics.raw4888; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4888 hH).trans (PairSemantics.sound709 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue523, PairSemantics.value0, PairSemantics.value11, PairSemantics.value65, PairSemantics.value232, PairSemantics.value709, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue524 : Sparse (Fin 909) := [(0, (-13 / 432)), (1, (-5 / 18)), (2, (5 / 144)), (3, (-10 / 27)), (12, (-10 / 27)), (25, (5 / 18))]

theorem singlePair524 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node524 node524Labels = Sparse.eval singlePairValue524 (familyPairVector B) := by
  have hp := single_label_three B hB node524
  have hl : node524Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node524 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node524 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node524 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node524 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value1323 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node524 (EqualityPatterns.family3.label 1) = PairSemantics.raw7658 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node524 PairSemantics.raw7658; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7658 hH).trans (PairSemantics.sound1323 hH)
  have hm2 : familyPairMoment B (groupedColumns node524 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value1323 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node524 (EqualityPatterns.family3.label 2) = PairSemantics.raw7739 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node524 PairSemantics.raw7739; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7739 hH).trans (PairSemantics.sound1323 hH)
  have hm3 : familyPairMoment B (groupedColumns node524 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node524 (EqualityPatterns.family3.label 3) = PairSemantics.raw5163 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node524 PairSemantics.raw5163; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5163 hH).trans (PairSemantics.sound4 hH)
  have hm4 : familyPairMoment B (groupedColumns node524 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2304 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node524 (EqualityPatterns.family3.label 4) = PairSemantics.raw4929 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node524 PairSemantics.raw4929; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4929 hH).trans (PairSemantics.sound2304 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue524, PairSemantics.value0, PairSemantics.value4, PairSemantics.value1323, PairSemantics.value2304, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue525 : Sparse (Fin 909) := [(0, (1 / 72)), (1, (35 / 432)), (2, (5 / 432)), (3, (-5 / 27)), (4, (-10 / 27)), (12, (-5 / 54))]

theorem singlePair525 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node525 node525Labels = Sparse.eval singlePairValue525 (familyPairVector B) := by
  have hp := single_label_three B hB node525
  have hl : node525Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node525 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node525 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node525 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node525 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value1323 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node525 (EqualityPatterns.family3.label 1) = PairSemantics.raw7658 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node525 PairSemantics.raw7658; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7658 hH).trans (PairSemantics.sound1323 hH)
  have hm2 : familyPairMoment B (groupedColumns node525 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node525 (EqualityPatterns.family3.label 2) = PairSemantics.raw7741 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node525 PairSemantics.raw7741; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7741 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node525 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node525 (EqualityPatterns.family3.label 3) = PairSemantics.raw5164 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node525 PairSemantics.raw5164; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5164 hH).trans (PairSemantics.sound11 hH)
  have hm4 : familyPairMoment B (groupedColumns node525 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2306 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node525 (EqualityPatterns.family3.label 4) = PairSemantics.raw4930 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node525 PairSemantics.raw4930; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4930 hH).trans (PairSemantics.sound2306 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue525, PairSemantics.value0, PairSemantics.value11, PairSemantics.value65, PairSemantics.value1323, PairSemantics.value2306, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue526 : Sparse (Fin 909) := [(0, (67 / 864)), (1, (-25 / 288)), (4, (5 / 54))]

theorem singlePair526 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node526 node526Labels = Sparse.eval singlePairValue526 (familyPairVector B) := by
  have hp := single_label_three B hB node526
  have hl : node526Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node526 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node526 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node526 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node526 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node526 (EqualityPatterns.family3.label 1) = PairSemantics.raw7677 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node526 PairSemantics.raw7677; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7677 hH).trans (PairSemantics.sound65 hH)
  have hm2 : familyPairMoment B (groupedColumns node526 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node526 (EqualityPatterns.family3.label 2) = PairSemantics.raw7732 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node526 PairSemantics.raw7732; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7732 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node526 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node526 (EqualityPatterns.family3.label 3) = PairSemantics.raw5167 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node526 PairSemantics.raw5167; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5167 hH).trans (PairSemantics.sound11 hH)
  have hm4 : familyPairMoment B (groupedColumns node526 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value711 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node526 (EqualityPatterns.family3.label 4) = PairSemantics.raw4941 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node526 PairSemantics.raw4941; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4941 hH).trans (PairSemantics.sound711 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue526, PairSemantics.value0, PairSemantics.value11, PairSemantics.value65, PairSemantics.value711, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue527 : Sparse (Fin 909) := [(0, (1 / 18)), (1, (5 / 18))]

theorem singlePair527 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node527 node527Labels = Sparse.eval singlePairValue527 (familyPairVector B) := by
  have hp := single_label_three B hB node527
  have hl : node527Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node527 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node527 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node527 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node527 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node527 (EqualityPatterns.family3.label 1) = PairSemantics.raw7678 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node527 PairSemantics.raw7678; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7678 hH).trans (PairSemantics.sound65 hH)
  have hm2 : familyPairMoment B (groupedColumns node527 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node527 (EqualityPatterns.family3.label 2) = PairSemantics.raw7731 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node527 PairSemantics.raw7731; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7731 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node527 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node527 (EqualityPatterns.family3.label 3) = PairSemantics.raw5169 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node527 PairSemantics.raw5169; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5169 hH).trans (PairSemantics.sound4 hH)
  have hm4 : familyPairMoment B (groupedColumns node527 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value227 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node527 (EqualityPatterns.family3.label 4) = PairSemantics.raw4943 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node527 PairSemantics.raw4943; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4943 hH).trans (PairSemantics.sound227 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue527, PairSemantics.value0, PairSemantics.value4, PairSemantics.value65, PairSemantics.value227, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue528 : Sparse (Fin 909) := [(0, (23 / 432)), (1, (-5 / 144)), (4, (-5 / 27))]

theorem singlePair528 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node528 node528Labels = Sparse.eval singlePairValue528 (familyPairVector B) := by
  have hp := single_label_three B hB node528
  have hl : node528Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node528 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node528 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node528 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node528 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node528 (EqualityPatterns.family3.label 1) = PairSemantics.raw7671 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node528 PairSemantics.raw7671; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7671 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node528 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node528 (EqualityPatterns.family3.label 2) = PairSemantics.raw7738 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node528 PairSemantics.raw7738; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7738 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node528 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node528 (EqualityPatterns.family3.label 3) = PairSemantics.raw5177 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node528 PairSemantics.raw5177; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5177 hH).trans (PairSemantics.sound11 hH)
  have hm4 : familyPairMoment B (groupedColumns node528 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value230 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node528 (EqualityPatterns.family3.label 4) = PairSemantics.raw4946 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node528 PairSemantics.raw4946; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4946 hH).trans (PairSemantics.sound230 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue528, PairSemantics.value0, PairSemantics.value11, PairSemantics.value65, PairSemantics.value230, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue529 : Sparse (Fin 909) := []

theorem singlePair529 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node529 node529Labels = Sparse.eval singlePairValue529 (familyPairVector B) := by
  have hp := single_label_three B hB node529
  have hl : node529Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node529 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node529 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node529 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node529 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node529 (EqualityPatterns.family3.label 1) = PairSemantics.raw7678 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node529 PairSemantics.raw7678; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7678 hH).trans (PairSemantics.sound65 hH)
  have hm2 : familyPairMoment B (groupedColumns node529 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value5 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node529 (EqualityPatterns.family3.label 2) = PairSemantics.raw7736 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node529 PairSemantics.raw7736; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7736 hH).trans (PairSemantics.sound5 hH)
  have hm3 : familyPairMoment B (groupedColumns node529 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node529 (EqualityPatterns.family3.label 3) = PairSemantics.raw5177 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node529 PairSemantics.raw5177; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5177 hH).trans (PairSemantics.sound11 hH)
  have hm4 : familyPairMoment B (groupedColumns node529 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value287 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node529 (EqualityPatterns.family3.label 4) = PairSemantics.raw4947 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node529 PairSemantics.raw4947; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4947 hH).trans (PairSemantics.sound287 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue529, PairSemantics.value0, PairSemantics.value5, PairSemantics.value11, PairSemantics.value65, PairSemantics.value287, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue530 : Sparse (Fin 909) := [(0, (7 / 144)), (1, (-5 / 48)), (4, (5 / 9))]

theorem singlePair530 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node530 node530Labels = Sparse.eval singlePairValue530 (familyPairVector B) := by
  have hp := single_label_three B hB node530
  have hl : node530Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node530 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node530 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node530 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node530 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node530 (EqualityPatterns.family3.label 1) = PairSemantics.raw7683 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node530 PairSemantics.raw7683; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7683 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node530 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node530 (EqualityPatterns.family3.label 2) = PairSemantics.raw7749 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node530 PairSemantics.raw7749; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7749 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node530 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node530 (EqualityPatterns.family3.label 3) = PairSemantics.raw5199 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node530 PairSemantics.raw5199; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5199 hH).trans (PairSemantics.sound11 hH)
  have hm4 : familyPairMoment B (groupedColumns node530 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value44 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node530 (EqualityPatterns.family3.label 4) = PairSemantics.raw4966 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node530 PairSemantics.raw4966; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4966 hH).trans (PairSemantics.sound44 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue530, PairSemantics.value0, PairSemantics.value11, PairSemantics.value44, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue531 : Sparse (Fin 909) := [(0, (79 / 432)), (1, (35 / 144)), (12, (-5 / 54))]

theorem singlePair531 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node531 node531Labels = Sparse.eval singlePairValue531 (familyPairVector B) := by
  have hp := single_label_three B hB node531
  have hl : node531Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node531 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node531 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node531 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node531 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node531 (EqualityPatterns.family3.label 1) = PairSemantics.raw7680 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node531 PairSemantics.raw7680; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7680 hH).trans (PairSemantics.sound65 hH)
  have hm2 : familyPairMoment B (groupedColumns node531 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node531 (EqualityPatterns.family3.label 2) = PairSemantics.raw9044 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node531 PairSemantics.raw9044; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9044 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node531 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node531 (EqualityPatterns.family3.label 3) = PairSemantics.raw7668 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node531 PairSemantics.raw7668; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7668 hH).trans (PairSemantics.sound65 hH)
  have hm4 : familyPairMoment B (groupedColumns node531 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2792 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node531 (EqualityPatterns.family3.label 4) = PairSemantics.raw7385 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node531 PairSemantics.raw7385; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7385 hH).trans (PairSemantics.sound2792 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue531, PairSemantics.value0, PairSemantics.value65, PairSemantics.value2792, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue532 : Sparse (Fin 909) := []

theorem singlePair532 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node532 node532Labels = Sparse.eval singlePairValue532 (familyPairVector B) := by
  have hp := single_label_three B hB node532
  have hl : node532Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node532 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node532 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node532 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node532 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node532 (EqualityPatterns.family3.label 1) = PairSemantics.raw7677 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node532 PairSemantics.raw7677; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7677 hH).trans (PairSemantics.sound65 hH)
  have hm2 : familyPairMoment B (groupedColumns node532 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value5 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node532 (EqualityPatterns.family3.label 2) = PairSemantics.raw9051 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node532 PairSemantics.raw9051; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9051 hH).trans (PairSemantics.sound5 hH)
  have hm3 : familyPairMoment B (groupedColumns node532 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node532 (EqualityPatterns.family3.label 3) = PairSemantics.raw7670 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node532 PairSemantics.raw7670; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7670 hH).trans (PairSemantics.sound65 hH)
  have hm4 : familyPairMoment B (groupedColumns node532 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1294 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node532 (EqualityPatterns.family3.label 4) = PairSemantics.raw7386 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node532 PairSemantics.raw7386; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7386 hH).trans (PairSemantics.sound1294 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue532, PairSemantics.value0, PairSemantics.value5, PairSemantics.value65, PairSemantics.value1294, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue533 : Sparse (Fin 909) := [(0, (47 / 432)), (1, (35 / 144)), (4, (-5 / 27))]

theorem singlePair533 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node533 node533Labels = Sparse.eval singlePairValue533 (familyPairVector B) := by
  have hp := single_label_three B hB node533
  have hl : node533Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node533 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node533 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node533 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node533 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node533 (EqualityPatterns.family3.label 1) = PairSemantics.raw7702 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node533 PairSemantics.raw7702; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7702 hH).trans (PairSemantics.sound65 hH)
  have hm2 : familyPairMoment B (groupedColumns node533 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node533 (EqualityPatterns.family3.label 2) = PairSemantics.raw9026 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node533 PairSemantics.raw9026; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9026 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node533 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node533 (EqualityPatterns.family3.label 3) = PairSemantics.raw7668 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node533 PairSemantics.raw7668; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7668 hH).trans (PairSemantics.sound65 hH)
  have hm4 : familyPairMoment B (groupedColumns node533 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2796 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node533 (EqualityPatterns.family3.label 4) = PairSemantics.raw7392 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node533 PairSemantics.raw7392; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7392 hH).trans (PairSemantics.sound2796 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue533, PairSemantics.value0, PairSemantics.value65, PairSemantics.value2796, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
