import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleRules
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical122
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical123
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical160
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical161
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical281
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical282
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound43

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue473 : Sparse (Fin 909) := [(0, (41 / 864)), (1, (5 / 48)), (2, (-5 / 54)), (3, (-20 / 27)), (5, (-5 / 216)), (6, (5 / 864)), (7, (-5 / 27)), (12, (-25 / 54)), (23, (5 / 18)), (27, (5 / 72))]

theorem singlePair473 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node473 node473Labels = Sparse.eval singlePairValue473 (familyPairVector B) := by
  have hp := single_label_three B hB node473
  have hl : node473Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node473 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node473 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node473 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node473 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node473 (EqualityPatterns.family3.label 1) = PairSemantics.raw5168 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node473 PairSemantics.raw5168; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5168 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node473 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node473 (EqualityPatterns.family3.label 2) = PairSemantics.raw9006 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node473 PairSemantics.raw9006; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9006 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node473 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value717 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node473 (EqualityPatterns.family3.label 3) = PairSemantics.raw5120 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node473 PairSemantics.raw5120; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5120 hH).trans (PairSemantics.sound717 hH)
  have hm4 : familyPairMoment B (groupedColumns node473 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2131 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node473 (EqualityPatterns.family3.label 4) = PairSemantics.raw3935 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node473 PairSemantics.raw3935; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3935 hH).trans (PairSemantics.sound2131 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue473, PairSemantics.value0, PairSemantics.value11, PairSemantics.value717, PairSemantics.value2131, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue474 : Sparse (Fin 909) := [(0, (1 / 18)), (1, (-5 / 108)), (5, (5 / 216)), (8, (5 / 54)), (24, (-5 / 18)), (27, (-5 / 72))]

theorem singlePair474 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node474 node474Labels = Sparse.eval singlePairValue474 (familyPairVector B) := by
  have hp := single_label_three B hB node474
  have hl : node474Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node474 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node474 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node474 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node474 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node474 (EqualityPatterns.family3.label 1) = PairSemantics.raw5167 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node474 PairSemantics.raw5167; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5167 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node474 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node474 (EqualityPatterns.family3.label 2) = PairSemantics.raw9011 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node474 PairSemantics.raw9011; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9011 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node474 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value231 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node474 (EqualityPatterns.family3.label 3) = PairSemantics.raw5122 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node474 PairSemantics.raw5122; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5122 hH).trans (PairSemantics.sound231 hH)
  have hm4 : familyPairMoment B (groupedColumns node474 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value654 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node474 (EqualityPatterns.family3.label 4) = PairSemantics.raw3936 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node474 PairSemantics.raw3936; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3936 hH).trans (PairSemantics.sound654 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue474, PairSemantics.value0, PairSemantics.value11, PairSemantics.value65, PairSemantics.value231, PairSemantics.value654, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue475 : Sparse (Fin 909) := [(0, (1 / 27)), (1, (-5 / 108)), (2, (5 / 864)), (3, (-10 / 27)), (4, (-5 / 27)), (5, (-5 / 108)), (6, (5 / 864)), (25, (5 / 9)), (26, (-5 / 27)), (27, (5 / 72)), (31, (5 / 18)), (33, (5 / 9)), (63, (5 / 18)), (64, (5 / 9)), (123, (5 / 18))]

theorem singlePair475 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node475 node475Labels = Sparse.eval singlePairValue475 (familyPairVector B) := by
  have hp := single_label_three B hB node475
  have hl : node475Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node475 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node475 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node475 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node475 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node475 (EqualityPatterns.family3.label 1) = PairSemantics.raw5171 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node475 PairSemantics.raw5171; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5171 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node475 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node475 (EqualityPatterns.family3.label 2) = PairSemantics.raw8999 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node475 PairSemantics.raw8999; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8999 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node475 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value717 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node475 (EqualityPatterns.family3.label 3) = PairSemantics.raw5120 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node475 PairSemantics.raw5120; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5120 hH).trans (PairSemantics.sound717 hH)
  have hm4 : familyPairMoment B (groupedColumns node475 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2103 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node475 (EqualityPatterns.family3.label 4) = PairSemantics.raw3937 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node475 PairSemantics.raw3937; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3937 hH).trans (PairSemantics.sound2103 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue475, PairSemantics.value0, PairSemantics.value46, PairSemantics.value717, PairSemantics.value2103, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue476 : Sparse (Fin 909) := [(0, (25 / 864)), (1, (65 / 432)), (2, (-5 / 216)), (3, (-35 / 54)), (4, (-5 / 18)), (5, (-5 / 108)), (6, (5 / 864)), (12, (-5 / 18)), (25, (5 / 9)), (26, (-5 / 54)), (27, (5 / 72)), (31, (5 / 9)), (33, (5 / 6)), (51, (5 / 18)), (55, (5 / 18)), (64, (5 / 18)), (123, (5 / 18))]

theorem singlePair476 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node476 node476Labels = Sparse.eval singlePairValue476 (familyPairVector B) := by
  have hp := single_label_three B hB node476
  have hl : node476Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node476 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node476 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node476 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node476 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node476 (EqualityPatterns.family3.label 1) = PairSemantics.raw5172 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node476 PairSemantics.raw5172; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5172 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node476 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node476 (EqualityPatterns.family3.label 2) = PairSemantics.raw8997 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node476 PairSemantics.raw8997; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8997 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node476 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value717 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node476 (EqualityPatterns.family3.label 3) = PairSemantics.raw5120 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node476 PairSemantics.raw5120; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5120 hH).trans (PairSemantics.sound717 hH)
  have hm4 : familyPairMoment B (groupedColumns node476 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2104 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node476 (EqualityPatterns.family3.label 4) = PairSemantics.raw3938 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node476 PairSemantics.raw3938; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3938 hH).trans (PairSemantics.sound2104 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue476, PairSemantics.value0, PairSemantics.value46, PairSemantics.value232, PairSemantics.value717, PairSemantics.value2104, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue477 : Sparse (Fin 909) := [(0, (25 / 864)), (1, (5 / 288)), (2, (-35 / 864)), (3, (-5 / 18)), (4, (-5 / 54)), (5, (-5 / 108)), (6, (5 / 864)), (12, (-5 / 54)), (26, (-5 / 27)), (27, (5 / 72)), (35, (-5 / 54)), (51, (5 / 18)), (52, (-5 / 54)), (55, (5 / 18))]

theorem singlePair477 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node477 node477Labels = Sparse.eval singlePairValue477 (familyPairVector B) := by
  have hp := single_label_three B hB node477
  have hl : node477Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node477 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node477 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node477 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node477 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node477 (EqualityPatterns.family3.label 1) = PairSemantics.raw5174 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node477 PairSemantics.raw5174; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5174 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node477 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node477 (EqualityPatterns.family3.label 2) = PairSemantics.raw8994 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node477 PairSemantics.raw8994; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8994 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node477 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value717 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node477 (EqualityPatterns.family3.label 3) = PairSemantics.raw5120 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node477 PairSemantics.raw5120; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5120 hH).trans (PairSemantics.sound717 hH)
  have hm4 : familyPairMoment B (groupedColumns node477 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2136 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node477 (EqualityPatterns.family3.label 4) = PairSemantics.raw3939 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node477 PairSemantics.raw3939; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3939 hH).trans (PairSemantics.sound2136 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue477, PairSemantics.value0, PairSemantics.value11, PairSemantics.value232, PairSemantics.value717, PairSemantics.value2136, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue478 : Sparse (Fin 909) := [(0, (13 / 432)), (2, (25 / 432)), (3, (-10 / 27)), (4, (-5 / 27)), (25, (5 / 18)), (26, (-5 / 27))]

theorem singlePair478 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node478 node478Labels = Sparse.eval singlePairValue478 (familyPairVector B) := by
  have hp := single_label_three B hB node478
  have hl : node478Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node478 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node478 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node478 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node478 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node478 (EqualityPatterns.family3.label 1) = PairSemantics.raw5155 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node478 PairSemantics.raw5155; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5155 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node478 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node478 (EqualityPatterns.family3.label 2) = PairSemantics.raw9026 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node478 PairSemantics.raw9026; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9026 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node478 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node478 (EqualityPatterns.family3.label 3) = PairSemantics.raw5123 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node478 PairSemantics.raw5123; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5123 hH).trans (PairSemantics.sound46 hH)
  have hm4 : familyPairMoment B (groupedColumns node478 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2795 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node478 (EqualityPatterns.family3.label 4) = PairSemantics.raw3941 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node478 PairSemantics.raw3941; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3941 hH).trans (PairSemantics.sound2795 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue478, PairSemantics.value0, PairSemantics.value46, PairSemantics.value65, PairSemantics.value2795, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue479 : Sparse (Fin 909) := [(0, (7 / 432)), (1, (85 / 864)), (2, (-25 / 864)), (3, (-25 / 54)), (4, (-5 / 27)), (12, (-5 / 27)), (26, (-5 / 54))]

theorem singlePair479 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node479 node479Labels = Sparse.eval singlePairValue479 (familyPairVector B) := by
  have hp := single_label_three B hB node479
  have hl : node479Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node479 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node479 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node479 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node479 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node479 (EqualityPatterns.family3.label 1) = PairSemantics.raw5156 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node479 PairSemantics.raw5156; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5156 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node479 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node479 (EqualityPatterns.family3.label 2) = PairSemantics.raw9024 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node479 PairSemantics.raw9024; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9024 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node479 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node479 (EqualityPatterns.family3.label 3) = PairSemantics.raw5123 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node479 PairSemantics.raw5123; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5123 hH).trans (PairSemantics.sound46 hH)
  have hm4 : familyPairMoment B (groupedColumns node479 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2666 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node479 (EqualityPatterns.family3.label 4) = PairSemantics.raw3942 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node479 PairSemantics.raw3942; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3942 hH).trans (PairSemantics.sound2666 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue479, PairSemantics.value0, PairSemantics.value46, PairSemantics.value65, PairSemantics.value232, PairSemantics.value2666, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue480 : Sparse (Fin 909) := [(0, (5 / 288)), (1, (5 / 48)), (2, (-35 / 864)), (3, (-20 / 27)), (4, (-5 / 27)), (12, (-10 / 27)), (13, (-10 / 27)), (26, (-5 / 54)), (33, (5 / 9)), (34, (-5 / 54))]

theorem singlePair480 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node480 node480Labels = Sparse.eval singlePairValue480 (familyPairVector B) := by
  have hp := single_label_three B hB node480
  have hl : node480Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node480 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node480 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node480 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node480 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node480 (EqualityPatterns.family3.label 1) = PairSemantics.raw5158 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node480 PairSemantics.raw5158; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5158 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node480 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node480 (EqualityPatterns.family3.label 2) = PairSemantics.raw9023 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node480 PairSemantics.raw9023; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9023 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node480 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node480 (EqualityPatterns.family3.label 3) = PairSemantics.raw5123 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node480 PairSemantics.raw5123; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5123 hH).trans (PairSemantics.sound46 hH)
  have hm4 : familyPairMoment B (groupedColumns node480 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2097 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node480 (EqualityPatterns.family3.label 4) = PairSemantics.raw3943 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node480 PairSemantics.raw3943; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3943 hH).trans (PairSemantics.sound2097 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue480, PairSemantics.value0, PairSemantics.value46, PairSemantics.value232, PairSemantics.value2097, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue481 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 48)), (3, (-10 / 9)), (12, (-5 / 9)), (13, (-10 / 9)), (34, (-5 / 27))]

theorem singlePair481 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node481 node481Labels = Sparse.eval singlePairValue481 (familyPairVector B) := by
  have hp := single_label_three B hB node481
  have hl : node481Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node481 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node481 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node481 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node481 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node481 (EqualityPatterns.family3.label 1) = PairSemantics.raw5160 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node481 PairSemantics.raw5160; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5160 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node481 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node481 (EqualityPatterns.family3.label 2) = PairSemantics.raw9022 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node481 PairSemantics.raw9022; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9022 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node481 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node481 (EqualityPatterns.family3.label 3) = PairSemantics.raw5123 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node481 PairSemantics.raw5123; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5123 hH).trans (PairSemantics.sound46 hH)
  have hm4 : familyPairMoment B (groupedColumns node481 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2098 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node481 (EqualityPatterns.family3.label 4) = PairSemantics.raw3944 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node481 PairSemantics.raw3944; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3944 hH).trans (PairSemantics.sound2098 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue481, PairSemantics.value0, PairSemantics.value46, PairSemantics.value2098, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue482 : Sparse (Fin 909) := []

theorem singlePair482 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node482 node482Labels = Sparse.eval singlePairValue482 (familyPairVector B) := by
  have hp := single_label_three B hB node482
  have hl : node482Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node482 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node482 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node482 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node482 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node482 (EqualityPatterns.family3.label 1) = PairSemantics.raw5156 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node482 PairSemantics.raw5156; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5156 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node482 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value5 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node482 (EqualityPatterns.family3.label 2) = PairSemantics.raw9029 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node482 PairSemantics.raw9029; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9029 hH).trans (PairSemantics.sound5 hH)
  have hm3 : familyPairMoment B (groupedColumns node482 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node482 (EqualityPatterns.family3.label 3) = PairSemantics.raw5127 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node482 PairSemantics.raw5127; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5127 hH).trans (PairSemantics.sound232 hH)
  have hm4 : familyPairMoment B (groupedColumns node482 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2798 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node482 (EqualityPatterns.family3.label 4) = PairSemantics.raw3945 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node482 PairSemantics.raw3945; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3945 hH).trans (PairSemantics.sound2798 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue482, PairSemantics.value0, PairSemantics.value5, PairSemantics.value232, PairSemantics.value2798, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue483 : Sparse (Fin 909) := [(0, (1 / 27)), (1, (-35 / 432)), (2, (25 / 432)), (3, (5 / 27)), (12, (5 / 54))]

theorem singlePair483 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node483 node483Labels = Sparse.eval singlePairValue483 (familyPairVector B) := by
  have hp := single_label_three B hB node483
  have hl : node483Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node483 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node483 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node483 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node483 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node483 (EqualityPatterns.family3.label 1) = PairSemantics.raw5159 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node483 PairSemantics.raw5159; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5159 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node483 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node483 (EqualityPatterns.family3.label 2) = PairSemantics.raw9025 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node483 PairSemantics.raw9025; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9025 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node483 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node483 (EqualityPatterns.family3.label 3) = PairSemantics.raw5128 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node483 PairSemantics.raw5128; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5128 hH).trans (PairSemantics.sound46 hH)
  have hm4 : familyPairMoment B (groupedColumns node483 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1142 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node483 (EqualityPatterns.family3.label 4) = PairSemantics.raw3946 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node483 PairSemantics.raw3946; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3946 hH).trans (PairSemantics.sound1142 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue483, PairSemantics.value0, PairSemantics.value46, PairSemantics.value65, PairSemantics.value1142, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue484 : Sparse (Fin 909) := [(0, (1 / 432)), (1, (25 / 216)), (2, (-25 / 432)), (3, (-35 / 54)), (4, (-10 / 27)), (12, (-5 / 27)), (25, (5 / 9)), (26, (-5 / 54)), (31, (5 / 9)), (33, (5 / 6))]

theorem singlePair484 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node484 node484Labels = Sparse.eval singlePairValue484 (familyPairVector B) := by
  have hp := single_label_three B hB node484
  have hl : node484Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node484 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node484 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node484 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node484 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node484 (EqualityPatterns.family3.label 1) = PairSemantics.raw5178 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node484 PairSemantics.raw5178; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5178 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node484 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node484 (EqualityPatterns.family3.label 2) = PairSemantics.raw9003 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node484 PairSemantics.raw9003; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9003 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node484 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node484 (EqualityPatterns.family3.label 3) = PairSemantics.raw5123 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node484 PairSemantics.raw5123; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5123 hH).trans (PairSemantics.sound46 hH)
  have hm4 : familyPairMoment B (groupedColumns node484 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2099 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node484 (EqualityPatterns.family3.label 4) = PairSemantics.raw3948 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node484 PairSemantics.raw3948; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3948 hH).trans (PairSemantics.sound2099 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue484, PairSemantics.value0, PairSemantics.value46, PairSemantics.value232, PairSemantics.value2099, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue485 : Sparse (Fin 909) := [(0, (1 / 216)), (1, (25 / 216)), (2, (-5 / 108)), (3, (-35 / 54)), (4, (-5 / 18)), (12, (-5 / 27)), (13, (-5 / 54)), (25, (5 / 18)), (26, (-5 / 18)), (31, (5 / 18)), (33, (5 / 18)), (34, (-5 / 54))]

theorem singlePair485 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node485 node485Labels = Sparse.eval singlePairValue485 (familyPairVector B) := by
  have hp := single_label_three B hB node485
  have hl : node485Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node485 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node485 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node485 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node485 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node485 (EqualityPatterns.family3.label 1) = PairSemantics.raw5171 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node485 PairSemantics.raw5171; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5171 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node485 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node485 (EqualityPatterns.family3.label 2) = PairSemantics.raw9017 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node485 PairSemantics.raw9017; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9017 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node485 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node485 (EqualityPatterns.family3.label 3) = PairSemantics.raw5127 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node485 PairSemantics.raw5127; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5127 hH).trans (PairSemantics.sound232 hH)
  have hm4 : familyPairMoment B (groupedColumns node485 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2100 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node485 (EqualityPatterns.family3.label 4) = PairSemantics.raw3949 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node485 PairSemantics.raw3949; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3949 hH).trans (PairSemantics.sound2100 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue485, PairSemantics.value0, PairSemantics.value46, PairSemantics.value232, PairSemantics.value2100, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue486 : Sparse (Fin 909) := [(0, (-1 / 864)), (1, (35 / 108)), (2, (-5 / 96)), (3, (-5 / 6)), (4, (-5 / 9)), (12, (-10 / 27)), (25, (5 / 18)), (26, (-5 / 27))]

theorem singlePair486 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node486 node486Labels = Sparse.eval singlePairValue486 (familyPairVector B) := by
  have hp := single_label_three B hB node486
  have hl : node486Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node486 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node486 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node486 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node486 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node486 (EqualityPatterns.family3.label 1) = PairSemantics.raw5172 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node486 PairSemantics.raw5172; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5172 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node486 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node486 (EqualityPatterns.family3.label 2) = PairSemantics.raw9016 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node486 PairSemantics.raw9016; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9016 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node486 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node486 (EqualityPatterns.family3.label 3) = PairSemantics.raw5127 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node486 PairSemantics.raw5127; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5127 hH).trans (PairSemantics.sound232 hH)
  have hm4 : familyPairMoment B (groupedColumns node486 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2301 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node486 (EqualityPatterns.family3.label 4) = PairSemantics.raw3950 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node486 PairSemantics.raw3950; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3950 hH).trans (PairSemantics.sound2301 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue486, PairSemantics.value0, PairSemantics.value11, PairSemantics.value232, PairSemantics.value2301, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue487 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-25 / 432)), (2, (5 / 144)), (3, (5 / 27)), (4, (5 / 54)), (25, (-5 / 18)), (26, (5 / 54))]

theorem singlePair487 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node487 node487Labels = Sparse.eval singlePairValue487 (familyPairVector B) := by
  have hp := single_label_three B hB node487
  have hl : node487Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node487 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node487 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node487 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node487 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node487 (EqualityPatterns.family3.label 1) = PairSemantics.raw5173 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node487 PairSemantics.raw5173; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5173 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node487 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node487 (EqualityPatterns.family3.label 2) = PairSemantics.raw9015 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node487 PairSemantics.raw9015; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9015 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node487 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node487 (EqualityPatterns.family3.label 3) = PairSemantics.raw5128 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node487 PairSemantics.raw5128; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5128 hH).trans (PairSemantics.sound46 hH)
  have hm4 : familyPairMoment B (groupedColumns node487 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value706 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node487 (EqualityPatterns.family3.label 4) = PairSemantics.raw3951 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node487 PairSemantics.raw3951; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3951 hH).trans (PairSemantics.sound706 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue487, PairSemantics.value0, PairSemantics.value11, PairSemantics.value46, PairSemantics.value706, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue488 : Sparse (Fin 909) := [(0, (29 / 864)), (1, (5 / 48)), (2, (-5 / 96)), (3, (-5 / 18)), (4, (-5 / 27)), (12, (-5 / 27))]

theorem singlePair488 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node488 node488Labels = Sparse.eval singlePairValue488 (familyPairVector B) := by
  have hp := single_label_three B hB node488
  have hl : node488Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node488 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node488 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node488 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node488 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node488 (EqualityPatterns.family3.label 1) = PairSemantics.raw5174 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node488 PairSemantics.raw5174; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5174 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node488 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node488 (EqualityPatterns.family3.label 2) = PairSemantics.raw9012 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node488 PairSemantics.raw9012; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9012 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node488 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node488 (EqualityPatterns.family3.label 3) = PairSemantics.raw5127 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node488 PairSemantics.raw5127; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5127 hH).trans (PairSemantics.sound232 hH)
  have hm4 : familyPairMoment B (groupedColumns node488 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2137 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node488 (EqualityPatterns.family3.label 4) = PairSemantics.raw3953 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node488 PairSemantics.raw3953; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3953 hH).trans (PairSemantics.sound2137 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue488, PairSemantics.value0, PairSemantics.value11, PairSemantics.value65, PairSemantics.value232, PairSemantics.value2137, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
