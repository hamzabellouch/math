import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleRules
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical159
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical160
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical161
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical162
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound6

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue120 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (-5 / 216)), (2, (-5 / 48)), (5, (5 / 36)), (6, (-5 / 432)), (7, (-5 / 27)), (8, (-5 / 27)), (9, (-5 / 54)), (58, (5 / 864)), (69, (-5 / 54)), (71, (-10 / 27))]

theorem singlePair120 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node120 node120Labels = Sparse.eval singlePairValue120 (familyPairVector B) := by
  have hp := single_label_three B hB node120
  have hl : node120Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node120 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node120 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node120 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node120 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node120 (EqualityPatterns.family3.label 1) = PairSemantics.raw5127 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node120 PairSemantics.raw5127; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5127 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node120 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node120 (EqualityPatterns.family3.label 2) = PairSemantics.raw5174 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node120 PairSemantics.raw5174; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5174 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node120 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value296 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node120 (EqualityPatterns.family3.label 3) = PairSemantics.raw187 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node120 PairSemantics.raw187; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical187 hH).trans (PairSemantics.sound296 hH)
  have hm4 : familyPairMoment B (groupedColumns node120 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1538 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node120 (EqualityPatterns.family3.label 4) = PairSemantics.raw138 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node120 PairSemantics.raw138; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical138 hH).trans (PairSemantics.sound1538 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue120, PairSemantics.value0, PairSemantics.value11, PairSemantics.value232, PairSemantics.value296, PairSemantics.value1538, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue121 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (-35 / 864)), (2, (25 / 432)), (6, (25 / 864)), (8, (5 / 54)), (58, (-5 / 864)), (71, (5 / 54))]

theorem singlePair121 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node121 node121Labels = Sparse.eval singlePairValue121 (familyPairVector B) := by
  have hp := single_label_three B hB node121
  have hl : node121Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node121 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node121 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node121 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node121 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node121 (EqualityPatterns.family3.label 1) = PairSemantics.raw5128 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node121 PairSemantics.raw5128; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5128 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node121 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node121 (EqualityPatterns.family3.label 2) = PairSemantics.raw5175 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node121 PairSemantics.raw5175; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5175 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node121 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value67 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node121 (EqualityPatterns.family3.label 3) = PairSemantics.raw188 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node121 PairSemantics.raw188; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical188 hH).trans (PairSemantics.sound67 hH)
  have hm4 : familyPairMoment B (groupedColumns node121 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value432 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node121 (EqualityPatterns.family3.label 4) = PairSemantics.raw139 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node121 PairSemantics.raw139; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical139 hH).trans (PairSemantics.sound432 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue121, PairSemantics.value0, PairSemantics.value11, PairSemantics.value46, PairSemantics.value67, PairSemantics.value432, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue122 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-25 / 864)), (2, (5 / 72)), (3, (5 / 54)), (5, (-5 / 108)), (6, (5 / 216)), (7, (5 / 54)), (9, (5 / 216)), (35, (5 / 27)), (52, (5 / 27)), (58, (-5 / 864)), (69, (5 / 54)), (495, (5 / 54))]

theorem singlePair122 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node122 node122Labels = Sparse.eval singlePairValue122 (familyPairVector B) := by
  have hp := single_label_three B hB node122
  have hl : node122Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node122 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node122 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node122 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node122 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node122 (EqualityPatterns.family3.label 1) = PairSemantics.raw5131 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node122 PairSemantics.raw5131; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5131 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node122 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node122 (EqualityPatterns.family3.label 2) = PairSemantics.raw5173 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node122 PairSemantics.raw5173; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5173 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node122 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value67 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node122 (EqualityPatterns.family3.label 3) = PairSemantics.raw188 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node122 PairSemantics.raw188; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical188 hH).trans (PairSemantics.sound67 hH)
  have hm4 : familyPairMoment B (groupedColumns node122 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value415 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node122 (EqualityPatterns.family3.label 4) = PairSemantics.raw140 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node122 PairSemantics.raw140; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical140 hH).trans (PairSemantics.sound415 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue122, PairSemantics.value0, PairSemantics.value46, PairSemantics.value67, PairSemantics.value415, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue123 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 72)), (2, (-5 / 108)), (3, (5 / 54)), (6, (-5 / 432)), (7, (5 / 27)), (9, (5 / 108)), (26, (5 / 54)), (35, (10 / 27)), (67, (5 / 27)), (70, (5 / 54)), (257, (5 / 54))]

theorem singlePair123 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node123 node123Labels = Sparse.eval singlePairValue123 (familyPairVector B) := by
  have hp := single_label_three B hB node123
  have hl : node123Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node123 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node123 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node123 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node123 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node123 (EqualityPatterns.family3.label 1) = PairSemantics.raw5125 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node123 PairSemantics.raw5125; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5125 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node123 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node123 (EqualityPatterns.family3.label 2) = PairSemantics.raw5182 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node123 PairSemantics.raw5182; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5182 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node123 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value68 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node123 (EqualityPatterns.family3.label 3) = PairSemantics.raw189 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node123 PairSemantics.raw189; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical189 hH).trans (PairSemantics.sound68 hH)
  have hm4 : familyPairMoment B (groupedColumns node123 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value352 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node123 (EqualityPatterns.family3.label 4) = PairSemantics.raw141 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node123 PairSemantics.raw141; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical141 hH).trans (PairSemantics.sound352 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue123, PairSemantics.value0, PairSemantics.value10, PairSemantics.value46, PairSemantics.value68, PairSemantics.value352, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue124 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (-5 / 96)), (2, (5 / 216)), (5, (-5 / 54)), (6, (-5 / 432)), (7, (5 / 27)), (8, (5 / 27)), (9, (5 / 108)), (69, (5 / 54)), (71, (5 / 54))]

theorem singlePair124 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node124 node124Labels = Sparse.eval singlePairValue124 (familyPairVector B) := by
  have hp := single_label_three B hB node124
  have hl : node124Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node124 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node124 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node124 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node124 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node124 (EqualityPatterns.family3.label 1) = PairSemantics.raw5128 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node124 PairSemantics.raw5128; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5128 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node124 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node124 (EqualityPatterns.family3.label 2) = PairSemantics.raw5179 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node124 PairSemantics.raw5179; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5179 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node124 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value68 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node124 (EqualityPatterns.family3.label 3) = PairSemantics.raw189 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node124 PairSemantics.raw189; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical189 hH).trans (PairSemantics.sound68 hH)
  have hm4 : familyPairMoment B (groupedColumns node124 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value434 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node124 (EqualityPatterns.family3.label 4) = PairSemantics.raw142 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node124 PairSemantics.raw142; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical142 hH).trans (PairSemantics.sound434 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue124, PairSemantics.value0, PairSemantics.value11, PairSemantics.value46, PairSemantics.value68, PairSemantics.value434, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue125 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (35 / 216)), (2, (5 / 288)), (3, (-5 / 18)), (5, (-5 / 108)), (9, (-5 / 54)), (35, (-5 / 27)), (58, (5 / 864)), (69, (-5 / 18)), (70, (-5 / 27))]

theorem singlePair125 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node125 node125Labels = Sparse.eval singlePairValue125 (familyPairVector B) := by
  have hp := single_label_three B hB node125
  have hl : node125Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node125 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node125 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node125 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node125 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node125 (EqualityPatterns.family3.label 1) = PairSemantics.raw5140 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node125 PairSemantics.raw5140; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5140 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node125 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node125 (EqualityPatterns.family3.label 2) = PairSemantics.raw5163 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node125 PairSemantics.raw5163; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5163 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node125 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value296 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node125 (EqualityPatterns.family3.label 3) = PairSemantics.raw187 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node125 PairSemantics.raw187; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical187 hH).trans (PairSemantics.sound296 hH)
  have hm4 : familyPairMoment B (groupedColumns node125 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1536 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node125 (EqualityPatterns.family3.label 4) = PairSemantics.raw143 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node125 PairSemantics.raw143; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical143 hH).trans (PairSemantics.sound1536 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue125, PairSemantics.value0, PairSemantics.value4, PairSemantics.value232, PairSemantics.value296, PairSemantics.value1536, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue126 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (55 / 432)), (2, (-5 / 432)), (5, (5 / 54)), (6, (5 / 288)), (7, (5 / 54)), (58, (-5 / 864)), (69, (5 / 54))]

theorem singlePair126 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node126 node126Labels = Sparse.eval singlePairValue126 (familyPairVector B) := by
  have hp := single_label_three B hB node126
  have hl : node126Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node126 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node126 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node126 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node126 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node126 (EqualityPatterns.family3.label 1) = PairSemantics.raw5139 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node126 PairSemantics.raw5139; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5139 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node126 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node126 (EqualityPatterns.family3.label 2) = PairSemantics.raw5165 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node126 PairSemantics.raw5165; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5165 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node126 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value67 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node126 (EqualityPatterns.family3.label 3) = PairSemantics.raw188 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node126 PairSemantics.raw188; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical188 hH).trans (PairSemantics.sound67 hH)
  have hm4 : familyPairMoment B (groupedColumns node126 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value429 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node126 (EqualityPatterns.family3.label 4) = PairSemantics.raw144 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node126 PairSemantics.raw144; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical144 hH).trans (PairSemantics.sound429 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue126, PairSemantics.value0, PairSemantics.value4, PairSemantics.value67, PairSemantics.value232, PairSemantics.value429, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue127 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 54)), (3, (5 / 54)), (5, (-5 / 216)), (6, (-5 / 432)), (9, (5 / 108)), (35, (5 / 54)), (69, (5 / 54)), (70, (5 / 54))]

theorem singlePair127 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node127 node127Labels = Sparse.eval singlePairValue127 (familyPairVector B) := by
  have hp := single_label_three B hB node127
  have hl : node127Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node127 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node127 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node127 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node127 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node127 (EqualityPatterns.family3.label 1) = PairSemantics.raw5136 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node127 PairSemantics.raw5136; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5136 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node127 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node127 (EqualityPatterns.family3.label 2) = PairSemantics.raw5170 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node127 PairSemantics.raw5170; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5170 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node127 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value68 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node127 (EqualityPatterns.family3.label 3) = PairSemantics.raw189 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node127 PairSemantics.raw189; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical189 hH).trans (PairSemantics.sound68 hH)
  have hm4 : familyPairMoment B (groupedColumns node127 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value430 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node127 (EqualityPatterns.family3.label 4) = PairSemantics.raw145 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node127 PairSemantics.raw145; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical145 hH).trans (PairSemantics.sound430 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue127, PairSemantics.value0, PairSemantics.value4, PairSemantics.value46, PairSemantics.value68, PairSemantics.value430, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue128 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 216)), (2, (-5 / 432)), (5, (-5 / 108)), (6, (-5 / 432)), (9, (5 / 108)), (71, (5 / 27))]

theorem singlePair128 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node128 node128Labels = Sparse.eval singlePairValue128 (familyPairVector B) := by
  have hp := single_label_three B hB node128
  have hl : node128Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node128 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node128 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node128 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node128 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node128 (EqualityPatterns.family3.label 1) = PairSemantics.raw5139 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node128 PairSemantics.raw5139; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5139 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node128 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node128 (EqualityPatterns.family3.label 2) = PairSemantics.raw5167 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node128 PairSemantics.raw5167; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5167 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node128 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value68 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node128 (EqualityPatterns.family3.label 3) = PairSemantics.raw189 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node128 PairSemantics.raw189; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical189 hH).trans (PairSemantics.sound68 hH)
  have hm4 : familyPairMoment B (groupedColumns node128 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value433 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node128 (EqualityPatterns.family3.label 4) = PairSemantics.raw146 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node128 PairSemantics.raw146; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical146 hH).trans (PairSemantics.sound433 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue128, PairSemantics.value0, PairSemantics.value11, PairSemantics.value68, PairSemantics.value232, PairSemantics.value433, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue129 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 48)), (2, (5 / 432)), (5, (-5 / 54)), (6, (-5 / 216)), (9, (5 / 108)), (58, (5 / 432))]

theorem singlePair129 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node129 node129Labels = Sparse.eval singlePairValue129 (familyPairVector B) := by
  have hp := single_label_three B hB node129
  have hl : node129Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node129 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node129 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node129 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node129 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node129 (EqualityPatterns.family3.label 1) = PairSemantics.raw5141 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node129 PairSemantics.raw5141; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5141 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node129 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node129 (EqualityPatterns.family3.label 2) = PairSemantics.raw5169 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node129 PairSemantics.raw5169; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5169 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node129 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value14 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node129 (EqualityPatterns.family3.label 3) = PairSemantics.raw190 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node129 PairSemantics.raw190; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical190 hH).trans (PairSemantics.sound14 hH)
  have hm4 : familyPairMoment B (groupedColumns node129 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value139 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node129 (EqualityPatterns.family3.label 4) = PairSemantics.raw147 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node129 PairSemantics.raw147; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical147 hH).trans (PairSemantics.sound139 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue129, PairSemantics.value0, PairSemantics.value4, PairSemantics.value14, PairSemantics.value46, PairSemantics.value139, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue130 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 96)), (2, (5 / 864)), (3, (5 / 54)), (5, (-5 / 216)), (6, (-5 / 432)), (7, (5 / 27)), (8, (5 / 54)), (9, (5 / 108)), (35, (5 / 54)), (81, (-5 / 18)), (256, (-5 / 18))]

theorem singlePair130 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node130 node130Labels = Sparse.eval singlePairValue130 (familyPairVector B) := by
  have hp := single_label_three B hB node130
  have hl : node130Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node130 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node130 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node130 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node130 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node130 (EqualityPatterns.family3.label 1) = PairSemantics.raw5147 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node130 PairSemantics.raw5147; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5147 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node130 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node130 (EqualityPatterns.family3.label 2) = PairSemantics.raw5159 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node130 PairSemantics.raw5159; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5159 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node130 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value68 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node130 (EqualityPatterns.family3.label 3) = PairSemantics.raw189 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node130 PairSemantics.raw189; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical189 hH).trans (PairSemantics.sound68 hH)
  have hm4 : familyPairMoment B (groupedColumns node130 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value417 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node130 (EqualityPatterns.family3.label 4) = PairSemantics.raw148 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node130 PairSemantics.raw148; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical148 hH).trans (PairSemantics.sound417 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue130, PairSemantics.value0, PairSemantics.value46, PairSemantics.value68, PairSemantics.value417, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue131 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 48)), (2, (-5 / 216)), (5, (-5 / 108)), (6, (5 / 432)), (7, (-5 / 27)), (9, (-5 / 108)), (35, (-5 / 27)), (70, (-5 / 27))]

theorem singlePair131 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node131 node131Labels = Sparse.eval singlePairValue131 (familyPairVector B) := by
  have hp := single_label_three B hB node131
  have hl : node131Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node131 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node131 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node131 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node131 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node131 (EqualityPatterns.family3.label 1) = PairSemantics.raw5132 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node131 PairSemantics.raw5132; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5132 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node131 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node131 (EqualityPatterns.family3.label 2) = PairSemantics.raw5185 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node131 PairSemantics.raw5185; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5185 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node131 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value15 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node131 (EqualityPatterns.family3.label 3) = PairSemantics.raw191 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node131 PairSemantics.raw191; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical191 hH).trans (PairSemantics.sound15 hH)
  have hm4 : familyPairMoment B (groupedColumns node131 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value141 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node131 (EqualityPatterns.family3.label 4) = PairSemantics.raw149 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node131 PairSemantics.raw149; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical149 hH).trans (PairSemantics.sound141 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue131, PairSemantics.value0, PairSemantics.value4, PairSemantics.value10, PairSemantics.value15, PairSemantics.value141, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue132 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-5 / 72)), (2, (5 / 432)), (6, (5 / 432)), (8, (-5 / 27)), (9, (-5 / 108)), (71, (-5 / 27))]

theorem singlePair132 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node132 node132Labels = Sparse.eval singlePairValue132 (familyPairVector B) := by
  have hp := single_label_three B hB node132
  have hl : node132Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node132 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node132 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node132 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node132 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node132 (EqualityPatterns.family3.label 1) = PairSemantics.raw5141 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node132 PairSemantics.raw5141; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5141 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node132 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node132 (EqualityPatterns.family3.label 2) = PairSemantics.raw5177 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node132 PairSemantics.raw5177; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5177 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node132 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value15 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node132 (EqualityPatterns.family3.label 3) = PairSemantics.raw191 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node132 PairSemantics.raw191; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical191 hH).trans (PairSemantics.sound15 hH)
  have hm4 : familyPairMoment B (groupedColumns node132 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value144 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node132 (EqualityPatterns.family3.label 4) = PairSemantics.raw150 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node132 PairSemantics.raw150; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical150 hH).trans (PairSemantics.sound144 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue132, PairSemantics.value0, PairSemantics.value11, PairSemantics.value15, PairSemantics.value46, PairSemantics.value144, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue133 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 48)), (2, (5 / 432)), (6, (5 / 432)), (7, (-5 / 27)), (9, (-5 / 108)), (69, (-5 / 27))]

theorem singlePair133 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node133 node133Labels = Sparse.eval singlePairValue133 (familyPairVector B) := by
  have hp := single_label_three B hB node133
  have hl : node133Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node133 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node133 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node133 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node133 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node133 (EqualityPatterns.family3.label 1) = PairSemantics.raw5149 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node133 PairSemantics.raw5149; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5149 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node133 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node133 (EqualityPatterns.family3.label 2) = PairSemantics.raw5169 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node133 PairSemantics.raw5169; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5169 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node133 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value15 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node133 (EqualityPatterns.family3.label 3) = PairSemantics.raw191 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node133 PairSemantics.raw191; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical191 hH).trans (PairSemantics.sound15 hH)
  have hm4 : familyPairMoment B (groupedColumns node133 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value140 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node133 (EqualityPatterns.family3.label 4) = PairSemantics.raw151 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node133 PairSemantics.raw151; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical151 hH).trans (PairSemantics.sound140 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue133, PairSemantics.value0, PairSemantics.value4, PairSemantics.value15, PairSemantics.value46, PairSemantics.value140, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue134 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 72)), (2, (-25 / 432)), (5, (-5 / 108)), (6, (5 / 432)), (9, (-5 / 108)), (35, (-5 / 27)), (67, (-5 / 27)), (257, (-5 / 27))]

theorem singlePair134 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node134 node134Labels = Sparse.eval singlePairValue134 (familyPairVector B) := by
  have hp := single_label_three B hB node134
  have hl : node134Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node134 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node134 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node134 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node134 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node134 (EqualityPatterns.family3.label 1) = PairSemantics.raw5152 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node134 PairSemantics.raw5152; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5152 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node134 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node134 (EqualityPatterns.family3.label 2) = PairSemantics.raw5161 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node134 PairSemantics.raw5161; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5161 hH).trans (PairSemantics.sound10 hH)
  have hm3 : familyPairMoment B (groupedColumns node134 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value15 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node134 (EqualityPatterns.family3.label 3) = PairSemantics.raw191 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node134 PairSemantics.raw191; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical191 hH).trans (PairSemantics.sound15 hH)
  have hm4 : familyPairMoment B (groupedColumns node134 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value94 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node134 (EqualityPatterns.family3.label 4) = PairSemantics.raw152 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node134 PairSemantics.raw152; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical152 hH).trans (PairSemantics.sound94 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue134, PairSemantics.value0, PairSemantics.value10, PairSemantics.value15, PairSemantics.value94, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue135 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (35 / 216)), (2, (-5 / 432)), (5, (-5 / 108)), (6, (-5 / 144)), (13, (-5 / 27)), (35, (-5 / 27)), (82, (-5 / 27))]

theorem singlePair135 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node135 node135Labels = Sparse.eval singlePairValue135 (familyPairVector B) := by
  have hp := single_label_three B hB node135
  have hl : node135Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node135 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node135 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node135 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node135 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node135 (EqualityPatterns.family3.label 1) = PairSemantics.raw5112 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node135 PairSemantics.raw5112; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5112 hH).trans (PairSemantics.sound25 hH)
  have hm2 : familyPairMoment B (groupedColumns node135 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node135 (EqualityPatterns.family3.label 2) = PairSemantics.raw5215 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node135 PairSemantics.raw5215; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5215 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node135 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node135 (EqualityPatterns.family3.label 3) = PairSemantics.raw198 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node135 PairSemantics.raw198; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical198 hH).trans (PairSemantics.sound8 hH)
  have hm4 : familyPairMoment B (groupedColumns node135 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value147 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node135 (EqualityPatterns.family3.label 4) = PairSemantics.raw153 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node135 PairSemantics.raw153; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical153 hH).trans (PairSemantics.sound147 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue135, PairSemantics.value0, PairSemantics.value4, PairSemantics.value8, PairSemantics.value25, PairSemantics.value147, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
