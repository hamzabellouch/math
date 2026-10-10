import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleRules
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical159
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical160
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical162
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical163
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound6

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue136 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 36)), (5, (5 / 36)), (10, (5 / 9)), (27, (5 / 36))]

theorem singlePair136 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node136 node136Labels = Sparse.eval singlePairValue136 (familyPairVector B) := by
  have hp := single_label_three B hB node136
  have hl : node136Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node136 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node136 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node136 PairSemantics.raw7980
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node136 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value45 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node136 (EqualityPatterns.family3.label 1) = PairSemantics.raw5116 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node136 PairSemantics.raw5116
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5116 hH).trans (PairSemantics.sound45 hH)
  have hm2 : familyPairMoment B (groupedColumns node136 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node136 (EqualityPatterns.family3.label 2) = PairSemantics.raw5215 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node136 PairSemantics.raw5215
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5215 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node136 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value9 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node136 (EqualityPatterns.family3.label 3) = PairSemantics.raw199 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node136 PairSemantics.raw199
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical199 hH).trans (PairSemantics.sound9 hH)
  have hm4 : familyPairMoment B (groupedColumns node136 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value151 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node136 (EqualityPatterns.family3.label 4) = PairSemantics.raw154 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node136 PairSemantics.raw154
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical154 hH).trans (PairSemantics.sound151 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue136, PairSemantics.value0, PairSemantics.value4, PairSemantics.value9, PairSemantics.value45, PairSemantics.value151, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue137 : Sparse (Fin 909) := [(0, (31 / 864)), (1, (5 / 864)), (2, (-35 / 864)), (5, (-5 / 108)), (6, (-35 / 864)), (13, (5 / 54)), (35, (5 / 27)), (82, (5 / 54))]

theorem singlePair137 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node137 node137Labels = Sparse.eval singlePairValue137 (familyPairVector B) := by
  have hp := single_label_three B hB node137
  have hl : node137Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node137 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node137 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node137 PairSemantics.raw7981
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node137 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node137 (EqualityPatterns.family3.label 1) = PairSemantics.raw5121 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node137 PairSemantics.raw5121
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5121 hH).trans (PairSemantics.sound118 hH)
  have hm2 : familyPairMoment B (groupedColumns node137 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node137 (EqualityPatterns.family3.label 2) = PairSemantics.raw5205 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node137 PairSemantics.raw5205
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5205 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node137 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node137 (EqualityPatterns.family3.label 3) = PairSemantics.raw193 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node137 PairSemantics.raw193
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical193 hH).trans (PairSemantics.sound8 hH)
  have hm4 : familyPairMoment B (groupedColumns node137 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value445 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node137 (EqualityPatterns.family3.label 4) = PairSemantics.raw155 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node137 PairSemantics.raw155
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical155 hH).trans (PairSemantics.sound445 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue137, PairSemantics.value0, PairSemantics.value8, PairSemantics.value11, PairSemantics.value118, PairSemantics.value445, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue138 : Sparse (Fin 909) := [(0, (1 / 27)), (5, (35 / 216)), (7, (5 / 27)), (8, (5 / 27)), (10, (-5 / 18)), (27, (-5 / 72))]

theorem singlePair138 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node138 node138Labels = Sparse.eval singlePairValue138 (familyPairVector B) := by
  have hp := single_label_three B hB node138
  have hl : node138Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node138 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node138 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node138 PairSemantics.raw7981
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node138 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value231 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node138 (EqualityPatterns.family3.label 1) = PairSemantics.raw5122 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node138 PairSemantics.raw5122
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5122 hH).trans (PairSemantics.sound231 hH)
  have hm2 : familyPairMoment B (groupedColumns node138 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node138 (EqualityPatterns.family3.label 2) = PairSemantics.raw5205 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node138 PairSemantics.raw5205
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5205 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node138 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value9 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node138 (EqualityPatterns.family3.label 3) = PairSemantics.raw194 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node138 PairSemantics.raw194
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical194 hH).trans (PairSemantics.sound9 hH)
  have hm4 : familyPairMoment B (groupedColumns node138 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value446 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node138 (EqualityPatterns.family3.label 4) = PairSemantics.raw156 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node138 PairSemantics.raw156
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical156 hH).trans (PairSemantics.sound446 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue138, PairSemantics.value0, PairSemantics.value9, PairSemantics.value11, PairSemantics.value231, PairSemantics.value446, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue139 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 144)), (2, (5 / 144)), (5, (5 / 54)), (8, (5 / 54)), (35, (5 / 27)), (67, (5 / 54))]

theorem singlePair139 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node139 node139Labels = Sparse.eval singlePairValue139 (familyPairVector B) := by
  have hp := single_label_three B hB node139
  have hl : node139Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node139 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node139 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node139 PairSemantics.raw7981
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node139 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node139 (EqualityPatterns.family3.label 1) = PairSemantics.raw5136 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node139 PairSemantics.raw5136
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5136 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node139 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node139 (EqualityPatterns.family3.label 2) = PairSemantics.raw5193 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node139 PairSemantics.raw5193
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5193 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node139 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value9 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node139 (EqualityPatterns.family3.label 3) = PairSemantics.raw194 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node139 PairSemantics.raw194
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical194 hH).trans (PairSemantics.sound9 hH)
  have hm4 : familyPairMoment B (groupedColumns node139 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value420 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node139 (EqualityPatterns.family3.label 4) = PairSemantics.raw157 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node139 PairSemantics.raw157
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical157 hH).trans (PairSemantics.sound420 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue139, PairSemantics.value0, PairSemantics.value9, PairSemantics.value46, PairSemantics.value420, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue140 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 108)), (5, (-5 / 54)), (6, (25 / 216))]

theorem singlePair140 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node140 node140Labels = Sparse.eval singlePairValue140 (familyPairVector B) := by
  have hp := single_label_three B hB node140
  have hl : node140Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node140 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node140 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node140 PairSemantics.raw7980
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node140 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node140 (EqualityPatterns.family3.label 1) = PairSemantics.raw5141 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node140 PairSemantics.raw5141
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5141 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node140 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node140 (EqualityPatterns.family3.label 2) = PairSemantics.raw5192 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node140 PairSemantics.raw5192
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5192 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node140 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value2 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node140 (EqualityPatterns.family3.label 3) = PairSemantics.raw195 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node140 PairSemantics.raw195
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical195 hH).trans (PairSemantics.sound2 hH)
  have hm4 : familyPairMoment B (groupedColumns node140 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value131 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node140 (EqualityPatterns.family3.label 4) = PairSemantics.raw158 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node140 PairSemantics.raw158
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical158 hH).trans (PairSemantics.sound131 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue140, PairSemantics.value0, PairSemantics.value2, PairSemantics.value46, PairSemantics.value131, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue141 : Sparse (Fin 909) := [(0, (23 / 864)), (1, (-25 / 432)), (2, (-205 / 864)), (3, (-5 / 18)), (5, (10 / 27)), (6, (-5 / 144)), (7, (-5 / 9)), (8, (-5 / 9)), (35, (-5 / 27))]

theorem singlePair141 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node141 node141Labels = Sparse.eval singlePairValue141 (familyPairVector B) := by
  have hp := single_label_three B hB node141
  have hl : node141Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node141 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node141 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node141 PairSemantics.raw7982
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node141 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node141 (EqualityPatterns.family3.label 1) = PairSemantics.raw5127 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node141 PairSemantics.raw5127
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5127 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node141 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node141 (EqualityPatterns.family3.label 2) = PairSemantics.raw5206 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node141 PairSemantics.raw5206
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5206 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node141 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value69 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node141 (EqualityPatterns.family3.label 3) = PairSemantics.raw196 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node141 PairSemantics.raw196
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical196 hH).trans (PairSemantics.sound69 hH)
  have hm4 : familyPairMoment B (groupedColumns node141 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1542 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node141 (EqualityPatterns.family3.label 4) = PairSemantics.raw159 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node141 PairSemantics.raw159
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical159 hH).trans (PairSemantics.sound1542 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue141, PairSemantics.value0, PairSemantics.value11, PairSemantics.value69, PairSemantics.value232, PairSemantics.value1542, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue142 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (-5 / 96)), (2, (5 / 96)), (3, (5 / 54)), (5, (-25 / 216)), (6, (5 / 288)), (7, (5 / 27)), (8, (5 / 54)), (35, (5 / 54))]

theorem singlePair142 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node142 node142Labels = Sparse.eval singlePairValue142 (familyPairVector B) := by
  have hp := single_label_three B hB node142
  have hl : node142Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node142 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node142 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node142 PairSemantics.raw7981
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node142 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node142 (EqualityPatterns.family3.label 1) = PairSemantics.raw5128 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node142 PairSemantics.raw5128
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5128 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node142 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node142 (EqualityPatterns.family3.label 2) = PairSemantics.raw5205 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node142 PairSemantics.raw5205
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5205 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node142 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node142 (EqualityPatterns.family3.label 3) = PairSemantics.raw197 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node142 PairSemantics.raw197
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical197 hH).trans (PairSemantics.sound16 hH)
  have hm4 : familyPairMoment B (groupedColumns node142 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value443 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node142 (EqualityPatterns.family3.label 4) = PairSemantics.raw160 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node142 PairSemantics.raw160
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical160 hH).trans (PairSemantics.sound443 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue142, PairSemantics.value0, PairSemantics.value11, PairSemantics.value16, PairSemantics.value46, PairSemantics.value443, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue143 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-35 / 432)), (2, (-5 / 108)), (5, (5 / 108)), (6, (-5 / 108)), (35, (-5 / 27))]

theorem singlePair143 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node143 node143Labels = Sparse.eval singlePairValue143 (familyPairVector B) := by
  have hp := single_label_three B hB node143
  have hl : node143Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node143 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node143 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node143 PairSemantics.raw7980
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node143 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node143 (EqualityPatterns.family3.label 1) = PairSemantics.raw5132 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node143 PairSemantics.raw5132
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5132 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node143 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node143 (EqualityPatterns.family3.label 2) = PairSemantics.raw5204 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node143 PairSemantics.raw5204
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5204 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node143 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node143 (EqualityPatterns.family3.label 3) = PairSemantics.raw198 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node143 PairSemantics.raw198
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical198 hH).trans (PairSemantics.sound8 hH)
  have hm4 : familyPairMoment B (groupedColumns node143 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value155 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node143 (EqualityPatterns.family3.label 4) = PairSemantics.raw161 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node143 PairSemantics.raw161
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical161 hH).trans (PairSemantics.sound155 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue143, PairSemantics.value0, PairSemantics.value8, PairSemantics.value10, PairSemantics.value11, PairSemantics.value155, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue144 : Sparse (Fin 909) := [(0, (19 / 864)), (1, (25 / 432)), (2, (5 / 72)), (5, (-5 / 36)), (6, (5 / 288)), (7, (5 / 54)), (8, (5 / 27))]

theorem singlePair144 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node144 node144Labels = Sparse.eval singlePairValue144 (familyPairVector B) := by
  have hp := single_label_three B hB node144
  have hl : node144Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node144 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node144 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node144 PairSemantics.raw7981
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node144 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node144 (EqualityPatterns.family3.label 1) = PairSemantics.raw5139 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node144 PairSemantics.raw5139
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5139 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node144 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node144 (EqualityPatterns.family3.label 2) = PairSemantics.raw5196 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node144 PairSemantics.raw5196
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5196 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node144 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node144 (EqualityPatterns.family3.label 3) = PairSemantics.raw197 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node144 PairSemantics.raw197
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical197 hH).trans (PairSemantics.sound16 hH)
  have hm4 : familyPairMoment B (groupedColumns node144 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value440 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node144 (EqualityPatterns.family3.label 4) = PairSemantics.raw162 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node144 PairSemantics.raw162
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical162 hH).trans (PairSemantics.sound440 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue144, PairSemantics.value0, PairSemantics.value11, PairSemantics.value16, PairSemantics.value232, PairSemantics.value440, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue145 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 108)), (2, (25 / 432)), (3, (5 / 27)), (5, (-5 / 72)), (6, (5 / 432)), (7, (5 / 27)), (26, (5 / 54)), (35, (5 / 18)), (52, (5 / 54)), (67, (5 / 54))]

theorem singlePair145 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node145 node145Labels = Sparse.eval singlePairValue145 (familyPairVector B) := by
  have hp := single_label_three B hB node145
  have hl : node145Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node145 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node145 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node145 PairSemantics.raw7981
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node145 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node145 (EqualityPatterns.family3.label 1) = PairSemantics.raw5142 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node145 PairSemantics.raw5142
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5142 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node145 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node145 (EqualityPatterns.family3.label 2) = PairSemantics.raw5194 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node145 PairSemantics.raw5194
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5194 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node145 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node145 (EqualityPatterns.family3.label 3) = PairSemantics.raw197 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node145 PairSemantics.raw197
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical197 hH).trans (PairSemantics.sound16 hH)
  have hm4 : familyPairMoment B (groupedColumns node145 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value421 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node145 (EqualityPatterns.family3.label 4) = PairSemantics.raw163 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node145 PairSemantics.raw163
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical163 hH).trans (PairSemantics.sound421 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue145, PairSemantics.value0, PairSemantics.value16, PairSemantics.value46, PairSemantics.value421, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue146 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-5 / 54)), (2, (-5 / 72)), (5, (5 / 54)), (6, (-5 / 108))]

theorem singlePair146 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node146 node146Labels = Sparse.eval singlePairValue146 (familyPairVector B) := by
  have hp := single_label_three B hB node146
  have hl : node146Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node146 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node146 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node146 PairSemantics.raw7980
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node146 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node146 (EqualityPatterns.family3.label 1) = PairSemantics.raw5141 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node146 PairSemantics.raw5141
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5141 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node146 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node146 (EqualityPatterns.family3.label 2) = PairSemantics.raw5197 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node146 PairSemantics.raw5197
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5197 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node146 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node146 (EqualityPatterns.family3.label 3) = PairSemantics.raw198 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node146 PairSemantics.raw198
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical198 hH).trans (PairSemantics.sound8 hH)
  have hm4 : familyPairMoment B (groupedColumns node146 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value149 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node146 (EqualityPatterns.family3.label 4) = PairSemantics.raw164 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node146 PairSemantics.raw164
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical164 hH).trans (PairSemantics.sound149 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue146, PairSemantics.value0, PairSemantics.value8, PairSemantics.value11, PairSemantics.value46, PairSemantics.value149, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue147 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-25 / 432)), (2, (-5 / 216)), (5, (5 / 108)), (6, (-5 / 144)), (35, (-5 / 27)), (52, (-5 / 27))]

theorem singlePair147 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node147 node147Labels = Sparse.eval singlePairValue147 (familyPairVector B) := by
  have hp := single_label_three B hB node147
  have hl : node147Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node147 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node147 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node147 PairSemantics.raw7980
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node147 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node147 (EqualityPatterns.family3.label 1) = PairSemantics.raw5149 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node147 PairSemantics.raw5149
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5149 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node147 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node147 (EqualityPatterns.family3.label 2) = PairSemantics.raw5192 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node147 PairSemantics.raw5192
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5192 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node147 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node147 (EqualityPatterns.family3.label 3) = PairSemantics.raw198 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node147 PairSemantics.raw198
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical198 hH).trans (PairSemantics.sound8 hH)
  have hm4 : familyPairMoment B (groupedColumns node147 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value132 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node147 (EqualityPatterns.family3.label 4) = PairSemantics.raw165 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node147 PairSemantics.raw165
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical165 hH).trans (PairSemantics.sound132 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue147, PairSemantics.value0, PairSemantics.value8, PairSemantics.value46, PairSemantics.value132, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue148 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-25 / 432)), (2, (-5 / 216)), (5, (5 / 36)), (7, (-5 / 27)), (35, (-5 / 27)), (67, (-5 / 27))]

theorem singlePair148 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node148 node148Labels = Sparse.eval singlePairValue148 (familyPairVector B) := by
  have hp := single_label_three B hB node148
  have hl : node148Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node148 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node148 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node148 PairSemantics.raw7980
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node148 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node148 (EqualityPatterns.family3.label 1) = PairSemantics.raw5132 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node148 PairSemantics.raw5132
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5132 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node148 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node148 (EqualityPatterns.family3.label 2) = PairSemantics.raw5208 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node148 PairSemantics.raw5208
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5208 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node148 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value9 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node148 (EqualityPatterns.family3.label 3) = PairSemantics.raw199 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node148 PairSemantics.raw199
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical199 hH).trans (PairSemantics.sound9 hH)
  have hm4 : familyPairMoment B (groupedColumns node148 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value102 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node148 (EqualityPatterns.family3.label 4) = PairSemantics.raw166 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node148 PairSemantics.raw166
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical166 hH).trans (PairSemantics.sound102 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue148, PairSemantics.value0, PairSemantics.value9, PairSemantics.value10, PairSemantics.value46, PairSemantics.value102, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue149 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-5 / 72)), (5, (5 / 27)), (7, (-5 / 27)), (8, (-5 / 27))]

theorem singlePair149 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node149 node149Labels = Sparse.eval singlePairValue149 (familyPairVector B) := by
  have hp := single_label_three B hB node149
  have hl : node149Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node149 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node149 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node149 PairSemantics.raw7980
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node149 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node149 (EqualityPatterns.family3.label 1) = PairSemantics.raw5141 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node149 PairSemantics.raw5141
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5141 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node149 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node149 (EqualityPatterns.family3.label 2) = PairSemantics.raw5204 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node149 PairSemantics.raw5204
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5204 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node149 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value9 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node149 (EqualityPatterns.family3.label 3) = PairSemantics.raw199 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node149 PairSemantics.raw199
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical199 hH).trans (PairSemantics.sound9 hH)
  have hm4 : familyPairMoment B (groupedColumns node149 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value153 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node149 (EqualityPatterns.family3.label 4) = PairSemantics.raw167 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node149 PairSemantics.raw167
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical167 hH).trans (PairSemantics.sound153 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue149, PairSemantics.value0, PairSemantics.value9, PairSemantics.value11, PairSemantics.value46, PairSemantics.value153, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue150 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (-35 / 432)), (2, (-5 / 216)), (3, (5 / 27)), (4, (5 / 54)), (5, (5 / 72)), (6, (-5 / 288)), (7, (5 / 54)), (26, (5 / 27)), (35, (5 / 27)), (67, (5 / 54)), (81, (-5 / 18))]

theorem singlePair150 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node150 node150Labels = Sparse.eval singlePairValue150 (familyPairVector B) := by
  have hp := single_label_three B hB node150
  have hl : node150Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node150 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node150 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node150 PairSemantics.raw7981
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node150 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node150 (EqualityPatterns.family3.label 1) = PairSemantics.raw5128 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node150 PairSemantics.raw5128
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5128 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node150 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node150 (EqualityPatterns.family3.label 2) = PairSemantics.raw5217 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node150 PairSemantics.raw5217
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5217 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node150 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value69 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node150 (EqualityPatterns.family3.label 3) = PairSemantics.raw207 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node150 PairSemantics.raw207
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical207 hH).trans (PairSemantics.sound69 hH)
  have hm4 : familyPairMoment B (groupedColumns node150 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value422 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node150 (EqualityPatterns.family3.label 4) = PairSemantics.raw168 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node150 PairSemantics.raw168
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical168 hH).trans (PairSemantics.sound422 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue150, PairSemantics.value0, PairSemantics.value46, PairSemantics.value69, PairSemantics.value422, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue151 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (5 / 54)), (2, (-35 / 864)), (3, (5 / 18)), (5, (5 / 108)), (6, (-5 / 288)), (7, (5 / 18)), (35, (5 / 27))]

theorem singlePair151 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node151 node151Labels = Sparse.eval singlePairValue151 (familyPairVector B) := by
  have hp := single_label_three B hB node151
  have hl : node151Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node151 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node151 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node151 PairSemantics.raw7981
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node151 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node151 (EqualityPatterns.family3.label 1) = PairSemantics.raw5139 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node151 PairSemantics.raw5139
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5139 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node151 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node151 (EqualityPatterns.family3.label 2) = PairSemantics.raw5216 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node151 PairSemantics.raw5216
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5216 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node151 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value69 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node151 (EqualityPatterns.family3.label 3) = PairSemantics.raw207 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node151 PairSemantics.raw207
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical207 hH).trans (PairSemantics.sound69 hH)
  have hm4 : familyPairMoment B (groupedColumns node151 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value437 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node151 (EqualityPatterns.family3.label 4) = PairSemantics.raw169 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node151 PairSemantics.raw169
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical169 hH).trans (PairSemantics.sound437 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue151, PairSemantics.value0, PairSemantics.value4, PairSemantics.value69, PairSemantics.value232, PairSemantics.value437, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
