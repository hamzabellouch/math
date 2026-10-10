import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleRules
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical160
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical161
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical162
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical163
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical279
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical280
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound6

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue152 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (55 / 432)), (2, (5 / 144)), (3, (-5 / 27)), (5, (-5 / 108)), (6, (5 / 432)), (7, (-5 / 27)), (35, (-5 / 27))]

theorem singlePair152 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node152 node152Labels = Sparse.eval singlePairValue152 (familyPairVector B) := by
  have hp := single_label_three B hB node152
  have hl : node152Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node152 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node152 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node152 PairSemantics.raw7980
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node152 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node152 (EqualityPatterns.family3.label 1) = PairSemantics.raw5141 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node152 PairSemantics.raw5141
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5141 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node152 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node152 (EqualityPatterns.family3.label 2) = PairSemantics.raw5215 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node152 PairSemantics.raw5215
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5215 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node152 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node152 (EqualityPatterns.family3.label 3) = PairSemantics.raw208 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node152 PairSemantics.raw208
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical208 hH).trans (PairSemantics.sound16 hH)
  have hm4 : familyPairMoment B (groupedColumns node152 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value146 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node152 (EqualityPatterns.family3.label 4) = PairSemantics.raw170 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node152 PairSemantics.raw170
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical170 hH).trans (PairSemantics.sound146 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue152, PairSemantics.value0, PairSemantics.value4, PairSemantics.value16, PairSemantics.value46, PairSemantics.value146, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue153 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 144)), (2, (5 / 108)), (5, (-5 / 108)), (6, (5 / 432)), (81, (5 / 9))]

theorem singlePair153 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node153 node153Labels = Sparse.eval singlePairValue153 (familyPairVector B) := by
  have hp := single_label_three B hB node153
  have hl : node153Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node153 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node153 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node153 PairSemantics.raw7980
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node153 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node153 (EqualityPatterns.family3.label 1) = PairSemantics.raw5149 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node153 PairSemantics.raw5149
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5149 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node153 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node153 (EqualityPatterns.family3.label 2) = PairSemantics.raw5213 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node153 PairSemantics.raw5213
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5213 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node153 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node153 (EqualityPatterns.family3.label 3) = PairSemantics.raw208 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node153 PairSemantics.raw208
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical208 hH).trans (PairSemantics.sound16 hH)
  have hm4 : familyPairMoment B (groupedColumns node153 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value134 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node153 (EqualityPatterns.family3.label 4) = PairSemantics.raw171 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node153 PairSemantics.raw171
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical171 hH).trans (PairSemantics.sound134 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue153, PairSemantics.value0, PairSemantics.value16, PairSemantics.value46, PairSemantics.value134, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue154 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 48)), (2, (-5 / 72)), (6, (-5 / 144)), (35, (5 / 9))]

theorem singlePair154 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node154 node154Labels = Sparse.eval singlePairValue154 (familyPairVector B) := by
  have hp := single_label_three B hB node154
  have hl : node154Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node154 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node154 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node154 PairSemantics.raw7979
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node154 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node154 (EqualityPatterns.family3.label 1) = PairSemantics.raw5151 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node154 PairSemantics.raw5151
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5151 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node154 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node154 (EqualityPatterns.family3.label 2) = PairSemantics.raw5214 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node154 PairSemantics.raw5214
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5214 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node154 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node154 (EqualityPatterns.family3.label 3) = PairSemantics.raw211 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node154 PairSemantics.raw211
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical211 hH).trans (PairSemantics.sound8 hH)
  have hm4 : familyPairMoment B (groupedColumns node154 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value32 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node154 (EqualityPatterns.family3.label 4) = PairSemantics.raw172 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node154 PairSemantics.raw172
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical172 hH).trans (PairSemantics.sound32 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue154, PairSemantics.value0, PairSemantics.value4, PairSemantics.value8, PairSemantics.value10, PairSemantics.value32, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue155 : Sparse (Fin 909) := [(0, (37 / 864)), (1, (-35 / 432)), (6, (-5 / 288)), (7, (5 / 54)), (8, (5 / 27))]

theorem singlePair155 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node155 node155Labels = Sparse.eval singlePairValue155 (familyPairVector B) := by
  have hp := single_label_three B hB node155
  have hl : node155Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node155 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node155 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node155 PairSemantics.raw7981
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node155 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node155 (EqualityPatterns.family3.label 1) = PairSemantics.raw5167 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node155 PairSemantics.raw5167
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5167 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node155 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node155 (EqualityPatterns.family3.label 2) = PairSemantics.raw5205 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node155 PairSemantics.raw5205
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5205 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node155 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value69 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node155 (EqualityPatterns.family3.label 3) = PairSemantics.raw207 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node155 PairSemantics.raw207
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical207 hH).trans (PairSemantics.sound69 hH)
  have hm4 : familyPairMoment B (groupedColumns node155 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value441 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node155 (EqualityPatterns.family3.label 4) = PairSemantics.raw173 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node155 PairSemantics.raw173
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical173 hH).trans (PairSemantics.sound441 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue155, PairSemantics.value0, PairSemantics.value11, PairSemantics.value69, PairSemantics.value441, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue156 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (5 / 36)), (6, (5 / 432)), (7, (-5 / 27))]

theorem singlePair156 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node156 node156Labels = Sparse.eval singlePairValue156 (familyPairVector B) := by
  have hp := single_label_three B hB node156
  have hl : node156Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node156 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node156 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node156 PairSemantics.raw7980
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node156 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node156 (EqualityPatterns.family3.label 1) = PairSemantics.raw5169 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node156 PairSemantics.raw5169
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5169 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node156 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node156 (EqualityPatterns.family3.label 2) = PairSemantics.raw5204 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node156 PairSemantics.raw5204
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5204 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node156 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node156 (EqualityPatterns.family3.label 3) = PairSemantics.raw208 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node156 PairSemantics.raw208
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical208 hH).trans (PairSemantics.sound16 hH)
  have hm4 : familyPairMoment B (groupedColumns node156 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value145 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node156 (EqualityPatterns.family3.label 4) = PairSemantics.raw174 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node156 PairSemantics.raw174
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical174 hH).trans (PairSemantics.sound145 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue156, PairSemantics.value0, PairSemantics.value4, PairSemantics.value11, PairSemantics.value16, PairSemantics.value145, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue157 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-5 / 54)), (6, (5 / 432)), (8, (-5 / 27))]

theorem singlePair157 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node157 node157Labels = Sparse.eval singlePairValue157 (familyPairVector B) := by
  have hp := single_label_three B hB node157
  have hl : node157Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node157 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node157 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node157 PairSemantics.raw7980
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node157 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node157 (EqualityPatterns.family3.label 1) = PairSemantics.raw5177 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node157 PairSemantics.raw5177
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5177 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node157 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node157 (EqualityPatterns.family3.label 2) = PairSemantics.raw5197 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node157 PairSemantics.raw5197
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5197 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node157 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node157 (EqualityPatterns.family3.label 3) = PairSemantics.raw208 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node157 PairSemantics.raw208
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical208 hH).trans (PairSemantics.sound16 hH)
  have hm4 : familyPairMoment B (groupedColumns node157 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value150 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node157 (EqualityPatterns.family3.label 4) = PairSemantics.raw175 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node157 PairSemantics.raw175
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical175 hH).trans (PairSemantics.sound150 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue157, PairSemantics.value0, PairSemantics.value11, PairSemantics.value16, PairSemantics.value150, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue158 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (5 / 36)), (5, (-5 / 36)), (6, (-5 / 144))]

theorem singlePair158 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node158 node158Labels = Sparse.eval singlePairValue158 (familyPairVector B) := by
  have hp := single_label_three B hB node158
  have hl : node158Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node158 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node158 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node158 PairSemantics.raw7979
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node158 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node158 (EqualityPatterns.family3.label 1) = PairSemantics.raw5183 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node158 PairSemantics.raw5183
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5183 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node158 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node158 (EqualityPatterns.family3.label 2) = PairSemantics.raw5199 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node158 PairSemantics.raw5199
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5199 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node158 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node158 (EqualityPatterns.family3.label 3) = PairSemantics.raw211 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node158 PairSemantics.raw211
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical211 hH).trans (PairSemantics.sound8 hH)
  have hm4 : familyPairMoment B (groupedColumns node158 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value52 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node158 (EqualityPatterns.family3.label 4) = PairSemantics.raw176 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node158 PairSemantics.raw176
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical176 hH).trans (PairSemantics.sound52 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue158, PairSemantics.value0, PairSemantics.value4, PairSemantics.value8, PairSemantics.value11, PairSemantics.value52, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue159 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 72)), (2, (-5 / 72)), (5, (5 / 36)), (67, (5 / 9))]

theorem singlePair159 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node159 node159Labels = Sparse.eval singlePairValue159 (familyPairVector B) := by
  have hp := single_label_three B hB node159
  have hl : node159Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node159 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node159 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node159 PairSemantics.raw7979
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node159 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node159 (EqualityPatterns.family3.label 1) = PairSemantics.raw5151 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node159 PairSemantics.raw5151
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5151 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node159 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node159 (EqualityPatterns.family3.label 2) = PairSemantics.raw5218 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node159 PairSemantics.raw5218
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5218 hH).trans (PairSemantics.sound10 hH)
  have hm3 : familyPairMoment B (groupedColumns node159 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value9 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node159 (EqualityPatterns.family3.label 3) = PairSemantics.raw214 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node159 PairSemantics.raw214
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical214 hH).trans (PairSemantics.sound9 hH)
  have hm4 : familyPairMoment B (groupedColumns node159 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value20 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node159 (EqualityPatterns.family3.label 4) = PairSemantics.raw177 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node159 PairSemantics.raw177
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical177 hH).trans (PairSemantics.sound20 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue159, PairSemantics.value0, PairSemantics.value9, PairSemantics.value10, PairSemantics.value20, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue160 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 18)), (5, (5 / 36)), (7, (5 / 9))]

theorem singlePair160 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node160 node160Labels = Sparse.eval singlePairValue160 (familyPairVector B) := by
  have hp := single_label_three B hB node160
  have hl : node160Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node160 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node160 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node160 PairSemantics.raw7979
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node160 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node160 (EqualityPatterns.family3.label 1) = PairSemantics.raw5183 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node160 PairSemantics.raw5183
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5183 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node160 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node160 (EqualityPatterns.family3.label 2) = PairSemantics.raw5214 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node160 PairSemantics.raw5214
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5214 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node160 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value9 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node160 (EqualityPatterns.family3.label 3) = PairSemantics.raw214 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node160 PairSemantics.raw214
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical214 hH).trans (PairSemantics.sound9 hH)
  have hm4 : familyPairMoment B (groupedColumns node160 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value31 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node160 (EqualityPatterns.family3.label 4) = PairSemantics.raw178 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node160 PairSemantics.raw178
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical178 hH).trans (PairSemantics.sound31 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue160, PairSemantics.value0, PairSemantics.value4, PairSemantics.value9, PairSemantics.value31, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue161 : Sparse (Fin 909) := [(0, (1 / 24)), (1, (-5 / 72)), (5, (5 / 36)), (8, (5 / 9))]

theorem singlePair161 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node161 node161Labels = Sparse.eval singlePairValue161 (familyPairVector B) := by
  have hp := single_label_three B hB node161
  have hl : node161Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node161 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node161 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node161 PairSemantics.raw7979
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node161 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node161 (EqualityPatterns.family3.label 1) = PairSemantics.raw5199 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node161 PairSemantics.raw5199
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5199 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node161 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node161 (EqualityPatterns.family3.label 2) = PairSemantics.raw5199 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node161 PairSemantics.raw5199
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5199 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node161 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value9 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node161 (EqualityPatterns.family3.label 3) = PairSemantics.raw214 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node161 PairSemantics.raw214
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical214 hH).trans (PairSemantics.sound9 hH)
  have hm4 : familyPairMoment B (groupedColumns node161 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value35 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node161 (EqualityPatterns.family3.label 4) = PairSemantics.raw179 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node161 PairSemantics.raw179
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical179 hH).trans (PairSemantics.sound35 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue161, PairSemantics.value0, PairSemantics.value9, PairSemantics.value11, PairSemantics.value35, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue162 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 18)), (5, (5 / 9)), (6, (5 / 36))]

theorem singlePair162 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node162 node162Labels = Sparse.eval singlePairValue162 (familyPairVector B) := by
  have hp := single_label_three B hB node162
  have hl : node162Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node162 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node162 (EqualityPatterns.family3.label 0) = PairSemantics.raw7978 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node162 PairSemantics.raw7978
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7978 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node162 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node162 (EqualityPatterns.family3.label 1) = PairSemantics.raw5210 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node162 PairSemantics.raw5210
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5210 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node162 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node162 (EqualityPatterns.family3.label 2) = PairSemantics.raw5210 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node162 PairSemantics.raw5210
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5210 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node162 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value2 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node162 (EqualityPatterns.family3.label 3) = PairSemantics.raw215 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node162 PairSemantics.raw215
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical215 hH).trans (PairSemantics.sound2 hH)
  have hm4 : familyPairMoment B (groupedColumns node162 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value9 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node162 (EqualityPatterns.family3.label 4) = PairSemantics.raw180 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node162 PairSemantics.raw180
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical180 hH).trans (PairSemantics.sound9 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue162, PairSemantics.value0, PairSemantics.value2, PairSemantics.value4, PairSemantics.value9, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue163 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (5 / 144)), (3, (-5 / 18)), (5, (5 / 54)), (6, (-5 / 144)), (7, (-10 / 27)), (9, (5 / 216)), (13, (-5 / 54)), (26, (-10 / 27)), (34, (-5 / 54)), (35, (-20 / 27)), (67, (-5 / 27)), (68, (-5 / 72)), (69, (-5 / 54)), (70, (-5 / 18)), (124, (5 / 18)), (196, (5 / 18)), (197, (5 / 9)), (257, (-5 / 54)), (266, (5 / 18))]

theorem singlePair163 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node163 node163Labels = Sparse.eval singlePairValue163 (familyPairVector B) := by
  have hp := single_label_three B hB node163
  have hl : node163Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node163 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node163 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node163 PairSemantics.raw7982
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node163 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node163 (EqualityPatterns.family3.label 1) = PairSemantics.raw889 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node163 PairSemantics.raw889
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical889 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node163 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node163 (EqualityPatterns.family3.label 2) = PairSemantics.raw8961 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node163 PairSemantics.raw8961
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8961 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node163 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value116 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node163 (EqualityPatterns.family3.label 3) = PairSemantics.raw844 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node163 PairSemantics.raw844
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical844 hH).trans (PairSemantics.sound116 hH)
  have hm4 : familyPairMoment B (groupedColumns node163 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1392 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node163 (EqualityPatterns.family3.label 4) = PairSemantics.raw368 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node163 PairSemantics.raw368
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical368 hH).trans (PairSemantics.sound1392 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue163, PairSemantics.value0, PairSemantics.value10, PairSemantics.value116, PairSemantics.value232, PairSemantics.value1392, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue164 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (-5 / 864)), (2, (5 / 864)), (3, (-25 / 54)), (5, (5 / 54)), (6, (-5 / 288)), (7, (-10 / 27)), (9, (5 / 216)), (13, (-5 / 18)), (26, (-5 / 27)), (34, (-5 / 54)), (35, (-5 / 9)), (52, (-5 / 27)), (60, (-5 / 54)), (64, (5 / 18)), (67, (-5 / 54)), (68, (-5 / 72)), (69, (-5 / 54)), (70, (-5 / 27)), (125, (5 / 9)), (126, (5 / 18)), (197, (5 / 18)), (257, (-5 / 54)), (260, (5 / 18)), (268, (5 / 18))]

theorem singlePair164 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node164 node164Labels = Sparse.eval singlePairValue164 (familyPairVector B) := by
  have hp := single_label_three B hB node164
  have hl : node164Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node164 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node164 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node164 PairSemantics.raw7982
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node164 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node164 (EqualityPatterns.family3.label 1) = PairSemantics.raw890 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node164 PairSemantics.raw890
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical890 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node164 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node164 (EqualityPatterns.family3.label 2) = PairSemantics.raw8960 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node164 PairSemantics.raw8960
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8960 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node164 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value116 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node164 (EqualityPatterns.family3.label 3) = PairSemantics.raw844 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node164 PairSemantics.raw844
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical844 hH).trans (PairSemantics.sound116 hH)
  have hm4 : familyPairMoment B (groupedColumns node164 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1395 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node164 (EqualityPatterns.family3.label 4) = PairSemantics.raw369 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node164 PairSemantics.raw369
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical369 hH).trans (PairSemantics.sound1395 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue164, PairSemantics.value0, PairSemantics.value26, PairSemantics.value46, PairSemantics.value116, PairSemantics.value1395, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue165 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 96)), (2, (-5 / 288)), (3, (-5 / 54)), (5, (5 / 108)), (7, (-5 / 54)), (13, (-5 / 54)), (23, (5 / 9)), (27, (-5 / 72)), (35, (-5 / 54)), (54, (5 / 9)), (55, (5 / 18)), (63, (5 / 18)), (65, (5 / 18)), (68, (-5 / 36)), (124, (5 / 18)), (125, (5 / 6)), (196, (5 / 9)), (197, (5 / 18)), (264, (5 / 9)), (266, (5 / 18))]

theorem singlePair165 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node165 node165Labels = Sparse.eval singlePairValue165 (familyPairVector B) := by
  have hp := single_label_three B hB node165
  have hl : node165Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node165 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node165 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node165 PairSemantics.raw7982
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node165 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node165 (EqualityPatterns.family3.label 1) = PairSemantics.raw889 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node165 PairSemantics.raw889
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical889 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node165 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node165 (EqualityPatterns.family3.label 2) = PairSemantics.raw8963 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node165 PairSemantics.raw8963
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8963 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node165 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value117 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node165 (EqualityPatterns.family3.label 3) = PairSemantics.raw845 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node165 PairSemantics.raw845
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical845 hH).trans (PairSemantics.sound117 hH)
  have hm4 : familyPairMoment B (groupedColumns node165 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1394 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node165 (EqualityPatterns.family3.label 4) = PairSemantics.raw370 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node165 PairSemantics.raw370
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical370 hH).trans (PairSemantics.sound1394 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue165, PairSemantics.value0, PairSemantics.value10, PairSemantics.value46, PairSemantics.value117, PairSemantics.value1394, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue166 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 288)), (2, (-5 / 288)), (3, (-5 / 27)), (5, (5 / 54)), (6, (-5 / 432)), (7, (-5 / 27)), (9, (5 / 216)), (13, (-10 / 27)), (32, (-5 / 54)), (35, (-10 / 27)), (52, (-5 / 27)), (54, (5 / 9)), (60, (-5 / 27)), (62, (5 / 9)), (68, (-5 / 72)), (69, (-5 / 54)), (70, (-5 / 54)), (125, (5 / 9)), (257, (-5 / 54)), (260, (5 / 9)), (264, (5 / 6))]

theorem singlePair166 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node166 node166Labels = Sparse.eval singlePairValue166 (familyPairVector B) := by
  have hp := single_label_three B hB node166
  have hl : node166Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node166 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node166 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node166 PairSemantics.raw7982
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node166 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node166 (EqualityPatterns.family3.label 1) = PairSemantics.raw894 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node166 PairSemantics.raw894
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical894 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node166 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node166 (EqualityPatterns.family3.label 2) = PairSemantics.raw8957 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node166 PairSemantics.raw8957
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8957 hH).trans (PairSemantics.sound10 hH)
  have hm3 : familyPairMoment B (groupedColumns node166 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value116 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node166 (EqualityPatterns.family3.label 3) = PairSemantics.raw844 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node166 PairSemantics.raw844
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical844 hH).trans (PairSemantics.sound116 hH)
  have hm4 : familyPairMoment B (groupedColumns node166 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1397 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node166 (EqualityPatterns.family3.label 4) = PairSemantics.raw371 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node166 PairSemantics.raw371
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical371 hH).trans (PairSemantics.sound1397 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue166, PairSemantics.value0, PairSemantics.value10, PairSemantics.value26, PairSemantics.value116, PairSemantics.value1397, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue167 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (5 / 432)), (2, (5 / 288)), (5, (5 / 216)), (23, (5 / 18)), (24, (5 / 18)), (27, (-5 / 36)), (51, (5 / 18)), (54, (5 / 18)), (55, (5 / 18)), (56, (5 / 18)), (61, (5 / 18)), (68, (-5 / 36)), (124, (5 / 18)), (125, (5 / 18)), (126, (5 / 18)), (196, (5 / 18)), (197, (5 / 9)), (263, (-5 / 9)), (266, (5 / 18)), (268, (5 / 18))]

theorem singlePair167 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node167 node167Labels = Sparse.eval singlePairValue167 (familyPairVector B) := by
  have hp := single_label_three B hB node167
  have hl : node167Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node167 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node167 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node167 PairSemantics.raw7982
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node167 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node167 (EqualityPatterns.family3.label 1) = PairSemantics.raw892 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node167 PairSemantics.raw892
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical892 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node167 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node167 (EqualityPatterns.family3.label 2) = PairSemantics.raw8958 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node167 PairSemantics.raw8958
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8958 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node167 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value117 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node167 (EqualityPatterns.family3.label 3) = PairSemantics.raw845 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node167 PairSemantics.raw845
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical845 hH).trans (PairSemantics.sound117 hH)
  have hm4 : familyPairMoment B (groupedColumns node167 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1396 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node167 (EqualityPatterns.family3.label 4) = PairSemantics.raw372 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node167 PairSemantics.raw372
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical372 hH).trans (PairSemantics.sound1396 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue167, PairSemantics.value0, PairSemantics.value26, PairSemantics.value46, PairSemantics.value117, PairSemantics.value1396, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
