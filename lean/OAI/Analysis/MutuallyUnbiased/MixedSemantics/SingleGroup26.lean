import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleRules
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical120
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical121
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical159
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical160
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical161
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical280
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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound9

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue425 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (25 / 216)), (2, (-5 / 108)), (5, (-5 / 108)), (8, (-5 / 27)), (24, (5 / 9)), (27, (-5 / 36)), (30, (5 / 9)), (68, (5 / 18)), (126, (5 / 9)), (236, (5 / 9))]

theorem singlePair425 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node425 node425Labels = Sparse.eval singlePairValue425 (familyPairVector B) := by
  have hp := single_label_three B hB node425
  have hl : node425Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node425 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node425 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node425 PairSemantics.raw7982
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node425 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node425 (EqualityPatterns.family3.label 1) = PairSemantics.raw5127 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node425 PairSemantics.raw5127
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5127 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node425 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node425 (EqualityPatterns.family3.label 2) = PairSemantics.raw9007 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node425 PairSemantics.raw9007
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9007 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node425 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value715 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node425 (EqualityPatterns.family3.label 3) = PairSemantics.raw5102 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node425 PairSemantics.raw5102
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5102 hH).trans (PairSemantics.sound715 hH)
  have hm4 : familyPairMoment B (groupedColumns node425 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2648 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node425 (EqualityPatterns.family3.label 4) = PairSemantics.raw3866 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node425 PairSemantics.raw3866
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3866 hH).trans (PairSemantics.sound2648 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue425, PairSemantics.value0, PairSemantics.value65, PairSemantics.value232, PairSemantics.value715, PairSemantics.value2648, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue426 : Sparse (Fin 909) := [(0, (5 / 288)), (1, (35 / 432)), (2, (5 / 96)), (3, (-5 / 27)), (4, (-5 / 54)), (5, (-5 / 54)), (12, (-5 / 54)), (27, (5 / 72)), (31, (5 / 18)), (51, (5 / 9)), (55, (5 / 18)), (68, (5 / 18)), (194, (-5 / 9)), (486, (-5 / 9)), (487, (-5 / 9))]

theorem singlePair426 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node426 node426Labels = Sparse.eval singlePairValue426 (familyPairVector B) := by
  have hp := single_label_three B hB node426
  have hl : node426Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node426 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node426 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node426 PairSemantics.raw7982
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node426 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node426 (EqualityPatterns.family3.label 1) = PairSemantics.raw5130 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node426 PairSemantics.raw5130
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5130 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node426 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node426 (EqualityPatterns.family3.label 2) = PairSemantics.raw9003 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node426 PairSemantics.raw9003
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9003 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node426 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value715 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node426 (EqualityPatterns.family3.label 3) = PairSemantics.raw5102 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node426 PairSemantics.raw5102
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5102 hH).trans (PairSemantics.sound715 hH)
  have hm4 : familyPairMoment B (groupedColumns node426 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2089 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node426 (EqualityPatterns.family3.label 4) = PairSemantics.raw3867 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node426 PairSemantics.raw3867
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3867 hH).trans (PairSemantics.sound2089 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue426, PairSemantics.value0, PairSemantics.value46, PairSemantics.value232, PairSemantics.value715, PairSemantics.value2089, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue427 : Sparse (Fin 909) := [(0, (1 / 48)), (1, (-5 / 288)), (2, (25 / 288)), (3, (-5 / 54)), (5, (-5 / 54)), (12, (-5 / 54)), (23, (5 / 9)), (24, (5 / 18)), (25, (5 / 18)), (27, (5 / 72)), (54, (5 / 18)), (55, (5 / 18)), (68, (5 / 18)), (195, (-5 / 9)), (263, (-5 / 9)), (487, (-5 / 9))]

theorem singlePair427 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node427 node427Labels = Sparse.eval singlePairValue427 (familyPairVector B) := by
  have hp := single_label_three B hB node427
  have hl : node427Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node427 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node427 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node427 PairSemantics.raw7982
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node427 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node427 (EqualityPatterns.family3.label 1) = PairSemantics.raw5134 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node427 PairSemantics.raw5134
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5134 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node427 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node427 (EqualityPatterns.family3.label 2) = PairSemantics.raw8996 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node427 PairSemantics.raw8996
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8996 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node427 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value715 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node427 (EqualityPatterns.family3.label 3) = PairSemantics.raw5102 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node427 PairSemantics.raw5102
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5102 hH).trans (PairSemantics.sound715 hH)
  have hm4 : familyPairMoment B (groupedColumns node427 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2090 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node427 (EqualityPatterns.family3.label 4) = PairSemantics.raw3868 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node427 PairSemantics.raw3868
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3868 hH).trans (PairSemantics.sound2090 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue427, PairSemantics.value0, PairSemantics.value46, PairSemantics.value715, PairSemantics.value2090, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue428 : Sparse (Fin 909) := [(0, (7 / 432)), (1, (5 / 36)), (2, (-25 / 432)), (23, (5 / 9)), (24, (10 / 9)), (27, (-5 / 18)), (30, (5 / 9)), (55, (5 / 9)), (194, (-5 / 9))]

theorem singlePair428 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node428 node428Labels = Sparse.eval singlePairValue428 (familyPairVector B) := by
  have hp := single_label_three B hB node428
  have hl : node428Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node428 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node428 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node428 PairSemantics.raw7982
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node428 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node428 (EqualityPatterns.family3.label 1) = PairSemantics.raw5138 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node428 PairSemantics.raw5138
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5138 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node428 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node428 (EqualityPatterns.family3.label 2) = PairSemantics.raw9003 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node428 PairSemantics.raw9003
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9003 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node428 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value45 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node428 (EqualityPatterns.family3.label 3) = PairSemantics.raw5104 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node428 PairSemantics.raw5104
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5104 hH).trans (PairSemantics.sound45 hH)
  have hm4 : familyPairMoment B (groupedColumns node428 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2092 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node428 (EqualityPatterns.family3.label 4) = PairSemantics.raw3869 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node428 PairSemantics.raw3869
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3869 hH).trans (PairSemantics.sound2092 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue428, PairSemantics.value0, PairSemantics.value45, PairSemantics.value232, PairSemantics.value2092, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue429 : Sparse (Fin 909) := [(0, (5 / 108)), (2, (-5 / 72)), (3, (-5 / 18)), (5, (5 / 54)), (7, (-5 / 54)), (8, (-5 / 54)), (12, (-5 / 54)), (23, (5 / 18)), (24, (5 / 18)), (27, (-5 / 24)), (55, (5 / 18))]

theorem singlePair429 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node429 node429Labels = Sparse.eval singlePairValue429 (familyPairVector B) := by
  have hp := single_label_three B hB node429
  have hl : node429Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node429 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node429 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node429 PairSemantics.raw7982
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node429 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node429 (EqualityPatterns.family3.label 1) = PairSemantics.raw5134 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node429 PairSemantics.raw5134
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5134 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node429 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node429 (EqualityPatterns.family3.label 2) = PairSemantics.raw9012 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node429 PairSemantics.raw9012
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9012 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node429 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value231 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node429 (EqualityPatterns.family3.label 3) = PairSemantics.raw5105 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node429 PairSemantics.raw5105
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5105 hH).trans (PairSemantics.sound231 hH)
  have hm4 : familyPairMoment B (groupedColumns node429 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2663 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node429 (EqualityPatterns.family3.label 4) = PairSemantics.raw3870 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node429 PairSemantics.raw3870
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3870 hH).trans (PairSemantics.sound2663 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue429, PairSemantics.value0, PairSemantics.value46, PairSemantics.value65, PairSemantics.value231, PairSemantics.value2663, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue430 : Sparse (Fin 909) := [(0, (1 / 48)), (1, (155 / 864)), (2, (-115 / 864)), (3, (-5 / 27)), (4, (-5 / 54)), (5, (5 / 72)), (7, (-5 / 54)), (8, (-5 / 54)), (24, (5 / 18)), (27, (-5 / 18)), (30, (5 / 18)), (31, (5 / 18)), (51, (5 / 18))]

theorem singlePair430 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node430 node430Labels = Sparse.eval singlePairValue430 (familyPairVector B) := by
  have hp := single_label_three B hB node430
  have hl : node430Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node430 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node430 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node430 PairSemantics.raw7982
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node430 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node430 (EqualityPatterns.family3.label 1) = PairSemantics.raw5135 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node430 PairSemantics.raw5135
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5135 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node430 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node430 (EqualityPatterns.family3.label 2) = PairSemantics.raw9010 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node430 PairSemantics.raw9010
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9010 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node430 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value231 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node430 (EqualityPatterns.family3.label 3) = PairSemantics.raw5105 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node430 PairSemantics.raw5105
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5105 hH).trans (PairSemantics.sound231 hH)
  have hm4 : familyPairMoment B (groupedColumns node430 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2656 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node430 (EqualityPatterns.family3.label 4) = PairSemantics.raw3871 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node430 PairSemantics.raw3871
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3871 hH).trans (PairSemantics.sound2656 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue430, PairSemantics.value0, PairSemantics.value65, PairSemantics.value231, PairSemantics.value232, PairSemantics.value2656, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue431 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 36)), (2, (-5 / 48)), (3, (-5 / 9)), (4, (-5 / 27)), (5, (5 / 108)), (7, (-5 / 54)), (8, (-5 / 54)), (12, (-5 / 18)), (23, (5 / 18)), (24, (5 / 18)), (27, (-5 / 36)), (51, (5 / 9)), (55, (5 / 9))]

theorem singlePair431 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node431 node431Labels = Sparse.eval singlePairValue431 (familyPairVector B) := by
  have hp := single_label_three B hB node431
  have hl : node431Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node431 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node431 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node431 PairSemantics.raw7982
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node431 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node431 (EqualityPatterns.family3.label 1) = PairSemantics.raw5140 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node431 PairSemantics.raw5140
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5140 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node431 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node431 (EqualityPatterns.family3.label 2) = PairSemantics.raw9006 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node431 PairSemantics.raw9006
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9006 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node431 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value231 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node431 (EqualityPatterns.family3.label 3) = PairSemantics.raw5105 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node431 PairSemantics.raw5105
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5105 hH).trans (PairSemantics.sound231 hH)
  have hm4 : familyPairMoment B (groupedColumns node431 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2130 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node431 (EqualityPatterns.family3.label 4) = PairSemantics.raw3872 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node431 PairSemantics.raw3872
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3872 hH).trans (PairSemantics.sound2130 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue431, PairSemantics.value0, PairSemantics.value11, PairSemantics.value231, PairSemantics.value232, PairSemantics.value2130, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue432 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (-5 / 72)), (2, (5 / 288)), (23, (-5 / 18)), (24, (-5 / 18)), (27, (5 / 24)), (55, (-5 / 18))]

theorem singlePair432 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node432 node432Labels = Sparse.eval singlePairValue432 (familyPairVector B) := by
  have hp := single_label_three B hB node432
  have hl : node432Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node432 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node432 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node432 PairSemantics.raw7981
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node432 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node432 (EqualityPatterns.family3.label 1) = PairSemantics.raw5136 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node432 PairSemantics.raw5136
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5136 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node432 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node432 (EqualityPatterns.family3.label 2) = PairSemantics.raw9015 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node432 PairSemantics.raw9015
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9015 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node432 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value45 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node432 (EqualityPatterns.family3.label 3) = PairSemantics.raw5106 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node432 PairSemantics.raw5106
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5106 hH).trans (PairSemantics.sound45 hH)
  have hm4 : familyPairMoment B (groupedColumns node432 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value647 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node432 (EqualityPatterns.family3.label 4) = PairSemantics.raw3873 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node432 PairSemantics.raw3873
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3873 hH).trans (PairSemantics.sound647 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue432, PairSemantics.value0, PairSemantics.value11, PairSemantics.value45, PairSemantics.value46, PairSemantics.value647, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue433 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (5 / 216)), (24, (-5 / 18)), (27, (5 / 18)), (30, (-5 / 18))]

theorem singlePair433 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node433 node433Labels = Sparse.eval singlePairValue433 (familyPairVector B) := by
  have hp := single_label_three B hB node433
  have hl : node433Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node433 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node433 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node433 PairSemantics.raw7981
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node433 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node433 (EqualityPatterns.family3.label 1) = PairSemantics.raw5139 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node433 PairSemantics.raw5139
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5139 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node433 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node433 (EqualityPatterns.family3.label 2) = PairSemantics.raw9011 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node433 PairSemantics.raw9011
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9011 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node433 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value45 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node433 (EqualityPatterns.family3.label 3) = PairSemantics.raw5106 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node433 PairSemantics.raw5106
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5106 hH).trans (PairSemantics.sound45 hH)
  have hm4 : familyPairMoment B (groupedColumns node433 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1131 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node433 (EqualityPatterns.family3.label 4) = PairSemantics.raw3874 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node433 PairSemantics.raw3874
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3874 hH).trans (PairSemantics.sound1131 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue433, PairSemantics.value0, PairSemantics.value45, PairSemantics.value65, PairSemantics.value232, PairSemantics.value1131, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue434 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (25 / 432)), (2, (-5 / 432)), (3, (-35 / 54)), (4, (-5 / 54)), (5, (5 / 216)), (12, (-10 / 27)), (13, (-25 / 54)), (27, (-5 / 72)), (33, (5 / 9)), (51, (5 / 18)), (55, (5 / 18)), (59, (5 / 18)), (61, (5 / 18)), (194, (-5 / 9))]

theorem singlePair434 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node434 node434Labels = Sparse.eval singlePairValue434 (familyPairVector B) := by
  have hp := single_label_three B hB node434
  have hl : node434Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node434 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node434 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node434 PairSemantics.raw7982
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node434 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node434 (EqualityPatterns.family3.label 1) = PairSemantics.raw5148 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node434 PairSemantics.raw5148
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5148 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node434 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node434 (EqualityPatterns.family3.label 2) = PairSemantics.raw8993 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node434 PairSemantics.raw8993
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8993 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node434 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value231 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node434 (EqualityPatterns.family3.label 3) = PairSemantics.raw5105 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node434 PairSemantics.raw5105
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5105 hH).trans (PairSemantics.sound231 hH)
  have hm4 : familyPairMoment B (groupedColumns node434 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2091 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node434 (EqualityPatterns.family3.label 4) = PairSemantics.raw3875 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node434 PairSemantics.raw3875
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3875 hH).trans (PairSemantics.sound2091 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue434, PairSemantics.value0, PairSemantics.value46, PairSemantics.value231, PairSemantics.value2091, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue435 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 108)), (2, (5 / 216)), (27, (5 / 36)), (194, (5 / 9))]

theorem singlePair435 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node435 node435Labels = Sparse.eval singlePairValue435 (familyPairVector B) := by
  have hp := single_label_three B hB node435
  have hl : node435Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node435 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node435 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node435 PairSemantics.raw7981
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node435 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node435 (EqualityPatterns.family3.label 1) = PairSemantics.raw5147 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node435 PairSemantics.raw5147
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5147 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node435 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node435 (EqualityPatterns.family3.label 2) = PairSemantics.raw8998 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node435 PairSemantics.raw8998
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8998 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node435 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value45 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node435 (EqualityPatterns.family3.label 3) = PairSemantics.raw5106 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node435 PairSemantics.raw5106
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5106 hH).trans (PairSemantics.sound45 hH)
  have hm4 : familyPairMoment B (groupedColumns node435 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value622 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node435 (EqualityPatterns.family3.label 4) = PairSemantics.raw3876 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node435 PairSemantics.raw3876
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3876 hH).trans (PairSemantics.sound622 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue435, PairSemantics.value0, PairSemantics.value45, PairSemantics.value46, PairSemantics.value622, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue436 : Sparse (Fin 909) := [(0, (19 / 432)), (2, (25 / 432)), (3, (-5 / 18)), (4, (-5 / 27)), (5, (-5 / 108)), (12, (-5 / 54)), (27, (5 / 72)), (31, (5 / 9)), (51, (5 / 9)), (55, (5 / 18))]

theorem singlePair436 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node436 node436Labels = Sparse.eval singlePairValue436 (familyPairVector B) := by
  have hp := single_label_three B hB node436
  have hl : node436Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node436 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node436 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node436 PairSemantics.raw7982
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node436 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node436 (EqualityPatterns.family3.label 1) = PairSemantics.raw5123 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node436 PairSemantics.raw5123
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5123 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node436 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node436 (EqualityPatterns.family3.label 2) = PairSemantics.raw9031 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node436 PairSemantics.raw9031
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9031 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node436 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value716 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node436 (EqualityPatterns.family3.label 3) = PairSemantics.raw5109 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node436 PairSemantics.raw5109
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5109 hH).trans (PairSemantics.sound716 hH)
  have hm4 : familyPairMoment B (groupedColumns node436 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2668 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node436 (EqualityPatterns.family3.label 4) = PairSemantics.raw3877 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node436 PairSemantics.raw3877
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3877 hH).trans (PairSemantics.sound2668 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue436, PairSemantics.value0, PairSemantics.value46, PairSemantics.value65, PairSemantics.value716, PairSemantics.value2668, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue437 : Sparse (Fin 909) := [(0, (35 / 864)), (1, (-5 / 144)), (2, (5 / 864)), (5, (5 / 216)), (31, (-5 / 18)), (51, (-5 / 18))]

theorem singlePair437 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node437 node437Labels = Sparse.eval singlePairValue437 (familyPairVector B) := by
  have hp := single_label_three B hB node437
  have hl : node437Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node437 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node437 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node437 PairSemantics.raw7981
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node437 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node437 (EqualityPatterns.family3.label 1) = PairSemantics.raw5131 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node437 PairSemantics.raw5131
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5131 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node437 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node437 (EqualityPatterns.family3.label 2) = PairSemantics.raw9025 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node437 PairSemantics.raw9025
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9025 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node437 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value231 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node437 (EqualityPatterns.family3.label 3) = PairSemantics.raw5110 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node437 PairSemantics.raw5110
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5110 hH).trans (PairSemantics.sound231 hH)
  have hm4 : familyPairMoment B (groupedColumns node437 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1136 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node437 (EqualityPatterns.family3.label 4) = PairSemantics.raw3878 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node437 PairSemantics.raw3878
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3878 hH).trans (PairSemantics.sound1136 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue437, PairSemantics.value0, PairSemantics.value46, PairSemantics.value65, PairSemantics.value231, PairSemantics.value1136, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue438 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-35 / 432)), (2, (-5 / 432)), (3, (5 / 27)), (4, (5 / 54)), (5, (5 / 216)), (12, (5 / 54)), (27, (-5 / 72)), (51, (-5 / 18)), (55, (-5 / 18))]

theorem singlePair438 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node438 node438Labels = Sparse.eval singlePairValue438 (familyPairVector B) := by
  have hp := single_label_three B hB node438
  have hl : node438Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node438 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node438 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node438 PairSemantics.raw7981
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node438 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node438 (EqualityPatterns.family3.label 1) = PairSemantics.raw5142 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node438 PairSemantics.raw5142
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5142 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node438 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node438 (EqualityPatterns.family3.label 2) = PairSemantics.raw9018 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node438 PairSemantics.raw9018
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9018 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node438 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value231 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node438 (EqualityPatterns.family3.label 3) = PairSemantics.raw5110 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node438 PairSemantics.raw5110
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5110 hH).trans (PairSemantics.sound231 hH)
  have hm4 : familyPairMoment B (groupedColumns node438 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value660 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node438 (EqualityPatterns.family3.label 4) = PairSemantics.raw3879 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node438 PairSemantics.raw3879
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3879 hH).trans (PairSemantics.sound660 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue438, PairSemantics.value0, PairSemantics.value11, PairSemantics.value46, PairSemantics.value231, PairSemantics.value660, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue439 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (55 / 432)), (2, (55 / 864)), (3, (-10 / 27)), (5, (-5 / 54)), (7, (-5 / 27)), (12, (-5 / 27)), (23, (5 / 9)), (25, (5 / 18)), (27, (5 / 36)), (54, (5 / 9)), (68, (5 / 18)), (124, (5 / 18)), (125, (5 / 9)), (196, (5 / 18))]

theorem singlePair439 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node439 node439Labels = Sparse.eval singlePairValue439 (familyPairVector B) := by
  have hp := single_label_three B hB node439
  have hl : node439Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node439 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node439 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node439 PairSemantics.raw7982
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node439 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node439 (EqualityPatterns.family3.label 1) = PairSemantics.raw5155 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node439 PairSemantics.raw5155
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5155 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node439 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node439 (EqualityPatterns.family3.label 2) = PairSemantics.raw8970 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node439 PairSemantics.raw8970
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8970 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node439 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value715 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node439 (EqualityPatterns.family3.label 3) = PairSemantics.raw5102 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node439 PairSemantics.raw5102
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5102 hH).trans (PairSemantics.sound715 hH)
  have hm4 : familyPairMoment B (groupedColumns node439 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2112 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node439 (EqualityPatterns.family3.label 4) = PairSemantics.raw3880 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node439 PairSemantics.raw3880
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3880 hH).trans (PairSemantics.sound2112 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue439, PairSemantics.value0, PairSemantics.value4, PairSemantics.value46, PairSemantics.value715, PairSemantics.value2112, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue440 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 216)), (2, (5 / 432)), (23, (5 / 9)), (24, (5 / 9)), (55, (10 / 9)), (63, (5 / 9)), (65, (5 / 9))]

theorem singlePair440 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node440 node440Labels = Sparse.eval singlePairValue440 (familyPairVector B) := by
  have hp := single_label_three B hB node440
  have hl : node440Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node440 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node440 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node440 PairSemantics.raw7982
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node440 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node440 (EqualityPatterns.family3.label 1) = PairSemantics.raw5155 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node440 PairSemantics.raw5155
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5155 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node440 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node440 (EqualityPatterns.family3.label 2) = PairSemantics.raw8975 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node440 PairSemantics.raw8975
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8975 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node440 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value45 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node440 (EqualityPatterns.family3.label 3) = PairSemantics.raw5104 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node440 PairSemantics.raw5104
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5104 hH).trans (PairSemantics.sound45 hH)
  have hm4 : familyPairMoment B (groupedColumns node440 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2095 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node440 (EqualityPatterns.family3.label 4) = PairSemantics.raw3881 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node440 PairSemantics.raw3881
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3881 hH).trans (PairSemantics.sound2095 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue440, PairSemantics.value0, PairSemantics.value45, PairSemantics.value46, PairSemantics.value2095, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
