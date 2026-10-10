import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleRules
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical120
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical159
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical160
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical161
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical162
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical163
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical238
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical240
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical241
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical242
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical281
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound8

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue408 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 72)), (2, (-5 / 72)), (27, (5 / 36)), (65, (5 / 9))]

theorem singlePair408 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node408 node408Labels = Sparse.eval singlePairValue408 (familyPairVector B) := by
  have hp := single_label_three B hB node408
  have hl : node408Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node408 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node408 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node408 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node408 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value45 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node408 (EqualityPatterns.family3.label 1) = PairSemantics.raw5211 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node408 PairSemantics.raw5211; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5211 hH).trans (PairSemantics.sound45 hH)
  have hm2 : familyPairMoment B (groupedColumns node408 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node408 (EqualityPatterns.family3.label 2) = PairSemantics.raw7643 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node408 PairSemantics.raw7643; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7643 hH).trans (PairSemantics.sound10 hH)
  have hm3 : familyPairMoment B (groupedColumns node408 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node408 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node408 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node408 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value110 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node408 (EqualityPatterns.family3.label 4) = PairSemantics.raw786 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node408 PairSemantics.raw786; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical786 hH).trans (PairSemantics.sound110 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue408, PairSemantics.value0, PairSemantics.value10, PairSemantics.value45, PairSemantics.value110, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue409 : Sparse (Fin 909) := [(0, (17 / 864)), (1, (-25 / 864)), (2, (5 / 108)), (3, (5 / 18)), (4, (5 / 54)), (12, (5 / 54)), (13, (5 / 54)), (26, (5 / 54)), (33, (-5 / 18)), (34, (5 / 54))]

theorem singlePair409 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node409 node409Labels = Sparse.eval singlePairValue409 (familyPairVector B) := by
  have hp := single_label_three B hB node409
  have hl : node409Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node409 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node409 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node409 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node409 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node409 (EqualityPatterns.family3.label 1) = PairSemantics.raw5212 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node409 PairSemantics.raw5212; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5212 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node409 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node409 (EqualityPatterns.family3.label 2) = PairSemantics.raw7640 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node409 PairSemantics.raw7640; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7640 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node409 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node409 (EqualityPatterns.family3.label 3) = PairSemantics.raw893 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node409 PairSemantics.raw893; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical893 hH).trans (PairSemantics.sound26 hH)
  have hm4 : familyPairMoment B (groupedColumns node409 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value377 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node409 (EqualityPatterns.family3.label 4) = PairSemantics.raw787 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node409 PairSemantics.raw787; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical787 hH).trans (PairSemantics.sound377 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue409, PairSemantics.value0, PairSemantics.value26, PairSemantics.value46, PairSemantics.value377, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue410 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-35 / 432)), (2, (-5 / 432)), (33, (5 / 9))]

theorem singlePair410 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node410 node410Labels = Sparse.eval singlePairValue410 (familyPairVector B) := by
  have hp := single_label_three B hB node410
  have hl : node410Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node410 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node410 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node410 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node410 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node410 (EqualityPatterns.family3.label 1) = PairSemantics.raw5213 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node410 PairSemantics.raw5213; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5213 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node410 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node410 (EqualityPatterns.family3.label 2) = PairSemantics.raw7639 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node410 PairSemantics.raw7639; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7639 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node410 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node410 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node410 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node410 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value111 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node410 (EqualityPatterns.family3.label 4) = PairSemantics.raw789 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node410 PairSemantics.raw789; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical789 hH).trans (PairSemantics.sound111 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue410, PairSemantics.value0, PairSemantics.value10, PairSemantics.value46, PairSemantics.value111, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue411 : Sparse (Fin 909) := [(0, (11 / 864)), (1, (5 / 36)), (2, (5 / 288)), (3, (5 / 18)), (12, (5 / 18)), (13, (5 / 27))]

theorem singlePair411 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node411 node411Labels = Sparse.eval singlePairValue411 (familyPairVector B) := by
  have hp := single_label_three B hB node411
  have hl : node411Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node411 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node411 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node411 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node411 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node411 (EqualityPatterns.family3.label 1) = PairSemantics.raw5216 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node411 PairSemantics.raw5216; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5216 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node411 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node411 (EqualityPatterns.family3.label 2) = PairSemantics.raw7634 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node411 PairSemantics.raw7634; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7634 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node411 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node411 (EqualityPatterns.family3.label 3) = PairSemantics.raw893 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node411 PairSemantics.raw893; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical893 hH).trans (PairSemantics.sound26 hH)
  have hm4 : familyPairMoment B (groupedColumns node411 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value566 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node411 (EqualityPatterns.family3.label 4) = PairSemantics.raw791 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node411 PairSemantics.raw791; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical791 hH).trans (PairSemantics.sound566 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue411, PairSemantics.value0, PairSemantics.value4, PairSemantics.value26, PairSemantics.value232, PairSemantics.value566, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue412 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (35 / 432)), (2, (-5 / 216)), (3, (-5 / 27)), (12, (-5 / 27)), (13, (-5 / 27))]

theorem singlePair412 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node412 node412Labels = Sparse.eval singlePairValue412 (familyPairVector B) := by
  have hp := single_label_three B hB node412
  have hl : node412Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node412 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node412 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node412 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node412 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node412 (EqualityPatterns.family3.label 1) = PairSemantics.raw5215 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node412 PairSemantics.raw5215; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5215 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node412 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node412 (EqualityPatterns.family3.label 2) = PairSemantics.raw7636 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node412 PairSemantics.raw7636; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7636 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node412 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node412 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node412 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node412 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value177 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node412 (EqualityPatterns.family3.label 4) = PairSemantics.raw792 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node412 PairSemantics.raw792; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical792 hH).trans (PairSemantics.sound177 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue412, PairSemantics.value0, PairSemantics.value4, PairSemantics.value10, PairSemantics.value46, PairSemantics.value177, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue413 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 72)), (2, (5 / 108)), (27, (5 / 36)), (66, (5 / 9))]

theorem singlePair413 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node413 node413Labels = Sparse.eval singlePairValue413 (familyPairVector B) := by
  have hp := single_label_three B hB node413
  have hl : node413Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node413 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node413 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node413 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node413 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value45 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node413 (EqualityPatterns.family3.label 1) = PairSemantics.raw5116 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node413 PairSemantics.raw5116; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5116 hH).trans (PairSemantics.sound45 hH)
  have hm2 : familyPairMoment B (groupedColumns node413 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node413 (EqualityPatterns.family3.label 2) = PairSemantics.raw7761 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node413 PairSemantics.raw7761; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7761 hH).trans (PairSemantics.sound26 hH)
  have hm3 : familyPairMoment B (groupedColumns node413 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node413 (EqualityPatterns.family3.label 3) = PairSemantics.raw914 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node413 PairSemantics.raw914; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical914 hH).trans (PairSemantics.sound26 hH)
  have hm4 : familyPairMoment B (groupedColumns node413 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value114 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node413 (EqualityPatterns.family3.label 4) = PairSemantics.raw800 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node413 PairSemantics.raw800; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical800 hH).trans (PairSemantics.sound114 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue413, PairSemantics.value0, PairSemantics.value26, PairSemantics.value45, PairSemantics.value114, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue414 : Sparse (Fin 909) := [(0, (13 / 432)), (1, (-5 / 216)), (2, (5 / 144)), (3, (-5 / 27)), (4, (-5 / 27)), (26, (-5 / 27))]

theorem singlePair414 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node414 node414Labels = Sparse.eval singlePairValue414 (familyPairVector B) := by
  have hp := single_label_three B hB node414
  have hl : node414Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node414 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node414 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node414 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node414 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node414 (EqualityPatterns.family3.label 1) = PairSemantics.raw5141 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node414 PairSemantics.raw5141; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5141 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node414 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node414 (EqualityPatterns.family3.label 2) = PairSemantics.raw7757 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node414 PairSemantics.raw7757; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7757 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node414 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node414 (EqualityPatterns.family3.label 3) = PairSemantics.raw914 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node414 PairSemantics.raw914; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical914 hH).trans (PairSemantics.sound26 hH)
  have hm4 : familyPairMoment B (groupedColumns node414 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value229 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node414 (EqualityPatterns.family3.label 4) = PairSemantics.raw805 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node414 PairSemantics.raw805; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical805 hH).trans (PairSemantics.sound229 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue414, PairSemantics.value0, PairSemantics.value11, PairSemantics.value26, PairSemantics.value46, PairSemantics.value229, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue415 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 48)), (2, (-5 / 72)), (26, (5 / 9))]

theorem singlePair415 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node415 node415Labels = Sparse.eval singlePairValue415 (familyPairVector B) := by
  have hp := single_label_three B hB node415
  have hl : node415Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node415 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node415 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node415 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node415 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node415 (EqualityPatterns.family3.label 1) = PairSemantics.raw5151 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node415 PairSemantics.raw5151; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5151 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node415 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node415 (EqualityPatterns.family3.label 2) = PairSemantics.raw7749 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node415 PairSemantics.raw7749; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7749 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node415 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node415 (EqualityPatterns.family3.label 3) = PairSemantics.raw917 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node415 PairSemantics.raw917; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical917 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node415 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value43 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node415 (EqualityPatterns.family3.label 4) = PairSemantics.raw806 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node415 PairSemantics.raw806; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical806 hH).trans (PairSemantics.sound43 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue415, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value43, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue416 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (55 / 216)), (2, (5 / 432)), (3, (-5 / 27))]

theorem singlePair416 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node416 node416Labels = Sparse.eval singlePairValue416 (familyPairVector B) := by
  have hp := single_label_three B hB node416
  have hl : node416Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node416 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node416 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node416 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node416 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node416 (EqualityPatterns.family3.label 1) = PairSemantics.raw5169 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node416 PairSemantics.raw5169; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5169 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node416 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node416 (EqualityPatterns.family3.label 2) = PairSemantics.raw7738 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node416 PairSemantics.raw7738; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7738 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node416 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node416 (EqualityPatterns.family3.label 3) = PairSemantics.raw914 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node416 PairSemantics.raw914; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical914 hH).trans (PairSemantics.sound26 hH)
  have hm4 : familyPairMoment B (groupedColumns node416 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value176 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node416 (EqualityPatterns.family3.label 4) = PairSemantics.raw808 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node416 PairSemantics.raw808; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical808 hH).trans (PairSemantics.sound176 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue416, PairSemantics.value0, PairSemantics.value4, PairSemantics.value26, PairSemantics.value65, PairSemantics.value176, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue417 : Sparse (Fin 909) := []

theorem singlePair417 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node417 node417Labels = Sparse.eval singlePairValue417 (familyPairVector B) := by
  have hp := single_label_three B hB node417
  have hl : node417Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node417 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node417 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node417 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node417 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node417 (EqualityPatterns.family3.label 1) = PairSemantics.raw5177 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node417 PairSemantics.raw5177; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5177 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node417 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value5 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node417 (EqualityPatterns.family3.label 2) = PairSemantics.raw7736 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node417 PairSemantics.raw7736; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7736 hH).trans (PairSemantics.sound5 hH)
  have hm3 : familyPairMoment B (groupedColumns node417 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node417 (EqualityPatterns.family3.label 3) = PairSemantics.raw914 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node417 PairSemantics.raw914; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical914 hH).trans (PairSemantics.sound26 hH)
  have hm4 : familyPairMoment B (groupedColumns node417 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value271 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node417 (EqualityPatterns.family3.label 4) = PairSemantics.raw809 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node417 PairSemantics.raw809; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical809 hH).trans (PairSemantics.sound271 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue417, PairSemantics.value0, PairSemantics.value5, PairSemantics.value11, PairSemantics.value26, PairSemantics.value271, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue418 : Sparse (Fin 909) := []

theorem singlePair418 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node418 node418Labels = Sparse.eval singlePairValue418 (familyPairVector B) := by
  have hp := single_label_three B hB node418
  have hl : node418Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node418 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node418 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node418 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node418 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node418 (EqualityPatterns.family3.label 1) = PairSemantics.raw5183 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node418 PairSemantics.raw5183; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5183 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node418 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value5 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node418 (EqualityPatterns.family3.label 2) = PairSemantics.raw7735 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node418 PairSemantics.raw7735; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7735 hH).trans (PairSemantics.sound5 hH)
  have hm3 : familyPairMoment B (groupedColumns node418 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node418 (EqualityPatterns.family3.label 3) = PairSemantics.raw917 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node418 PairSemantics.raw917; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical917 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node418 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value57 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node418 (EqualityPatterns.family3.label 4) = PairSemantics.raw810 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node418 PairSemantics.raw810; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical810 hH).trans (PairSemantics.sound57 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue418, PairSemantics.value0, PairSemantics.value4, PairSemantics.value5, PairSemantics.value10, PairSemantics.value57, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue419 : Sparse (Fin 909) := []

theorem singlePair419 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node419 node419Labels = Sparse.eval singlePairValue419 (familyPairVector B) := by
  have hp := single_label_three B hB node419
  have hl : node419Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node419 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node419 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node419 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node419 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node419 (EqualityPatterns.family3.label 1) = PairSemantics.raw5199 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node419 PairSemantics.raw5199; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5199 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node419 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value5 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node419 (EqualityPatterns.family3.label 2) = PairSemantics.raw7709 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node419 PairSemantics.raw7709; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7709 hH).trans (PairSemantics.sound5 hH)
  have hm3 : familyPairMoment B (groupedColumns node419 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node419 (EqualityPatterns.family3.label 3) = PairSemantics.raw917 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node419 PairSemantics.raw917; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical917 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node419 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value56 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node419 (EqualityPatterns.family3.label 4) = PairSemantics.raw811 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node419 PairSemantics.raw811; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical811 hH).trans (PairSemantics.sound56 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue419, PairSemantics.value0, PairSemantics.value5, PairSemantics.value10, PairSemantics.value11, PairSemantics.value56, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue421 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 48)), (2, (-5 / 48)), (34, (5 / 9))]

theorem singlePair421 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node421 node421Labels = Sparse.eval singlePairValue421 (familyPairVector B) := by
  have hp := single_label_three B hB node421
  have hl : node421Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node421 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node421 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node421 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node421 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node421 (EqualityPatterns.family3.label 1) = PairSemantics.raw5218 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node421 PairSemantics.raw5218; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5218 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node421 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node421 (EqualityPatterns.family3.label 2) = PairSemantics.raw7642 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node421 PairSemantics.raw7642; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7642 hH).trans (PairSemantics.sound10 hH)
  have hm3 : familyPairMoment B (groupedColumns node421 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node421 (EqualityPatterns.family3.label 3) = PairSemantics.raw917 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node421 PairSemantics.raw917; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical917 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node421 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value21 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node421 (EqualityPatterns.family3.label 4) = PairSemantics.raw814 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node421 PairSemantics.raw814; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical814 hH).trans (PairSemantics.sound21 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue421, PairSemantics.value0, PairSemantics.value10, PairSemantics.value21, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue422 : Sparse (Fin 909) := []

theorem singlePair422 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node422 node422Labels = Sparse.eval singlePairValue422 (familyPairVector B) := by
  have hp := single_label_three B hB node422
  have hl : node422Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node422 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node422 (EqualityPatterns.family3.label 0) = PairSemantics.raw7978 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node422 PairSemantics.raw7978; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7978 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node422 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node422 (EqualityPatterns.family3.label 1) = PairSemantics.raw5210 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node422 PairSemantics.raw5210; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5210 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node422 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value5 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node422 (EqualityPatterns.family3.label 2) = PairSemantics.raw7718 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node422 PairSemantics.raw7718; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7718 hH).trans (PairSemantics.sound5 hH)
  have hm3 : familyPairMoment B (groupedColumns node422 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node422 (EqualityPatterns.family3.label 3) = PairSemantics.raw926 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node422 PairSemantics.raw926; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical926 hH).trans (PairSemantics.sound3 hH)
  have hm4 : familyPairMoment B (groupedColumns node422 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node422 (EqualityPatterns.family3.label 4) = PairSemantics.raw816 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node422 PairSemantics.raw816; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical816 hH).trans (PairSemantics.sound10 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue422, PairSemantics.value0, PairSemantics.value3, PairSemantics.value4, PairSemantics.value5, PairSemantics.value10, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue423 : Sparse (Fin 909) := [(0, (1 / 24)), (1, (5 / 432)), (2, (5 / 144)), (5, (-5 / 108)), (31, (5 / 18)), (51, (5 / 9)), (68, (5 / 18)), (124, (5 / 18)), (126, (5 / 9)), (236, (5 / 18))]

theorem singlePair423 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node423 node423Labels = Sparse.eval singlePairValue423 (familyPairVector B) := by
  have hp := single_label_three B hB node423
  have hl : node423Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node423 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node423 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node423 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node423 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node423 (EqualityPatterns.family3.label 1) = PairSemantics.raw5123 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node423 PairSemantics.raw5123; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5123 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node423 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node423 (EqualityPatterns.family3.label 2) = PairSemantics.raw9012 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node423 PairSemantics.raw9012; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9012 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node423 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value715 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node423 (EqualityPatterns.family3.label 3) = PairSemantics.raw5102 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node423 PairSemantics.raw5102; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5102 hH).trans (PairSemantics.sound715 hH)
  have hm4 : familyPairMoment B (groupedColumns node423 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2653 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node423 (EqualityPatterns.family3.label 4) = PairSemantics.raw3864 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node423 PairSemantics.raw3864; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3864 hH).trans (PairSemantics.sound2653 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue423, PairSemantics.value0, PairSemantics.value46, PairSemantics.value65, PairSemantics.value715, PairSemantics.value2653, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue424 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (5 / 432)), (2, (5 / 96)), (3, (-10 / 27)), (4, (-5 / 54)), (5, (-5 / 72)), (7, (-5 / 27)), (12, (-5 / 54)), (23, (5 / 9)), (24, (5 / 9)), (51, (5 / 18)), (55, (5 / 9)), (68, (5 / 18)), (124, (5 / 18)), (125, (5 / 18)), (126, (5 / 18)), (197, (5 / 18))]

theorem singlePair424 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node424 node424Labels = Sparse.eval singlePairValue424 (familyPairVector B) := by
  have hp := single_label_three B hB node424
  have hl : node424Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node424 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node424 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node424 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node424 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node424 (EqualityPatterns.family3.label 1) = PairSemantics.raw5126 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node424 PairSemantics.raw5126; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5126 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node424 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node424 (EqualityPatterns.family3.label 2) = PairSemantics.raw9009 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node424 PairSemantics.raw9009; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9009 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node424 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value715 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node424 (EqualityPatterns.family3.label 3) = PairSemantics.raw5102 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node424 PairSemantics.raw5102; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5102 hH).trans (PairSemantics.sound715 hH)
  have hm4 : familyPairMoment B (groupedColumns node424 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2115 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node424 (EqualityPatterns.family3.label 4) = PairSemantics.raw3865 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node424 PairSemantics.raw3865; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3865 hH).trans (PairSemantics.sound2115 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue424, PairSemantics.value0, PairSemantics.value11, PairSemantics.value46, PairSemantics.value715, PairSemantics.value2115, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
