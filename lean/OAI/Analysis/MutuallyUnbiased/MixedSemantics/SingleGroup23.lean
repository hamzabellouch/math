import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleRules
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical160
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical161
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical241
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical242
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound5

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue376 : Sparse (Fin 909) := [(0, (17 / 864)), (1, (55 / 216)), (2, (-5 / 288)), (3, (-25 / 54)), (4, (-5 / 27)), (26, (-5 / 27))]

theorem singlePair376 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node376 node376Labels = Sparse.eval singlePairValue376 (familyPairVector B) := by
  have hp := single_label_three B hB node376
  have hl : node376Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node376 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node376 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node376 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node376 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node376 (EqualityPatterns.family3.label 1) = PairSemantics.raw5135 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node376 PairSemantics.raw5135; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5135 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node376 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node376 (EqualityPatterns.family3.label 2) = PairSemantics.raw7733 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node376 PairSemantics.raw7733; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7733 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node376 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node376 (EqualityPatterns.family3.label 3) = PairSemantics.raw883 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node376 PairSemantics.raw883; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical883 hH).trans (PairSemantics.sound26 hH)
  have hm4 : familyPairMoment B (groupedColumns node376 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2469 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node376 (EqualityPatterns.family3.label 4) = PairSemantics.raw731 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node376 PairSemantics.raw731; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical731 hH).trans (PairSemantics.sound2469 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue376, PairSemantics.value0, PairSemantics.value26, PairSemantics.value65, PairSemantics.value232, PairSemantics.value2469, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue377 : Sparse (Fin 909) := [(0, (17 / 432)), (1, (-35 / 864)), (2, (-5 / 96)), (3, (5 / 54)), (26, (5 / 54))]

theorem singlePair377 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node377 node377Labels = Sparse.eval singlePairValue377 (familyPairVector B) := by
  have hp := single_label_three B hB node377
  have hl : node377Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node377 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node377 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node377 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node377 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node377 (EqualityPatterns.family3.label 1) = PairSemantics.raw5136 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node377 PairSemantics.raw5136; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5136 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node377 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node377 (EqualityPatterns.family3.label 2) = PairSemantics.raw7732 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node377 PairSemantics.raw7732; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7732 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node377 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node377 (EqualityPatterns.family3.label 3) = PairSemantics.raw884 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node377 PairSemantics.raw884; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical884 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node377 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value869 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node377 (EqualityPatterns.family3.label 4) = PairSemantics.raw732 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node377 PairSemantics.raw732; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical732 hH).trans (PairSemantics.sound869 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue377, PairSemantics.value0, PairSemantics.value10, PairSemantics.value46, PairSemantics.value65, PairSemantics.value869, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue378 : Sparse (Fin 909) := [(0, (29 / 864)), (1, (-5 / 216)), (2, (-35 / 864)), (3, (5 / 54))]

theorem singlePair378 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node378 node378Labels = Sparse.eval singlePairValue378 (familyPairVector B) := by
  have hp := single_label_three B hB node378
  have hl : node378Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node378 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node378 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node378 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node378 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node378 (EqualityPatterns.family3.label 1) = PairSemantics.raw5139 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node378 PairSemantics.raw5139; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5139 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node378 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node378 (EqualityPatterns.family3.label 2) = PairSemantics.raw7730 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node378 PairSemantics.raw7730; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7730 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node378 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node378 (EqualityPatterns.family3.label 3) = PairSemantics.raw884 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node378 PairSemantics.raw884; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical884 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node378 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value868 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node378 (EqualityPatterns.family3.label 4) = PairSemantics.raw733 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node378 PairSemantics.raw733; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical733 hH).trans (PairSemantics.sound868 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue378, PairSemantics.value0, PairSemantics.value10, PairSemantics.value65, PairSemantics.value232, PairSemantics.value868, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue379 : Sparse (Fin 909) := [(0, (1 / 24)), (2, (5 / 24))]

theorem singlePair379 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node379 node379Labels = Sparse.eval singlePairValue379 (familyPairVector B) := by
  have hp := single_label_three B hB node379
  have hl : node379Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node379 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node379 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node379 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node379 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node379 (EqualityPatterns.family3.label 1) = PairSemantics.raw5141 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node379 PairSemantics.raw5141; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5141 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node379 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node379 (EqualityPatterns.family3.label 2) = PairSemantics.raw7731 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node379 PairSemantics.raw7731; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7731 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node379 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node379 (EqualityPatterns.family3.label 3) = PairSemantics.raw887 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node379 PairSemantics.raw887; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical887 hH).trans (PairSemantics.sound3 hH)
  have hm4 : familyPairMoment B (groupedColumns node379 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value259 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node379 (EqualityPatterns.family3.label 4) = PairSemantics.raw735 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node379 PairSemantics.raw735; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical735 hH).trans (PairSemantics.sound259 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue379, PairSemantics.value0, PairSemantics.value3, PairSemantics.value46, PairSemantics.value65, PairSemantics.value259, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue380 : Sparse (Fin 909) := [(0, (31 / 864)), (1, (5 / 48)), (2, (5 / 432)), (3, (-65 / 54)), (4, (-10 / 27)), (5, (-5 / 108)), (6, (5 / 864)), (12, (-10 / 27)), (13, (-5 / 9)), (26, (-5 / 9)), (27, (5 / 72)), (33, (5 / 9)), (34, (-10 / 27)), (35, (-5 / 54)), (54, (5 / 18)), (65, (5 / 18)), (67, (-5 / 54))]

theorem singlePair380 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node380 node380Labels = Sparse.eval singlePairValue380 (familyPairVector B) := by
  have hp := single_label_three B hB node380
  have hl : node380Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node380 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node380 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node380 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node380 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value717 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node380 (EqualityPatterns.family3.label 1) = PairSemantics.raw5144 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node380 PairSemantics.raw5144; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5144 hH).trans (PairSemantics.sound717 hH)
  have hm2 : familyPairMoment B (groupedColumns node380 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node380 (EqualityPatterns.family3.label 2) = PairSemantics.raw7724 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node380 PairSemantics.raw7724; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7724 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node380 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node380 (EqualityPatterns.family3.label 3) = PairSemantics.raw883 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node380 PairSemantics.raw883; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical883 hH).trans (PairSemantics.sound26 hH)
  have hm4 : familyPairMoment B (groupedColumns node380 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1431 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node380 (EqualityPatterns.family3.label 4) = PairSemantics.raw736 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node380 PairSemantics.raw736; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical736 hH).trans (PairSemantics.sound1431 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue380, PairSemantics.value0, PairSemantics.value26, PairSemantics.value46, PairSemantics.value717, PairSemantics.value1431, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue381 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-55 / 864)), (2, (-35 / 864)), (3, (5 / 54)), (5, (5 / 216)), (26, (5 / 54)), (27, (-5 / 72)), (33, (-5 / 18)), (54, (-5 / 18)), (65, (-5 / 18))]

theorem singlePair381 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node381 node381Labels = Sparse.eval singlePairValue381 (familyPairVector B) := by
  have hp := single_label_three B hB node381
  have hl : node381Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node381 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node381 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node381 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node381 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value231 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node381 (EqualityPatterns.family3.label 1) = PairSemantics.raw5145 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node381 PairSemantics.raw5145; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5145 hH).trans (PairSemantics.sound231 hH)
  have hm2 : familyPairMoment B (groupedColumns node381 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node381 (EqualityPatterns.family3.label 2) = PairSemantics.raw7723 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node381 PairSemantics.raw7723; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7723 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node381 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node381 (EqualityPatterns.family3.label 3) = PairSemantics.raw884 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node381 PairSemantics.raw884; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical884 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node381 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value367 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node381 (EqualityPatterns.family3.label 4) = PairSemantics.raw737 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node381 PairSemantics.raw737; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical737 hH).trans (PairSemantics.sound367 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue381, PairSemantics.value0, PairSemantics.value10, PairSemantics.value46, PairSemantics.value231, PairSemantics.value367, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue382 : Sparse (Fin 909) := [(0, (7 / 432)), (1, (155 / 864)), (2, (-35 / 864)), (3, (-10 / 9)), (4, (-5 / 27)), (12, (-5 / 9)), (13, (-35 / 54)), (26, (-5 / 27)), (33, (5 / 9)), (34, (-5 / 27))]

theorem singlePair382 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node382 node382Labels = Sparse.eval singlePairValue382 (familyPairVector B) := by
  have hp := single_label_three B hB node382
  have hl : node382Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node382 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node382 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node382 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node382 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node382 (EqualityPatterns.family3.label 1) = PairSemantics.raw5146 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node382 PairSemantics.raw5146; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5146 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node382 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node382 (EqualityPatterns.family3.label 2) = PairSemantics.raw7721 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node382 PairSemantics.raw7721; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7721 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node382 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node382 (EqualityPatterns.family3.label 3) = PairSemantics.raw883 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node382 PairSemantics.raw883; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical883 hH).trans (PairSemantics.sound26 hH)
  have hm4 : familyPairMoment B (groupedColumns node382 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1432 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node382 (EqualityPatterns.family3.label 4) = PairSemantics.raw738 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node382 PairSemantics.raw738; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical738 hH).trans (PairSemantics.sound1432 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue382, PairSemantics.value0, PairSemantics.value26, PairSemantics.value46, PairSemantics.value232, PairSemantics.value1432, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue383 : Sparse (Fin 909) := [(0, (1 / 72)), (1, (-5 / 864)), (2, (-5 / 864)), (3, (5 / 27)), (12, (5 / 54)), (13, (5 / 27)), (33, (-5 / 18))]

theorem singlePair383 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node383 node383Labels = Sparse.eval singlePairValue383 (familyPairVector B) := by
  have hp := single_label_three B hB node383
  have hl : node383Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node383 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node383 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node383 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node383 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node383 (EqualityPatterns.family3.label 1) = PairSemantics.raw5147 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node383 PairSemantics.raw5147; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5147 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node383 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node383 (EqualityPatterns.family3.label 2) = PairSemantics.raw7720 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node383 PairSemantics.raw7720; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7720 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node383 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node383 (EqualityPatterns.family3.label 3) = PairSemantics.raw884 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node383 PairSemantics.raw884; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical884 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node383 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value368 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node383 (EqualityPatterns.family3.label 4) = PairSemantics.raw739 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node383 PairSemantics.raw739; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical739 hH).trans (PairSemantics.sound368 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue383, PairSemantics.value0, PairSemantics.value10, PairSemantics.value46, PairSemantics.value232, PairSemantics.value368, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue384 : Sparse (Fin 909) := [(0, (19 / 864)), (1, (-25 / 288)), (3, (5 / 18)), (12, (5 / 27)), (13, (10 / 27)), (34, (5 / 54))]

theorem singlePair384 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node384 node384Labels = Sparse.eval singlePairValue384 (familyPairVector B) := by
  have hp := single_label_three B hB node384
  have hl : node384Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node384 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node384 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node384 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node384 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node384 (EqualityPatterns.family3.label 1) = PairSemantics.raw5150 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node384 PairSemantics.raw5150; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5150 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node384 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node384 (EqualityPatterns.family3.label 2) = PairSemantics.raw7719 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node384 PairSemantics.raw7719; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7719 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node384 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node384 (EqualityPatterns.family3.label 3) = PairSemantics.raw884 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node384 PairSemantics.raw884; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical884 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node384 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value369 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node384 (EqualityPatterns.family3.label 4) = PairSemantics.raw740 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node384 PairSemantics.raw740; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical740 hH).trans (PairSemantics.sound369 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue384, PairSemantics.value0, PairSemantics.value10, PairSemantics.value46, PairSemantics.value369, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue385 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 72)), (2, (5 / 36)), (13, (-10 / 27))]

theorem singlePair385 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node385 node385Labels = Sparse.eval singlePairValue385 (familyPairVector B) := by
  have hp := single_label_three B hB node385
  have hl : node385Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node385 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node385 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node385 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node385 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node385 (EqualityPatterns.family3.label 1) = PairSemantics.raw5149 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node385 PairSemantics.raw5149; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5149 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node385 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node385 (EqualityPatterns.family3.label 2) = PairSemantics.raw7722 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node385 PairSemantics.raw7722; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7722 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node385 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node385 (EqualityPatterns.family3.label 3) = PairSemantics.raw887 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node385 PairSemantics.raw887; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical887 hH).trans (PairSemantics.sound3 hH)
  have hm4 : familyPairMoment B (groupedColumns node385 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value105 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node385 (EqualityPatterns.family3.label 4) = PairSemantics.raw741 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node385 PairSemantics.raw741; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical741 hH).trans (PairSemantics.sound105 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue385, PairSemantics.value0, PairSemantics.value3, PairSemantics.value46, PairSemantics.value105, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue386 : Sparse (Fin 909) := [(0, (13 / 864)), (1, (5 / 288)), (2, (-5 / 216)), (3, (5 / 18)), (13, (5 / 54)), (26, (5 / 27)), (34, (5 / 27))]

theorem singlePair386 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node386 node386Labels = Sparse.eval singlePairValue386 (familyPairVector B) := by
  have hp := single_label_three B hB node386
  have hl : node386Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node386 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node386 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node386 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node386 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node386 (EqualityPatterns.family3.label 1) = PairSemantics.raw5125 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node386 PairSemantics.raw5125; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5125 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node386 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node386 (EqualityPatterns.family3.label 2) = PairSemantics.raw7744 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node386 PairSemantics.raw7744; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7744 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node386 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node386 (EqualityPatterns.family3.label 3) = PairSemantics.raw893 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node386 PairSemantics.raw893; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical893 hH).trans (PairSemantics.sound26 hH)
  have hm4 : familyPairMoment B (groupedColumns node386 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value372 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node386 (EqualityPatterns.family3.label 4) = PairSemantics.raw746 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node386 PairSemantics.raw746; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical746 hH).trans (PairSemantics.sound372 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue386, PairSemantics.value0, PairSemantics.value10, PairSemantics.value26, PairSemantics.value232, PairSemantics.value372, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue387 : Sparse (Fin 909) := [(0, (17 / 432)), (1, (-5 / 432)), (2, (5 / 108)), (3, (5 / 27)), (4, (5 / 54)), (26, (5 / 54))]

theorem singlePair387 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node387 node387Labels = Sparse.eval singlePairValue387 (familyPairVector B) := by
  have hp := single_label_three B hB node387
  have hl : node387Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node387 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node387 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node387 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node387 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node387 (EqualityPatterns.family3.label 1) = PairSemantics.raw5128 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node387 PairSemantics.raw5128; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5128 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node387 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node387 (EqualityPatterns.family3.label 2) = PairSemantics.raw7742 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node387 PairSemantics.raw7742; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7742 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node387 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node387 (EqualityPatterns.family3.label 3) = PairSemantics.raw893 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node387 PairSemantics.raw893; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical893 hH).trans (PairSemantics.sound26 hH)
  have hm4 : familyPairMoment B (groupedColumns node387 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value872 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node387 (EqualityPatterns.family3.label 4) = PairSemantics.raw747 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node387 PairSemantics.raw747; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical747 hH).trans (PairSemantics.sound872 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue387, PairSemantics.value0, PairSemantics.value26, PairSemantics.value46, PairSemantics.value65, PairSemantics.value872, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue388 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-5 / 144)), (2, (-5 / 108)), (26, (-5 / 27))]

theorem singlePair388 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node388 node388Labels = Sparse.eval singlePairValue388 (familyPairVector B) := by
  have hp := single_label_three B hB node388
  have hl : node388Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node388 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node388 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node388 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node388 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node388 (EqualityPatterns.family3.label 1) = PairSemantics.raw5132 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node388 PairSemantics.raw5132; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5132 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node388 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node388 (EqualityPatterns.family3.label 2) = PairSemantics.raw7738 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node388 PairSemantics.raw7738; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7738 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node388 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node388 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node388 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node388 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value263 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node388 (EqualityPatterns.family3.label 4) = PairSemantics.raw748 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node388 PairSemantics.raw748; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical748 hH).trans (PairSemantics.sound263 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue388, PairSemantics.value0, PairSemantics.value10, PairSemantics.value65, PairSemantics.value263, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue389 : Sparse (Fin 909) := []

theorem singlePair389 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node389 node389Labels = Sparse.eval singlePairValue389 (familyPairVector B) := by
  have hp := single_label_three B hB node389
  have hl : node389Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node389 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node389 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node389 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node389 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node389 (EqualityPatterns.family3.label 1) = PairSemantics.raw5141 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node389 PairSemantics.raw5141; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5141 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node389 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value5 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node389 (EqualityPatterns.family3.label 2) = PairSemantics.raw7736 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node389 PairSemantics.raw7736; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7736 hH).trans (PairSemantics.sound5 hH)
  have hm3 : familyPairMoment B (groupedColumns node389 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node389 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node389 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node389 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value272 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node389 (EqualityPatterns.family3.label 4) = PairSemantics.raw749 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node389 PairSemantics.raw749; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical749 hH).trans (PairSemantics.sound272 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue389, PairSemantics.value0, PairSemantics.value5, PairSemantics.value10, PairSemantics.value46, PairSemantics.value272, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue390 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-5 / 54)), (2, (-25 / 432)), (3, (-5 / 27))]

theorem singlePair390 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node390 node390Labels = Sparse.eval singlePairValue390 (familyPairVector B) := by
  have hp := single_label_three B hB node390
  have hl : node390Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node390 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node390 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node390 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node390 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node390 (EqualityPatterns.family3.label 1) = PairSemantics.raw5149 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node390 PairSemantics.raw5149; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5149 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node390 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node390 (EqualityPatterns.family3.label 2) = PairSemantics.raw7731 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node390 PairSemantics.raw7731; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7731 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node390 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node390 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node390 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node390 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value261 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node390 (EqualityPatterns.family3.label 4) = PairSemantics.raw750 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node390 PairSemantics.raw750; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical750 hH).trans (PairSemantics.sound261 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue390, PairSemantics.value0, PairSemantics.value10, PairSemantics.value46, PairSemantics.value65, PairSemantics.value261, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue391 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 54)), (2, (-25 / 432)), (3, (-5 / 27)), (13, (-5 / 27)), (34, (-5 / 27))]

theorem singlePair391 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node391 node391Labels = Sparse.eval singlePairValue391 (familyPairVector B) := by
  have hp := single_label_three B hB node391
  have hl : node391Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node391 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node391 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node391 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node391 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node391 (EqualityPatterns.family3.label 1) = PairSemantics.raw5152 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node391 PairSemantics.raw5152; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5152 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node391 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node391 (EqualityPatterns.family3.label 2) = PairSemantics.raw7722 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node391 PairSemantics.raw7722; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7722 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node391 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node391 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node391 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node391 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value107 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node391 (EqualityPatterns.family3.label 4) = PairSemantics.raw751 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node391 PairSemantics.raw751; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical751 hH).trans (PairSemantics.sound107 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue391, PairSemantics.value0, PairSemantics.value10, PairSemantics.value46, PairSemantics.value107, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
