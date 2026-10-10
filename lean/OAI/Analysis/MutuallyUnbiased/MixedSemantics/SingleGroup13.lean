import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleRules
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical281
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical282
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound8

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue216 : Sparse (Fin 909) := [(0, (41 / 864)), (1, (35 / 864)), (2, (-35 / 864)), (3, (-5 / 54)), (5, (5 / 36)), (6, (5 / 864)), (11, (-5 / 54)), (13, (-5 / 27)), (26, (-5 / 27)), (35, (-10 / 27)), (52, (-5 / 54))]

theorem singlePair216 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node216 node216Labels = Sparse.eval singlePairValue216 (familyPairVector B) := by
  have hp := single_label_three B hB node216
  have hl : node216Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node216 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node216 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node216 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node216 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node216 (EqualityPatterns.family3.label 1) = PairSemantics.raw875 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node216 PairSemantics.raw875; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical875 hH).trans (PairSemantics.sound118 hH)
  have hm2 : familyPairMoment B (groupedColumns node216 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node216 (EqualityPatterns.family3.label 2) = PairSemantics.raw9024 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node216 PairSemantics.raw9024; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9024 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node216 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node216 (EqualityPatterns.family3.label 3) = PairSemantics.raw857 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node216 PairSemantics.raw857; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical857 hH).trans (PairSemantics.sound24 hH)
  have hm4 : familyPairMoment B (groupedColumns node216 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2468 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node216 (EqualityPatterns.family3.label 4) = PairSemantics.raw421 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node216 PairSemantics.raw421; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical421 hH).trans (PairSemantics.sound2468 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue216, PairSemantics.value0, PairSemantics.value24, PairSemantics.value65, PairSemantics.value118, PairSemantics.value2468, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue217 : Sparse (Fin 909) := [(0, (7 / 144)), (1, (55 / 864)), (2, (5 / 96)), (3, (-5 / 54)), (5, (-5 / 216)), (6, (-5 / 216)), (7, (-5 / 54)), (8, (-5 / 54)), (13, (-5 / 54)), (35, (-5 / 54)), (52, (-5 / 54)), (54, (5 / 18)), (56, (5 / 18)), (228, (5 / 18))]

theorem singlePair217 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node217 node217Labels = Sparse.eval singlePairValue217 (familyPairVector B) := by
  have hp := single_label_three B hB node217
  have hl : node217Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node217 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node217 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node217 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node217 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node217 (EqualityPatterns.family3.label 1) = PairSemantics.raw875 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node217 PairSemantics.raw875; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical875 hH).trans (PairSemantics.sound118 hH)
  have hm2 : familyPairMoment B (groupedColumns node217 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node217 (EqualityPatterns.family3.label 2) = PairSemantics.raw9026 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node217 PairSemantics.raw9026; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9026 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node217 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node217 (EqualityPatterns.family3.label 3) = PairSemantics.raw858 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node217 PairSemantics.raw858; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical858 hH).trans (PairSemantics.sound25 hH)
  have hm4 : familyPairMoment B (groupedColumns node217 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2664 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node217 (EqualityPatterns.family3.label 4) = PairSemantics.raw422 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node217 PairSemantics.raw422; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical422 hH).trans (PairSemantics.sound2664 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue217, PairSemantics.value0, PairSemantics.value25, PairSemantics.value65, PairSemantics.value118, PairSemantics.value2664, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue218 : Sparse (Fin 909) := [(0, (11 / 432)), (2, (-5 / 432)), (3, (-10 / 27)), (5, (5 / 108)), (12, (-5 / 54)), (13, (-40 / 27)), (32, (-10 / 27)), (35, (-10 / 27)), (52, (-10 / 27)), (60, (-10 / 27)), (62, (5 / 9)), (128, (-5 / 54))]

theorem singlePair218 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node218 node218Labels = Sparse.eval singlePairValue218 (familyPairVector B) := by
  have hp := single_label_three B hB node218
  have hl : node218Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node218 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node218 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node218 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node218 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node218 (EqualityPatterns.family3.label 1) = PairSemantics.raw894 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node218 PairSemantics.raw894; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical894 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node218 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node218 (EqualityPatterns.family3.label 2) = PairSemantics.raw9001 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node218 PairSemantics.raw9001; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9001 hH).trans (PairSemantics.sound26 hH)
  have hm3 : familyPairMoment B (groupedColumns node218 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node218 (EqualityPatterns.family3.label 3) = PairSemantics.raw857 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node218 PairSemantics.raw857; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical857 hH).trans (PairSemantics.sound24 hH)
  have hm4 : familyPairMoment B (groupedColumns node218 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1407 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node218 (EqualityPatterns.family3.label 4) = PairSemantics.raw423 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node218 PairSemantics.raw423; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical423 hH).trans (PairSemantics.sound1407 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue218, PairSemantics.value0, PairSemantics.value24, PairSemantics.value26, PairSemantics.value1407, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue219 : Sparse (Fin 909) := [(0, (5 / 144)), (2, (-5 / 216)), (6, (5 / 144)), (11, (5 / 54)), (26, (5 / 54)), (35, (5 / 27)), (226, (-5 / 18))]

theorem singlePair219 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node219 node219Labels = Sparse.eval singlePairValue219 (familyPairVector B) := by
  have hp := single_label_three B hB node219
  have hl : node219Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node219 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node219 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node219 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node219 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node219 (EqualityPatterns.family3.label 1) = PairSemantics.raw888 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node219 PairSemantics.raw888; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical888 hH).trans (PairSemantics.sound24 hH)
  have hm2 : familyPairMoment B (groupedColumns node219 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node219 (EqualityPatterns.family3.label 2) = PairSemantics.raw9015 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node219 PairSemantics.raw9015; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9015 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node219 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node219 (EqualityPatterns.family3.label 3) = PairSemantics.raw860 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node219 PairSemantics.raw860; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical860 hH).trans (PairSemantics.sound24 hH)
  have hm4 : familyPairMoment B (groupedColumns node219 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value700 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node219 (EqualityPatterns.family3.label 4) = PairSemantics.raw424 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node219 PairSemantics.raw424; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical424 hH).trans (PairSemantics.sound700 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue219, PairSemantics.value0, PairSemantics.value11, PairSemantics.value24, PairSemantics.value700, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue220 : Sparse (Fin 909) := [(0, (7 / 144)), (1, (-25 / 432)), (2, (-5 / 72)), (3, (-5 / 27)), (5, (5 / 54)), (6, (-5 / 216)), (7, (-5 / 54)), (13, (-5 / 54)), (26, (-5 / 27)), (35, (-5 / 27)), (54, (5 / 18))]

theorem singlePair220 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node220 node220Labels = Sparse.eval singlePairValue220 (familyPairVector B) := by
  have hp := single_label_three B hB node220
  have hl : node220Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node220 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node220 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node220 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node220 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node220 (EqualityPatterns.family3.label 1) = PairSemantics.raw889 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node220 PairSemantics.raw889; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical889 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node220 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node220 (EqualityPatterns.family3.label 2) = PairSemantics.raw9012 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node220 PairSemantics.raw9012; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9012 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node220 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node220 (EqualityPatterns.family3.label 3) = PairSemantics.raw859 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node220 PairSemantics.raw859; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical859 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node220 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2788 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node220 (EqualityPatterns.family3.label 4) = PairSemantics.raw425 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node220 PairSemantics.raw425; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical425 hH).trans (PairSemantics.sound2788 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue220, PairSemantics.value0, PairSemantics.value10, PairSemantics.value65, PairSemantics.value118, PairSemantics.value2788, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue221 : Sparse (Fin 909) := [(0, (37 / 864)), (1, (85 / 864)), (2, (35 / 864)), (3, (-5 / 18)), (4, (-5 / 54)), (5, (25 / 216)), (6, (-5 / 288)), (8, (-5 / 54)), (13, (-5 / 27)), (26, (-5 / 54)), (35, (-5 / 54)), (52, (-5 / 54)), (56, (5 / 18))]

theorem singlePair221 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node221 node221Labels = Sparse.eval singlePairValue221 (familyPairVector B) := by
  have hp := single_label_three B hB node221
  have hl : node221Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node221 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node221 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node221 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node221 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node221 (EqualityPatterns.family3.label 1) = PairSemantics.raw890 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node221 PairSemantics.raw890; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical890 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node221 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node221 (EqualityPatterns.family3.label 2) = PairSemantics.raw9010 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node221 PairSemantics.raw9010; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9010 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node221 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node221 (EqualityPatterns.family3.label 3) = PairSemantics.raw859 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node221 PairSemantics.raw859; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical859 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node221 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2657 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node221 (EqualityPatterns.family3.label 4) = PairSemantics.raw426 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node221 PairSemantics.raw426; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical426 hH).trans (PairSemantics.sound2657 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue221, PairSemantics.value0, PairSemantics.value26, PairSemantics.value65, PairSemantics.value118, PairSemantics.value2657, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue222 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-5 / 108)), (2, (-25 / 432)), (5, (-5 / 216)), (6, (5 / 216)), (26, (5 / 54)), (35, (5 / 54))]

theorem singlePair222 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node222 node222Labels = Sparse.eval singlePairValue222 (familyPairVector B) := by
  have hp := single_label_three B hB node222
  have hl : node222Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node222 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node222 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node222 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node222 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node222 (EqualityPatterns.family3.label 1) = PairSemantics.raw891 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node222 PairSemantics.raw891; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical891 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node222 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node222 (EqualityPatterns.family3.label 2) = PairSemantics.raw9011 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node222 PairSemantics.raw9011; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9011 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node222 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node222 (EqualityPatterns.family3.label 3) = PairSemantics.raw860 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node222 PairSemantics.raw860; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical860 hH).trans (PairSemantics.sound24 hH)
  have hm4 : familyPairMoment B (groupedColumns node222 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value864 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node222 (EqualityPatterns.family3.label 4) = PairSemantics.raw427 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node222 PairSemantics.raw427; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical427 hH).trans (PairSemantics.sound864 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue222, PairSemantics.value0, PairSemantics.value10, PairSemantics.value24, PairSemantics.value65, PairSemantics.value864, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue223 : Sparse (Fin 909) := [(0, (31 / 864)), (1, (65 / 864)), (2, (5 / 432)), (3, (-20 / 27)), (5, (5 / 72)), (6, (-5 / 432)), (7, (-5 / 54)), (12, (-10 / 27)), (13, (-5 / 6)), (35, (-5 / 18)), (52, (-5 / 27)), (54, (5 / 18))]

theorem singlePair223 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node223 node223Labels = Sparse.eval singlePairValue223 (familyPairVector B) := by
  have hp := single_label_three B hB node223
  have hl : node223Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node223 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node223 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node223 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node223 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node223 (EqualityPatterns.family3.label 1) = PairSemantics.raw894 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node223 PairSemantics.raw894; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical894 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node223 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node223 (EqualityPatterns.family3.label 2) = PairSemantics.raw9006 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node223 PairSemantics.raw9006; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9006 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node223 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node223 (EqualityPatterns.family3.label 3) = PairSemantics.raw859 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node223 PairSemantics.raw859; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical859 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node223 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2132 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node223 (EqualityPatterns.family3.label 4) = PairSemantics.raw428 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node223 PairSemantics.raw428; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical428 hH).trans (PairSemantics.sound2132 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue223, PairSemantics.value0, PairSemantics.value11, PairSemantics.value26, PairSemantics.value118, PairSemantics.value2132, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue224 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (35 / 864)), (2, (5 / 864)), (3, (5 / 54)), (5, (-5 / 216)), (6, (5 / 288)), (13, (5 / 27)), (35, (5 / 54)), (52, (5 / 54))]

theorem singlePair224 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node224 node224Labels = Sparse.eval singlePairValue224 (familyPairVector B) := by
  have hp := single_label_three B hB node224
  have hl : node224Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node224 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node224 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node224 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node224 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node224 (EqualityPatterns.family3.label 1) = PairSemantics.raw893 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node224 PairSemantics.raw893; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical893 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node224 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node224 (EqualityPatterns.family3.label 2) = PairSemantics.raw9008 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node224 PairSemantics.raw9008; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9008 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node224 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node224 (EqualityPatterns.family3.label 3) = PairSemantics.raw860 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node224 PairSemantics.raw860; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical860 hH).trans (PairSemantics.sound24 hH)
  have hm4 : familyPairMoment B (groupedColumns node224 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value563 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node224 (EqualityPatterns.family3.label 4) = PairSemantics.raw429 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node224 PairSemantics.raw429; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical429 hH).trans (PairSemantics.sound563 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue224, PairSemantics.value0, PairSemantics.value11, PairSemantics.value24, PairSemantics.value26, PairSemantics.value563, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue225 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 216)), (2, (-5 / 216)), (3, (5 / 54)), (6, (5 / 432)), (13, (5 / 18)), (32, (5 / 54)), (35, (5 / 54)), (52, (5 / 54)), (60, (5 / 54)), (62, (-5 / 18))]

theorem singlePair225 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node225 node225Labels = Sparse.eval singlePairValue225 (familyPairVector B) := by
  have hp := single_label_three B hB node225
  have hl : node225Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node225 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node225 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node225 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node225 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node225 (EqualityPatterns.family3.label 1) = PairSemantics.raw896 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node225 PairSemantics.raw896; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical896 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node225 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node225 (EqualityPatterns.family3.label 2) = PairSemantics.raw9004 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node225 PairSemantics.raw9004; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9004 hH).trans (PairSemantics.sound26 hH)
  have hm3 : familyPairMoment B (groupedColumns node225 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node225 (EqualityPatterns.family3.label 3) = PairSemantics.raw860 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node225 PairSemantics.raw860; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical860 hH).trans (PairSemantics.sound24 hH)
  have hm4 : familyPairMoment B (groupedColumns node225 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value339 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node225 (EqualityPatterns.family3.label 4) = PairSemantics.raw430 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node225 PairSemantics.raw430; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical430 hH).trans (PairSemantics.sound339 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue225, PairSemantics.value0, PairSemantics.value10, PairSemantics.value24, PairSemantics.value26, PairSemantics.value339, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue226 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-55 / 864)), (2, (-25 / 864)), (3, (5 / 54)), (5, (-5 / 72)), (7, (5 / 54)), (13, (5 / 54)), (35, (5 / 54)), (54, (-5 / 18))]

theorem singlePair226 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node226 node226Labels = Sparse.eval singlePairValue226 (familyPairVector B) := by
  have hp := single_label_three B hB node226
  have hl : node226Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node226 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node226 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node226 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node226 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node226 (EqualityPatterns.family3.label 1) = PairSemantics.raw891 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node226 PairSemantics.raw891; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical891 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node226 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node226 (EqualityPatterns.family3.label 2) = PairSemantics.raw9015 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node226 PairSemantics.raw9015; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9015 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node226 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node226 (EqualityPatterns.family3.label 3) = PairSemantics.raw861 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node226 PairSemantics.raw861; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical861 hH).trans (PairSemantics.sound25 hH)
  have hm4 : familyPairMoment B (groupedColumns node226 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value648 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node226 (EqualityPatterns.family3.label 4) = PairSemantics.raw431 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node226 PairSemantics.raw431; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical431 hH).trans (PairSemantics.sound648 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue226, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value25, PairSemantics.value648, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue227 : Sparse (Fin 909) := [(0, (17 / 432)), (1, (35 / 432)), (2, (5 / 108)), (5, (-5 / 54)), (8, (5 / 54)), (56, (-5 / 18))]

theorem singlePair227 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node227 node227Labels = Sparse.eval singlePairValue227 (familyPairVector B) := by
  have hp := single_label_three B hB node227
  have hl : node227Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node227 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node227 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node227 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node227 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node227 (EqualityPatterns.family3.label 1) = PairSemantics.raw893 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node227 PairSemantics.raw893; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical893 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node227 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node227 (EqualityPatterns.family3.label 2) = PairSemantics.raw9011 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node227 PairSemantics.raw9011; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9011 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node227 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node227 (EqualityPatterns.family3.label 3) = PairSemantics.raw861 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node227 PairSemantics.raw861; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical861 hH).trans (PairSemantics.sound25 hH)
  have hm4 : familyPairMoment B (groupedColumns node227 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1132 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node227 (EqualityPatterns.family3.label 4) = PairSemantics.raw432 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node227 PairSemantics.raw432; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical432 hH).trans (PairSemantics.sound1132 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue227, PairSemantics.value0, PairSemantics.value25, PairSemantics.value26, PairSemantics.value65, PairSemantics.value1132, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue228 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-25 / 432)), (2, (-5 / 54)), (6, (5 / 432)), (12, (5 / 54)), (13, (5 / 9)), (32, (5 / 27)), (60, (5 / 27)), (128, (5 / 54))]

theorem singlePair228 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node228 node228Labels = Sparse.eval singlePairValue228 (familyPairVector B) := by
  have hp := single_label_three B hB node228
  have hl : node228Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node228 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node228 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node228 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node228 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node228 (EqualityPatterns.family3.label 1) = PairSemantics.raw899 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node228 PairSemantics.raw899; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical899 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node228 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node228 (EqualityPatterns.family3.label 2) = PairSemantics.raw8992 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node228 PairSemantics.raw8992; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8992 hH).trans (PairSemantics.sound10 hH)
  have hm3 : familyPairMoment B (groupedColumns node228 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node228 (EqualityPatterns.family3.label 3) = PairSemantics.raw860 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node228 PairSemantics.raw860; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical860 hH).trans (PairSemantics.sound24 hH)
  have hm4 : familyPairMoment B (groupedColumns node228 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value340 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node228 (EqualityPatterns.family3.label 4) = PairSemantics.raw433 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node228 PairSemantics.raw433; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical433 hH).trans (PairSemantics.sound340 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue228, PairSemantics.value0, PairSemantics.value10, PairSemantics.value24, PairSemantics.value340, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue229 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 216)), (2, (5 / 432)), (3, (5 / 54)), (5, (-5 / 108)), (12, (5 / 54)), (13, (5 / 18)), (59, (-5 / 18)), (61, (-5 / 18))]

theorem singlePair229 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node229 node229Labels = Sparse.eval singlePairValue229 (familyPairVector B) := by
  have hp := single_label_three B hB node229
  have hl : node229Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node229 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node229 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node229 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node229 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node229 (EqualityPatterns.family3.label 1) = PairSemantics.raw897 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node229 PairSemantics.raw897; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical897 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node229 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node229 (EqualityPatterns.family3.label 2) = PairSemantics.raw8998 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node229 PairSemantics.raw8998; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8998 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node229 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node229 (EqualityPatterns.family3.label 3) = PairSemantics.raw861 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node229 PairSemantics.raw861; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical861 hH).trans (PairSemantics.sound25 hH)
  have hm4 : familyPairMoment B (groupedColumns node229 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value338 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node229 (EqualityPatterns.family3.label 4) = PairSemantics.raw434 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node229 PairSemantics.raw434; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical434 hH).trans (PairSemantics.sound338 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue229, PairSemantics.value0, PairSemantics.value10, PairSemantics.value25, PairSemantics.value46, PairSemantics.value338, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue230 : Sparse (Fin 909) := [(0, (31 / 864)), (1, (-5 / 288)), (2, (-25 / 432)), (3, (5 / 54)), (5, (5 / 216)), (6, (5 / 432)), (11, (5 / 54)), (13, (5 / 54)), (26, (5 / 27)), (35, (5 / 18))]

theorem singlePair230 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node230 node230Labels = Sparse.eval singlePairValue230 (familyPairVector B) := by
  have hp := single_label_three B hB node230
  have hl : node230Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node230 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node230 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node230 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node230 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node230 (EqualityPatterns.family3.label 1) = PairSemantics.raw876 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node230 PairSemantics.raw876; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical876 hH).trans (PairSemantics.sound24 hH)
  have hm2 : familyPairMoment B (groupedColumns node230 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node230 (EqualityPatterns.family3.label 2) = PairSemantics.raw9034 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node230 PairSemantics.raw9034; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9034 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node230 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node230 (EqualityPatterns.family3.label 3) = PairSemantics.raw867 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node230 PairSemantics.raw867; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical867 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node230 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value696 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node230 (EqualityPatterns.family3.label 4) = PairSemantics.raw435 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node230 PairSemantics.raw435; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical435 hH).trans (PairSemantics.sound696 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue230, PairSemantics.value0, PairSemantics.value11, PairSemantics.value24, PairSemantics.value118, PairSemantics.value696, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue231 : Sparse (Fin 909) := [(0, (31 / 864)), (1, (-5 / 864)), (2, (25 / 864)), (5, (-5 / 108)), (6, (-5 / 864)), (54, (-5 / 18)), (56, (-5 / 18)), (228, (-5 / 18))]

theorem singlePair231 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node231 node231Labels = Sparse.eval singlePairValue231 (familyPairVector B) := by
  have hp := single_label_three B hB node231
  have hl : node231Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node231 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node231 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node231 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node231 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node231 (EqualityPatterns.family3.label 1) = PairSemantics.raw877 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node231 PairSemantics.raw877; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical877 hH).trans (PairSemantics.sound25 hH)
  have hm2 : familyPairMoment B (groupedColumns node231 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node231 (EqualityPatterns.family3.label 2) = PairSemantics.raw9033 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node231 PairSemantics.raw9033; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9033 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node231 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node231 (EqualityPatterns.family3.label 3) = PairSemantics.raw867 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node231 PairSemantics.raw867; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical867 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node231 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value698 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node231 (EqualityPatterns.family3.label 4) = PairSemantics.raw436 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node231 PairSemantics.raw436; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical436 hH).trans (PairSemantics.sound698 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue231, PairSemantics.value0, PairSemantics.value11, PairSemantics.value25, PairSemantics.value118, PairSemantics.value698, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
