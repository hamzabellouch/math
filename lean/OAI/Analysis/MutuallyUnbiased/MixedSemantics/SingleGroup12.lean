import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleRules
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical280
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical281
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical282
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound8

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue200 : Sparse (Fin 909) := [(0, (11 / 288)), (1, (55 / 864)), (2, (65 / 864)), (3, (-25 / 54)), (5, (5 / 216)), (6, (-5 / 288)), (7, (-5 / 18)), (12, (-5 / 54)), (13, (-25 / 54)), (26, (-5 / 27)), (35, (-25 / 54)), (54, (5 / 6)), (82, (-5 / 54)), (199, (5 / 18))]

theorem singlePair200 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node200 node200Labels = Sparse.eval singlePairValue200 (familyPairVector B) := by
  have hp := single_label_three B hB node200
  have hl : node200Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node200 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node200 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node200 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node200 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node200 (EqualityPatterns.family3.label 1) = PairSemantics.raw865 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node200 PairSemantics.raw865; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical865 hH).trans (PairSemantics.sound118 hH)
  have hm2 : familyPairMoment B (groupedColumns node200 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node200 (EqualityPatterns.family3.label 2) = PairSemantics.raw9046 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node200 PairSemantics.raw9046; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9046 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node200 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node200 (EqualityPatterns.family3.label 3) = PairSemantics.raw858 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node200 PairSemantics.raw858; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical858 hH).trans (PairSemantics.sound25 hH)
  have hm4 : familyPairMoment B (groupedColumns node200 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2122 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node200 (EqualityPatterns.family3.label 4) = PairSemantics.raw405 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node200 PairSemantics.raw405; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical405 hH).trans (PairSemantics.sound2122 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue200, PairSemantics.value0, PairSemantics.value11, PairSemantics.value25, PairSemantics.value118, PairSemantics.value2122, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue201 : Sparse (Fin 909) := [(0, (31 / 864)), (1, (25 / 864)), (2, (5 / 432)), (3, (5 / 54)), (6, (5 / 432)), (13, (5 / 18)), (52, (5 / 27)), (128, (5 / 54))]

theorem singlePair201 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node201 node201Labels = Sparse.eval singlePairValue201 (familyPairVector B) := by
  have hp := single_label_three B hB node201
  have hl : node201Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node201 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node201 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node201 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node201 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node201 (EqualityPatterns.family3.label 1) = PairSemantics.raw868 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node201 PairSemantics.raw868; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical868 hH).trans (PairSemantics.sound118 hH)
  have hm2 : familyPairMoment B (groupedColumns node201 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node201 (EqualityPatterns.family3.label 2) = PairSemantics.raw9045 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node201 PairSemantics.raw9045; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9045 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node201 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node201 (EqualityPatterns.family3.label 3) = PairSemantics.raw860 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node201 PairSemantics.raw860; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical860 hH).trans (PairSemantics.sound24 hH)
  have hm4 : familyPairMoment B (groupedColumns node201 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value575 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node201 (EqualityPatterns.family3.label 4) = PairSemantics.raw406 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node201 PairSemantics.raw406; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical406 hH).trans (PairSemantics.sound575 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue201, PairSemantics.value0, PairSemantics.value11, PairSemantics.value24, PairSemantics.value118, PairSemantics.value575, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue202 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (5 / 216)), (2, (-5 / 288)), (3, (5 / 54)), (5, (-5 / 72)), (6, (5 / 288)), (13, (5 / 27)), (26, (5 / 54)), (35, (5 / 18)), (82, (5 / 54))]

theorem singlePair202 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node202 node202Labels = Sparse.eval singlePairValue202 (familyPairVector B) := by
  have hp := single_label_three B hB node202
  have hl : node202Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node202 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node202 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node202 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node202 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node202 (EqualityPatterns.family3.label 1) = PairSemantics.raw864 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node202 PairSemantics.raw864; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical864 hH).trans (PairSemantics.sound24 hH)
  have hm2 : familyPairMoment B (groupedColumns node202 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node202 (EqualityPatterns.family3.label 2) = PairSemantics.raw9053 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node202 PairSemantics.raw9053; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9053 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node202 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node202 (EqualityPatterns.family3.label 3) = PairSemantics.raw861 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node202 PairSemantics.raw861; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical861 hH).trans (PairSemantics.sound25 hH)
  have hm4 : familyPairMoment B (groupedColumns node202 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value671 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node202 (EqualityPatterns.family3.label 4) = PairSemantics.raw407 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node202 PairSemantics.raw407; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical407 hH).trans (PairSemantics.sound671 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue202, PairSemantics.value0, PairSemantics.value11, PairSemantics.value24, PairSemantics.value25, PairSemantics.value671, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue203 : Sparse (Fin 909) := [(0, (25 / 864)), (1, (35 / 216)), (2, (-5 / 432)), (3, (5 / 54)), (5, (5 / 216)), (6, (5 / 864)), (12, (5 / 54)), (13, (5 / 54)), (35, (5 / 54)), (82, (5 / 54)), (128, (5 / 54))]

theorem singlePair203 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node203 node203Labels = Sparse.eval singlePairValue203 (familyPairVector B) := by
  have hp := single_label_three B hB node203
  have hl : node203Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node203 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node203 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node203 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node203 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node203 (EqualityPatterns.family3.label 1) = PairSemantics.raw871 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node203 PairSemantics.raw871; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical871 hH).trans (PairSemantics.sound118 hH)
  have hm2 : familyPairMoment B (groupedColumns node203 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node203 (EqualityPatterns.family3.label 2) = PairSemantics.raw9036 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node203 PairSemantics.raw9036; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9036 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node203 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node203 (EqualityPatterns.family3.label 3) = PairSemantics.raw860 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node203 PairSemantics.raw860; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical860 hH).trans (PairSemantics.sound24 hH)
  have hm4 : familyPairMoment B (groupedColumns node203 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value557 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node203 (EqualityPatterns.family3.label 4) = PairSemantics.raw408 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node203 PairSemantics.raw408; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical408 hH).trans (PairSemantics.sound557 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue203, PairSemantics.value0, PairSemantics.value4, PairSemantics.value24, PairSemantics.value118, PairSemantics.value557, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue204 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 27)), (2, (5 / 108)), (5, (-5 / 54)), (12, (5 / 54)), (13, (5 / 27)), (54, (-5 / 9)), (199, (-5 / 18))]

theorem singlePair204 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node204 node204Labels = Sparse.eval singlePairValue204 (familyPairVector B) := by
  have hp := single_label_three B hB node204
  have hl : node204Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node204 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node204 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node204 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node204 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node204 (EqualityPatterns.family3.label 1) = PairSemantics.raw870 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node204 PairSemantics.raw870; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical870 hH).trans (PairSemantics.sound25 hH)
  have hm2 : familyPairMoment B (groupedColumns node204 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node204 (EqualityPatterns.family3.label 2) = PairSemantics.raw9041 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node204 PairSemantics.raw9041; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9041 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node204 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node204 (EqualityPatterns.family3.label 3) = PairSemantics.raw861 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node204 PairSemantics.raw861; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical861 hH).trans (PairSemantics.sound25 hH)
  have hm4 : familyPairMoment B (groupedColumns node204 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value643 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node204 (EqualityPatterns.family3.label 4) = PairSemantics.raw409 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node204 PairSemantics.raw409; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical409 hH).trans (PairSemantics.sound643 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue204, PairSemantics.value0, PairSemantics.value4, PairSemantics.value25, PairSemantics.value643, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue205 : Sparse (Fin 909) := [(0, (37 / 864)), (1, (5 / 288)), (2, (215 / 864)), (5, (-5 / 54)), (9, (-5 / 216)), (13, (-5 / 27)), (35, (-10 / 27)), (58, (5 / 864)), (68, (5 / 72)), (70, (-5 / 27)), (196, (5 / 18))]

theorem singlePair205 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node205 node205Labels = Sparse.eval singlePairValue205 (familyPairVector B) := by
  have hp := single_label_three B hB node205
  have hl : node205Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node205 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node205 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node205 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node205 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node205 (EqualityPatterns.family3.label 1) = PairSemantics.raw878 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node205 PairSemantics.raw878; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical878 hH).trans (PairSemantics.sound3 hH)
  have hm2 : familyPairMoment B (groupedColumns node205 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node205 (EqualityPatterns.family3.label 2) = PairSemantics.raw9012 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node205 PairSemantics.raw9012; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9012 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node205 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value381 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node205 (EqualityPatterns.family3.label 3) = PairSemantics.raw854 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node205 PairSemantics.raw854; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical854 hH).trans (PairSemantics.sound381 hH)
  have hm4 : familyPairMoment B (groupedColumns node205 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2787 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node205 (EqualityPatterns.family3.label 4) = PairSemantics.raw410 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node205 PairSemantics.raw410; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical410 hH).trans (PairSemantics.sound2787 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue205, PairSemantics.value0, PairSemantics.value3, PairSemantics.value65, PairSemantics.value381, PairSemantics.value2787, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue206 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-5 / 216)), (2, (-5 / 144)), (3, (-5 / 54)), (5, (5 / 216)), (6, (-35 / 864)), (7, (-5 / 54)), (9, (-5 / 216)), (26, (-5 / 27)), (35, (-5 / 18)), (58, (5 / 864)), (68, (5 / 72)), (70, (-5 / 54)), (71, (-5 / 54)), (197, (5 / 18))]

theorem singlePair206 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node206 node206Labels = Sparse.eval singlePairValue206 (familyPairVector B) := by
  have hp := single_label_three B hB node206
  have hl : node206Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node206 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node206 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node206 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node206 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node206 (EqualityPatterns.family3.label 1) = PairSemantics.raw879 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node206 PairSemantics.raw879; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical879 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node206 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node206 (EqualityPatterns.family3.label 2) = PairSemantics.raw9010 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node206 PairSemantics.raw9010; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9010 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node206 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value381 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node206 (EqualityPatterns.family3.label 3) = PairSemantics.raw854 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node206 PairSemantics.raw854; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical854 hH).trans (PairSemantics.sound381 hH)
  have hm4 : familyPairMoment B (groupedColumns node206 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2461 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node206 (EqualityPatterns.family3.label 4) = PairSemantics.raw411 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node206 PairSemantics.raw411; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical411 hH).trans (PairSemantics.sound2461 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue206, PairSemantics.value0, PairSemantics.value10, PairSemantics.value65, PairSemantics.value381, PairSemantics.value2461, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue207 : Sparse (Fin 909) := [(0, (29 / 864)), (1, (-25 / 432)), (3, (-10 / 27)), (5, (5 / 54)), (6, (-25 / 432)), (7, (-5 / 27)), (9, (-5 / 216)), (13, (-25 / 54)), (35, (-10 / 27)), (52, (-10 / 27)), (58, (5 / 864)), (68, (5 / 72)), (69, (-5 / 54)), (70, (-5 / 54)), (125, (5 / 18))]

theorem singlePair207 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node207 node207Labels = Sparse.eval singlePairValue207 (familyPairVector B) := by
  have hp := single_label_three B hB node207
  have hl : node207Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node207 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node207 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node207 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node207 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node207 (EqualityPatterns.family3.label 1) = PairSemantics.raw883 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node207 PairSemantics.raw883; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical883 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node207 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node207 (EqualityPatterns.family3.label 2) = PairSemantics.raw9006 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node207 PairSemantics.raw9006; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9006 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node207 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value381 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node207 (EqualityPatterns.family3.label 3) = PairSemantics.raw854 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node207 PairSemantics.raw854; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical854 hH).trans (PairSemantics.sound381 hH)
  have hm4 : familyPairMoment B (groupedColumns node207 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1878 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node207 (EqualityPatterns.family3.label 4) = PairSemantics.raw412 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node207 PairSemantics.raw412; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical412 hH).trans (PairSemantics.sound1878 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue207, PairSemantics.value0, PairSemantics.value11, PairSemantics.value26, PairSemantics.value381, PairSemantics.value1878, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue208 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 144)), (2, (-5 / 864)), (3, (-10 / 27)), (5, (-5 / 54)), (6, (-5 / 216)), (9, (-5 / 108)), (12, (-5 / 27)), (13, (-65 / 54)), (32, (-5 / 18)), (35, (-25 / 54)), (52, (-10 / 27)), (54, (5 / 18)), (58, (5 / 864)), (60, (-25 / 54)), (62, (5 / 9)), (68, (5 / 72)), (128, (-5 / 27)), (257, (-5 / 54)), (260, (5 / 18)), (264, (5 / 18)), (495, (-5 / 54))]

theorem singlePair208 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node208 node208Labels = Sparse.eval singlePairValue208 (familyPairVector B) := by
  have hp := single_label_three B hB node208
  have hl : node208Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node208 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node208 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node208 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node208 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node208 (EqualityPatterns.family3.label 1) = PairSemantics.raw885 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node208 PairSemantics.raw885; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical885 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node208 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node208 (EqualityPatterns.family3.label 2) = PairSemantics.raw9005 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node208 PairSemantics.raw9005; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9005 hH).trans (PairSemantics.sound26 hH)
  have hm3 : familyPairMoment B (groupedColumns node208 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value381 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node208 (EqualityPatterns.family3.label 3) = PairSemantics.raw854 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node208 PairSemantics.raw854; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical854 hH).trans (PairSemantics.sound381 hH)
  have hm4 : familyPairMoment B (groupedColumns node208 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1402 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node208 (EqualityPatterns.family3.label 4) = PairSemantics.raw413 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node208 PairSemantics.raw413; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical413 hH).trans (PairSemantics.sound1402 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue208, PairSemantics.value0, PairSemantics.value10, PairSemantics.value26, PairSemantics.value381, PairSemantics.value1402, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue209 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 48)), (2, (-25 / 432)), (3, (-10 / 27)), (5, (5 / 72)), (6, (5 / 432)), (7, (-5 / 18)), (9, (-5 / 108)), (12, (-5 / 54)), (13, (-10 / 27)), (23, (5 / 18)), (27, (5 / 72)), (35, (-10 / 27)), (52, (-5 / 27)), (54, (5 / 9)), (68, (5 / 36)), (69, (-5 / 54)), (70, (-5 / 54)), (125, (5 / 18)), (196, (5 / 18))]

theorem singlePair209 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node209 node209Labels = Sparse.eval singlePairValue209 (familyPairVector B) := by
  have hp := single_label_three B hB node209
  have hl : node209Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node209 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node209 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node209 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node209 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node209 (EqualityPatterns.family3.label 1) = PairSemantics.raw882 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node209 PairSemantics.raw882; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical882 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node209 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node209 (EqualityPatterns.family3.label 2) = PairSemantics.raw9009 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node209 PairSemantics.raw9009; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9009 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node209 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value382 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node209 (EqualityPatterns.family3.label 3) = PairSemantics.raw855 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node209 PairSemantics.raw855; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical855 hH).trans (PairSemantics.sound382 hH)
  have hm4 : familyPairMoment B (groupedColumns node209 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2116 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node209 (EqualityPatterns.family3.label 4) = PairSemantics.raw414 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node209 PairSemantics.raw414; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical414 hH).trans (PairSemantics.sound2116 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue209, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value382, PairSemantics.value2116, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue210 : Sparse (Fin 909) := [(0, (1 / 24)), (1, (5 / 108)), (2, (5 / 216)), (5, (35 / 216)), (8, (-5 / 18)), (9, (-5 / 108)), (24, (5 / 18)), (27, (5 / 72)), (56, (5 / 9)), (68, (5 / 36)), (71, (-5 / 27)), (197, (5 / 9))]

theorem singlePair210 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node210 node210Labels = Sparse.eval singlePairValue210 (familyPairVector B) := by
  have hp := single_label_three B hB node210
  have hl : node210Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node210 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node210 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node210 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node210 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node210 (EqualityPatterns.family3.label 1) = PairSemantics.raw883 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node210 PairSemantics.raw883; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical883 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node210 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node210 (EqualityPatterns.family3.label 2) = PairSemantics.raw9007 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node210 PairSemantics.raw9007; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9007 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node210 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value382 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node210 (EqualityPatterns.family3.label 3) = PairSemantics.raw855 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node210 PairSemantics.raw855; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical855 hH).trans (PairSemantics.sound382 hH)
  have hm4 : familyPairMoment B (groupedColumns node210 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2649 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node210 (EqualityPatterns.family3.label 4) = PairSemantics.raw415 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node210 PairSemantics.raw415; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical415 hH).trans (PairSemantics.sound2649 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue210, PairSemantics.value0, PairSemantics.value26, PairSemantics.value65, PairSemantics.value382, PairSemantics.value2649, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue211 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-65 / 864)), (2, (-25 / 864)), (6, (-5 / 432)), (9, (5 / 216)), (13, (5 / 54)), (52, (5 / 27)), (68, (-5 / 72)), (69, (5 / 54)), (125, (-5 / 18))]

theorem singlePair211 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node211 node211Labels = Sparse.eval singlePairValue211 (familyPairVector B) := by
  have hp := single_label_three B hB node211
  have hl : node211Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node211 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node211 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node211 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node211 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node211 (EqualityPatterns.family3.label 1) = PairSemantics.raw886 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node211 PairSemantics.raw886; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical886 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node211 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node211 (EqualityPatterns.family3.label 2) = PairSemantics.raw9008 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node211 PairSemantics.raw9008; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9008 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node211 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value116 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node211 (EqualityPatterns.family3.label 3) = PairSemantics.raw856 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node211 PairSemantics.raw856; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical856 hH).trans (PairSemantics.sound116 hH)
  have hm4 : familyPairMoment B (groupedColumns node211 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value549 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node211 (EqualityPatterns.family3.label 4) = PairSemantics.raw416 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node211 PairSemantics.raw416; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical416 hH).trans (PairSemantics.sound549 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue211, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value116, PairSemantics.value549, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue212 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-25 / 864)), (2, (5 / 96)), (3, (-10 / 27)), (4, (-5 / 54)), (5, (-5 / 72)), (6, (-25 / 864)), (9, (-5 / 108)), (13, (-5 / 18)), (26, (-5 / 18)), (34, (-5 / 27)), (35, (-10 / 27)), (52, (-5 / 18)), (56, (5 / 18)), (58, (5 / 864)), (60, (-5 / 27)), (67, (-5 / 54)), (68, (5 / 72)), (128, (-5 / 54)), (257, (-5 / 54)), (262, (5 / 18)), (268, (5 / 18)), (495, (-5 / 54))]

theorem singlePair212 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node212 node212Labels = Sparse.eval singlePairValue212 (familyPairVector B) := by
  have hp := single_label_three B hB node212
  have hl : node212Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node212 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node212 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node212 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node212 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node212 (EqualityPatterns.family3.label 1) = PairSemantics.raw890 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node212 PairSemantics.raw890; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical890 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node212 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node212 (EqualityPatterns.family3.label 2) = PairSemantics.raw8993 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node212 PairSemantics.raw8993; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8993 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node212 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value381 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node212 (EqualityPatterns.family3.label 3) = PairSemantics.raw854 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node212 PairSemantics.raw854; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical854 hH).trans (PairSemantics.sound381 hH)
  have hm4 : familyPairMoment B (groupedColumns node212 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1404 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node212 (EqualityPatterns.family3.label 4) = PairSemantics.raw417 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node212 PairSemantics.raw417; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical417 hH).trans (PairSemantics.sound1404 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue212, PairSemantics.value0, PairSemantics.value26, PairSemantics.value46, PairSemantics.value381, PairSemantics.value1404, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue213 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 864)), (2, (25 / 864)), (3, (-10 / 27)), (4, (-5 / 54)), (5, (-5 / 216)), (6, (5 / 216)), (9, (-5 / 108)), (12, (-5 / 27)), (13, (-10 / 27)), (26, (-5 / 54)), (27, (5 / 72)), (35, (-5 / 27)), (51, (5 / 9)), (54, (5 / 9)), (55, (5 / 18)), (56, (5 / 9)), (59, (5 / 18)), (61, (5 / 9)), (68, (5 / 36)), (259, (5 / 18)), (262, (5 / 18)), (266, (5 / 18)), (268, (5 / 18))]

theorem singlePair213 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node213 node213Labels = Sparse.eval singlePairValue213 (familyPairVector B) := by
  have hp := single_label_three B hB node213
  have hl : node213Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node213 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node213 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node213 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node213 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node213 (EqualityPatterns.family3.label 1) = PairSemantics.raw892 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node213 PairSemantics.raw892; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical892 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node213 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node213 (EqualityPatterns.family3.label 2) = PairSemantics.raw8991 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node213 PairSemantics.raw8991; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8991 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node213 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value382 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node213 (EqualityPatterns.family3.label 3) = PairSemantics.raw855 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node213 PairSemantics.raw855; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical855 hH).trans (PairSemantics.sound382 hH)
  have hm4 : familyPairMoment B (groupedColumns node213 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1406 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node213 (EqualityPatterns.family3.label 4) = PairSemantics.raw418 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node213 PairSemantics.raw418; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical418 hH).trans (PairSemantics.sound1406 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue213, PairSemantics.value0, PairSemantics.value26, PairSemantics.value46, PairSemantics.value382, PairSemantics.value1406, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue214 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 72)), (2, (-5 / 108)), (5, (5 / 108)), (6, (-5 / 432)), (9, (5 / 216)), (26, (5 / 54)), (35, (5 / 54)), (54, (-5 / 18)), (68, (-5 / 72)), (259, (-5 / 18)), (266, (-5 / 18))]

theorem singlePair214 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node214 node214Labels = Sparse.eval singlePairValue214 (familyPairVector B) := by
  have hp := single_label_three B hB node214
  have hl : node214Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node214 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node214 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node214 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node214 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node214 (EqualityPatterns.family3.label 1) = PairSemantics.raw891 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node214 PairSemantics.raw891; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical891 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node214 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node214 (EqualityPatterns.family3.label 2) = PairSemantics.raw8998 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node214 PairSemantics.raw8998; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8998 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node214 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value116 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node214 (EqualityPatterns.family3.label 3) = PairSemantics.raw856 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node214 PairSemantics.raw856; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical856 hH).trans (PairSemantics.sound116 hH)
  have hm4 : familyPairMoment B (groupedColumns node214 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value337 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node214 (EqualityPatterns.family3.label 4) = PairSemantics.raw419 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node214 PairSemantics.raw419; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical419 hH).trans (PairSemantics.sound337 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue214, PairSemantics.value0, PairSemantics.value10, PairSemantics.value46, PairSemantics.value116, PairSemantics.value337, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue215 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (35 / 432)), (5, (5 / 108)), (6, (5 / 72)), (11, (-5 / 27)), (26, (-5 / 27)), (35, (-10 / 27)), (226, (5 / 18))]

theorem singlePair215 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node215 node215Labels = Sparse.eval singlePairValue215 (familyPairVector B) := by
  have hp := single_label_three B hB node215
  have hl : node215Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node215 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node215 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node215 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node215 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node215 (EqualityPatterns.family3.label 1) = PairSemantics.raw874 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node215 PairSemantics.raw874; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical874 hH).trans (PairSemantics.sound24 hH)
  have hm2 : familyPairMoment B (groupedColumns node215 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node215 (EqualityPatterns.family3.label 2) = PairSemantics.raw9026 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node215 PairSemantics.raw9026; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9026 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node215 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node215 (EqualityPatterns.family3.label 3) = PairSemantics.raw857 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node215 PairSemantics.raw857; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical857 hH).trans (PairSemantics.sound24 hH)
  have hm4 : familyPairMoment B (groupedColumns node215 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2794 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node215 (EqualityPatterns.family3.label 4) = PairSemantics.raw420 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node215 PairSemantics.raw420; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical420 hH).trans (PairSemantics.sound2794 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue215, PairSemantics.value0, PairSemantics.value24, PairSemantics.value65, PairSemantics.value2794, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
