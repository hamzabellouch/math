import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleRules
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical121
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical122
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical159
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical160
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical161
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical280
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical282
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound9

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue441 : Sparse (Fin 909) := [(0, (11 / 288)), (1, (25 / 864)), (2, (-5 / 144)), (3, (-35 / 54)), (4, (-5 / 54)), (5, (5 / 108)), (7, (-5 / 27)), (12, (-5 / 18)), (13, (-5 / 54)), (23, (5 / 9)), (24, (5 / 18)), (25, (5 / 18)), (26, (-5 / 54)), (27, (-5 / 36)), (35, (-5 / 54)), (54, (5 / 18)), (55, (5 / 18))]

theorem singlePair441 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node441 node441Labels = Sparse.eval singlePairValue441 (familyPairVector B) := by
  have hp := single_label_three B hB node441
  have hl : node441Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node441 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node441 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node441 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node441 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node441 (EqualityPatterns.family3.label 1) = PairSemantics.raw5153 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node441 PairSemantics.raw5153; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5153 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node441 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node441 (EqualityPatterns.family3.label 2) = PairSemantics.raw8982 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node441 PairSemantics.raw8982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8982 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node441 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value231 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node441 (EqualityPatterns.family3.label 3) = PairSemantics.raw5105 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node441 PairSemantics.raw5105; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5105 hH).trans (PairSemantics.sound231 hH)
  have hm4 : familyPairMoment B (groupedColumns node441 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2121 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node441 (EqualityPatterns.family3.label 4) = PairSemantics.raw3882 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node441 PairSemantics.raw3882; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3882 hH).trans (PairSemantics.sound2121 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue441, PairSemantics.value0, PairSemantics.value11, PairSemantics.value46, PairSemantics.value231, PairSemantics.value2121, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue442 : Sparse (Fin 909) := [(0, (19 / 864)), (1, (155 / 864)), (2, (-5 / 48)), (3, (-5 / 6)), (4, (-10 / 27)), (5, (5 / 108)), (7, (-5 / 18)), (12, (-5 / 54)), (23, (5 / 18)), (24, (5 / 9)), (26, (-5 / 27)), (27, (-5 / 36)), (35, (-5 / 54)), (55, (5 / 18))]

theorem singlePair442 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node442 node442Labels = Sparse.eval singlePairValue442 (familyPairVector B) := by
  have hp := single_label_three B hB node442
  have hl : node442Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node442 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node442 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node442 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node442 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node442 (EqualityPatterns.family3.label 1) = PairSemantics.raw5156 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node442 PairSemantics.raw5156; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5156 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node442 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node442 (EqualityPatterns.family3.label 2) = PairSemantics.raw8977 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node442 PairSemantics.raw8977; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8977 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node442 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value231 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node442 (EqualityPatterns.family3.label 3) = PairSemantics.raw5105 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node442 PairSemantics.raw5105; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5105 hH).trans (PairSemantics.sound231 hH)
  have hm4 : familyPairMoment B (groupedColumns node442 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2119 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node442 (EqualityPatterns.family3.label 4) = PairSemantics.raw3883 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node442 PairSemantics.raw3883; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3883 hH).trans (PairSemantics.sound2119 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue442, PairSemantics.value0, PairSemantics.value11, PairSemantics.value231, PairSemantics.value232, PairSemantics.value2119, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue443 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (5 / 432)), (2, (-5 / 288)), (3, (-5 / 9)), (4, (-5 / 54)), (5, (5 / 216)), (7, (-5 / 54)), (12, (-5 / 18)), (23, (5 / 9)), (25, (5 / 9)), (26, (-5 / 54)), (27, (-5 / 72)), (33, (5 / 9)), (51, (5 / 18)), (54, (5 / 9)), (55, (5 / 18)), (63, (5 / 18)), (64, (5 / 18)), (65, (5 / 18))]

theorem singlePair443 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node443 node443Labels = Sparse.eval singlePairValue443 (familyPairVector B) := by
  have hp := single_label_three B hB node443
  have hl : node443Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node443 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node443 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node443 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node443 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node443 (EqualityPatterns.family3.label 1) = PairSemantics.raw5158 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node443 PairSemantics.raw5158; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5158 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node443 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node443 (EqualityPatterns.family3.label 2) = PairSemantics.raw8976 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node443 PairSemantics.raw8976; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8976 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node443 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value231 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node443 (EqualityPatterns.family3.label 3) = PairSemantics.raw5105 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node443 PairSemantics.raw5105; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5105 hH).trans (PairSemantics.sound231 hH)
  have hm4 : familyPairMoment B (groupedColumns node443 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2096 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node443 (EqualityPatterns.family3.label 4) = PairSemantics.raw3884 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node443 PairSemantics.raw3884; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3884 hH).trans (PairSemantics.sound2096 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue443, PairSemantics.value0, PairSemantics.value46, PairSemantics.value231, PairSemantics.value2096, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue444 : Sparse (Fin 909) := [(0, (1 / 27)), (1, (-5 / 144)), (2, (5 / 48)), (3, (-5 / 9)), (4, (-5 / 18)), (5, (-5 / 72)), (12, (-5 / 27)), (23, (5 / 18)), (25, (5 / 9)), (26, (-5 / 27)), (27, (5 / 24)), (31, (5 / 18)), (33, (5 / 9)), (54, (5 / 9)), (65, (5 / 18)), (195, (-5 / 9))]

theorem singlePair444 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node444 node444Labels = Sparse.eval singlePairValue444 (familyPairVector B) := by
  have hp := single_label_three B hB node444
  have hl : node444Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node444 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node444 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node444 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node444 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node444 (EqualityPatterns.family3.label 1) = PairSemantics.raw5153 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node444 PairSemantics.raw5153; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5153 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node444 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node444 (EqualityPatterns.family3.label 2) = PairSemantics.raw8990 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node444 PairSemantics.raw8990; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8990 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node444 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value716 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node444 (EqualityPatterns.family3.label 3) = PairSemantics.raw5109 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node444 PairSemantics.raw5109; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5109 hH).trans (PairSemantics.sound716 hH)
  have hm4 : familyPairMoment B (groupedColumns node444 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2101 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node444 (EqualityPatterns.family3.label 4) = PairSemantics.raw3885 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node444 PairSemantics.raw3885; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3885 hH).trans (PairSemantics.sound2101 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue444, PairSemantics.value0, PairSemantics.value46, PairSemantics.value716, PairSemantics.value2101, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue445 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (5 / 36)), (2, (55 / 864)), (3, (-35 / 54)), (5, (-5 / 72)), (7, (-5 / 54)), (12, (-5 / 9)), (23, (5 / 6)), (25, (5 / 6)), (27, (5 / 24)), (54, (5 / 9))]

theorem singlePair445 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node445 node445Labels = Sparse.eval singlePairValue445 (familyPairVector B) := by
  have hp := single_label_three B hB node445
  have hl : node445Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node445 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node445 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node445 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node445 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node445 (EqualityPatterns.family3.label 1) = PairSemantics.raw5156 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node445 PairSemantics.raw5156; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5156 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node445 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node445 (EqualityPatterns.family3.label 2) = PairSemantics.raw8989 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node445 PairSemantics.raw8989; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8989 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node445 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value716 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node445 (EqualityPatterns.family3.label 3) = PairSemantics.raw5109 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node445 PairSemantics.raw5109; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5109 hH).trans (PairSemantics.sound716 hH)
  have hm4 : familyPairMoment B (groupedColumns node445 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node445 (EqualityPatterns.family3.label 4) = PairSemantics.raw3886 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node445 PairSemantics.raw3886; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3886 hH).trans (PairSemantics.sound2118 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue445, PairSemantics.value0, PairSemantics.value4, PairSemantics.value232, PairSemantics.value716, PairSemantics.value2118, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue446 : Sparse (Fin 909) := [(0, (23 / 864)), (1, (95 / 864)), (2, (-5 / 432)), (3, (5 / 54)), (5, (5 / 216)), (12, (5 / 54)), (23, (-5 / 18)), (25, (-5 / 18)), (27, (-5 / 72)), (54, (-5 / 18))]

theorem singlePair446 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node446 node446Labels = Sparse.eval singlePairValue446 (familyPairVector B) := by
  have hp := single_label_three B hB node446
  have hl : node446Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node446 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node446 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node446 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node446 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node446 (EqualityPatterns.family3.label 1) = PairSemantics.raw5157 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node446 PairSemantics.raw5157; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5157 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node446 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node446 (EqualityPatterns.family3.label 2) = PairSemantics.raw8988 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node446 PairSemantics.raw8988; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8988 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node446 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value231 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node446 (EqualityPatterns.family3.label 3) = PairSemantics.raw5110 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node446 PairSemantics.raw5110; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5110 hH).trans (PairSemantics.sound231 hH)
  have hm4 : familyPairMoment B (groupedColumns node446 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value642 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node446 (EqualityPatterns.family3.label 4) = PairSemantics.raw3887 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node446 PairSemantics.raw3887; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3887 hH).trans (PairSemantics.sound642 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue446, PairSemantics.value0, PairSemantics.value4, PairSemantics.value46, PairSemantics.value231, PairSemantics.value642, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue447 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 144)), (5, (5 / 216)), (27, (-5 / 72)), (195, (5 / 9))]

theorem singlePair447 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node447 node447Labels = Sparse.eval singlePairValue447 (familyPairVector B) := by
  have hp := single_label_three B hB node447
  have hl : node447Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node447 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node447 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node447 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node447 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node447 (EqualityPatterns.family3.label 1) = PairSemantics.raw5159 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node447 PairSemantics.raw5159; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5159 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node447 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node447 (EqualityPatterns.family3.label 2) = PairSemantics.raw8986 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node447 PairSemantics.raw8986; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8986 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node447 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value231 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node447 (EqualityPatterns.family3.label 3) = PairSemantics.raw5110 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node447 PairSemantics.raw5110; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5110 hH).trans (PairSemantics.sound231 hH)
  have hm4 : familyPairMoment B (groupedColumns node447 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value625 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node447 (EqualityPatterns.family3.label 4) = PairSemantics.raw3888 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node447 PairSemantics.raw3888; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3888 hH).trans (PairSemantics.sound625 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue447, PairSemantics.value0, PairSemantics.value46, PairSemantics.value231, PairSemantics.value625, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue448 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (5 / 432)), (2, (5 / 108)), (3, (-20 / 27)), (4, (-10 / 27)), (5, (-5 / 72)), (7, (-5 / 18)), (12, (-5 / 27)), (23, (5 / 18)), (24, (5 / 9)), (27, (5 / 24))]

theorem singlePair448 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node448 node448Labels = Sparse.eval singlePairValue448 (familyPairVector B) := by
  have hp := single_label_three B hB node448
  have hl : node448Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node448 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node448 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node448 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node448 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node448 (EqualityPatterns.family3.label 1) = PairSemantics.raw5164 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node448 PairSemantics.raw5164; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5164 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node448 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node448 (EqualityPatterns.family3.label 2) = PairSemantics.raw8982 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node448 PairSemantics.raw8982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8982 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node448 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value716 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node448 (EqualityPatterns.family3.label 3) = PairSemantics.raw5109 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node448 PairSemantics.raw5109; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5109 hH).trans (PairSemantics.sound716 hH)
  have hm4 : familyPairMoment B (groupedColumns node448 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2120 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node448 (EqualityPatterns.family3.label 4) = PairSemantics.raw3889 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node448 PairSemantics.raw3889; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3889 hH).trans (PairSemantics.sound2120 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue448, PairSemantics.value0, PairSemantics.value11, PairSemantics.value716, PairSemantics.value2120, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue449 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (5 / 36)), (2, (-5 / 432)), (3, (5 / 27)), (5, (5 / 216)), (7, (5 / 54)), (12, (5 / 54)), (23, (-5 / 18)), (27, (-5 / 72))]

theorem singlePair449 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node449 node449Labels = Sparse.eval singlePairValue449 (familyPairVector B) := by
  have hp := single_label_three B hB node449
  have hl : node449Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node449 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node449 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node449 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node449 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node449 (EqualityPatterns.family3.label 1) = PairSemantics.raw5165 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node449 PairSemantics.raw5165; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5165 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node449 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node449 (EqualityPatterns.family3.label 2) = PairSemantics.raw8981 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node449 PairSemantics.raw8981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8981 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node449 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value231 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node449 (EqualityPatterns.family3.label 3) = PairSemantics.raw5110 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node449 PairSemantics.raw5110; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5110 hH).trans (PairSemantics.sound231 hH)
  have hm4 : familyPairMoment B (groupedColumns node449 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value641 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node449 (EqualityPatterns.family3.label 4) = PairSemantics.raw3890 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node449 PairSemantics.raw3890; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3890 hH).trans (PairSemantics.sound641 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue449, PairSemantics.value0, PairSemantics.value4, PairSemantics.value11, PairSemantics.value231, PairSemantics.value641, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue450 : Sparse (Fin 909) := [(0, (13 / 288)), (1, (-35 / 288)), (2, (-5 / 432)), (3, (5 / 27)), (4, (5 / 54)), (5, (5 / 216)), (7, (5 / 54)), (24, (-5 / 18)), (27, (-5 / 72))]

theorem singlePair450 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node450 node450Labels = Sparse.eval singlePairValue450 (familyPairVector B) := by
  have hp := single_label_three B hB node450
  have hl : node450Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node450 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node450 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node450 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node450 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node450 (EqualityPatterns.family3.label 1) = PairSemantics.raw5167 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node450 PairSemantics.raw5167; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5167 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node450 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node450 (EqualityPatterns.family3.label 2) = PairSemantics.raw8978 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node450 PairSemantics.raw8978; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8978 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node450 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value231 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node450 (EqualityPatterns.family3.label 3) = PairSemantics.raw5110 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node450 PairSemantics.raw5110; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5110 hH).trans (PairSemantics.sound231 hH)
  have hm4 : familyPairMoment B (groupedColumns node450 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value646 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node450 (EqualityPatterns.family3.label 4) = PairSemantics.raw3891 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node450 PairSemantics.raw3891; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3891 hH).trans (PairSemantics.sound646 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue450, PairSemantics.value0, PairSemantics.value11, PairSemantics.value231, PairSemantics.value646, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue451 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 18)), (23, (5 / 9)), (27, (5 / 36))]

theorem singlePair451 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node451 node451Labels = Sparse.eval singlePairValue451 (familyPairVector B) := by
  have hp := single_label_three B hB node451
  have hl : node451Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node451 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node451 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node451 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node451 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node451 (EqualityPatterns.family3.label 1) = PairSemantics.raw5169 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node451 PairSemantics.raw5169; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5169 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node451 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node451 (EqualityPatterns.family3.label 2) = PairSemantics.raw8987 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node451 PairSemantics.raw8987; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8987 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node451 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value45 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node451 (EqualityPatterns.family3.label 3) = PairSemantics.raw5116 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node451 PairSemantics.raw5116; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5116 hH).trans (PairSemantics.sound45 hH)
  have hm4 : familyPairMoment B (groupedColumns node451 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value197 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node451 (EqualityPatterns.family3.label 4) = PairSemantics.raw3892 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node451 PairSemantics.raw3892; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3892 hH).trans (PairSemantics.sound197 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue451, PairSemantics.value0, PairSemantics.value4, PairSemantics.value45, PairSemantics.value197, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue452 : Sparse (Fin 909) := [(0, (1 / 24)), (1, (-5 / 72)), (24, (5 / 9)), (27, (5 / 36))]

theorem singlePair452 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node452 node452Labels = Sparse.eval singlePairValue452 (familyPairVector B) := by
  have hp := single_label_three B hB node452
  have hl : node452Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node452 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node452 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node452 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node452 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node452 (EqualityPatterns.family3.label 1) = PairSemantics.raw5177 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node452 PairSemantics.raw5177; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5177 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node452 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node452 (EqualityPatterns.family3.label 2) = PairSemantics.raw8979 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node452 PairSemantics.raw8979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8979 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node452 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value45 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node452 (EqualityPatterns.family3.label 3) = PairSemantics.raw5116 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node452 PairSemantics.raw5116; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5116 hH).trans (PairSemantics.sound45 hH)
  have hm4 : familyPairMoment B (groupedColumns node452 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value202 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node452 (EqualityPatterns.family3.label 4) = PairSemantics.raw3893 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node452 PairSemantics.raw3893; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3893 hH).trans (PairSemantics.sound202 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue452, PairSemantics.value0, PairSemantics.value11, PairSemantics.value45, PairSemantics.value202, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue453 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 54)), (2, (-5 / 48)), (3, (-5 / 27)), (4, (-5 / 27)), (5, (5 / 72)), (8, (-5 / 27)), (24, (5 / 9)), (27, (-5 / 24)), (30, (5 / 18)), (56, (5 / 18))]

theorem singlePair453 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node453 node453Labels = Sparse.eval singlePairValue453 (familyPairVector B) := by
  have hp := single_label_three B hB node453
  have hl : node453Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node453 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node453 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node453 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node453 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node453 (EqualityPatterns.family3.label 1) = PairSemantics.raw5127 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node453 PairSemantics.raw5127; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5127 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node453 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node453 (EqualityPatterns.family3.label 2) = PairSemantics.raw9044 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node453 PairSemantics.raw9044; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9044 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node453 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value231 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node453 (EqualityPatterns.family3.label 3) = PairSemantics.raw5119 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node453 PairSemantics.raw5119; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5119 hH).trans (PairSemantics.sound231 hH)
  have hm4 : familyPairMoment B (groupedColumns node453 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2652 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node453 (EqualityPatterns.family3.label 4) = PairSemantics.raw3908 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node453 PairSemantics.raw3908; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3908 hH).trans (PairSemantics.sound2652 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue453, PairSemantics.value0, PairSemantics.value65, PairSemantics.value231, PairSemantics.value232, PairSemantics.value2652, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue454 : Sparse (Fin 909) := [(0, (7 / 144)), (1, (5 / 216)), (2, (-5 / 96)), (3, (-25 / 54)), (4, (-5 / 54)), (5, (-5 / 216)), (6, (5 / 864)), (12, (-5 / 27)), (13, (-5 / 54)), (31, (5 / 18)), (51, (5 / 18)), (52, (-5 / 54))]

theorem singlePair454 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node454 node454Labels = Sparse.eval singlePairValue454 (familyPairVector B) := by
  have hp := single_label_three B hB node454
  have hl : node454Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node454 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node454 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node454 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node454 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node454 (EqualityPatterns.family3.label 1) = PairSemantics.raw5124 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node454 PairSemantics.raw5124; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5124 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node454 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node454 (EqualityPatterns.family3.label 2) = PairSemantics.raw9050 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node454 PairSemantics.raw9050; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9050 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node454 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value717 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node454 (EqualityPatterns.family3.label 3) = PairSemantics.raw5120 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node454 PairSemantics.raw5120; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5120 hH).trans (PairSemantics.sound717 hH)
  have hm4 : familyPairMoment B (groupedColumns node454 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2661 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node454 (EqualityPatterns.family3.label 4) = PairSemantics.raw3909 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node454 PairSemantics.raw3909; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3909 hH).trans (PairSemantics.sound2661 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue454, PairSemantics.value0, PairSemantics.value46, PairSemantics.value65, PairSemantics.value717, PairSemantics.value2661, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue455 : Sparse (Fin 909) := [(0, (1 / 24)), (1, (65 / 864)), (2, (-5 / 432)), (3, (-35 / 54)), (4, (-5 / 18)), (5, (-5 / 108)), (6, (5 / 864)), (12, (-5 / 18)), (13, (-5 / 18)), (26, (-5 / 54)), (27, (5 / 72)), (35, (-5 / 54)), (51, (5 / 18)), (52, (-5 / 54)), (55, (5 / 18))]

theorem singlePair455 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node455 node455Labels = Sparse.eval singlePairValue455 (familyPairVector B) := by
  have hp := single_label_three B hB node455
  have hl : node455Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node455 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node455 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node455 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node455 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node455 (EqualityPatterns.family3.label 1) = PairSemantics.raw5129 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node455 PairSemantics.raw5129; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5129 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node455 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node455 (EqualityPatterns.family3.label 2) = PairSemantics.raw9047 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node455 PairSemantics.raw9047; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9047 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node455 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value717 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node455 (EqualityPatterns.family3.label 3) = PairSemantics.raw5120 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node455 PairSemantics.raw5120; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5120 hH).trans (PairSemantics.sound717 hH)
  have hm4 : familyPairMoment B (groupedColumns node455 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2138 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node455 (EqualityPatterns.family3.label 4) = PairSemantics.raw3910 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node455 PairSemantics.raw3910; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3910 hH).trans (PairSemantics.sound2138 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue455, PairSemantics.value0, PairSemantics.value11, PairSemantics.value46, PairSemantics.value717, PairSemantics.value2138, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue456 : Sparse (Fin 909) := [(0, (37 / 864)), (1, (-5 / 432)), (2, (5 / 216)), (3, (-5 / 6)), (4, (-10 / 27)), (5, (-5 / 108)), (6, (5 / 864)), (7, (-5 / 54)), (12, (-5 / 27)), (23, (5 / 18)), (25, (5 / 9)), (26, (-10 / 27)), (27, (5 / 72)), (35, (-5 / 54)), (54, (5 / 18))]

theorem singlePair456 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node456 node456Labels = Sparse.eval singlePairValue456 (familyPairVector B) := by
  have hp := single_label_three B hB node456
  have hl : node456Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node456 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node456 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node456 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node456 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node456 (EqualityPatterns.family3.label 1) = PairSemantics.raw5134 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node456 PairSemantics.raw5134; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5134 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node456 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node456 (EqualityPatterns.family3.label 2) = PairSemantics.raw9040 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node456 PairSemantics.raw9040; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9040 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node456 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value717 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node456 (EqualityPatterns.family3.label 3) = PairSemantics.raw5120 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node456 PairSemantics.raw5120; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5120 hH).trans (PairSemantics.sound717 hH)
  have hm4 : familyPairMoment B (groupedColumns node456 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2300 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node456 (EqualityPatterns.family3.label 4) = PairSemantics.raw3911 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node456 PairSemantics.raw3911; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3911 hH).trans (PairSemantics.sound2300 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue456, PairSemantics.value0, PairSemantics.value11, PairSemantics.value46, PairSemantics.value717, PairSemantics.value2300, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
