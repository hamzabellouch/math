import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleRules
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical279
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical280
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical282
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound5

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue184 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 72)), (2, (-5 / 144)), (5, (5 / 216)), (27, (-5 / 72)), (68, (-5 / 36)), (263, (5 / 9))]

theorem singlePair184 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node184 node184Labels = Sparse.eval singlePairValue184 (familyPairVector B) := by
  have hp := single_label_three B hB node184
  have hl : node184Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node184 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node184 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node184 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node184 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node184 (EqualityPatterns.family3.label 1) = PairSemantics.raw897 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node184 PairSemantics.raw897; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical897 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node184 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node184 (EqualityPatterns.family3.label 2) = PairSemantics.raw8964 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node184 PairSemantics.raw8964; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8964 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node184 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value117 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node184 (EqualityPatterns.family3.label 3) = PairSemantics.raw849 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node184 PairSemantics.raw849; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical849 hH).trans (PairSemantics.sound117 hH)
  have hm4 : familyPairMoment B (groupedColumns node184 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value329 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node184 (EqualityPatterns.family3.label 4) = PairSemantics.raw389 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node184 PairSemantics.raw389; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical389 hH).trans (PairSemantics.sound329 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue184, PairSemantics.value0, PairSemantics.value10, PairSemantics.value46, PairSemantics.value117, PairSemantics.value329, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue185 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 36)), (2, (5 / 36)), (68, (5 / 36)), (196, (5 / 9))]

theorem singlePair185 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node185 node185Labels = Sparse.eval singlePairValue185 (familyPairVector B) := by
  have hp := single_label_three B hB node185
  have hl : node185Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node185 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node185 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node185 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node185 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node185 (EqualityPatterns.family3.label 1) = PairSemantics.raw887 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node185 PairSemantics.raw887; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical887 hH).trans (PairSemantics.sound3 hH)
  have hm2 : familyPairMoment B (groupedColumns node185 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node185 (EqualityPatterns.family3.label 2) = PairSemantics.raw8987 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node185 PairSemantics.raw8987; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8987 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node185 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value23 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node185 (EqualityPatterns.family3.label 3) = PairSemantics.raw852 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node185 PairSemantics.raw852; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical852 hH).trans (PairSemantics.sound23 hH)
  have hm4 : familyPairMoment B (groupedColumns node185 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value192 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node185 (EqualityPatterns.family3.label 4) = PairSemantics.raw390 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node185 PairSemantics.raw390; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical390 hH).trans (PairSemantics.sound192 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue185, PairSemantics.value0, PairSemantics.value3, PairSemantics.value4, PairSemantics.value23, PairSemantics.value192, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue186 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 72)), (2, (-5 / 144)), (68, (5 / 36)), (197, (5 / 9))]

theorem singlePair186 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node186 node186Labels = Sparse.eval singlePairValue186 (familyPairVector B) := by
  have hp := single_label_three B hB node186
  have hl : node186Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node186 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node186 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node186 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node186 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node186 (EqualityPatterns.family3.label 1) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node186 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node186 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node186 (EqualityPatterns.family3.label 2) = PairSemantics.raw8979 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node186 PairSemantics.raw8979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8979 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node186 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value23 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node186 (EqualityPatterns.family3.label 3) = PairSemantics.raw852 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node186 PairSemantics.raw852; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical852 hH).trans (PairSemantics.sound23 hH)
  have hm4 : familyPairMoment B (groupedColumns node186 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value196 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node186 (EqualityPatterns.family3.label 4) = PairSemantics.raw391 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node186 PairSemantics.raw391; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical391 hH).trans (PairSemantics.sound196 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue186, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value23, PairSemantics.value196, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue187 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 48)), (2, (-5 / 144)), (68, (5 / 36)), (125, (5 / 9))]

theorem singlePair187 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node187 node187Labels = Sparse.eval singlePairValue187 (familyPairVector B) := by
  have hp := single_label_three B hB node187
  have hl : node187Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node187 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node187 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node187 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node187 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node187 (EqualityPatterns.family3.label 1) = PairSemantics.raw898 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node187 PairSemantics.raw898; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical898 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node187 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node187 (EqualityPatterns.family3.label 2) = PairSemantics.raw8972 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node187 PairSemantics.raw8972; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8972 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node187 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value23 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node187 (EqualityPatterns.family3.label 3) = PairSemantics.raw852 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node187 PairSemantics.raw852; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical852 hH).trans (PairSemantics.sound23 hH)
  have hm4 : familyPairMoment B (groupedColumns node187 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value163 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node187 (EqualityPatterns.family3.label 4) = PairSemantics.raw392 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node187 PairSemantics.raw392; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical392 hH).trans (PairSemantics.sound163 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue187, PairSemantics.value0, PairSemantics.value4, PairSemantics.value10, PairSemantics.value23, PairSemantics.value163, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue188 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 144)), (2, (5 / 48)), (68, (5 / 36)), (264, (5 / 9))]

theorem singlePair188 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node188 node188Labels = Sparse.eval singlePairValue188 (familyPairVector B) := by
  have hp := single_label_three B hB node188
  have hl : node188Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node188 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node188 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node188 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node188 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node188 (EqualityPatterns.family3.label 1) = PairSemantics.raw901 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node188 PairSemantics.raw901; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical901 hH).trans (PairSemantics.sound3 hH)
  have hm2 : familyPairMoment B (groupedColumns node188 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node188 (EqualityPatterns.family3.label 2) = PairSemantics.raw8966 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node188 PairSemantics.raw8966; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8966 hH).trans (PairSemantics.sound10 hH)
  have hm3 : familyPairMoment B (groupedColumns node188 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value23 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node188 (EqualityPatterns.family3.label 3) = PairSemantics.raw852 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node188 PairSemantics.raw852; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical852 hH).trans (PairSemantics.sound23 hH)
  have hm4 : familyPairMoment B (groupedColumns node188 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value91 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node188 (EqualityPatterns.family3.label 4) = PairSemantics.raw393 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node188 PairSemantics.raw393; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical393 hH).trans (PairSemantics.sound91 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue188, PairSemantics.value0, PairSemantics.value3, PairSemantics.value10, PairSemantics.value23, PairSemantics.value91, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue189 : Sparse (Fin 909) := [(0, (19 / 864)), (1, (65 / 864)), (2, (25 / 288)), (3, (-5 / 18)), (5, (-5 / 36)), (6, (5 / 288)), (9, (-5 / 216)), (13, (-5 / 54)), (26, (-5 / 9)), (27, (5 / 24)), (34, (-5 / 18)), (35, (-5 / 18)), (54, (5 / 6)), (65, (5 / 6)), (67, (-5 / 18)), (68, (25 / 72)), (257, (-5 / 54)), (264, (5 / 9)), (266, (5 / 6))]

theorem singlePair189 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node189 node189Labels = Sparse.eval singlePairValue189 (familyPairVector B) := by
  have hp := single_label_three B hB node189
  have hl : node189Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node189 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node189 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node189 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node189 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node189 (EqualityPatterns.family3.label 1) = PairSemantics.raw904 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node189 PairSemantics.raw904; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical904 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node189 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node189 (EqualityPatterns.family3.label 2) = PairSemantics.raw8952 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node189 PairSemantics.raw8952; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8952 hH).trans (PairSemantics.sound26 hH)
  have hm3 : familyPairMoment B (groupedColumns node189 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value380 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node189 (EqualityPatterns.family3.label 3) = PairSemantics.raw847 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node189 PairSemantics.raw847; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical847 hH).trans (PairSemantics.sound380 hH)
  have hm4 : familyPairMoment B (groupedColumns node189 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1408 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node189 (EqualityPatterns.family3.label 4) = PairSemantics.raw394 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node189 PairSemantics.raw394; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical394 hH).trans (PairSemantics.sound1408 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue189, PairSemantics.value0, PairSemantics.value10, PairSemantics.value26, PairSemantics.value380, PairSemantics.value1408, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue190 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 432)), (2, (-5 / 144)), (5, (5 / 108)), (6, (-5 / 432)), (9, (5 / 216)), (26, (5 / 27)), (34, (5 / 54)), (35, (5 / 27)), (67, (5 / 27)), (68, (-5 / 72)), (257, (5 / 54)), (266, (-5 / 18))]

theorem singlePair190 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node190 node190Labels = Sparse.eval singlePairValue190 (familyPairVector B) := by
  have hp := single_label_three B hB node190
  have hl : node190Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node190 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node190 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node190 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node190 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node190 (EqualityPatterns.family3.label 1) = PairSemantics.raw906 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node190 PairSemantics.raw906; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical906 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node190 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node190 (EqualityPatterns.family3.label 2) = PairSemantics.raw8951 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node190 PairSemantics.raw8951; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8951 hH).trans (PairSemantics.sound26 hH)
  have hm3 : familyPairMoment B (groupedColumns node190 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value116 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node190 (EqualityPatterns.family3.label 3) = PairSemantics.raw848 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node190 PairSemantics.raw848; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical848 hH).trans (PairSemantics.sound116 hH)
  have hm4 : familyPairMoment B (groupedColumns node190 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value342 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node190 (EqualityPatterns.family3.label 4) = PairSemantics.raw395 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node190 PairSemantics.raw395; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical395 hH).trans (PairSemantics.sound342 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue190, PairSemantics.value0, PairSemantics.value10, PairSemantics.value26, PairSemantics.value116, PairSemantics.value342, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue191 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 108)), (2, (35 / 864)), (3, (-10 / 27)), (5, (-5 / 36)), (6, (5 / 288)), (9, (-5 / 216)), (12, (-5 / 27)), (13, (-5 / 9)), (26, (-5 / 27)), (27, (5 / 24)), (32, (-5 / 54)), (34, (-5 / 27)), (35, (-5 / 18)), (54, (5 / 18)), (55, (5 / 9)), (60, (-5 / 27)), (61, (5 / 9)), (65, (5 / 18)), (67, (-5 / 54)), (68, (25 / 72)), (257, (-5 / 54)), (264, (5 / 18)), (266, (5 / 9)), (268, (5 / 9))]

theorem singlePair191 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node191 node191Labels = Sparse.eval singlePairValue191 (familyPairVector B) := by
  have hp := single_label_three B hB node191
  have hl : node191Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node191 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node191 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node191 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node191 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node191 (EqualityPatterns.family3.label 1) = PairSemantics.raw908 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node191 PairSemantics.raw908; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical908 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node191 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node191 (EqualityPatterns.family3.label 2) = PairSemantics.raw8949 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node191 PairSemantics.raw8949; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8949 hH).trans (PairSemantics.sound10 hH)
  have hm3 : familyPairMoment B (groupedColumns node191 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value380 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node191 (EqualityPatterns.family3.label 3) = PairSemantics.raw847 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node191 PairSemantics.raw847; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical847 hH).trans (PairSemantics.sound380 hH)
  have hm4 : familyPairMoment B (groupedColumns node191 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1412 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node191 (EqualityPatterns.family3.label 4) = PairSemantics.raw396 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node191 PairSemantics.raw396; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical396 hH).trans (PairSemantics.sound1412 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue191, PairSemantics.value0, PairSemantics.value10, PairSemantics.value26, PairSemantics.value380, PairSemantics.value1412, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue192 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 288)), (2, (-5 / 288)), (3, (5 / 54)), (5, (5 / 108)), (6, (-5 / 432)), (9, (5 / 216)), (13, (5 / 54)), (26, (5 / 54)), (34, (5 / 54)), (35, (5 / 27)), (60, (5 / 54)), (67, (5 / 54)), (68, (-5 / 72)), (257, (5 / 54)), (268, (-5 / 18))]

theorem singlePair192 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node192 node192Labels = Sparse.eval singlePairValue192 (familyPairVector B) := by
  have hp := single_label_three B hB node192
  have hl : node192Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node192 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node192 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node192 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node192 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node192 (EqualityPatterns.family3.label 1) = PairSemantics.raw907 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node192 PairSemantics.raw907; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical907 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node192 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node192 (EqualityPatterns.family3.label 2) = PairSemantics.raw8950 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node192 PairSemantics.raw8950; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8950 hH).trans (PairSemantics.sound10 hH)
  have hm3 : familyPairMoment B (groupedColumns node192 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value116 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node192 (EqualityPatterns.family3.label 3) = PairSemantics.raw848 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node192 PairSemantics.raw848; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical848 hH).trans (PairSemantics.sound116 hH)
  have hm4 : familyPairMoment B (groupedColumns node192 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value348 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node192 (EqualityPatterns.family3.label 4) = PairSemantics.raw397 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node192 PairSemantics.raw397; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical397 hH).trans (PairSemantics.sound348 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue192, PairSemantics.value0, PairSemantics.value10, PairSemantics.value26, PairSemantics.value116, PairSemantics.value348, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue193 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-35 / 432)), (2, (-35 / 432)), (5, (5 / 216)), (27, (-5 / 72)), (54, (-5 / 18)), (65, (-5 / 18)), (68, (-5 / 36)), (264, (-5 / 18)), (266, (-5 / 18))]

theorem singlePair193 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node193 node193Labels = Sparse.eval singlePairValue193 (familyPairVector B) := by
  have hp := single_label_three B hB node193
  have hl : node193Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node193 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node193 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node193 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node193 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node193 (EqualityPatterns.family3.label 1) = PairSemantics.raw906 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node193 PairSemantics.raw906; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical906 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node193 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node193 (EqualityPatterns.family3.label 2) = PairSemantics.raw8954 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node193 PairSemantics.raw8954; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8954 hH).trans (PairSemantics.sound10 hH)
  have hm3 : familyPairMoment B (groupedColumns node193 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value117 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node193 (EqualityPatterns.family3.label 3) = PairSemantics.raw849 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node193 PairSemantics.raw849; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical849 hH).trans (PairSemantics.sound117 hH)
  have hm4 : familyPairMoment B (groupedColumns node193 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value344 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node193 (EqualityPatterns.family3.label 4) = PairSemantics.raw398 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node193 PairSemantics.raw398; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical398 hH).trans (PairSemantics.sound344 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue193, PairSemantics.value0, PairSemantics.value10, PairSemantics.value117, PairSemantics.value344, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue194 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 216)), (2, (5 / 36)), (5, (5 / 108)), (6, (-5 / 432)), (9, (5 / 216)), (13, (5 / 27)), (32, (5 / 54)), (35, (5 / 27)), (60, (5 / 27)), (68, (-5 / 72)), (257, (5 / 54)), (264, (-5 / 18))]

theorem singlePair194 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node194 node194Labels = Sparse.eval singlePairValue194 (familyPairVector B) := by
  have hp := single_label_three B hB node194
  have hl : node194Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node194 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node194 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node194 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node194 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node194 (EqualityPatterns.family3.label 1) = PairSemantics.raw915 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node194 PairSemantics.raw915; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical915 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node194 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node194 (EqualityPatterns.family3.label 2) = PairSemantics.raw8947 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node194 PairSemantics.raw8947; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8947 hH).trans (PairSemantics.sound3 hH)
  have hm3 : familyPairMoment B (groupedColumns node194 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value116 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node194 (EqualityPatterns.family3.label 3) = PairSemantics.raw848 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node194 PairSemantics.raw848; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical848 hH).trans (PairSemantics.sound116 hH)
  have hm4 : familyPairMoment B (groupedColumns node194 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value333 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node194 (EqualityPatterns.family3.label 4) = PairSemantics.raw399 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node194 PairSemantics.raw399; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical399 hH).trans (PairSemantics.sound333 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue194, PairSemantics.value0, PairSemantics.value3, PairSemantics.value26, PairSemantics.value116, PairSemantics.value333, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue195 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 432)), (2, (-5 / 216)), (5, (5 / 216)), (27, (-5 / 72)), (55, (-5 / 18)), (61, (-5 / 18)), (68, (-5 / 36)), (266, (-5 / 18)), (268, (-5 / 18))]

theorem singlePair195 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node195 node195Labels = Sparse.eval singlePairValue195 (familyPairVector B) := by
  have hp := single_label_three B hB node195
  have hl : node195Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node195 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node195 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node195 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node195 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node195 (EqualityPatterns.family3.label 1) = PairSemantics.raw912 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node195 PairSemantics.raw912; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical912 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node195 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node195 (EqualityPatterns.family3.label 2) = PairSemantics.raw8948 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node195 PairSemantics.raw8948; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8948 hH).trans (PairSemantics.sound10 hH)
  have hm3 : familyPairMoment B (groupedColumns node195 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value117 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node195 (EqualityPatterns.family3.label 3) = PairSemantics.raw849 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node195 PairSemantics.raw849; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical849 hH).trans (PairSemantics.sound117 hH)
  have hm4 : familyPairMoment B (groupedColumns node195 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value350 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node195 (EqualityPatterns.family3.label 4) = PairSemantics.raw400 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node195 PairSemantics.raw400; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical400 hH).trans (PairSemantics.sound350 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue195, PairSemantics.value0, PairSemantics.value10, PairSemantics.value26, PairSemantics.value117, PairSemantics.value350, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue196 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 72)), (2, (-5 / 72)), (68, (5 / 36)), (266, (5 / 9))]

theorem singlePair196 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node196 node196Labels = Sparse.eval singlePairValue196 (familyPairVector B) := by
  have hp := single_label_three B hB node196
  have hl : node196Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node196 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node196 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node196 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node196 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node196 (EqualityPatterns.family3.label 1) = PairSemantics.raw909 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node196 PairSemantics.raw909; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical909 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node196 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node196 (EqualityPatterns.family3.label 2) = PairSemantics.raw8955 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node196 PairSemantics.raw8955; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8955 hH).trans (PairSemantics.sound10 hH)
  have hm3 : familyPairMoment B (groupedColumns node196 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value23 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node196 (EqualityPatterns.family3.label 3) = PairSemantics.raw852 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node196 PairSemantics.raw852; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical852 hH).trans (PairSemantics.sound23 hH)
  have hm4 : familyPairMoment B (groupedColumns node196 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value96 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node196 (EqualityPatterns.family3.label 4) = PairSemantics.raw401 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node196 PairSemantics.raw401; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical401 hH).trans (PairSemantics.sound96 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue196, PairSemantics.value0, PairSemantics.value10, PairSemantics.value23, PairSemantics.value96, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue197 : Sparse (Fin 909) := [(0, (11 / 432)), (2, (-5 / 432)), (68, (5 / 36)), (268, (5 / 9))]

theorem singlePair197 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node197 node197Labels = Sparse.eval singlePairValue197 (familyPairVector B) := by
  have hp := single_label_three B hB node197
  have hl : node197Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node197 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node197 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node197 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node197 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node197 (EqualityPatterns.family3.label 1) = PairSemantics.raw914 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node197 PairSemantics.raw914; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical914 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node197 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node197 (EqualityPatterns.family3.label 2) = PairSemantics.raw8953 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node197 PairSemantics.raw8953; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8953 hH).trans (PairSemantics.sound10 hH)
  have hm3 : familyPairMoment B (groupedColumns node197 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value23 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node197 (EqualityPatterns.family3.label 3) = PairSemantics.raw852 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node197 PairSemantics.raw852; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical852 hH).trans (PairSemantics.sound23 hH)
  have hm4 : familyPairMoment B (groupedColumns node197 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value100 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node197 (EqualityPatterns.family3.label 4) = PairSemantics.raw402 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node197 PairSemantics.raw402; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical402 hH).trans (PairSemantics.sound100 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue197, PairSemantics.value0, PairSemantics.value10, PairSemantics.value23, PairSemantics.value26, PairSemantics.value100, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue198 : Sparse (Fin 909) := [(0, (7 / 144)), (1, (25 / 216)), (2, (-25 / 864)), (3, (-5 / 54)), (5, (5 / 36)), (6, (5 / 864)), (13, (-5 / 27)), (26, (-5 / 27)), (35, (-10 / 27)), (82, (-5 / 54))]

theorem singlePair198 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node198 node198Labels = Sparse.eval singlePairValue198 (familyPairVector B) := by
  have hp := single_label_three B hB node198
  have hl : node198Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node198 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node198 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node198 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node198 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node198 (EqualityPatterns.family3.label 1) = PairSemantics.raw865 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node198 PairSemantics.raw865; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical865 hH).trans (PairSemantics.sound118 hH)
  have hm2 : familyPairMoment B (groupedColumns node198 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node198 (EqualityPatterns.family3.label 2) = PairSemantics.raw9044 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node198 PairSemantics.raw9044; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9044 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node198 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node198 (EqualityPatterns.family3.label 3) = PairSemantics.raw857 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node198 PairSemantics.raw857; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical857 hH).trans (PairSemantics.sound24 hH)
  have hm4 : familyPairMoment B (groupedColumns node198 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2464 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node198 (EqualityPatterns.family3.label 4) = PairSemantics.raw403 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node198 PairSemantics.raw403; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical403 hH).trans (PairSemantics.sound2464 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue198, PairSemantics.value0, PairSemantics.value24, PairSemantics.value65, PairSemantics.value118, PairSemantics.value2464, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue199 : Sparse (Fin 909) := [(0, (41 / 864)), (1, (-25 / 144)), (2, (-55 / 432)), (3, (-10 / 27)), (5, (5 / 108)), (6, (5 / 288)), (12, (-5 / 54)), (13, (-5 / 9)), (35, (-5 / 27)), (52, (-10 / 27)), (82, (-5 / 54)), (128, (-5 / 27))]

theorem singlePair199 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node199 node199Labels = Sparse.eval singlePairValue199 (familyPairVector B) := by
  have hp := single_label_three B hB node199
  have hl : node199Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node199 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node199 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node199 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node199 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value383 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node199 (EqualityPatterns.family3.label 1) = PairSemantics.raw866 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node199 PairSemantics.raw866; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical866 hH).trans (PairSemantics.sound383 hH)
  have hm2 : familyPairMoment B (groupedColumns node199 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node199 (EqualityPatterns.family3.label 2) = PairSemantics.raw9043 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node199 PairSemantics.raw9043; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9043 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node199 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node199 (EqualityPatterns.family3.label 3) = PairSemantics.raw857 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node199 PairSemantics.raw857; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical857 hH).trans (PairSemantics.sound24 hH)
  have hm4 : familyPairMoment B (groupedColumns node199 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1887 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node199 (EqualityPatterns.family3.label 4) = PairSemantics.raw404 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node199 PairSemantics.raw404; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical404 hH).trans (PairSemantics.sound1887 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue199, PairSemantics.value0, PairSemantics.value11, PairSemantics.value24, PairSemantics.value383, PairSemantics.value1887, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
