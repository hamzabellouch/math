import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleRules
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical160
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical161
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical238
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical239
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical279
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical280
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical281
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical282
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound8

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue264 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 72)), (2, (5 / 72)), (13, (-10 / 27)), (32, (-5 / 27))]

theorem singlePair264 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node264 node264Labels = Sparse.eval singlePairValue264 (familyPairVector B) := by
  have hp := single_label_three B hB node264
  have hl : node264Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node264 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node264 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node264 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node264 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node264 (EqualityPatterns.family3.label 1) = PairSemantics.raw918 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node264 PairSemantics.raw918; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical918 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node264 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node264 (EqualityPatterns.family3.label 2) = PairSemantics.raw9000 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node264 PairSemantics.raw9000; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9000 hH).trans (PairSemantics.sound10 hH)
  have hm3 : familyPairMoment B (groupedColumns node264 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node264 (EqualityPatterns.family3.label 3) = PairSemantics.raw887 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node264 PairSemantics.raw887; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical887 hH).trans (PairSemantics.sound3 hH)
  have hm4 : familyPairMoment B (groupedColumns node264 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value93 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node264 (EqualityPatterns.family3.label 4) = PairSemantics.raw527 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node264 PairSemantics.raw527; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical527 hH).trans (PairSemantics.sound93 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue264, PairSemantics.value0, PairSemantics.value3, PairSemantics.value10, PairSemantics.value93, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue265 : Sparse (Fin 909) := []

theorem singlePair265 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node265 node265Labels = Sparse.eval singlePairValue265 (familyPairVector B) := by
  have hp := single_label_three B hB node265
  have hl : node265Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node265 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node265 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node265 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node265 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node265 (EqualityPatterns.family3.label 1) = PairSemantics.raw907 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node265 PairSemantics.raw907; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical907 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node265 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value5 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node265 (EqualityPatterns.family3.label 2) = PairSemantics.raw9028 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node265 PairSemantics.raw9028; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9028 hH).trans (PairSemantics.sound5 hH)
  have hm3 : familyPairMoment B (groupedColumns node265 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node265 (EqualityPatterns.family3.label 3) = PairSemantics.raw893 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node265 PairSemantics.raw893; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical893 hH).trans (PairSemantics.sound26 hH)
  have hm4 : familyPairMoment B (groupedColumns node265 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1293 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node265 (EqualityPatterns.family3.label 4) = PairSemantics.raw535 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node265 PairSemantics.raw535; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical535 hH).trans (PairSemantics.sound1293 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue265, PairSemantics.value0, PairSemantics.value5, PairSemantics.value26, PairSemantics.value1293, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue266 : Sparse (Fin 909) := []

theorem singlePair266 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node266 node266Labels = Sparse.eval singlePairValue266 (familyPairVector B) := by
  have hp := single_label_three B hB node266
  have hl : node266Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node266 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node266 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node266 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node266 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node266 (EqualityPatterns.family3.label 1) = PairSemantics.raw909 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node266 PairSemantics.raw909; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical909 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node266 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value5 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node266 (EqualityPatterns.family3.label 2) = PairSemantics.raw9027 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node266 PairSemantics.raw9027; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9027 hH).trans (PairSemantics.sound5 hH)
  have hm3 : familyPairMoment B (groupedColumns node266 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node266 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node266 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node266 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value292 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node266 (EqualityPatterns.family3.label 4) = PairSemantics.raw536 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node266 PairSemantics.raw536; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical536 hH).trans (PairSemantics.sound292 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue266, PairSemantics.value0, PairSemantics.value5, PairSemantics.value10, PairSemantics.value292, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue267 : Sparse (Fin 909) := []

theorem singlePair267 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node267 node267Labels = Sparse.eval singlePairValue267 (familyPairVector B) := by
  have hp := single_label_three B hB node267
  have hl : node267Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node267 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node267 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node267 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node267 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node267 (EqualityPatterns.family3.label 1) = PairSemantics.raw914 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node267 PairSemantics.raw914; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical914 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node267 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value5 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node267 (EqualityPatterns.family3.label 2) = PairSemantics.raw9020 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node267 PairSemantics.raw9020; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9020 hH).trans (PairSemantics.sound5 hH)
  have hm3 : familyPairMoment B (groupedColumns node267 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node267 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node267 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node267 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value285 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node267 (EqualityPatterns.family3.label 4) = PairSemantics.raw537 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node267 PairSemantics.raw537; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical537 hH).trans (PairSemantics.sound285 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue267, PairSemantics.value0, PairSemantics.value5, PairSemantics.value10, PairSemantics.value26, PairSemantics.value285, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue268 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-55 / 432)), (2, (-5 / 54)), (3, (-5 / 27)), (13, (-5 / 27))]

theorem singlePair268 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node268 node268Labels = Sparse.eval singlePairValue268 (familyPairVector B) := by
  have hp := single_label_three B hB node268
  have hl : node268Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node268 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node268 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node268 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node268 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node268 (EqualityPatterns.family3.label 1) = PairSemantics.raw918 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node268 PairSemantics.raw918; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical918 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node268 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node268 (EqualityPatterns.family3.label 2) = PairSemantics.raw9013 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node268 PairSemantics.raw9013; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9013 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node268 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node268 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node268 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node268 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value215 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node268 (EqualityPatterns.family3.label 4) = PairSemantics.raw538 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node268 PairSemantics.raw538; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical538 hH).trans (PairSemantics.sound215 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue268, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value215, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue269 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 72)), (2, (-5 / 72)), (12, (-5 / 27)), (13, (-10 / 27))]

theorem singlePair269 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node269 node269Labels = Sparse.eval singlePairValue269 (familyPairVector B) := by
  have hp := single_label_three B hB node269
  have hl : node269Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node269 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node269 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node269 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node269 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node269 (EqualityPatterns.family3.label 1) = PairSemantics.raw925 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node269 PairSemantics.raw925; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical925 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node269 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node269 (EqualityPatterns.family3.label 2) = PairSemantics.raw8972 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node269 PairSemantics.raw8972; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8972 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node269 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node269 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node269 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node269 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value204 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node269 (EqualityPatterns.family3.label 4) = PairSemantics.raw553 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node269 PairSemantics.raw553; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical553 hH).trans (PairSemantics.sound204 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue269, PairSemantics.value0, PairSemantics.value4, PairSemantics.value10, PairSemantics.value204, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue270 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 48)), (2, (5 / 48)), (13, (5 / 9))]

theorem singlePair270 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node270 node270Labels = Sparse.eval singlePairValue270 (familyPairVector B) := by
  have hp := single_label_three B hB node270
  have hl : node270Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node270 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node270 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node270 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node270 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node270 (EqualityPatterns.family3.label 1) = PairSemantics.raw924 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node270 PairSemantics.raw924; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical924 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node270 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node270 (EqualityPatterns.family3.label 2) = PairSemantics.raw8985 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node270 PairSemantics.raw8985; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8985 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node270 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node270 (EqualityPatterns.family3.label 3) = PairSemantics.raw900 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node270 PairSemantics.raw900; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical900 hH).trans (PairSemantics.sound3 hH)
  have hm4 : familyPairMoment B (groupedColumns node270 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value37 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node270 (EqualityPatterns.family3.label 4) = PairSemantics.raw556 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node270 PairSemantics.raw556; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical556 hH).trans (PairSemantics.sound37 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue270, PairSemantics.value0, PairSemantics.value3, PairSemantics.value4, PairSemantics.value10, PairSemantics.value37, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue271 : Sparse (Fin 909) := [(0, (1 / 36)), (2, (5 / 12)), (32, (5 / 9))]

theorem singlePair271 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node271 node271Labels = Sparse.eval singlePairValue271 (familyPairVector B) := by
  have hp := single_label_three B hB node271
  have hl : node271Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node271 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node271 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node271 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node271 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node271 (EqualityPatterns.family3.label 1) = PairSemantics.raw927 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node271 PairSemantics.raw927; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical927 hH).trans (PairSemantics.sound3 hH)
  have hm2 : familyPairMoment B (groupedColumns node271 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node271 (EqualityPatterns.family3.label 2) = PairSemantics.raw8956 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node271 PairSemantics.raw8956; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8956 hH).trans (PairSemantics.sound3 hH)
  have hm3 : familyPairMoment B (groupedColumns node271 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node271 (EqualityPatterns.family3.label 3) = PairSemantics.raw900 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node271 PairSemantics.raw900; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical900 hH).trans (PairSemantics.sound3 hH)
  have hm4 : familyPairMoment B (groupedColumns node271 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value19 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node271 (EqualityPatterns.family3.label 4) = PairSemantics.raw565 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node271 PairSemantics.raw565; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical565 hH).trans (PairSemantics.sound19 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue271, PairSemantics.value0, PairSemantics.value3, PairSemantics.value19, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue272 : Sparse (Fin 909) := []

theorem singlePair272 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node272 node272Labels = Sparse.eval singlePairValue272 (familyPairVector B) := by
  have hp := single_label_three B hB node272
  have hl : node272Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node272 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node272 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node272 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node272 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node272 (EqualityPatterns.family3.label 1) = PairSemantics.raw924 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node272 PairSemantics.raw924; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical924 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node272 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value5 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node272 (EqualityPatterns.family3.label 2) = PairSemantics.raw9021 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node272 PairSemantics.raw9021; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9021 hH).trans (PairSemantics.sound5 hH)
  have hm3 : familyPairMoment B (groupedColumns node272 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node272 (EqualityPatterns.family3.label 3) = PairSemantics.raw917 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node272 PairSemantics.raw917; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical917 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node272 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value63 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node272 (EqualityPatterns.family3.label 4) = PairSemantics.raw580 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node272 PairSemantics.raw580; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical580 hH).trans (PairSemantics.sound63 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue272, PairSemantics.value0, PairSemantics.value5, PairSemantics.value10, PairSemantics.value63, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue273 : Sparse (Fin 909) := [(0, (17 / 432)), (1, (-25 / 864)), (2, (5 / 216)), (6, (-5 / 864)), (8, (5 / 54)), (9, (5 / 216)), (68, (-5 / 72)), (71, (5 / 54)), (236, (-5 / 18))]

theorem singlePair273 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node273 node273Labels = Sparse.eval singlePairValue273 (familyPairVector B) := by
  have hp := single_label_three B hB node273
  have hl : node273Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node273 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node273 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node273 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node273 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node273 (EqualityPatterns.family3.label 1) = PairSemantics.raw5128 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node273 PairSemantics.raw5128; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5128 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node273 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node273 (EqualityPatterns.family3.label 2) = PairSemantics.raw7677 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node273 PairSemantics.raw7677; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7677 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node273 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value116 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node273 (EqualityPatterns.family3.label 3) = PairSemantics.raw848 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node273 PairSemantics.raw848; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical848 hH).trans (PairSemantics.sound116 hH)
  have hm4 : familyPairMoment B (groupedColumns node273 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value855 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node273 (EqualityPatterns.family3.label 4) = PairSemantics.raw597 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node273 PairSemantics.raw597; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical597 hH).trans (PairSemantics.sound855 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue273, PairSemantics.value0, PairSemantics.value46, PairSemantics.value65, PairSemantics.value116, PairSemantics.value855, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue274 : Sparse (Fin 909) := [(0, (19 / 864)), (1, (35 / 864)), (2, (5 / 216)), (6, (-5 / 432)), (8, (5 / 27)), (9, (5 / 216)), (68, (-5 / 72)), (71, (5 / 54)), (126, (-5 / 18))]

theorem singlePair274 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node274 node274Labels = Sparse.eval singlePairValue274 (familyPairVector B) := by
  have hp := single_label_three B hB node274
  have hl : node274Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node274 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node274 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node274 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node274 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node274 (EqualityPatterns.family3.label 1) = PairSemantics.raw5139 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node274 PairSemantics.raw5139; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5139 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node274 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node274 (EqualityPatterns.family3.label 2) = PairSemantics.raw7669 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node274 PairSemantics.raw7669; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7669 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node274 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value116 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node274 (EqualityPatterns.family3.label 3) = PairSemantics.raw848 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node274 PairSemantics.raw848; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical848 hH).trans (PairSemantics.sound116 hH)
  have hm4 : familyPairMoment B (groupedColumns node274 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value554 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node274 (EqualityPatterns.family3.label 4) = PairSemantics.raw600 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node274 PairSemantics.raw600; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical600 hH).trans (PairSemantics.sound554 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue274, PairSemantics.value0, PairSemantics.value11, PairSemantics.value116, PairSemantics.value232, PairSemantics.value554, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue275 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-25 / 288)), (2, (5 / 864)), (3, (5 / 54)), (5, (5 / 216)), (7, (5 / 54)), (24, (-5 / 18)), (27, (-5 / 72)), (68, (-5 / 36)), (126, (-5 / 18)), (197, (-5 / 18))]

theorem singlePair275 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node275 node275Labels = Sparse.eval singlePairValue275 (familyPairVector B) := by
  have hp := single_label_three B hB node275
  have hl : node275Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node275 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node275 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node275 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node275 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node275 (EqualityPatterns.family3.label 1) = PairSemantics.raw5136 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node275 PairSemantics.raw5136; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5136 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node275 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node275 (EqualityPatterns.family3.label 2) = PairSemantics.raw7672 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node275 PairSemantics.raw7672; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7672 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node275 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value117 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node275 (EqualityPatterns.family3.label 3) = PairSemantics.raw849 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node275 PairSemantics.raw849; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical849 hH).trans (PairSemantics.sound117 hH)
  have hm4 : familyPairMoment B (groupedColumns node275 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value640 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node275 (EqualityPatterns.family3.label 4) = PairSemantics.raw601 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node275 PairSemantics.raw601; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical601 hH).trans (PairSemantics.sound640 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue275, PairSemantics.value0, PairSemantics.value11, PairSemantics.value46, PairSemantics.value117, PairSemantics.value640, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue276 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (25 / 432)), (2, (-5 / 432)), (5, (5 / 216)), (8, (5 / 54)), (27, (-5 / 72)), (30, (-5 / 18)), (68, (-5 / 36)), (236, (-5 / 9))]

theorem singlePair276 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node276 node276Labels = Sparse.eval singlePairValue276 (familyPairVector B) := by
  have hp := single_label_three B hB node276
  have hl : node276Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node276 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node276 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node276 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node276 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node276 (EqualityPatterns.family3.label 1) = PairSemantics.raw5139 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node276 PairSemantics.raw5139; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5139 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node276 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node276 (EqualityPatterns.family3.label 2) = PairSemantics.raw7670 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node276 PairSemantics.raw7670; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7670 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node276 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value117 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node276 (EqualityPatterns.family3.label 3) = PairSemantics.raw849 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node276 PairSemantics.raw849; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical849 hH).trans (PairSemantics.sound117 hH)
  have hm4 : familyPairMoment B (groupedColumns node276 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value856 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node276 (EqualityPatterns.family3.label 4) = PairSemantics.raw602 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node276 PairSemantics.raw602; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical602 hH).trans (PairSemantics.sound856 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue276, PairSemantics.value0, PairSemantics.value65, PairSemantics.value117, PairSemantics.value232, PairSemantics.value856, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue277 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-25 / 432)), (2, (5 / 432)), (68, (5 / 36)), (126, (5 / 9))]

theorem singlePair277 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node277 node277Labels = Sparse.eval singlePairValue277 (familyPairVector B) := by
  have hp := single_label_three B hB node277
  have hl : node277Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node277 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node277 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node277 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node277 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node277 (EqualityPatterns.family3.label 1) = PairSemantics.raw5149 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node277 PairSemantics.raw5149; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5149 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node277 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node277 (EqualityPatterns.family3.label 2) = PairSemantics.raw7671 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node277 PairSemantics.raw7671; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7671 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node277 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value23 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node277 (EqualityPatterns.family3.label 3) = PairSemantics.raw852 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node277 PairSemantics.raw852; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical852 hH).trans (PairSemantics.sound23 hH)
  have hm4 : familyPairMoment B (groupedColumns node277 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value167 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node277 (EqualityPatterns.family3.label 4) = PairSemantics.raw603 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node277 PairSemantics.raw603; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical603 hH).trans (PairSemantics.sound167 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue277, PairSemantics.value0, PairSemantics.value11, PairSemantics.value23, PairSemantics.value46, PairSemantics.value167, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue278 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (-5 / 432)), (2, (-5 / 864)), (3, (-5 / 27)), (5, (5 / 216)), (7, (-5 / 27)), (23, (5 / 9)), (24, (5 / 18)), (27, (-5 / 36)), (51, (5 / 18)), (54, (5 / 18)), (55, (5 / 18)), (64, (5 / 18)), (68, (-5 / 36)), (124, (5 / 9)), (125, (5 / 6)), (126, (5 / 9)), (196, (5 / 18)), (197, (5 / 18)), (266, (5 / 18))]

theorem singlePair278 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node278 node278Labels = Sparse.eval singlePairValue278 (familyPairVector B) := by
  have hp := single_label_three B hB node278
  have hl : node278Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node278 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node278 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node278 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node278 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node278 (EqualityPatterns.family3.label 1) = PairSemantics.raw5155 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node278 PairSemantics.raw5155; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5155 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node278 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node278 (EqualityPatterns.family3.label 2) = PairSemantics.raw7632 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node278 PairSemantics.raw7632; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7632 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node278 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value117 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node278 (EqualityPatterns.family3.label 3) = PairSemantics.raw845 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node278 PairSemantics.raw845; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical845 hH).trans (PairSemantics.sound117 hH)
  have hm4 : familyPairMoment B (groupedColumns node278 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1857 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node278 (EqualityPatterns.family3.label 4) = PairSemantics.raw604 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node278 PairSemantics.raw604; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical604 hH).trans (PairSemantics.sound1857 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue278, PairSemantics.value0, PairSemantics.value46, PairSemantics.value117, PairSemantics.value1857, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue279 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 108)), (2, (5 / 216)), (68, (5 / 36)), (125, (-5 / 9)), (126, (-5 / 9))]

theorem singlePair279 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node279 node279Labels = Sparse.eval singlePairValue279 (familyPairVector B) := by
  have hp := single_label_three B hB node279
  have hl : node279Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node279 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node279 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node279 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node279 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node279 (EqualityPatterns.family3.label 1) = PairSemantics.raw5159 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node279 PairSemantics.raw5159; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5159 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node279 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node279 (EqualityPatterns.family3.label 2) = PairSemantics.raw7631 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node279 PairSemantics.raw7631; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7631 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node279 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value23 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node279 (EqualityPatterns.family3.label 3) = PairSemantics.raw846 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node279 PairSemantics.raw846; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical846 hH).trans (PairSemantics.sound23 hH)
  have hm4 : familyPairMoment B (groupedColumns node279 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value530 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node279 (EqualityPatterns.family3.label 4) = PairSemantics.raw605 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node279 PairSemantics.raw605; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical605 hH).trans (PairSemantics.sound530 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue279, PairSemantics.value0, PairSemantics.value23, PairSemantics.value46, PairSemantics.value530, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
