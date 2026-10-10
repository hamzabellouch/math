import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleRules
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical162
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical238
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical239
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical240
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound8

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue392 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (5 / 144)), (2, (25 / 216)), (3, (-10 / 9)), (4, (-10 / 27)), (5, (-5 / 72)), (13, (-5 / 27)), (26, (-10 / 9)), (27, (5 / 24)), (34, (-20 / 27)), (65, (5 / 18)), (66, (5 / 9)), (67, (-5 / 18))]

theorem singlePair392 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node392 node392Labels = Sparse.eval singlePairValue392 (familyPairVector B) := by
  have hp := single_label_three B hB node392
  have hl : node392Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node392 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node392 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node392 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node392 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value716 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node392 (EqualityPatterns.family3.label 1) = PairSemantics.raw5200 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node392 PairSemantics.raw5200; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5200 hH).trans (PairSemantics.sound716 hH)
  have hm2 : familyPairMoment B (groupedColumns node392 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node392 (EqualityPatterns.family3.label 2) = PairSemantics.raw7665 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node392 PairSemantics.raw7665; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7665 hH).trans (PairSemantics.sound26 hH)
  have hm3 : familyPairMoment B (groupedColumns node392 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node392 (EqualityPatterns.family3.label 3) = PairSemantics.raw883 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node392 PairSemantics.raw883; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical883 hH).trans (PairSemantics.sound26 hH)
  have hm4 : familyPairMoment B (groupedColumns node392 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1433 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node392 (EqualityPatterns.family3.label 4) = PairSemantics.raw764 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node392 PairSemantics.raw764; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical764 hH).trans (PairSemantics.sound1433 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue392, PairSemantics.value0, PairSemantics.value26, PairSemantics.value716, PairSemantics.value1433, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue393 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 864)), (2, (-25 / 864)), (3, (5 / 27)), (5, (5 / 216)), (13, (5 / 54)), (26, (5 / 27)), (27, (-5 / 72)), (34, (5 / 27)), (65, (-5 / 18)), (67, (5 / 54))]

theorem singlePair393 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node393 node393Labels = Sparse.eval singlePairValue393 (familyPairVector B) := by
  have hp := single_label_three B hB node393
  have hl : node393Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node393 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node393 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node393 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node393 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value231 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node393 (EqualityPatterns.family3.label 1) = PairSemantics.raw5201 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node393 PairSemantics.raw5201; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5201 hH).trans (PairSemantics.sound231 hH)
  have hm2 : familyPairMoment B (groupedColumns node393 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node393 (EqualityPatterns.family3.label 2) = PairSemantics.raw7664 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node393 PairSemantics.raw7664; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7664 hH).trans (PairSemantics.sound26 hH)
  have hm3 : familyPairMoment B (groupedColumns node393 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node393 (EqualityPatterns.family3.label 3) = PairSemantics.raw884 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node393 PairSemantics.raw884; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical884 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node393 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value373 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node393 (EqualityPatterns.family3.label 4) = PairSemantics.raw765 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node393 PairSemantics.raw765; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical765 hH).trans (PairSemantics.sound373 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue393, PairSemantics.value0, PairSemantics.value10, PairSemantics.value26, PairSemantics.value231, PairSemantics.value373, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue394 : Sparse (Fin 909) := [(0, (1 / 432)), (1, (25 / 96)), (2, (-65 / 864)), (3, (-65 / 54)), (4, (-5 / 9)), (12, (-5 / 54)), (13, (-5 / 54)), (26, (-35 / 54)), (33, (5 / 18)), (34, (-5 / 27))]

theorem singlePair394 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node394 node394Labels = Sparse.eval singlePairValue394 (familyPairVector B) := by
  have hp := single_label_three B hB node394
  have hl : node394Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node394 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node394 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node394 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node394 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node394 (EqualityPatterns.family3.label 1) = PairSemantics.raw5202 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node394 PairSemantics.raw5202; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5202 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node394 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node394 (EqualityPatterns.family3.label 2) = PairSemantics.raw7662 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node394 PairSemantics.raw7662; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7662 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node394 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node394 (EqualityPatterns.family3.label 3) = PairSemantics.raw883 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node394 PairSemantics.raw883; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical883 hH).trans (PairSemantics.sound26 hH)
  have hm4 : familyPairMoment B (groupedColumns node394 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1434 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node394 (EqualityPatterns.family3.label 4) = PairSemantics.raw766 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node394 PairSemantics.raw766; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical766 hH).trans (PairSemantics.sound1434 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue394, PairSemantics.value0, PairSemantics.value26, PairSemantics.value232, PairSemantics.value1434, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue395 : Sparse (Fin 909) := [(0, (5 / 864)), (1, (5 / 108)), (2, (-5 / 288)), (3, (5 / 27)), (26, (5 / 54)), (33, (-5 / 18))]

theorem singlePair395 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node395 node395Labels = Sparse.eval singlePairValue395 (familyPairVector B) := by
  have hp := single_label_three B hB node395
  have hl : node395Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node395 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node395 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node395 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node395 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node395 (EqualityPatterns.family3.label 1) = PairSemantics.raw5203 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node395 PairSemantics.raw5203; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5203 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node395 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node395 (EqualityPatterns.family3.label 2) = PairSemantics.raw7661 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node395 PairSemantics.raw7661; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7661 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node395 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node395 (EqualityPatterns.family3.label 3) = PairSemantics.raw884 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node395 PairSemantics.raw884; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical884 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node395 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value374 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node395 (EqualityPatterns.family3.label 4) = PairSemantics.raw767 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node395 PairSemantics.raw767; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical767 hH).trans (PairSemantics.sound374 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue395, PairSemantics.value0, PairSemantics.value10, PairSemantics.value232, PairSemantics.value374, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue396 : Sparse (Fin 909) := [(0, (-5 / 216)), (1, (5 / 36)), (2, (-5 / 72)), (3, (-5 / 9)), (12, (-5 / 18)), (13, (-5 / 27))]

theorem singlePair396 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node396 node396Labels = Sparse.eval singlePairValue396 (familyPairVector B) := by
  have hp := single_label_three B hB node396
  have hl : node396Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node396 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node396 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node396 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node396 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node396 (EqualityPatterns.family3.label 1) = PairSemantics.raw5206 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node396 PairSemantics.raw5206; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5206 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node396 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value1323 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node396 (EqualityPatterns.family3.label 2) = PairSemantics.raw7658 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node396 PairSemantics.raw7658; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7658 hH).trans (PairSemantics.sound1323 hH)
  have hm3 : familyPairMoment B (groupedColumns node396 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node396 (EqualityPatterns.family3.label 3) = PairSemantics.raw883 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node396 PairSemantics.raw883; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical883 hH).trans (PairSemantics.sound26 hH)
  have hm4 : familyPairMoment B (groupedColumns node396 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1891 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node396 (EqualityPatterns.family3.label 4) = PairSemantics.raw768 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node396 PairSemantics.raw768; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical768 hH).trans (PairSemantics.sound1891 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue396, PairSemantics.value0, PairSemantics.value11, PairSemantics.value26, PairSemantics.value1323, PairSemantics.value1891, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue397 : Sparse (Fin 909) := [(0, (1 / 48)), (1, (-55 / 864)), (2, (-25 / 864)), (3, (5 / 27)), (12, (5 / 54)), (13, (5 / 54))]

theorem singlePair397 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node397 node397Labels = Sparse.eval singlePairValue397 (familyPairVector B) := by
  have hp := single_label_three B hB node397
  have hl : node397Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node397 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node397 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node397 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node397 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node397 (EqualityPatterns.family3.label 1) = PairSemantics.raw5205 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node397 PairSemantics.raw5205; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5205 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node397 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node397 (EqualityPatterns.family3.label 2) = PairSemantics.raw7659 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node397 PairSemantics.raw7659; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7659 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node397 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node397 (EqualityPatterns.family3.label 3) = PairSemantics.raw884 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node397 PairSemantics.raw884; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical884 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node397 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value573 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node397 (EqualityPatterns.family3.label 4) = PairSemantics.raw769 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node397 PairSemantics.raw769; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical769 hH).trans (PairSemantics.sound573 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue397, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value232, PairSemantics.value573, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue398 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 108)), (2, (-5 / 108)), (3, (5 / 54)), (5, (5 / 216)), (12, (5 / 54)), (13, (5 / 54)), (27, (-5 / 72)), (33, (-5 / 18)), (55, (-5 / 18)), (61, (-5 / 18))]

theorem singlePair398 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node398 node398Labels = Sparse.eval singlePairValue398 (familyPairVector B) := by
  have hp := single_label_three B hB node398
  have hl : node398Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node398 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node398 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node398 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node398 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node398 (EqualityPatterns.family3.label 1) = PairSemantics.raw5209 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node398 PairSemantics.raw5209; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5209 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node398 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value231 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node398 (EqualityPatterns.family3.label 2) = PairSemantics.raw7647 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node398 PairSemantics.raw7647; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7647 hH).trans (PairSemantics.sound231 hH)
  have hm3 : familyPairMoment B (groupedColumns node398 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node398 (EqualityPatterns.family3.label 3) = PairSemantics.raw884 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node398 PairSemantics.raw884; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical884 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node398 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value379 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node398 (EqualityPatterns.family3.label 4) = PairSemantics.raw772 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node398 PairSemantics.raw772; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical772 hH).trans (PairSemantics.sound379 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue398, PairSemantics.value0, PairSemantics.value10, PairSemantics.value46, PairSemantics.value231, PairSemantics.value379, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue399 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (35 / 432)), (2, (5 / 216)), (3, (5 / 27)), (4, (5 / 54)), (5, (5 / 216)), (26, (5 / 18)), (27, (-5 / 72)), (34, (5 / 27)), (66, (-5 / 18)), (67, (5 / 54))]

theorem singlePair399 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node399 node399Labels = Sparse.eval singlePairValue399 (familyPairVector B) := by
  have hp := single_label_three B hB node399
  have hl : node399Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node399 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node399 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node399 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node399 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value231 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node399 (EqualityPatterns.family3.label 1) = PairSemantics.raw5187 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node399 PairSemantics.raw5187; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5187 hH).trans (PairSemantics.sound231 hH)
  have hm2 : familyPairMoment B (groupedColumns node399 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node399 (EqualityPatterns.family3.label 2) = PairSemantics.raw7691 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node399 PairSemantics.raw7691; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7691 hH).trans (PairSemantics.sound26 hH)
  have hm3 : familyPairMoment B (groupedColumns node399 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node399 (EqualityPatterns.family3.label 3) = PairSemantics.raw893 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node399 PairSemantics.raw893; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical893 hH).trans (PairSemantics.sound26 hH)
  have hm4 : familyPairMoment B (groupedColumns node399 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value375 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node399 (EqualityPatterns.family3.label 4) = PairSemantics.raw773 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node399 PairSemantics.raw773; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical773 hH).trans (PairSemantics.sound375 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue399, PairSemantics.value0, PairSemantics.value26, PairSemantics.value231, PairSemantics.value375, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue400 : Sparse (Fin 909) := [(0, (11 / 864)), (1, (5 / 432)), (2, (25 / 864)), (3, (10 / 27)), (4, (5 / 27)), (26, (5 / 18)), (34, (5 / 54))]

theorem singlePair400 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node400 node400Labels = Sparse.eval singlePairValue400 (familyPairVector B) := by
  have hp := single_label_three B hB node400
  have hl : node400Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node400 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node400 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node400 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node400 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node400 (EqualityPatterns.family3.label 1) = PairSemantics.raw5189 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node400 PairSemantics.raw5189; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5189 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node400 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node400 (EqualityPatterns.family3.label 2) = PairSemantics.raw7688 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node400 PairSemantics.raw7688; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7688 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node400 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node400 (EqualityPatterns.family3.label 3) = PairSemantics.raw893 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node400 PairSemantics.raw893; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical893 hH).trans (PairSemantics.sound26 hH)
  have hm4 : familyPairMoment B (groupedColumns node400 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value376 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node400 (EqualityPatterns.family3.label 4) = PairSemantics.raw776 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node400 PairSemantics.raw776; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical776 hH).trans (PairSemantics.sound376 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue400, PairSemantics.value0, PairSemantics.value26, PairSemantics.value46, PairSemantics.value232, PairSemantics.value376, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue401 : Sparse (Fin 909) := [(0, (7 / 288)), (2, (25 / 864)), (3, (5 / 18)), (4, (5 / 27)), (26, (5 / 27))]

theorem singlePair401 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node401 node401Labels = Sparse.eval singlePairValue401 (familyPairVector B) := by
  have hp := single_label_three B hB node401
  have hl : node401Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node401 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node401 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node401 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node401 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node401 (EqualityPatterns.family3.label 1) = PairSemantics.raw5190 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node401 PairSemantics.raw5190; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5190 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node401 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node401 (EqualityPatterns.family3.label 2) = PairSemantics.raw7686 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node401 PairSemantics.raw7686; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7686 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node401 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node401 (EqualityPatterns.family3.label 3) = PairSemantics.raw893 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node401 PairSemantics.raw893; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical893 hH).trans (PairSemantics.sound26 hH)
  have hm4 : familyPairMoment B (groupedColumns node401 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value708 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node401 (EqualityPatterns.family3.label 4) = PairSemantics.raw777 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node401 PairSemantics.raw777; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical777 hH).trans (PairSemantics.sound708 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue401, PairSemantics.value0, PairSemantics.value11, PairSemantics.value26, PairSemantics.value232, PairSemantics.value708, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue402 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-25 / 432)), (2, (-5 / 144)), (3, (-5 / 27)), (26, (-5 / 27))]

theorem singlePair402 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node402 node402Labels = Sparse.eval singlePairValue402 (familyPairVector B) := by
  have hp := single_label_three B hB node402
  have hl : node402Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node402 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node402 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node402 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node402 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node402 (EqualityPatterns.family3.label 1) = PairSemantics.raw5192 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node402 PairSemantics.raw5192; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5192 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node402 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node402 (EqualityPatterns.family3.label 2) = PairSemantics.raw7685 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node402 PairSemantics.raw7685; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7685 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node402 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node402 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node402 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node402 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value226 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node402 (EqualityPatterns.family3.label 4) = PairSemantics.raw778 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node402 PairSemantics.raw778; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical778 hH).trans (PairSemantics.sound226 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue402, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value46, PairSemantics.value226, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue403 : Sparse (Fin 909) := [(0, (47 / 864)), (1, (-5 / 216)), (2, (55 / 864)), (3, (5 / 54))]

theorem singlePair403 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node403 node403Labels = Sparse.eval singlePairValue403 (familyPairVector B) := by
  have hp := single_label_three B hB node403
  have hl : node403Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node403 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node403 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node403 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node403 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node403 (EqualityPatterns.family3.label 1) = PairSemantics.raw5196 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node403 PairSemantics.raw5196; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5196 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node403 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node403 (EqualityPatterns.family3.label 2) = PairSemantics.raw7679 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node403 PairSemantics.raw7679; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7679 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node403 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node403 (EqualityPatterns.family3.label 3) = PairSemantics.raw893 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node403 PairSemantics.raw893; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical893 hH).trans (PairSemantics.sound26 hH)
  have hm4 : familyPairMoment B (groupedColumns node403 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value570 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node403 (EqualityPatterns.family3.label 4) = PairSemantics.raw780 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node403 PairSemantics.raw780; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical780 hH).trans (PairSemantics.sound570 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue403, PairSemantics.value0, PairSemantics.value11, PairSemantics.value26, PairSemantics.value65, PairSemantics.value570, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue404 : Sparse (Fin 909) := [(0, (1 / 18)), (1, (-5 / 72)), (2, (-5 / 72))]

theorem singlePair404 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node404 node404Labels = Sparse.eval singlePairValue404 (familyPairVector B) := by
  have hp := single_label_three B hB node404
  have hl : node404Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node404 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 1) = PairSemantics.raw5197 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node404 PairSemantics.raw5197; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5197 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 2) = PairSemantics.raw7678 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node404 PairSemantics.raw7678; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7678 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node404 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value181 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 4) = PairSemantics.raw781 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node404 PairSemantics.raw781; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical781 hH).trans (PairSemantics.sound181 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue404, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value65, PairSemantics.value181, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue405 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-5 / 54)), (2, (-25 / 432)), (3, (-5 / 27))]

theorem singlePair405 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node405 node405Labels = Sparse.eval singlePairValue405 (familyPairVector B) := by
  have hp := single_label_three B hB node405
  have hl : node405Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node405 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 1) = PairSemantics.raw5204 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node405 PairSemantics.raw5204; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5204 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 2) = PairSemantics.raw7671 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node405 PairSemantics.raw7671; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7671 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node405 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value185 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 4) = PairSemantics.raw782 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node405 PairSemantics.raw782; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical782 hH).trans (PairSemantics.sound185 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue405, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value185, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue406 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 216)), (3, (-5 / 27)), (26, (-5 / 27)), (34, (-5 / 27))]

theorem singlePair406 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node406 node406Labels = Sparse.eval singlePairValue406 (familyPairVector B) := by
  have hp := single_label_three B hB node406
  have hl : node406Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node406 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node406 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node406 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node406 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node406 (EqualityPatterns.family3.label 1) = PairSemantics.raw5208 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node406 PairSemantics.raw5208; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5208 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node406 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node406 (EqualityPatterns.family3.label 2) = PairSemantics.raw7663 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node406 PairSemantics.raw7663; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7663 hH).trans (PairSemantics.sound26 hH)
  have hm3 : familyPairMoment B (groupedColumns node406 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node406 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node406 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node406 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value109 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node406 (EqualityPatterns.family3.label 4) = PairSemantics.raw783 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node406 PairSemantics.raw783; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical783 hH).trans (PairSemantics.sound109 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue406, PairSemantics.value0, PairSemantics.value10, PairSemantics.value26, PairSemantics.value46, PairSemantics.value109, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue407 : Sparse (Fin 909) := [(0, (1 / 24)), (2, (5 / 24))]

theorem singlePair407 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node407 node407Labels = Sparse.eval singlePairValue407 (familyPairVector B) := by
  have hp := single_label_three B hB node407
  have hl : node407Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node407 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node407 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node407 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node407 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node407 (EqualityPatterns.family3.label 1) = PairSemantics.raw5199 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node407 PairSemantics.raw5199; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5199 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node407 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node407 (EqualityPatterns.family3.label 2) = PairSemantics.raw7683 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node407 PairSemantics.raw7683; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7683 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node407 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node407 (EqualityPatterns.family3.label 3) = PairSemantics.raw900 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node407 PairSemantics.raw900; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical900 hH).trans (PairSemantics.sound3 hH)
  have hm4 : familyPairMoment B (groupedColumns node407 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value63 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node407 (EqualityPatterns.family3.label 4) = PairSemantics.raw784 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node407 PairSemantics.raw784; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical784 hH).trans (PairSemantics.sound63 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue407, PairSemantics.value0, PairSemantics.value3, PairSemantics.value11, PairSemantics.value63, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
