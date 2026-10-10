import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleRules
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical122
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical160
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical161
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical281
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical282
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound43

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue457 : Sparse (Fin 909) := [(0, (23 / 864)), (1, (35 / 216)), (2, (-5 / 216)), (3, (-35 / 54)), (4, (-10 / 27)), (5, (-5 / 108)), (6, (5 / 864)), (7, (-5 / 54)), (12, (-5 / 27)), (13, (-5 / 54)), (24, (5 / 18)), (26, (-5 / 27)), (27, (5 / 72)), (35, (-5 / 54)), (56, (5 / 18))]

theorem singlePair457 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node457 node457Labels = Sparse.eval singlePairValue457 (familyPairVector B) := by
  have hp := single_label_three B hB node457
  have hl : node457Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node457 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node457 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node457 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node457 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node457 (EqualityPatterns.family3.label 1) = PairSemantics.raw5135 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node457 PairSemantics.raw5135; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5135 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node457 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node457 (EqualityPatterns.family3.label 2) = PairSemantics.raw9038 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node457 PairSemantics.raw9038; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9038 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node457 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value717 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node457 (EqualityPatterns.family3.label 3) = PairSemantics.raw5120 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node457 PairSemantics.raw5120; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5120 hH).trans (PairSemantics.sound717 hH)
  have hm4 : familyPairMoment B (groupedColumns node457 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2299 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node457 (EqualityPatterns.family3.label 4) = PairSemantics.raw3912 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node457 PairSemantics.raw3912; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3912 hH).trans (PairSemantics.sound2299 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue457, PairSemantics.value0, PairSemantics.value11, PairSemantics.value232, PairSemantics.value717, PairSemantics.value2299, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue458 : Sparse (Fin 909) := [(0, (37 / 864)), (1, (25 / 432)), (3, (-20 / 27)), (4, (-5 / 27)), (5, (-5 / 108)), (6, (5 / 864)), (12, (-25 / 54)), (13, (-5 / 27)), (23, (5 / 18)), (25, (5 / 9)), (27, (5 / 72)), (31, (5 / 18)), (33, (10 / 9)), (54, (5 / 9)), (62, (5 / 18))]

theorem singlePair458 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node458 node458Labels = Sparse.eval singlePairValue458 (familyPairVector B) := by
  have hp := single_label_three B hB node458
  have hl : node458Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node458 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node458 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node458 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node458 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node458 (EqualityPatterns.family3.label 1) = PairSemantics.raw5137 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node458 PairSemantics.raw5137; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5137 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node458 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node458 (EqualityPatterns.family3.label 2) = PairSemantics.raw9037 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node458 PairSemantics.raw9037; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9037 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node458 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value717 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node458 (EqualityPatterns.family3.label 3) = PairSemantics.raw5120 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node458 PairSemantics.raw5120; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5120 hH).trans (PairSemantics.sound717 hH)
  have hm4 : familyPairMoment B (groupedColumns node458 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2093 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node458 (EqualityPatterns.family3.label 4) = PairSemantics.raw3913 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node458 PairSemantics.raw3913; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3913 hH).trans (PairSemantics.sound2093 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue458, PairSemantics.value0, PairSemantics.value46, PairSemantics.value717, PairSemantics.value2093, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue459 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (155 / 864)), (2, (-5 / 216)), (3, (-5 / 27)), (5, (-5 / 108)), (6, (5 / 864)), (7, (-5 / 54)), (12, (-5 / 54)), (13, (-5 / 18)), (23, (5 / 18)), (25, (5 / 18)), (27, (5 / 72)), (35, (-5 / 54)), (54, (5 / 18))]

theorem singlePair459 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node459 node459Labels = Sparse.eval singlePairValue459 (familyPairVector B) := by
  have hp := single_label_three B hB node459
  have hl : node459Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node459 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node459 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node459 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node459 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node459 (EqualityPatterns.family3.label 1) = PairSemantics.raw5140 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node459 PairSemantics.raw5140; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5140 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node459 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node459 (EqualityPatterns.family3.label 2) = PairSemantics.raw9035 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node459 PairSemantics.raw9035; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9035 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node459 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value717 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node459 (EqualityPatterns.family3.label 3) = PairSemantics.raw5120 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node459 PairSemantics.raw5120; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5120 hH).trans (PairSemantics.sound717 hH)
  have hm4 : familyPairMoment B (groupedColumns node459 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2126 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node459 (EqualityPatterns.family3.label 4) = PairSemantics.raw3914 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node459 PairSemantics.raw3914; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3914 hH).trans (PairSemantics.sound2126 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue459, PairSemantics.value0, PairSemantics.value4, PairSemantics.value232, PairSemantics.value717, PairSemantics.value2126, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue460 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 216)), (2, (-5 / 144)), (3, (5 / 27)), (4, (5 / 27)), (5, (5 / 216)), (24, (-5 / 18)), (27, (-5 / 72)), (56, (-5 / 18))]

theorem singlePair460 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node460 node460Labels = Sparse.eval singlePairValue460 (familyPairVector B) := by
  have hp := single_label_three B hB node460
  have hl : node460Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node460 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node460 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node460 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node460 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node460 (EqualityPatterns.family3.label 1) = PairSemantics.raw5139 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node460 PairSemantics.raw5139; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5139 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node460 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node460 (EqualityPatterns.family3.label 2) = PairSemantics.raw9039 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node460 PairSemantics.raw9039; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9039 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node460 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value231 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node460 (EqualityPatterns.family3.label 3) = PairSemantics.raw5122 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node460 PairSemantics.raw5122; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5122 hH).trans (PairSemantics.sound231 hH)
  have hm4 : familyPairMoment B (groupedColumns node460 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value703 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node460 (EqualityPatterns.family3.label 4) = PairSemantics.raw3915 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node460 PairSemantics.raw3915; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3915 hH).trans (PairSemantics.sound703 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue460, PairSemantics.value0, PairSemantics.value11, PairSemantics.value231, PairSemantics.value232, PairSemantics.value703, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue461 : Sparse (Fin 909) := [(0, (-1 / 216)), (1, (95 / 864)), (2, (-25 / 864)), (3, (-10 / 27)), (4, (-5 / 27)), (12, (-5 / 27)), (13, (-5 / 54))]

theorem singlePair461 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node461 node461Labels = Sparse.eval singlePairValue461 (familyPairVector B) := by
  have hp := single_label_three B hB node461
  have hl : node461Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node461 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node461 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node461 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node461 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node461 (EqualityPatterns.family3.label 1) = PairSemantics.raw5138 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node461 PairSemantics.raw5138; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5138 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node461 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node461 (EqualityPatterns.family3.label 2) = PairSemantics.raw9044 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node461 PairSemantics.raw9044; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9044 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node461 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node461 (EqualityPatterns.family3.label 3) = PairSemantics.raw5123 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node461 PairSemantics.raw5123; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5123 hH).trans (PairSemantics.sound46 hH)
  have hm4 : familyPairMoment B (groupedColumns node461 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2662 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node461 (EqualityPatterns.family3.label 4) = PairSemantics.raw3920 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node461 PairSemantics.raw3920; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3920 hH).trans (PairSemantics.sound2662 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue461, PairSemantics.value0, PairSemantics.value46, PairSemantics.value65, PairSemantics.value232, PairSemantics.value2662, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue462 : Sparse (Fin 909) := [(0, (1 / 108)), (1, (145 / 864)), (2, (-35 / 864)), (3, (-20 / 27)), (4, (-5 / 27)), (12, (-10 / 27)), (13, (-5 / 18))]

theorem singlePair462 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node462 node462Labels = Sparse.eval singlePairValue462 (familyPairVector B) := by
  have hp := single_label_three B hB node462
  have hl : node462Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node462 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node462 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node462 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node462 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node462 (EqualityPatterns.family3.label 1) = PairSemantics.raw5140 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node462 PairSemantics.raw5140; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5140 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node462 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node462 (EqualityPatterns.family3.label 2) = PairSemantics.raw9043 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node462 PairSemantics.raw9043; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9043 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node462 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node462 (EqualityPatterns.family3.label 3) = PairSemantics.raw5123 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node462 PairSemantics.raw5123; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5123 hH).trans (PairSemantics.sound46 hH)
  have hm4 : familyPairMoment B (groupedColumns node462 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2139 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node462 (EqualityPatterns.family3.label 4) = PairSemantics.raw3921 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node462 PairSemantics.raw3921; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3921 hH).trans (PairSemantics.sound2139 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue462, PairSemantics.value0, PairSemantics.value11, PairSemantics.value46, PairSemantics.value232, PairSemantics.value2139, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue463 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (5 / 48)), (3, (-10 / 9)), (4, (-5 / 27)), (12, (-5 / 9)), (13, (-10 / 9)), (32, (-5 / 54))]

theorem singlePair463 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node463 node463Labels = Sparse.eval singlePairValue463 (familyPairVector B) := by
  have hp := single_label_three B hB node463
  have hl : node463Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node463 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node463 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node463 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node463 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node463 (EqualityPatterns.family3.label 1) = PairSemantics.raw5143 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node463 PairSemantics.raw5143; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5143 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node463 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node463 (EqualityPatterns.family3.label 2) = PairSemantics.raw9042 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node463 PairSemantics.raw9042; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9042 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node463 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node463 (EqualityPatterns.family3.label 3) = PairSemantics.raw5123 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node463 PairSemantics.raw5123; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5123 hH).trans (PairSemantics.sound46 hH)
  have hm4 : familyPairMoment B (groupedColumns node463 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2094 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node463 (EqualityPatterns.family3.label 4) = PairSemantics.raw3922 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node463 PairSemantics.raw3922; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3922 hH).trans (PairSemantics.sound2094 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue463, PairSemantics.value0, PairSemantics.value46, PairSemantics.value2094, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue464 : Sparse (Fin 909) := []

theorem singlePair464 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node464 node464Labels = Sparse.eval singlePairValue464 (familyPairVector B) := by
  have hp := single_label_three B hB node464
  have hl : node464Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node464 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node464 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node464 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node464 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node464 (EqualityPatterns.family3.label 1) = PairSemantics.raw5135 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node464 PairSemantics.raw5135; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5135 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node464 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value5 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node464 (EqualityPatterns.family3.label 2) = PairSemantics.raw9052 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node464 PairSemantics.raw9052; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9052 hH).trans (PairSemantics.sound5 hH)
  have hm3 : familyPairMoment B (groupedColumns node464 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node464 (EqualityPatterns.family3.label 3) = PairSemantics.raw5127 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node464 PairSemantics.raw5127; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5127 hH).trans (PairSemantics.sound232 hH)
  have hm4 : familyPairMoment B (groupedColumns node464 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2801 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node464 (EqualityPatterns.family3.label 4) = PairSemantics.raw3923 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node464 PairSemantics.raw3923; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3923 hH).trans (PairSemantics.sound2801 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue464, PairSemantics.value0, PairSemantics.value5, PairSemantics.value232, PairSemantics.value2801, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue465 : Sparse (Fin 909) := []

theorem singlePair465 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node465 node465Labels = Sparse.eval singlePairValue465 (familyPairVector B) := by
  have hp := single_label_three B hB node465
  have hl : node465Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node465 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node465 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node465 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node465 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node465 (EqualityPatterns.family3.label 1) = PairSemantics.raw5136 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node465 PairSemantics.raw5136; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5136 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node465 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value5 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node465 (EqualityPatterns.family3.label 2) = PairSemantics.raw9051 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node465 PairSemantics.raw9051; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9051 hH).trans (PairSemantics.sound5 hH)
  have hm3 : familyPairMoment B (groupedColumns node465 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node465 (EqualityPatterns.family3.label 3) = PairSemantics.raw5128 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node465 PairSemantics.raw5128; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5128 hH).trans (PairSemantics.sound46 hH)
  have hm4 : familyPairMoment B (groupedColumns node465 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1292 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node465 (EqualityPatterns.family3.label 4) = PairSemantics.raw3924 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node465 PairSemantics.raw3924; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3924 hH).trans (PairSemantics.sound1292 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue465, PairSemantics.value0, PairSemantics.value5, PairSemantics.value46, PairSemantics.value1292, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue466 : Sparse (Fin 909) := []

theorem singlePair466 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node466 node466Labels = Sparse.eval singlePairValue466 (familyPairVector B) := by
  have hp := single_label_three B hB node466
  have hl : node466Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node466 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node466 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node466 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node466 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node466 (EqualityPatterns.family3.label 1) = PairSemantics.raw5139 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node466 PairSemantics.raw5139; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5139 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node466 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value5 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node466 (EqualityPatterns.family3.label 2) = PairSemantics.raw9048 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node466 PairSemantics.raw9048; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9048 hH).trans (PairSemantics.sound5 hH)
  have hm3 : familyPairMoment B (groupedColumns node466 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node466 (EqualityPatterns.family3.label 3) = PairSemantics.raw5128 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node466 PairSemantics.raw5128; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5128 hH).trans (PairSemantics.sound46 hH)
  have hm4 : familyPairMoment B (groupedColumns node466 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1152 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node466 (EqualityPatterns.family3.label 4) = PairSemantics.raw3925 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node466 PairSemantics.raw3925; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3925 hH).trans (PairSemantics.sound1152 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue466, PairSemantics.value0, PairSemantics.value5, PairSemantics.value46, PairSemantics.value232, PairSemantics.value1152, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue467 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 36)), (2, (5 / 144)), (3, (5 / 18)), (4, (5 / 54)), (12, (5 / 27)), (13, (5 / 54))]

theorem singlePair467 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node467 node467Labels = Sparse.eval singlePairValue467 (familyPairVector B) := by
  have hp := single_label_three B hB node467
  have hl : node467Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node467 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node467 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node467 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node467 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node467 (EqualityPatterns.family3.label 1) = PairSemantics.raw5142 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node467 PairSemantics.raw5142; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5142 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node467 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node467 (EqualityPatterns.family3.label 2) = PairSemantics.raw9045 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node467 PairSemantics.raw9045; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9045 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node467 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node467 (EqualityPatterns.family3.label 3) = PairSemantics.raw5128 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node467 PairSemantics.raw5128; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5128 hH).trans (PairSemantics.sound46 hH)
  have hm4 : familyPairMoment B (groupedColumns node467 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value670 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node467 (EqualityPatterns.family3.label 4) = PairSemantics.raw3926 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node467 PairSemantics.raw3926; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3926 hH).trans (PairSemantics.sound670 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue467, PairSemantics.value0, PairSemantics.value11, PairSemantics.value46, PairSemantics.value670, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue468 : Sparse (Fin 909) := [(0, (1 / 48)), (1, (25 / 432)), (2, (5 / 216)), (3, (5 / 27)), (13, (5 / 27))]

theorem singlePair468 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node468 node468Labels = Sparse.eval singlePairValue468 (familyPairVector B) := by
  have hp := single_label_three B hB node468
  have hl : node468Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node468 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node468 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node468 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node468 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node468 (EqualityPatterns.family3.label 1) = PairSemantics.raw5150 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node468 PairSemantics.raw5150; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5150 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node468 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node468 (EqualityPatterns.family3.label 2) = PairSemantics.raw9036 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node468 PairSemantics.raw9036; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9036 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node468 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node468 (EqualityPatterns.family3.label 3) = PairSemantics.raw5128 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node468 PairSemantics.raw5128; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5128 hH).trans (PairSemantics.sound46 hH)
  have hm4 : familyPairMoment B (groupedColumns node468 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value656 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node468 (EqualityPatterns.family3.label 4) = PairSemantics.raw3928 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node468 PairSemantics.raw3928; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3928 hH).trans (PairSemantics.sound656 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue468, PairSemantics.value0, PairSemantics.value4, PairSemantics.value46, PairSemantics.value656, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue469 : Sparse (Fin 909) := []

theorem singlePair469 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node469 node469Labels = Sparse.eval singlePairValue469 (familyPairVector B) := by
  have hp := single_label_three B hB node469
  have hl : node469Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node469 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node469 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node469 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node469 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node469 (EqualityPatterns.family3.label 1) = PairSemantics.raw5149 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node469 PairSemantics.raw5149; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5149 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node469 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value5 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node469 (EqualityPatterns.family3.label 2) = PairSemantics.raw9049 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node469 PairSemantics.raw9049; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9049 hH).trans (PairSemantics.sound5 hH)
  have hm3 : familyPairMoment B (groupedColumns node469 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node469 (EqualityPatterns.family3.label 3) = PairSemantics.raw5141 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node469 PairSemantics.raw5141; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5141 hH).trans (PairSemantics.sound46 hH)
  have hm4 : familyPairMoment B (groupedColumns node469 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value288 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node469 (EqualityPatterns.family3.label 4) = PairSemantics.raw3931 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node469 PairSemantics.raw3931; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3931 hH).trans (PairSemantics.sound288 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue469, PairSemantics.value0, PairSemantics.value5, PairSemantics.value46, PairSemantics.value288, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue470 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (35 / 288)), (2, (-25 / 432)), (3, (-5 / 6)), (4, (-5 / 18)), (5, (-5 / 108)), (6, (5 / 864)), (12, (-10 / 27)), (26, (-5 / 27)), (27, (5 / 72)), (33, (5 / 6)), (81, (5 / 18)), (195, (-5 / 9))]

theorem singlePair470 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node470 node470Labels = Sparse.eval singlePairValue470 (familyPairVector B) := by
  have hp := single_label_three B hB node470
  have hl : node470Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node470 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node470 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node470 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node470 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node470 (EqualityPatterns.family3.label 1) = PairSemantics.raw5162 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node470 PairSemantics.raw5162; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5162 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node470 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node470 (EqualityPatterns.family3.label 2) = PairSemantics.raw9014 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node470 PairSemantics.raw9014; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9014 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node470 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value717 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node470 (EqualityPatterns.family3.label 3) = PairSemantics.raw5120 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node470 PairSemantics.raw5120; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5120 hH).trans (PairSemantics.sound717 hH)
  have hm4 : familyPairMoment B (groupedColumns node470 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2102 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node470 (EqualityPatterns.family3.label 4) = PairSemantics.raw3932 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node470 PairSemantics.raw3932; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3932 hH).trans (PairSemantics.sound2102 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue470, PairSemantics.value0, PairSemantics.value46, PairSemantics.value232, PairSemantics.value717, PairSemantics.value2102, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue471 : Sparse (Fin 909) := [(0, (43 / 864)), (1, (55 / 216)), (2, (5 / 216)), (3, (-10 / 27)), (5, (-5 / 216)), (6, (5 / 864)), (7, (-5 / 27)), (12, (-5 / 27)), (23, (5 / 18)), (27, (5 / 72))]

theorem singlePair471 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node471 node471Labels = Sparse.eval singlePairValue471 (familyPairVector B) := by
  have hp := single_label_three B hB node471
  have hl : node471Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node471 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node471 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node471 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node471 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node471 (EqualityPatterns.family3.label 1) = PairSemantics.raw5163 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node471 PairSemantics.raw5163; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5163 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node471 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node471 (EqualityPatterns.family3.label 2) = PairSemantics.raw9012 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node471 PairSemantics.raw9012; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9012 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node471 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value717 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node471 (EqualityPatterns.family3.label 3) = PairSemantics.raw5120 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node471 PairSemantics.raw5120; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5120 hH).trans (PairSemantics.sound717 hH)
  have hm4 : familyPairMoment B (groupedColumns node471 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2125 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node471 (EqualityPatterns.family3.label 4) = PairSemantics.raw3933 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node471 PairSemantics.raw3933; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3933 hH).trans (PairSemantics.sound2125 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue471, PairSemantics.value0, PairSemantics.value4, PairSemantics.value65, PairSemantics.value717, PairSemantics.value2125, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue472 : Sparse (Fin 909) := [(0, (23 / 432)), (1, (-5 / 216)), (2, (-5 / 96)), (3, (-5 / 18)), (4, (-5 / 27)), (5, (-5 / 216)), (6, (5 / 864)), (7, (-5 / 54)), (8, (-5 / 54)), (24, (5 / 18)), (27, (5 / 72))]

theorem singlePair472 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node472 node472Labels = Sparse.eval singlePairValue472 (familyPairVector B) := by
  have hp := single_label_three B hB node472
  have hl : node472Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node472 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node472 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node472 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node472 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node472 (EqualityPatterns.family3.label 1) = PairSemantics.raw5164 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node472 PairSemantics.raw5164; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5164 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node472 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node472 (EqualityPatterns.family3.label 2) = PairSemantics.raw9010 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node472 PairSemantics.raw9010; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9010 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node472 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value717 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node472 (EqualityPatterns.family3.label 3) = PairSemantics.raw5120 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node472 PairSemantics.raw5120; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5120 hH).trans (PairSemantics.sound717 hH)
  have hm4 : familyPairMoment B (groupedColumns node472 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2129 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node472 (EqualityPatterns.family3.label 4) = PairSemantics.raw3934 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node472 PairSemantics.raw3934; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3934 hH).trans (PairSemantics.sound2129 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue472, PairSemantics.value0, PairSemantics.value11, PairSemantics.value65, PairSemantics.value717, PairSemantics.value2129, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
