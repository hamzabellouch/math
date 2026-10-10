import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleRules
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical123
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical124
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical128
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical129
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical160
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical161
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical162
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical280
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical281
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical282
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound9

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue489 : Sparse (Fin 909) := [(0, (1 / 18)), (1, (-35 / 864)), (2, (25 / 864)), (3, (5 / 54)), (4, (5 / 54))]

theorem singlePair489 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node489 node489Labels = Sparse.eval singlePairValue489 (familyPairVector B) := by
  have hp := single_label_three B hB node489
  have hl : node489Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node489 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node489 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node489 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node489 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node489 (EqualityPatterns.family3.label 1) = PairSemantics.raw5175 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node489 PairSemantics.raw5175; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5175 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node489 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node489 (EqualityPatterns.family3.label 2) = PairSemantics.raw9011 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node489 PairSemantics.raw9011; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9011 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node489 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node489 (EqualityPatterns.family3.label 3) = PairSemantics.raw5128 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node489 PairSemantics.raw5128; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5128 hH).trans (PairSemantics.sound46 hH)
  have hm4 : familyPairMoment B (groupedColumns node489 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value659 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node489 (EqualityPatterns.family3.label 4) = PairSemantics.raw3954 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node489 PairSemantics.raw3954; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3954 hH).trans (PairSemantics.sound659 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue489, PairSemantics.value0, PairSemantics.value11, PairSemantics.value46, PairSemantics.value65, PairSemantics.value659, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue490 : Sparse (Fin 909) := [(0, (1 / 24)), (1, (-5 / 27)), (2, (5 / 216)), (3, (5 / 27)), (12, (5 / 27))]

theorem singlePair490 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node490 node490Labels = Sparse.eval singlePairValue490 (familyPairVector B) := by
  have hp := single_label_three B hB node490
  have hl : node490Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node490 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node490 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node490 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node490 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node490 (EqualityPatterns.family3.label 1) = PairSemantics.raw5179 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node490 PairSemantics.raw5179; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5179 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node490 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node490 (EqualityPatterns.family3.label 2) = PairSemantics.raw9008 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node490 PairSemantics.raw9008; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9008 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node490 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node490 (EqualityPatterns.family3.label 3) = PairSemantics.raw5128 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node490 PairSemantics.raw5128; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5128 hH).trans (PairSemantics.sound46 hH)
  have hm4 : familyPairMoment B (groupedColumns node490 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value661 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node490 (EqualityPatterns.family3.label 4) = PairSemantics.raw3955 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node490 PairSemantics.raw3955; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3955 hH).trans (PairSemantics.sound661 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue490, PairSemantics.value0, PairSemantics.value11, PairSemantics.value46, PairSemantics.value661, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue491 : Sparse (Fin 909) := [(0, (1 / 54)), (1, (-5 / 48)), (2, (5 / 144)), (3, (5 / 27)), (12, (5 / 27)), (33, (-5 / 9))]

theorem singlePair491 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node491 node491Labels = Sparse.eval singlePairValue491 (familyPairVector B) := by
  have hp := single_label_three B hB node491
  have hl : node491Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node491 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node491 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node491 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node491 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node491 (EqualityPatterns.family3.label 1) = PairSemantics.raw5184 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node491 PairSemantics.raw5184; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5184 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node491 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node491 (EqualityPatterns.family3.label 2) = PairSemantics.raw8998 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node491 PairSemantics.raw8998; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8998 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node491 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node491 (EqualityPatterns.family3.label 3) = PairSemantics.raw5128 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node491 PairSemantics.raw5128; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5128 hH).trans (PairSemantics.sound46 hH)
  have hm4 : familyPairMoment B (groupedColumns node491 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value624 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node491 (EqualityPatterns.family3.label 4) = PairSemantics.raw3956 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node491 PairSemantics.raw3956; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3956 hH).trans (PairSemantics.sound624 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue491, PairSemantics.value0, PairSemantics.value46, PairSemantics.value624, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue492 : Sparse (Fin 909) := [(0, (1 / 432)), (1, (5 / 36)), (2, (-5 / 144)), (3, (-5 / 9)), (13, (-10 / 27))]

theorem singlePair492 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node492 node492Labels = Sparse.eval singlePairValue492 (familyPairVector B) := by
  have hp := single_label_three B hB node492
  have hl : node492Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node492 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node492 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node492 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node492 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node492 (EqualityPatterns.family3.label 1) = PairSemantics.raw5186 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node492 PairSemantics.raw5186; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5186 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node492 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node492 (EqualityPatterns.family3.label 2) = PairSemantics.raw8994 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node492 PairSemantics.raw8994; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8994 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node492 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node492 (EqualityPatterns.family3.label 3) = PairSemantics.raw5127 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node492 PairSemantics.raw5127; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5127 hH).trans (PairSemantics.sound232 hH)
  have hm4 : familyPairMoment B (groupedColumns node492 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2135 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node492 (EqualityPatterns.family3.label 4) = PairSemantics.raw3957 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node492 PairSemantics.raw3957; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3957 hH).trans (PairSemantics.sound2135 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue492, PairSemantics.value0, PairSemantics.value4, PairSemantics.value232, PairSemantics.value2135, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue493 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-25 / 288)), (2, (5 / 864)), (3, (5 / 18)), (4, (5 / 27)), (12, (5 / 54)), (26, (5 / 54))]

theorem singlePair493 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node493 node493Labels = Sparse.eval singlePairValue493 (familyPairVector B) := by
  have hp := single_label_three B hB node493
  have hl : node493Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node493 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node493 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node493 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node493 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node493 (EqualityPatterns.family3.label 1) = PairSemantics.raw5157 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node493 PairSemantics.raw5157; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5157 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node493 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node493 (EqualityPatterns.family3.label 2) = PairSemantics.raw9034 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node493 PairSemantics.raw9034; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9034 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node493 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node493 (EqualityPatterns.family3.label 3) = PairSemantics.raw5139 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node493 PairSemantics.raw5139; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5139 hH).trans (PairSemantics.sound232 hH)
  have hm4 : familyPairMoment B (groupedColumns node493 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value705 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node493 (EqualityPatterns.family3.label 4) = PairSemantics.raw3959 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node493 PairSemantics.raw3959; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3959 hH).trans (PairSemantics.sound705 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue493, PairSemantics.value0, PairSemantics.value11, PairSemantics.value46, PairSemantics.value232, PairSemantics.value705, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue494 : Sparse (Fin 909) := [(0, (11 / 288)), (1, (95 / 432)), (2, (-5 / 864)), (3, (5 / 54)), (12, (5 / 54))]

theorem singlePair494 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node494 node494Labels = Sparse.eval singlePairValue494 (familyPairVector B) := by
  have hp := single_label_three B hB node494
  have hl : node494Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node494 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node494 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node494 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node494 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node494 (EqualityPatterns.family3.label 1) = PairSemantics.raw5165 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node494 PairSemantics.raw5165; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5165 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node494 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node494 (EqualityPatterns.family3.label 2) = PairSemantics.raw9030 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node494 PairSemantics.raw9030; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9030 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node494 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node494 (EqualityPatterns.family3.label 3) = PairSemantics.raw5139 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node494 PairSemantics.raw5139; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5139 hH).trans (PairSemantics.sound232 hH)
  have hm4 : familyPairMoment B (groupedColumns node494 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value655 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node494 (EqualityPatterns.family3.label 4) = PairSemantics.raw3960 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node494 PairSemantics.raw3960; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3960 hH).trans (PairSemantics.sound655 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue494, PairSemantics.value0, PairSemantics.value4, PairSemantics.value65, PairSemantics.value232, PairSemantics.value655, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue495 : Sparse (Fin 909) := []

theorem singlePair495 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node495 node495Labels = Sparse.eval singlePairValue495 (familyPairVector B) := by
  have hp := single_label_three B hB node495
  have hl : node495Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node495 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node495 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node495 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node495 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node495 (EqualityPatterns.family3.label 1) = PairSemantics.raw5169 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node495 PairSemantics.raw5169; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5169 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node495 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value5 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node495 (EqualityPatterns.family3.label 2) = PairSemantics.raw9027 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node495 PairSemantics.raw9027; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9027 hH).trans (PairSemantics.sound5 hH)
  have hm3 : familyPairMoment B (groupedColumns node495 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node495 (EqualityPatterns.family3.label 3) = PairSemantics.raw5141 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node495 PairSemantics.raw5141; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5141 hH).trans (PairSemantics.sound46 hH)
  have hm4 : familyPairMoment B (groupedColumns node495 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value291 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node495 (EqualityPatterns.family3.label 4) = PairSemantics.raw3962 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node495 PairSemantics.raw3962; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3962 hH).trans (PairSemantics.sound291 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue495, PairSemantics.value0, PairSemantics.value4, PairSemantics.value5, PairSemantics.value46, PairSemantics.value291, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue497 : Sparse (Fin 909) := [(1, (115 / 432)), (2, (-25 / 432)), (3, (-20 / 27)), (4, (-10 / 27)), (12, (-10 / 27)), (13, (-5 / 27)), (25, (5 / 9)), (31, (5 / 9)), (33, (5 / 9))]

theorem singlePair497 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node497 node497Labels = Sparse.eval singlePairValue497 (familyPairVector B) := by
  have hp := single_label_three B hB node497
  have hl : node497Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node497 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node497 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node497 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node497 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node497 (EqualityPatterns.family3.label 1) = PairSemantics.raw5202 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node497 PairSemantics.raw5202; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5202 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node497 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node497 (EqualityPatterns.family3.label 2) = PairSemantics.raw8965 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node497 PairSemantics.raw8965; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8965 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node497 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node497 (EqualityPatterns.family3.label 3) = PairSemantics.raw5127 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node497 PairSemantics.raw5127; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5127 hH).trans (PairSemantics.sound232 hH)
  have hm4 : familyPairMoment B (groupedColumns node497 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2105 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node497 (EqualityPatterns.family3.label 4) = PairSemantics.raw3970 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node497 PairSemantics.raw3970; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3970 hH).trans (PairSemantics.sound2105 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue497, PairSemantics.value0, PairSemantics.value46, PairSemantics.value232, PairSemantics.value2105, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue498 : Sparse (Fin 909) := [(0, (11 / 864)), (1, (-25 / 864)), (2, (5 / 432)), (3, (5 / 54)), (4, (5 / 54)), (25, (-5 / 18)), (31, (-5 / 18)), (33, (-5 / 18))]

theorem singlePair498 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node498 node498Labels = Sparse.eval singlePairValue498 (familyPairVector B) := by
  have hp := single_label_three B hB node498
  have hl : node498Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node498 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node498 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node498 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node498 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node498 (EqualityPatterns.family3.label 1) = PairSemantics.raw5203 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node498 PairSemantics.raw5203; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5203 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node498 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node498 (EqualityPatterns.family3.label 2) = PairSemantics.raw8964 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node498 PairSemantics.raw8964; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8964 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node498 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node498 (EqualityPatterns.family3.label 3) = PairSemantics.raw5128 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node498 PairSemantics.raw5128; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5128 hH).trans (PairSemantics.sound46 hH)
  have hm4 : familyPairMoment B (groupedColumns node498 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value626 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node498 (EqualityPatterns.family3.label 4) = PairSemantics.raw3971 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node498 PairSemantics.raw3971; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3971 hH).trans (PairSemantics.sound626 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue498, PairSemantics.value0, PairSemantics.value46, PairSemantics.value232, PairSemantics.value626, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue499 : Sparse (Fin 909) := [(0, (-17 / 864)), (1, (5 / 12)), (2, (-5 / 96)), (3, (-5 / 6)), (4, (-5 / 9)), (12, (-5 / 9)), (13, (-5 / 27))]

theorem singlePair499 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node499 node499Labels = Sparse.eval singlePairValue499 (familyPairVector B) := by
  have hp := single_label_three B hB node499
  have hl : node499Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node499 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node499 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node499 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node499 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node499 (EqualityPatterns.family3.label 1) = PairSemantics.raw5206 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node499 PairSemantics.raw5206; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5206 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node499 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node499 (EqualityPatterns.family3.label 2) = PairSemantics.raw8961 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node499 PairSemantics.raw8961; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8961 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node499 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node499 (EqualityPatterns.family3.label 3) = PairSemantics.raw5127 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node499 PairSemantics.raw5127; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5127 hH).trans (PairSemantics.sound232 hH)
  have hm4 : familyPairMoment B (groupedColumns node499 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2142 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node499 (EqualityPatterns.family3.label 4) = PairSemantics.raw3972 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node499 PairSemantics.raw3972; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3972 hH).trans (PairSemantics.sound2142 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue499, PairSemantics.value0, PairSemantics.value11, PairSemantics.value232, PairSemantics.value2142, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue500 : Sparse (Fin 909) := [(0, (1 / 108)), (1, (25 / 216)), (2, (-5 / 216)), (3, (5 / 27)), (12, (5 / 27)), (25, (-5 / 18))]

theorem singlePair500 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node500 node500Labels = Sparse.eval singlePairValue500 (familyPairVector B) := by
  have hp := single_label_three B hB node500
  have hl : node500Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node500 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node500 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node500 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node500 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node500 (EqualityPatterns.family3.label 1) = PairSemantics.raw5190 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node500 PairSemantics.raw5190; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5190 hH).trans (PairSemantics.sound232 hH)
  have hm2 : familyPairMoment B (groupedColumns node500 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node500 (EqualityPatterns.family3.label 2) = PairSemantics.raw8988 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node500 PairSemantics.raw8988; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8988 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node500 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node500 (EqualityPatterns.family3.label 3) = PairSemantics.raw5139 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node500 PairSemantics.raw5139; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5139 hH).trans (PairSemantics.sound232 hH)
  have hm4 : familyPairMoment B (groupedColumns node500 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value704 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node500 (EqualityPatterns.family3.label 4) = PairSemantics.raw3975 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node500 PairSemantics.raw3975; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3975 hH).trans (PairSemantics.sound704 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue500, PairSemantics.value0, PairSemantics.value4, PairSemantics.value232, PairSemantics.value704, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue501 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 54)), (2, (5 / 216)), (25, (5 / 9))]

theorem singlePair501 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node501 node501Labels = Sparse.eval singlePairValue501 (familyPairVector B) := by
  have hp := single_label_three B hB node501
  have hl : node501Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node501 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node501 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node501 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node501 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node501 (EqualityPatterns.family3.label 1) = PairSemantics.raw5192 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node501 PairSemantics.raw5192; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5192 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node501 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node501 (EqualityPatterns.family3.label 2) = PairSemantics.raw8987 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node501 PairSemantics.raw8987; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8987 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node501 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node501 (EqualityPatterns.family3.label 3) = PairSemantics.raw5141 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node501 PairSemantics.raw5141; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5141 hH).trans (PairSemantics.sound46 hH)
  have hm4 : familyPairMoment B (groupedColumns node501 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value224 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node501 (EqualityPatterns.family3.label 4) = PairSemantics.raw3976 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node501 PairSemantics.raw3976; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3976 hH).trans (PairSemantics.sound224 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue501, PairSemantics.value0, PairSemantics.value4, PairSemantics.value46, PairSemantics.value224, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue502 : Sparse (Fin 909) := [(0, (17 / 432)), (1, (-25 / 216)), (2, (-5 / 432)), (3, (5 / 27)), (4, (5 / 27)), (12, (5 / 54))]

theorem singlePair502 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node502 node502Labels = Sparse.eval singlePairValue502 (familyPairVector B) := by
  have hp := single_label_three B hB node502
  have hl : node502Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node502 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node502 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node502 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node502 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node502 (EqualityPatterns.family3.label 1) = PairSemantics.raw5196 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node502 PairSemantics.raw5196; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5196 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node502 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node502 (EqualityPatterns.family3.label 2) = PairSemantics.raw8981 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node502 PairSemantics.raw8981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8981 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node502 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node502 (EqualityPatterns.family3.label 3) = PairSemantics.raw5139 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node502 PairSemantics.raw5139; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5139 hH).trans (PairSemantics.sound232 hH)
  have hm4 : familyPairMoment B (groupedColumns node502 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value667 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node502 (EqualityPatterns.family3.label 4) = PairSemantics.raw3977 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node502 PairSemantics.raw3977; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3977 hH).trans (PairSemantics.sound667 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue502, PairSemantics.value0, PairSemantics.value11, PairSemantics.value232, PairSemantics.value667, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue503 : Sparse (Fin 909) := [(0, (1 / 24)), (1, (-25 / 432)), (2, (5 / 432)), (3, (-5 / 27)), (4, (-5 / 27))]

theorem singlePair503 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node503 node503Labels = Sparse.eval singlePairValue503 (familyPairVector B) := by
  have hp := single_label_three B hB node503
  have hl : node503Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node503 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node503 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node503 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node503 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node503 (EqualityPatterns.family3.label 1) = PairSemantics.raw5197 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node503 PairSemantics.raw5197; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5197 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node503 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node503 (EqualityPatterns.family3.label 2) = PairSemantics.raw8979 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node503 PairSemantics.raw8979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8979 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node503 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node503 (EqualityPatterns.family3.label 3) = PairSemantics.raw5141 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node503 PairSemantics.raw5141; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5141 hH).trans (PairSemantics.sound46 hH)
  have hm4 : familyPairMoment B (groupedColumns node503 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value210 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node503 (EqualityPatterns.family3.label 4) = PairSemantics.raw3978 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node503 PairSemantics.raw3978; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3978 hH).trans (PairSemantics.sound210 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue503, PairSemantics.value0, PairSemantics.value11, PairSemantics.value46, PairSemantics.value210, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue504 : Sparse (Fin 909) := [(0, (35 / 432)), (1, (-25 / 144)), (12, (5 / 54))]

theorem singlePair504 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node504 node504Labels = Sparse.eval singlePairValue504 (familyPairVector B) := by
  have hp := single_label_three B hB node504
  have hl : node504Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node504 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node504 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node504 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node504 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node504 (EqualityPatterns.family3.label 1) = PairSemantics.raw5205 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node504 PairSemantics.raw5205; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5205 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node504 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node504 (EqualityPatterns.family3.label 2) = PairSemantics.raw9011 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node504 PairSemantics.raw9011; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9011 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node504 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node504 (EqualityPatterns.family3.label 3) = PairSemantics.raw5167 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node504 PairSemantics.raw5167; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5167 hH).trans (PairSemantics.sound11 hH)
  have hm4 : familyPairMoment B (groupedColumns node504 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value668 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node504 (EqualityPatterns.family3.label 4) = PairSemantics.raw4116 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node504 PairSemantics.raw4116; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4116 hH).trans (PairSemantics.sound668 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue504, PairSemantics.value0, PairSemantics.value11, PairSemantics.value65, PairSemantics.value668, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue506 : Sparse (Fin 909) := []

theorem singlePair506 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node506 node506Labels = Sparse.eval singlePairValue506 (familyPairVector B) := by
  have hp := single_label_three B hB node506
  have hl : node506Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node506 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node506 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node506 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node506 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node506 (EqualityPatterns.family3.label 1) = PairSemantics.raw5197 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node506 PairSemantics.raw5197; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5197 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node506 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value5 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node506 (EqualityPatterns.family3.label 2) = PairSemantics.raw9027 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node506 PairSemantics.raw9027; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9027 hH).trans (PairSemantics.sound5 hH)
  have hm3 : familyPairMoment B (groupedColumns node506 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node506 (EqualityPatterns.family3.label 3) = PairSemantics.raw5177 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node506 PairSemantics.raw5177; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5177 hH).trans (PairSemantics.sound11 hH)
  have hm4 : familyPairMoment B (groupedColumns node506 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value294 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node506 (EqualityPatterns.family3.label 4) = PairSemantics.raw4131 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node506 PairSemantics.raw4131; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4131 hH).trans (PairSemantics.sound294 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue506, PairSemantics.value0, PairSemantics.value5, PairSemantics.value11, PairSemantics.value294, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
