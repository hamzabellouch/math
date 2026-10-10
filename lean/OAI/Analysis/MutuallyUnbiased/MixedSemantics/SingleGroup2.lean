import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleRules
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical160
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical161
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical162
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical280
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical281
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical282
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound8

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue40 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 48)), (2, (-5 / 144)), (9, (5 / 36)), (69, (5 / 9))]

theorem singlePair40 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node40 node40Labels = Sparse.eval singlePairValue40 (familyPairVector B) := by
  have hp := single_label_three B hB node40
  have hl : node40Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node40 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node40 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node40 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node40 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node40 (EqualityPatterns.family3.label 1) = PairSemantics.raw924 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node40 PairSemantics.raw924; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical924 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node40 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node40 (EqualityPatterns.family3.label 2) = PairSemantics.raw5183 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node40 PairSemantics.raw5183; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5183 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node40 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value7 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node40 (EqualityPatterns.family3.label 3) = PairSemantics.raw51 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node40 PairSemantics.raw51; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical51 hH).trans (PairSemantics.sound7 hH)
  have hm4 : familyPairMoment B (groupedColumns node40 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value27 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node40 (EqualityPatterns.family3.label 4) = PairSemantics.raw32 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node40 PairSemantics.raw32; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical32 hH).trans (PairSemantics.sound27 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue40, PairSemantics.value0, PairSemantics.value4, PairSemantics.value7, PairSemantics.value10, PairSemantics.value27, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue41 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 144)), (2, (5 / 48)), (9, (5 / 36)), (257, (5 / 9))]

theorem singlePair41 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node41 node41Labels = Sparse.eval singlePairValue41 (familyPairVector B) := by
  have hp := single_label_three B hB node41
  have hl : node41Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node41 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node41 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node41 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node41 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node41 (EqualityPatterns.family3.label 1) = PairSemantics.raw927 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node41 PairSemantics.raw927; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical927 hH).trans (PairSemantics.sound3 hH)
  have hm2 : familyPairMoment B (groupedColumns node41 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node41 (EqualityPatterns.family3.label 2) = PairSemantics.raw5151 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node41 PairSemantics.raw5151; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5151 hH).trans (PairSemantics.sound10 hH)
  have hm3 : familyPairMoment B (groupedColumns node41 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value7 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node41 (EqualityPatterns.family3.label 3) = PairSemantics.raw51 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node41 PairSemantics.raw51; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical51 hH).trans (PairSemantics.sound7 hH)
  have hm4 : familyPairMoment B (groupedColumns node41 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value17 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node41 (EqualityPatterns.family3.label 4) = PairSemantics.raw33 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node41 PairSemantics.raw33; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical33 hH).trans (PairSemantics.sound17 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue41, PairSemantics.value0, PairSemantics.value3, PairSemantics.value7, PairSemantics.value10, PairSemantics.value17, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue42 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 36)), (2, (5 / 36)), (9, (5 / 9)), (58, (5 / 36))]

theorem singlePair42 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node42 node42Labels = Sparse.eval singlePairValue42 (familyPairVector B) := by
  have hp := single_label_three B hB node42
  have hl : node42Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node42 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node42 (EqualityPatterns.family3.label 0) = PairSemantics.raw7978 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node42 PairSemantics.raw7978; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7978 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node42 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node42 (EqualityPatterns.family3.label 1) = PairSemantics.raw926 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node42 PairSemantics.raw926; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical926 hH).trans (PairSemantics.sound3 hH)
  have hm2 : familyPairMoment B (groupedColumns node42 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node42 (EqualityPatterns.family3.label 2) = PairSemantics.raw5210 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node42 PairSemantics.raw5210; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5210 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node42 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value1 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node42 (EqualityPatterns.family3.label 3) = PairSemantics.raw53 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node42 PairSemantics.raw53; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical53 hH).trans (PairSemantics.sound1 hH)
  have hm4 : familyPairMoment B (groupedColumns node42 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value7 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node42 (EqualityPatterns.family3.label 4) = PairSemantics.raw34 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node42 PairSemantics.raw34; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical34 hH).trans (PairSemantics.sound7 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue42, PairSemantics.value0, PairSemantics.value1, PairSemantics.value3, PairSemantics.value4, PairSemantics.value7, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue43 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (35 / 432)), (2, (5 / 27)), (5, (-5 / 36)), (6, (5 / 72)), (7, (-5 / 27)), (35, (-10 / 27)), (82, (-5 / 27)), (199, (5 / 18))]

theorem singlePair43 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node43 node43Labels = Sparse.eval singlePairValue43 (familyPairVector B) := by
  have hp := single_label_three B hB node43
  have hl : node43Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node43 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node43 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node43 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node43 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node43 (EqualityPatterns.family3.label 1) = PairSemantics.raw204 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node43 PairSemantics.raw204; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical204 hH).trans (PairSemantics.sound16 hH)
  have hm2 : familyPairMoment B (groupedColumns node43 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node43 (EqualityPatterns.family3.label 2) = PairSemantics.raw9012 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node43 PairSemantics.raw9012; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9012 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node43 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node43 (EqualityPatterns.family3.label 3) = PairSemantics.raw192 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node43 PairSemantics.raw192; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical192 hH).trans (PairSemantics.sound16 hH)
  have hm4 : familyPairMoment B (groupedColumns node43 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2789 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node43 (EqualityPatterns.family3.label 4) = PairSemantics.raw59 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node43 PairSemantics.raw59; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical59 hH).trans (PairSemantics.sound2789 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue43, PairSemantics.value0, PairSemantics.value16, PairSemantics.value65, PairSemantics.value2789, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue44 : Sparse (Fin 909) := [(0, (7 / 144)), (1, (-5 / 48)), (2, (-55 / 432)), (3, (-5 / 54)), (5, (5 / 36)), (6, (-5 / 144)), (8, (-5 / 54)), (13, (-5 / 54)), (35, (-5 / 54)), (52, (-10 / 27)), (82, (-5 / 54)), (128, (-5 / 27)), (201, (5 / 18))]

theorem singlePair44 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node44 node44Labels = Sparse.eval singlePairValue44 (familyPairVector B) := by
  have hp := single_label_three B hB node44
  have hl : node44Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node44 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node44 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node44 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node44 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value69 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node44 (EqualityPatterns.family3.label 1) = PairSemantics.raw205 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node44 PairSemantics.raw205; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical205 hH).trans (PairSemantics.sound69 hH)
  have hm2 : familyPairMoment B (groupedColumns node44 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node44 (EqualityPatterns.family3.label 2) = PairSemantics.raw9010 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node44 PairSemantics.raw9010; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9010 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node44 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node44 (EqualityPatterns.family3.label 3) = PairSemantics.raw192 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node44 PairSemantics.raw192; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical192 hH).trans (PairSemantics.sound16 hH)
  have hm4 : familyPairMoment B (groupedColumns node44 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2658 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node44 (EqualityPatterns.family3.label 4) = PairSemantics.raw60 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node44 PairSemantics.raw60; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical60 hH).trans (PairSemantics.sound2658 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue44, PairSemantics.value0, PairSemantics.value16, PairSemantics.value65, PairSemantics.value69, PairSemantics.value2658, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue45 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (35 / 864)), (2, (-5 / 108)), (5, (-25 / 216)), (6, (-5 / 96)), (35, (5 / 54)), (82, (5 / 54))]

theorem singlePair45 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node45 node45Labels = Sparse.eval singlePairValue45 (familyPairVector B) := by
  have hp := single_label_three B hB node45
  have hl : node45Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node45 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node45 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node45 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node45 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node45 (EqualityPatterns.family3.label 1) = PairSemantics.raw206 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node45 PairSemantics.raw206; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical206 hH).trans (PairSemantics.sound16 hH)
  have hm2 : familyPairMoment B (groupedColumns node45 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node45 (EqualityPatterns.family3.label 2) = PairSemantics.raw9011 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node45 PairSemantics.raw9011; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9011 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node45 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node45 (EqualityPatterns.family3.label 3) = PairSemantics.raw193 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node45 PairSemantics.raw193; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical193 hH).trans (PairSemantics.sound8 hH)
  have hm4 : familyPairMoment B (groupedColumns node45 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value865 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node45 (EqualityPatterns.family3.label 4) = PairSemantics.raw61 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node45 PairSemantics.raw61; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical61 hH).trans (PairSemantics.sound865 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue45, PairSemantics.value0, PairSemantics.value8, PairSemantics.value16, PairSemantics.value65, PairSemantics.value865, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue46 : Sparse (Fin 909) := [(0, (31 / 864)), (1, (-5 / 96)), (2, (-55 / 864)), (6, (-5 / 96)), (13, (5 / 54)), (52, (5 / 27)), (82, (5 / 54)), (128, (5 / 27))]

theorem singlePair46 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node46 node46Labels = Sparse.eval singlePairValue46 (familyPairVector B) := by
  have hp := single_label_three B hB node46
  have hl : node46Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node46 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node46 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node46 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node46 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value69 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node46 (EqualityPatterns.family3.label 1) = PairSemantics.raw207 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node46 PairSemantics.raw207; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical207 hH).trans (PairSemantics.sound69 hH)
  have hm2 : familyPairMoment B (groupedColumns node46 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node46 (EqualityPatterns.family3.label 2) = PairSemantics.raw9008 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node46 PairSemantics.raw9008; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9008 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node46 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node46 (EqualityPatterns.family3.label 3) = PairSemantics.raw193 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node46 PairSemantics.raw193; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical193 hH).trans (PairSemantics.sound8 hH)
  have hm4 : familyPairMoment B (groupedColumns node46 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value565 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node46 (EqualityPatterns.family3.label 4) = PairSemantics.raw62 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node46 PairSemantics.raw62; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical62 hH).trans (PairSemantics.sound565 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue46, PairSemantics.value0, PairSemantics.value8, PairSemantics.value11, PairSemantics.value69, PairSemantics.value565, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue47 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 432)), (2, (5 / 108)), (5, (5 / 54)), (6, (5 / 216)), (7, (5 / 54)), (35, (5 / 27)), (82, (5 / 54)), (199, (-5 / 18))]

theorem singlePair47 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node47 node47Labels = Sparse.eval singlePairValue47 (familyPairVector B) := by
  have hp := single_label_three B hB node47
  have hl : node47Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node47 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node47 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node47 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node47 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node47 (EqualityPatterns.family3.label 1) = PairSemantics.raw206 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node47 PairSemantics.raw206; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical206 hH).trans (PairSemantics.sound16 hH)
  have hm2 : familyPairMoment B (groupedColumns node47 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node47 (EqualityPatterns.family3.label 2) = PairSemantics.raw9015 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node47 PairSemantics.raw9015; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9015 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node47 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value9 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node47 (EqualityPatterns.family3.label 3) = PairSemantics.raw194 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node47 PairSemantics.raw194; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical194 hH).trans (PairSemantics.sound9 hH)
  have hm4 : familyPairMoment B (groupedColumns node47 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value650 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node47 (EqualityPatterns.family3.label 4) = PairSemantics.raw63 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node47 PairSemantics.raw63; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical63 hH).trans (PairSemantics.sound650 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue47, PairSemantics.value0, PairSemantics.value9, PairSemantics.value11, PairSemantics.value16, PairSemantics.value650, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue48 : Sparse (Fin 909) := [(0, (13 / 288)), (2, (-5 / 432)), (5, (55 / 216)), (6, (-5 / 864)), (8, (5 / 54)), (201, (-5 / 18))]

theorem singlePair48 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node48 node48Labels = Sparse.eval singlePairValue48 (familyPairVector B) := by
  have hp := single_label_three B hB node48
  have hl : node48Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node48 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node48 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node48 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node48 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value69 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node48 (EqualityPatterns.family3.label 1) = PairSemantics.raw207 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node48 PairSemantics.raw207; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical207 hH).trans (PairSemantics.sound69 hH)
  have hm2 : familyPairMoment B (groupedColumns node48 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node48 (EqualityPatterns.family3.label 2) = PairSemantics.raw9011 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node48 PairSemantics.raw9011; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9011 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node48 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value9 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node48 (EqualityPatterns.family3.label 3) = PairSemantics.raw194 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node48 PairSemantics.raw194; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical194 hH).trans (PairSemantics.sound9 hH)
  have hm4 : familyPairMoment B (groupedColumns node48 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1134 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node48 (EqualityPatterns.family3.label 4) = PairSemantics.raw64 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node48 PairSemantics.raw64; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical64 hH).trans (PairSemantics.sound1134 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue48, PairSemantics.value0, PairSemantics.value9, PairSemantics.value65, PairSemantics.value69, PairSemantics.value1134, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue49 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 216)), (6, (25 / 144)), (82, (-5 / 27))]

theorem singlePair49 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node49 node49Labels = Sparse.eval singlePairValue49 (familyPairVector B) := by
  have hp := single_label_three B hB node49
  have hl : node49Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node49 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node49 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node49 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node49 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node49 (EqualityPatterns.family3.label 1) = PairSemantics.raw208 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node49 PairSemantics.raw208; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical208 hH).trans (PairSemantics.sound16 hH)
  have hm2 : familyPairMoment B (groupedColumns node49 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node49 (EqualityPatterns.family3.label 2) = PairSemantics.raw9013 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node49 PairSemantics.raw9013; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9013 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node49 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value2 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node49 (EqualityPatterns.family3.label 3) = PairSemantics.raw195 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node49 PairSemantics.raw195; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical195 hH).trans (PairSemantics.sound2 hH)
  have hm4 : familyPairMoment B (groupedColumns node49 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value157 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node49 (EqualityPatterns.family3.label 4) = PairSemantics.raw65 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node49 PairSemantics.raw65; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical65 hH).trans (PairSemantics.sound157 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue49, PairSemantics.value0, PairSemantics.value2, PairSemantics.value11, PairSemantics.value16, PairSemantics.value157, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue50 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (5 / 72)), (2, (5 / 48)), (5, (-5 / 36)), (6, (5 / 108)), (52, (5 / 27)), (128, (5 / 54))]

theorem singlePair50 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node50 node50Labels = Sparse.eval singlePairValue50 (familyPairVector B) := by
  have hp := single_label_three B hB node50
  have hl : node50Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node50 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node50 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node50 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node50 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node50 (EqualityPatterns.family3.label 1) = PairSemantics.raw202 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node50 PairSemantics.raw202; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical202 hH).trans (PairSemantics.sound16 hH)
  have hm2 : familyPairMoment B (groupedColumns node50 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node50 (EqualityPatterns.family3.label 2) = PairSemantics.raw9025 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node50 PairSemantics.raw9025; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9025 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node50 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node50 (EqualityPatterns.family3.label 3) = PairSemantics.raw197 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node50 PairSemantics.raw197; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical197 hH).trans (PairSemantics.sound16 hH)
  have hm4 : familyPairMoment B (groupedColumns node50 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1140 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node50 (EqualityPatterns.family3.label 4) = PairSemantics.raw66 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node50 PairSemantics.raw66; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical66 hH).trans (PairSemantics.sound1140 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue50, PairSemantics.value0, PairSemantics.value16, PairSemantics.value65, PairSemantics.value1140, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue51 : Sparse (Fin 909) := [(0, (5 / 144)), (2, (5 / 72)), (3, (5 / 54)), (5, (-5 / 36)), (6, (5 / 144)), (13, (5 / 54)), (35, (5 / 54)), (52, (5 / 54)), (82, (5 / 54)), (128, (5 / 54)), (201, (-5 / 18))]

theorem singlePair51 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node51 node51Labels = Sparse.eval singlePairValue51 (familyPairVector B) := by
  have hp := single_label_three B hB node51
  have hl : node51Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node51 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node51 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node51 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node51 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node51 (EqualityPatterns.family3.label 1) = PairSemantics.raw209 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node51 PairSemantics.raw209; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical209 hH).trans (PairSemantics.sound16 hH)
  have hm2 : familyPairMoment B (groupedColumns node51 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node51 (EqualityPatterns.family3.label 2) = PairSemantics.raw9018 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node51 PairSemantics.raw9018; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9018 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node51 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node51 (EqualityPatterns.family3.label 3) = PairSemantics.raw197 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node51 PairSemantics.raw197; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical197 hH).trans (PairSemantics.sound16 hH)
  have hm4 : familyPairMoment B (groupedColumns node51 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value665 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node51 (EqualityPatterns.family3.label 4) = PairSemantics.raw67 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node51 PairSemantics.raw67; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical67 hH).trans (PairSemantics.sound665 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue51, PairSemantics.value0, PairSemantics.value11, PairSemantics.value16, PairSemantics.value665, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue52 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 216)), (2, (-5 / 216)), (6, (-5 / 144)), (52, (-5 / 27)), (128, (-5 / 27))]

theorem singlePair52 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node52 node52Labels = Sparse.eval singlePairValue52 (familyPairVector B) := by
  have hp := single_label_three B hB node52
  have hl : node52Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node52 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node52 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node52 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node52 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node52 (EqualityPatterns.family3.label 1) = PairSemantics.raw210 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node52 PairSemantics.raw210; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical210 hH).trans (PairSemantics.sound16 hH)
  have hm2 : familyPairMoment B (groupedColumns node52 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node52 (EqualityPatterns.family3.label 2) = PairSemantics.raw9013 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node52 PairSemantics.raw9013; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9013 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node52 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node52 (EqualityPatterns.family3.label 3) = PairSemantics.raw198 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node52 PairSemantics.raw198; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical198 hH).trans (PairSemantics.sound8 hH)
  have hm4 : familyPairMoment B (groupedColumns node52 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value190 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node52 (EqualityPatterns.family3.label 4) = PairSemantics.raw68 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node52 PairSemantics.raw68; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical68 hH).trans (PairSemantics.sound190 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue52, PairSemantics.value0, PairSemantics.value8, PairSemantics.value11, PairSemantics.value16, PairSemantics.value190, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue53 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 144)), (2, (-5 / 108)), (5, (5 / 27)), (6, (-5 / 108)), (35, (-5 / 27)), (82, (-5 / 27))]

theorem singlePair53 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node53 node53Labels = Sparse.eval singlePairValue53 (familyPairVector B) := by
  have hp := single_label_three B hB node53
  have hl : node53Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node53 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node53 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node53 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node53 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node53 (EqualityPatterns.family3.label 1) = PairSemantics.raw203 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node53 PairSemantics.raw203; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical203 hH).trans (PairSemantics.sound8 hH)
  have hm2 : familyPairMoment B (groupedColumns node53 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node53 (EqualityPatterns.family3.label 2) = PairSemantics.raw9032 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node53 PairSemantics.raw9032; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9032 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node53 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value9 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node53 (EqualityPatterns.family3.label 3) = PairSemantics.raw199 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node53 PairSemantics.raw199; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical199 hH).trans (PairSemantics.sound9 hH)
  have hm4 : familyPairMoment B (groupedColumns node53 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value217 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node53 (EqualityPatterns.family3.label 4) = PairSemantics.raw69 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node53 PairSemantics.raw69; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical69 hH).trans (PairSemantics.sound217 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue53, PairSemantics.value0, PairSemantics.value8, PairSemantics.value9, PairSemantics.value11, PairSemantics.value217, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue54 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (65 / 432)), (2, (-5 / 432)), (5, (-5 / 108)), (6, (-5 / 216)), (13, (-5 / 27)), (82, (-5 / 27)), (128, (-5 / 27))]

theorem singlePair54 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node54 node54Labels = Sparse.eval singlePairValue54 (familyPairVector B) := by
  have hp := single_label_three B hB node54
  have hl : node54Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node54 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node54 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node54 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node54 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node54 (EqualityPatterns.family3.label 1) = PairSemantics.raw213 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node54 PairSemantics.raw213; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical213 hH).trans (PairSemantics.sound16 hH)
  have hm2 : familyPairMoment B (groupedColumns node54 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node54 (EqualityPatterns.family3.label 2) = PairSemantics.raw8972 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node54 PairSemantics.raw8972; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8972 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node54 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node54 (EqualityPatterns.family3.label 3) = PairSemantics.raw198 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node54 PairSemantics.raw198; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical198 hH).trans (PairSemantics.sound8 hH)
  have hm4 : familyPairMoment B (groupedColumns node54 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value171 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node54 (EqualityPatterns.family3.label 4) = PairSemantics.raw70 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node54 PairSemantics.raw70; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical70 hH).trans (PairSemantics.sound171 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue54, PairSemantics.value0, PairSemantics.value4, PairSemantics.value8, PairSemantics.value16, PairSemantics.value171, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue55 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 36)), (5, (5 / 18)), (199, (5 / 9))]

theorem singlePair55 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node55 node55Labels = Sparse.eval singlePairValue55 (familyPairVector B) := by
  have hp := single_label_three B hB node55
  have hl : node55Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node55 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node55 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node55 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node55 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value9 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node55 (EqualityPatterns.family3.label 1) = PairSemantics.raw212 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node55 PairSemantics.raw212; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical212 hH).trans (PairSemantics.sound9 hH)
  have hm2 : familyPairMoment B (groupedColumns node55 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node55 (EqualityPatterns.family3.label 2) = PairSemantics.raw8987 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node55 PairSemantics.raw8987; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8987 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node55 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value9 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node55 (EqualityPatterns.family3.label 3) = PairSemantics.raw199 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node55 PairSemantics.raw199; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical199 hH).trans (PairSemantics.sound9 hH)
  have hm4 : familyPairMoment B (groupedColumns node55 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value199 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node55 (EqualityPatterns.family3.label 4) = PairSemantics.raw71 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node55 PairSemantics.raw71; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical71 hH).trans (PairSemantics.sound199 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue55, PairSemantics.value0, PairSemantics.value4, PairSemantics.value9, PairSemantics.value199, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
