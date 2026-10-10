import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleRules
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical160
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical161
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical238
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical240
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical241
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical242
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound6

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue104 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 72)), (2, (-5 / 72)), (6, (5 / 36)), (128, (5 / 9))]

theorem singlePair104 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node104 node104Labels = Sparse.eval singlePairValue104 (familyPairVector B) := by
  have hp := single_label_three B hB node104
  have hl : node104Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node104 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node104 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node104 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node104 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node104 (EqualityPatterns.family3.label 1) = PairSemantics.raw924 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node104 PairSemantics.raw924; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical924 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node104 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node104 (EqualityPatterns.family3.label 2) = PairSemantics.raw7642 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node104 PairSemantics.raw7642; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7642 hH).trans (PairSemantics.sound10 hH)
  have hm3 : familyPairMoment B (groupedColumns node104 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value2 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node104 (EqualityPatterns.family3.label 3) = PairSemantics.raw200 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node104 PairSemantics.raw200; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical200 hH).trans (PairSemantics.sound2 hH)
  have hm4 : familyPairMoment B (groupedColumns node104 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value38 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node104 (EqualityPatterns.family3.label 4) = PairSemantics.raw122 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node104 PairSemantics.raw122; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical122 hH).trans (PairSemantics.sound38 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue104, PairSemantics.value0, PairSemantics.value2, PairSemantics.value10, PairSemantics.value38, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue105 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 432)), (5, (-5 / 108)), (6, (5 / 216)), (11, (-5 / 27)), (26, (-5 / 27)), (35, (-5 / 27))]

theorem singlePair105 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node105 node105Labels = Sparse.eval singlePairValue105 (familyPairVector B) := by
  have hp := single_label_three B hB node105
  have hl : node105Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node105 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node105 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node105 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node105 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node105 (EqualityPatterns.family3.label 1) = PairSemantics.raw869 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node105 PairSemantics.raw869; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical869 hH).trans (PairSemantics.sound24 hH)
  have hm2 : familyPairMoment B (groupedColumns node105 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node105 (EqualityPatterns.family3.label 2) = PairSemantics.raw7757 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node105 PairSemantics.raw7757; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7757 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node105 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node105 (EqualityPatterns.family3.label 3) = PairSemantics.raw208 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node105 PairSemantics.raw208; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical208 hH).trans (PairSemantics.sound16 hH)
  have hm4 : familyPairMoment B (groupedColumns node105 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value228 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node105 (EqualityPatterns.family3.label 4) = PairSemantics.raw123 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node105 PairSemantics.raw123; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical123 hH).trans (PairSemantics.sound228 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue105, PairSemantics.value0, PairSemantics.value11, PairSemantics.value16, PairSemantics.value24, PairSemantics.value228, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue106 : Sparse (Fin 909) := [(0, (5 / 144)), (2, (5 / 108)), (5, (-5 / 54)), (6, (5 / 432)), (228, (5 / 9))]

theorem singlePair106 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node106 node106Labels = Sparse.eval singlePairValue106 (familyPairVector B) := by
  have hp := single_label_three B hB node106
  have hl : node106Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node106 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node106 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node106 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node106 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node106 (EqualityPatterns.family3.label 1) = PairSemantics.raw872 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node106 PairSemantics.raw872; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical872 hH).trans (PairSemantics.sound25 hH)
  have hm2 : familyPairMoment B (groupedColumns node106 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node106 (EqualityPatterns.family3.label 2) = PairSemantics.raw7753 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node106 PairSemantics.raw7753; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7753 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node106 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node106 (EqualityPatterns.family3.label 3) = PairSemantics.raw208 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node106 PairSemantics.raw208; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical208 hH).trans (PairSemantics.sound16 hH)
  have hm4 : familyPairMoment B (groupedColumns node106 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value225 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node106 (EqualityPatterns.family3.label 4) = PairSemantics.raw124 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node106 PairSemantics.raw124; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical124 hH).trans (PairSemantics.sound225 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue106, PairSemantics.value0, PairSemantics.value11, PairSemantics.value16, PairSemantics.value25, PairSemantics.value225, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue107 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 144)), (2, (-5 / 72)), (6, (-5 / 72)), (11, (5 / 9))]

theorem singlePair107 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node107 node107Labels = Sparse.eval singlePairValue107 (familyPairVector B) := by
  have hp := single_label_three B hB node107
  have hl : node107Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node107 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node107 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node107 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node107 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node107 (EqualityPatterns.family3.label 1) = PairSemantics.raw873 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node107 PairSemantics.raw873; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical873 hH).trans (PairSemantics.sound8 hH)
  have hm2 : familyPairMoment B (groupedColumns node107 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node107 (EqualityPatterns.family3.label 2) = PairSemantics.raw7749 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node107 PairSemantics.raw7749; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7749 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node107 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node107 (EqualityPatterns.family3.label 3) = PairSemantics.raw211 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node107 PairSemantics.raw211; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical211 hH).trans (PairSemantics.sound8 hH)
  have hm4 : familyPairMoment B (groupedColumns node107 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value42 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node107 (EqualityPatterns.family3.label 4) = PairSemantics.raw125 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node107 PairSemantics.raw125; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical125 hH).trans (PairSemantics.sound42 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue107, PairSemantics.value0, PairSemantics.value8, PairSemantics.value11, PairSemantics.value42, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue108 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-5 / 96)), (2, (-65 / 864)), (3, (5 / 54)), (5, (5 / 216)), (6, (-5 / 432)), (35, (5 / 54)), (52, (5 / 27))]

theorem singlePair108 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node108 node108Labels = Sparse.eval singlePairValue108 (familyPairVector B) := by
  have hp := single_label_three B hB node108
  have hl : node108Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node108 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node108 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node108 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node108 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node108 (EqualityPatterns.family3.label 1) = PairSemantics.raw884 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node108 PairSemantics.raw884; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical884 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node108 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node108 (EqualityPatterns.family3.label 2) = PairSemantics.raw7742 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node108 PairSemantics.raw7742; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7742 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node108 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value69 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node108 (EqualityPatterns.family3.label 3) = PairSemantics.raw207 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node108 PairSemantics.raw207; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical207 hH).trans (PairSemantics.sound69 hH)
  have hm4 : familyPairMoment B (groupedColumns node108 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value742 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node108 (EqualityPatterns.family3.label 4) = PairSemantics.raw126 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node108 PairSemantics.raw126; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical126 hH).trans (PairSemantics.sound742 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue108, PairSemantics.value0, PairSemantics.value10, PairSemantics.value65, PairSemantics.value69, PairSemantics.value742, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue109 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (5 / 432)), (2, (25 / 108)), (5, (-5 / 108)), (35, (-5 / 27))]

theorem singlePair109 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node109 node109Labels = Sparse.eval singlePairValue109 (familyPairVector B) := by
  have hp := single_label_three B hB node109
  have hl : node109Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node109 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node109 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node109 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node109 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node109 (EqualityPatterns.family3.label 1) = PairSemantics.raw887 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node109 PairSemantics.raw887; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical887 hH).trans (PairSemantics.sound3 hH)
  have hm2 : familyPairMoment B (groupedColumns node109 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node109 (EqualityPatterns.family3.label 2) = PairSemantics.raw7738 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node109 PairSemantics.raw7738; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7738 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node109 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node109 (EqualityPatterns.family3.label 3) = PairSemantics.raw208 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node109 PairSemantics.raw208; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical208 hH).trans (PairSemantics.sound16 hH)
  have hm4 : familyPairMoment B (groupedColumns node109 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value248 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node109 (EqualityPatterns.family3.label 4) = PairSemantics.raw127 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node109 PairSemantics.raw127; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical127 hH).trans (PairSemantics.sound248 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue109, PairSemantics.value0, PairSemantics.value3, PairSemantics.value16, PairSemantics.value65, PairSemantics.value248, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue110 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-5 / 108)), (2, (-5 / 108)), (6, (5 / 432)), (52, (-5 / 27))]

theorem singlePair110 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node110 node110Labels = Sparse.eval singlePairValue110 (familyPairVector B) := by
  have hp := single_label_three B hB node110
  have hl : node110Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node110 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node110 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node110 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node110 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node110 (EqualityPatterns.family3.label 1) = PairSemantics.raw898 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node110 PairSemantics.raw898; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical898 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node110 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node110 (EqualityPatterns.family3.label 2) = PairSemantics.raw7731 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node110 PairSemantics.raw7731; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7731 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node110 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node110 (EqualityPatterns.family3.label 3) = PairSemantics.raw208 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node110 PairSemantics.raw208; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical208 hH).trans (PairSemantics.sound16 hH)
  have hm4 : familyPairMoment B (groupedColumns node110 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value246 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node110 (EqualityPatterns.family3.label 4) = PairSemantics.raw128 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node110 PairSemantics.raw128; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical128 hH).trans (PairSemantics.sound246 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue110, PairSemantics.value0, PairSemantics.value10, PairSemantics.value16, PairSemantics.value65, PairSemantics.value246, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue111 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-25 / 432)), (2, (-5 / 432)), (3, (-5 / 27)), (5, (-5 / 108)), (6, (5 / 432)), (35, (-5 / 27)), (52, (-5 / 27))]

theorem singlePair111 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node111 node111Labels = Sparse.eval singlePairValue111 (familyPairVector B) := by
  have hp := single_label_three B hB node111
  have hl : node111Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node111 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node111 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node111 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node111 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node111 (EqualityPatterns.family3.label 1) = PairSemantics.raw918 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node111 PairSemantics.raw918; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical918 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node111 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node111 (EqualityPatterns.family3.label 2) = PairSemantics.raw7705 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node111 PairSemantics.raw7705; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7705 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node111 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node111 (EqualityPatterns.family3.label 3) = PairSemantics.raw208 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node111 PairSemantics.raw208; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical208 hH).trans (PairSemantics.sound16 hH)
  have hm4 : familyPairMoment B (groupedColumns node111 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value206 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node111 (EqualityPatterns.family3.label 4) = PairSemantics.raw129 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node111 PairSemantics.raw129; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical129 hH).trans (PairSemantics.sound206 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue111, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value16, PairSemantics.value206, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue112 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 72)), (2, (-5 / 72)), (6, (-5 / 144)), (52, (5 / 9))]

theorem singlePair112 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node112 node112Labels = Sparse.eval singlePairValue112 (familyPairVector B) := by
  have hp := single_label_three B hB node112
  have hl : node112Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node112 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node112 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node112 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node112 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node112 (EqualityPatterns.family3.label 1) = PairSemantics.raw924 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node112 PairSemantics.raw924; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical924 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node112 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node112 (EqualityPatterns.family3.label 2) = PairSemantics.raw7683 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node112 PairSemantics.raw7683; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7683 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node112 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node112 (EqualityPatterns.family3.label 3) = PairSemantics.raw211 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node112 PairSemantics.raw211; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical211 hH).trans (PairSemantics.sound8 hH)
  have hm4 : familyPairMoment B (groupedColumns node112 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value40 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node112 (EqualityPatterns.family3.label 4) = PairSemantics.raw130 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node112 PairSemantics.raw130; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical130 hH).trans (PairSemantics.sound40 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue112, PairSemantics.value0, PairSemantics.value8, PairSemantics.value10, PairSemantics.value11, PairSemantics.value40, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue113 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 144)), (2, (5 / 36)), (5, (5 / 36)), (35, (5 / 9))]

theorem singlePair113 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node113 node113Labels = Sparse.eval singlePairValue113 (familyPairVector B) := by
  have hp := single_label_three B hB node113
  have hl : node113Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node113 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node113 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node113 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node113 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node113 (EqualityPatterns.family3.label 1) = PairSemantics.raw900 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node113 PairSemantics.raw900; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical900 hH).trans (PairSemantics.sound3 hH)
  have hm2 : familyPairMoment B (groupedColumns node113 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node113 (EqualityPatterns.family3.label 2) = PairSemantics.raw7749 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node113 PairSemantics.raw7749; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7749 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node113 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value9 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node113 (EqualityPatterns.family3.label 3) = PairSemantics.raw214 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node113 PairSemantics.raw214; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical214 hH).trans (PairSemantics.sound9 hH)
  have hm4 : familyPairMoment B (groupedColumns node113 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value32 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node113 (EqualityPatterns.family3.label 4) = PairSemantics.raw131 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node113 PairSemantics.raw131; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical131 hH).trans (PairSemantics.sound32 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue113, PairSemantics.value0, PairSemantics.value3, PairSemantics.value9, PairSemantics.value11, PairSemantics.value32, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue114 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (-5 / 108)), (2, (-25 / 432)), (3, (-10 / 27)), (5, (5 / 27)), (6, (-5 / 288)), (7, (-5 / 9)), (8, (-5 / 27)), (9, (5 / 108)), (26, (-5 / 54)), (35, (-20 / 27)), (52, (-5 / 54)), (67, (-5 / 27)), (69, (-10 / 27)), (70, (-10 / 27)), (71, (-5 / 54)), (257, (-5 / 54))]

theorem singlePair114 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node114 node114Labels = Sparse.eval singlePairValue114 (familyPairVector B) := by
  have hp := single_label_three B hB node114
  have hl : node114Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node114 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node114 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node114 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node114 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node114 (EqualityPatterns.family3.label 1) = PairSemantics.raw5134 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node114 PairSemantics.raw5134; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5134 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node114 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node114 (EqualityPatterns.family3.label 2) = PairSemantics.raw5158 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node114 PairSemantics.raw5158; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5158 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node114 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value68 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node114 (EqualityPatterns.family3.label 3) = PairSemantics.raw184 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node114 PairSemantics.raw184; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical184 hH).trans (PairSemantics.sound68 hH)
  have hm4 : familyPairMoment B (groupedColumns node114 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1526 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node114 (EqualityPatterns.family3.label 4) = PairSemantics.raw132 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node114 PairSemantics.raw132; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical132 hH).trans (PairSemantics.sound1526 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue114, PairSemantics.value0, PairSemantics.value46, PairSemantics.value68, PairSemantics.value1526, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue115 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-5 / 216)), (2, (35 / 432)), (9, (-5 / 54)), (58, (5 / 432))]

theorem singlePair115 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node115 node115Labels = Sparse.eval singlePairValue115 (familyPairVector B) := by
  have hp := single_label_three B hB node115
  have hl : node115Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node115 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node115 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node115 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node115 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node115 (EqualityPatterns.family3.label 1) = PairSemantics.raw5136 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node115 PairSemantics.raw5136; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5136 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node115 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node115 (EqualityPatterns.family3.label 2) = PairSemantics.raw5157 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node115 PairSemantics.raw5157; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5157 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node115 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value14 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node115 (EqualityPatterns.family3.label 3) = PairSemantics.raw185 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node115 PairSemantics.raw185; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical185 hH).trans (PairSemantics.sound14 hH)
  have hm4 : familyPairMoment B (groupedColumns node115 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value414 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node115 (EqualityPatterns.family3.label 4) = PairSemantics.raw133 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node115 PairSemantics.raw133; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical133 hH).trans (PairSemantics.sound414 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue115, PairSemantics.value0, PairSemantics.value14, PairSemantics.value46, PairSemantics.value414, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue116 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (-25 / 864)), (2, (5 / 96)), (5, (-25 / 216)), (6, (5 / 432)), (7, (5 / 27)), (8, (5 / 54)), (9, (-5 / 108)), (35, (5 / 54)), (52, (5 / 54)), (69, (5 / 27)), (70, (5 / 54)), (71, (5 / 54))]

theorem singlePair116 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node116 node116Labels = Sparse.eval singlePairValue116 (familyPairVector B) := by
  have hp := single_label_three B hB node116
  have hl : node116Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node116 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node116 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node116 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node116 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node116 (EqualityPatterns.family3.label 1) = PairSemantics.raw5136 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node116 PairSemantics.raw5136; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5136 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node116 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node116 (EqualityPatterns.family3.label 2) = PairSemantics.raw5159 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node116 PairSemantics.raw5159; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5159 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node116 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value15 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node116 (EqualityPatterns.family3.label 3) = PairSemantics.raw186 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node116 PairSemantics.raw186; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical186 hH).trans (PairSemantics.sound15 hH)
  have hm4 : familyPairMoment B (groupedColumns node116 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value416 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node116 (EqualityPatterns.family3.label 4) = PairSemantics.raw134 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node116 PairSemantics.raw134; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical134 hH).trans (PairSemantics.sound416 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue116, PairSemantics.value0, PairSemantics.value15, PairSemantics.value46, PairSemantics.value416, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue117 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 96)), (2, (-5 / 216)), (5, (-5 / 72)), (6, (5 / 288)), (7, (5 / 27)), (9, (-5 / 108)), (35, (5 / 18)), (67, (5 / 54)), (69, (5 / 54)), (70, (5 / 27)), (257, (5 / 54))]

theorem singlePair117 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node117 node117Labels = Sparse.eval singlePairValue117 (familyPairVector B) := by
  have hp := single_label_three B hB node117
  have hl : node117Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node117 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node117 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node117 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node117 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node117 (EqualityPatterns.family3.label 1) = PairSemantics.raw5142 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node117 PairSemantics.raw5142; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5142 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node117 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node117 (EqualityPatterns.family3.label 2) = PairSemantics.raw5154 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node117 PairSemantics.raw5154; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5154 hH).trans (PairSemantics.sound10 hH)
  have hm3 : familyPairMoment B (groupedColumns node117 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value15 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node117 (EqualityPatterns.family3.label 3) = PairSemantics.raw186 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node117 PairSemantics.raw186; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical186 hH).trans (PairSemantics.sound15 hH)
  have hm4 : familyPairMoment B (groupedColumns node117 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value326 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node117 (EqualityPatterns.family3.label 4) = PairSemantics.raw135 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node117 PairSemantics.raw135; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical135 hH).trans (PairSemantics.sound326 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue117, PairSemantics.value0, PairSemantics.value10, PairSemantics.value15, PairSemantics.value46, PairSemantics.value326, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue118 : Sparse (Fin 909) := [(0, (29 / 864)), (1, (-25 / 288)), (2, (-55 / 864)), (3, (-5 / 27)), (5, (25 / 108)), (6, (-5 / 216)), (7, (-10 / 27)), (8, (-10 / 27)), (9, (-5 / 54)), (35, (-5 / 27)), (58, (5 / 864)), (69, (-5 / 27)), (70, (-5 / 54)), (71, (-5 / 27))]

theorem singlePair118 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node118 node118Labels = Sparse.eval singlePairValue118 (familyPairVector B) := by
  have hp := single_label_three B hB node118
  have hl : node118Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node118 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node118 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node118 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node118 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node118 (EqualityPatterns.family3.label 1) = PairSemantics.raw5123 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node118 PairSemantics.raw5123; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5123 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node118 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node118 (EqualityPatterns.family3.label 2) = PairSemantics.raw5180 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node118 PairSemantics.raw5180; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5180 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node118 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value296 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node118 (EqualityPatterns.family3.label 3) = PairSemantics.raw187 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node118 PairSemantics.raw187; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical187 hH).trans (PairSemantics.sound296 hH)
  have hm4 : familyPairMoment B (groupedColumns node118 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1539 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node118 (EqualityPatterns.family3.label 4) = PairSemantics.raw136 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node118 PairSemantics.raw136; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical136 hH).trans (PairSemantics.sound1539 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue118, PairSemantics.value0, PairSemantics.value11, PairSemantics.value46, PairSemantics.value296, PairSemantics.value1539, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue119 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-65 / 864)), (2, (-35 / 864)), (5, (-5 / 108)), (6, (35 / 864)), (7, (5 / 54)), (35, (5 / 27)), (58, (-5 / 864)), (70, (5 / 54))]

theorem singlePair119 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node119 node119Labels = Sparse.eval singlePairValue119 (familyPairVector B) := by
  have hp := single_label_three B hB node119
  have hl : node119Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node119 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node119 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node119 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node119 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node119 (EqualityPatterns.family3.label 1) = PairSemantics.raw5125 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node119 PairSemantics.raw5125; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5125 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node119 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node119 (EqualityPatterns.family3.label 2) = PairSemantics.raw5179 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node119 PairSemantics.raw5179; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5179 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node119 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value67 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node119 (EqualityPatterns.family3.label 3) = PairSemantics.raw188 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node119 PairSemantics.raw188; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical188 hH).trans (PairSemantics.sound67 hH)
  have hm4 : familyPairMoment B (groupedColumns node119 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value435 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node119 (EqualityPatterns.family3.label 4) = PairSemantics.raw137 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node119 PairSemantics.raw137; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical137 hH).trans (PairSemantics.sound435 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue119, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value67, PairSemantics.value435, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
