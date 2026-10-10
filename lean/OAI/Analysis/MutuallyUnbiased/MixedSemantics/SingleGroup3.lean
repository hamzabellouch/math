import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleRules
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical239
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical240
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical280
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound9

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue56 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 216)), (2, (5 / 216)), (5, (5 / 54)), (6, (5 / 432)), (201, (5 / 9))]

theorem singlePair56 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node56 node56Labels = Sparse.eval singlePairValue56 (familyPairVector B) := by
  have hp := single_label_three B hB node56
  have hl : node56Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node56 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node56 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node56 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node56 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node56 (EqualityPatterns.family3.label 1) = PairSemantics.raw213 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node56 PairSemantics.raw213; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical213 hH).trans (PairSemantics.sound16 hH)
  have hm2 : familyPairMoment B (groupedColumns node56 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node56 (EqualityPatterns.family3.label 2) = PairSemantics.raw8979 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node56 PairSemantics.raw8979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8979 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node56 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value9 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node56 (EqualityPatterns.family3.label 3) = PairSemantics.raw199 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node56 PairSemantics.raw199; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical199 hH).trans (PairSemantics.sound9 hH)
  have hm4 : familyPairMoment B (groupedColumns node56 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value218 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node56 (EqualityPatterns.family3.label 4) = PairSemantics.raw72 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node56 PairSemantics.raw72; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical72 hH).trans (PairSemantics.sound218 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue56, PairSemantics.value0, PairSemantics.value9, PairSemantics.value11, PairSemantics.value16, PairSemantics.value218, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue57 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 36)), (5, (5 / 36)), (6, (5 / 36)), (82, (5 / 9))]

theorem singlePair57 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node57 node57Labels = Sparse.eval singlePairValue57 (familyPairVector B) := by
  have hp := single_label_three B hB node57
  have hl : node57Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node57 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node57 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node57 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node57 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value9 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node57 (EqualityPatterns.family3.label 1) = PairSemantics.raw214 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node57 PairSemantics.raw214; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical214 hH).trans (PairSemantics.sound9 hH)
  have hm2 : familyPairMoment B (groupedColumns node57 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node57 (EqualityPatterns.family3.label 2) = PairSemantics.raw8985 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node57 PairSemantics.raw8985; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8985 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node57 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value2 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node57 (EqualityPatterns.family3.label 3) = PairSemantics.raw200 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node57 PairSemantics.raw200; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical200 hH).trans (PairSemantics.sound2 hH)
  have hm4 : familyPairMoment B (groupedColumns node57 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value33 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node57 (EqualityPatterns.family3.label 4) = PairSemantics.raw73 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node57 PairSemantics.raw73; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical73 hH).trans (PairSemantics.sound33 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue57, PairSemantics.value0, PairSemantics.value2, PairSemantics.value4, PairSemantics.value9, PairSemantics.value33, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue58 : Sparse (Fin 909) := [(0, (7 / 288)), (2, (5 / 432)), (3, (-5 / 27)), (5, (5 / 24)), (6, (-5 / 216)), (7, (-5 / 54)), (9, (5 / 72)), (13, (-10 / 27)), (35, (-20 / 27)), (52, (-20 / 27)), (58, (-5 / 864)), (60, (-25 / 54)), (69, (-5 / 54)), (70, (-5 / 54)), (128, (-10 / 27)), (257, (-5 / 27)), (260, (5 / 18)), (495, (-5 / 18))]

theorem singlePair58 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node58 node58Labels = Sparse.eval singlePairValue58 (familyPairVector B) := by
  have hp := single_label_three B hB node58
  have hl : node58Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node58 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node58 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node58 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node58 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node58 (EqualityPatterns.family3.label 1) = PairSemantics.raw894 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node58 PairSemantics.raw894; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical894 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node58 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node58 (EqualityPatterns.family3.label 2) = PairSemantics.raw7653 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node58 PairSemantics.raw7653; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7653 hH).trans (PairSemantics.sound26 hH)
  have hm3 : familyPairMoment B (groupedColumns node58 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value67 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node58 (EqualityPatterns.family3.label 3) = PairSemantics.raw183 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node58 PairSemantics.raw183; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical183 hH).trans (PairSemantics.sound67 hH)
  have hm4 : familyPairMoment B (groupedColumns node58 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1385 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node58 (EqualityPatterns.family3.label 4) = PairSemantics.raw76 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node58 PairSemantics.raw76; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical76 hH).trans (PairSemantics.sound1385 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue58, PairSemantics.value0, PairSemantics.value26, PairSemantics.value67, PairSemantics.value1385, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue59 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (35 / 432)), (2, (5 / 54)), (5, (-5 / 54)), (9, (-5 / 108)), (52, (5 / 27)), (58, (5 / 432)), (128, (5 / 27)), (495, (5 / 27))]

theorem singlePair59 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node59 node59Labels = Sparse.eval singlePairValue59 (familyPairVector B) := by
  have hp := single_label_three B hB node59
  have hl : node59Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node59 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node59 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node59 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node59 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node59 (EqualityPatterns.family3.label 1) = PairSemantics.raw893 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node59 PairSemantics.raw893; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical893 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node59 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node59 (EqualityPatterns.family3.label 2) = PairSemantics.raw7656 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node59 PairSemantics.raw7656; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7656 hH).trans (PairSemantics.sound26 hH)
  have hm3 : familyPairMoment B (groupedColumns node59 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value14 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node59 (EqualityPatterns.family3.label 3) = PairSemantics.raw185 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node59 PairSemantics.raw185; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical185 hH).trans (PairSemantics.sound14 hH)
  have hm4 : familyPairMoment B (groupedColumns node59 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value311 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node59 (EqualityPatterns.family3.label 4) = PairSemantics.raw77 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node59 PairSemantics.raw77; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical77 hH).trans (PairSemantics.sound311 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue59, PairSemantics.value0, PairSemantics.value14, PairSemantics.value26, PairSemantics.value311, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue60 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 864)), (2, (5 / 864)), (5, (-5 / 72)), (6, (5 / 432)), (7, (5 / 54)), (9, (-5 / 108)), (35, (5 / 27)), (52, (5 / 54)), (60, (5 / 54)), (69, (5 / 54)), (70, (5 / 54)), (257, (5 / 54)), (260, (-5 / 18))]

theorem singlePair60 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node60 node60Labels = Sparse.eval singlePairValue60 (familyPairVector B) := by
  have hp := single_label_three B hB node60
  have hl : node60Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node60 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node60 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node60 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node60 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node60 (EqualityPatterns.family3.label 1) = PairSemantics.raw896 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node60 PairSemantics.raw896; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical896 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node60 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node60 (EqualityPatterns.family3.label 2) = PairSemantics.raw7656 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node60 PairSemantics.raw7656; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7656 hH).trans (PairSemantics.sound26 hH)
  have hm3 : familyPairMoment B (groupedColumns node60 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value15 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node60 (EqualityPatterns.family3.label 3) = PairSemantics.raw186 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node60 PairSemantics.raw186; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical186 hH).trans (PairSemantics.sound15 hH)
  have hm4 : familyPairMoment B (groupedColumns node60 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value309 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node60 (EqualityPatterns.family3.label 4) = PairSemantics.raw78 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node60 PairSemantics.raw78; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical78 hH).trans (PairSemantics.sound309 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue60, PairSemantics.value0, PairSemantics.value10, PairSemantics.value15, PairSemantics.value26, PairSemantics.value309, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue61 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-35 / 864)), (2, (-5 / 108)), (3, (-5 / 54)), (5, (5 / 54)), (6, (-5 / 432)), (7, (-5 / 27)), (9, (-5 / 54)), (35, (-5 / 27)), (52, (-5 / 27)), (58, (5 / 864)), (69, (-5 / 27)), (70, (-5 / 54)), (71, (-5 / 27))]

theorem singlePair61 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node61 node61Labels = Sparse.eval singlePairValue61 (familyPairVector B) := by
  have hp := single_label_three B hB node61
  have hl : node61Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node61 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node61 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node61 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node61 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node61 (EqualityPatterns.family3.label 1) = PairSemantics.raw879 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node61 PairSemantics.raw879; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical879 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node61 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node61 (EqualityPatterns.family3.label 2) = PairSemantics.raw7680 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node61 PairSemantics.raw7680; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7680 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node61 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value296 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node61 (EqualityPatterns.family3.label 3) = PairSemantics.raw187 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node61 PairSemantics.raw187; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical187 hH).trans (PairSemantics.sound296 hH)
  have hm4 : familyPairMoment B (groupedColumns node61 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2378 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node61 (EqualityPatterns.family3.label 4) = PairSemantics.raw79 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node61 PairSemantics.raw79; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical79 hH).trans (PairSemantics.sound2378 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue61, PairSemantics.value0, PairSemantics.value10, PairSemantics.value65, PairSemantics.value296, PairSemantics.value2378, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue62 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (5 / 432)), (2, (185 / 864)), (5, (5 / 216)), (35, (5 / 54)), (58, (-5 / 864)), (70, (5 / 54))]

theorem singlePair62 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node62 node62Labels = Sparse.eval singlePairValue62 (familyPairVector B) := by
  have hp := single_label_three B hB node62
  have hl : node62Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node62 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node62 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node62 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node62 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node62 (EqualityPatterns.family3.label 1) = PairSemantics.raw881 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node62 PairSemantics.raw881; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical881 hH).trans (PairSemantics.sound3 hH)
  have hm2 : familyPairMoment B (groupedColumns node62 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node62 (EqualityPatterns.family3.label 2) = PairSemantics.raw7679 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node62 PairSemantics.raw7679; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7679 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node62 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value67 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node62 (EqualityPatterns.family3.label 3) = PairSemantics.raw188 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node62 PairSemantics.raw188; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical188 hH).trans (PairSemantics.sound67 hH)
  have hm4 : familyPairMoment B (groupedColumns node62 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value734 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node62 (EqualityPatterns.family3.label 4) = PairSemantics.raw80 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node62 PairSemantics.raw80; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical80 hH).trans (PairSemantics.sound734 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue62, PairSemantics.value0, PairSemantics.value3, PairSemantics.value65, PairSemantics.value67, PairSemantics.value734, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue63 : Sparse (Fin 909) := [(0, (37 / 864)), (1, (-5 / 216)), (2, (-35 / 432)), (5, (5 / 18)), (6, (-5 / 144)), (8, (-10 / 27)), (9, (-5 / 54)), (52, (-5 / 27)), (58, (5 / 864)), (69, (-5 / 54)), (71, (-10 / 27))]

theorem singlePair63 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node63 node63Labels = Sparse.eval singlePairValue63 (familyPairVector B) := by
  have hp := single_label_three B hB node63
  have hl : node63Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node63 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node63 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node63 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node63 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node63 (EqualityPatterns.family3.label 1) = PairSemantics.raw883 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node63 PairSemantics.raw883; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical883 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node63 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node63 (EqualityPatterns.family3.label 2) = PairSemantics.raw7676 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node63 PairSemantics.raw7676; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7676 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node63 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value296 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node63 (EqualityPatterns.family3.label 3) = PairSemantics.raw187 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node63 PairSemantics.raw187; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical187 hH).trans (PairSemantics.sound296 hH)
  have hm4 : familyPairMoment B (groupedColumns node63 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2377 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node63 (EqualityPatterns.family3.label 4) = PairSemantics.raw81 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node63 PairSemantics.raw81; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical81 hH).trans (PairSemantics.sound2377 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue63, PairSemantics.value0, PairSemantics.value26, PairSemantics.value65, PairSemantics.value296, PairSemantics.value2377, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue64 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-35 / 864)), (2, (-5 / 108)), (5, (-5 / 108)), (6, (5 / 216)), (58, (-5 / 864)), (71, (5 / 54))]

theorem singlePair64 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node64 node64Labels = Sparse.eval singlePairValue64 (familyPairVector B) := by
  have hp := single_label_three B hB node64
  have hl : node64Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node64 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node64 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node64 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node64 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node64 (EqualityPatterns.family3.label 1) = PairSemantics.raw884 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node64 PairSemantics.raw884; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical884 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node64 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node64 (EqualityPatterns.family3.label 2) = PairSemantics.raw7677 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node64 PairSemantics.raw7677; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7677 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node64 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value67 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node64 (EqualityPatterns.family3.label 3) = PairSemantics.raw188 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node64 PairSemantics.raw188; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical188 hH).trans (PairSemantics.sound67 hH)
  have hm4 : familyPairMoment B (groupedColumns node64 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value732 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node64 (EqualityPatterns.family3.label 4) = PairSemantics.raw82 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node64 PairSemantics.raw82; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical82 hH).trans (PairSemantics.sound732 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue64, PairSemantics.value0, PairSemantics.value10, PairSemantics.value65, PairSemantics.value67, PairSemantics.value732, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue65 : Sparse (Fin 909) := [(0, (29 / 864)), (1, (-5 / 216)), (2, (-55 / 432)), (3, (-5 / 9)), (5, (5 / 18)), (6, (-5 / 144)), (7, (-5 / 9)), (9, (-5 / 54)), (35, (-5 / 9)), (52, (-5 / 9)), (58, (5 / 864)), (69, (-5 / 18)), (70, (-5 / 27))]

theorem singlePair65 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node65 node65Labels = Sparse.eval singlePairValue65 (familyPairVector B) := by
  have hp := single_label_three B hB node65
  have hl : node65Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node65 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node65 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node65 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node65 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node65 (EqualityPatterns.family3.label 1) = PairSemantics.raw894 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node65 PairSemantics.raw894; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical894 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node65 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node65 (EqualityPatterns.family3.label 2) = PairSemantics.raw7667 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node65 PairSemantics.raw7667; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7667 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node65 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value296 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node65 (EqualityPatterns.family3.label 3) = PairSemantics.raw187 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node65 PairSemantics.raw187; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical187 hH).trans (PairSemantics.sound296 hH)
  have hm4 : familyPairMoment B (groupedColumns node65 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2124 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node65 (EqualityPatterns.family3.label 4) = PairSemantics.raw83 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node65 PairSemantics.raw83; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical83 hH).trans (PairSemantics.sound2124 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue65, PairSemantics.value0, PairSemantics.value11, PairSemantics.value26, PairSemantics.value296, PairSemantics.value2124, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue66 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (5 / 108)), (2, (5 / 48)), (5, (-5 / 54)), (6, (5 / 144)), (52, (5 / 27)), (58, (-5 / 864)), (69, (5 / 54))]

theorem singlePair66 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node66 node66Labels = Sparse.eval singlePairValue66 (familyPairVector B) := by
  have hp := single_label_three B hB node66
  have hl : node66Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node66 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node66 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node66 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node66 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node66 (EqualityPatterns.family3.label 1) = PairSemantics.raw893 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node66 PairSemantics.raw893; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical893 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node66 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node66 (EqualityPatterns.family3.label 2) = PairSemantics.raw7669 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node66 PairSemantics.raw7669; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7669 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node66 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value67 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node66 (EqualityPatterns.family3.label 3) = PairSemantics.raw188 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node66 PairSemantics.raw188; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical188 hH).trans (PairSemantics.sound67 hH)
  have hm4 : familyPairMoment B (groupedColumns node66 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value553 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node66 (EqualityPatterns.family3.label 4) = PairSemantics.raw84 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node66 PairSemantics.raw84; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical84 hH).trans (PairSemantics.sound553 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue66, PairSemantics.value0, PairSemantics.value11, PairSemantics.value26, PairSemantics.value67, PairSemantics.value553, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue67 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 864)), (2, (5 / 864)), (3, (5 / 54)), (5, (5 / 216)), (6, (5 / 288)), (9, (5 / 216)), (13, (5 / 54)), (35, (5 / 18)), (52, (5 / 27)), (58, (-5 / 864)), (60, (5 / 27)), (128, (5 / 54)), (257, (5 / 54)), (495, (5 / 54))]

theorem singlePair67 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node67 node67Labels = Sparse.eval singlePairValue67 (familyPairVector B) := by
  have hp := single_label_three B hB node67
  have hl : node67Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node67 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node67 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node67 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node67 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node67 (EqualityPatterns.family3.label 1) = PairSemantics.raw896 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node67 PairSemantics.raw896; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical896 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node67 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node67 (EqualityPatterns.family3.label 2) = PairSemantics.raw7666 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node67 PairSemantics.raw7666; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7666 hH).trans (PairSemantics.sound26 hH)
  have hm3 : familyPairMoment B (groupedColumns node67 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value67 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node67 (EqualityPatterns.family3.label 3) = PairSemantics.raw188 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node67 PairSemantics.raw188; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical188 hH).trans (PairSemantics.sound67 hH)
  have hm4 : familyPairMoment B (groupedColumns node67 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value310 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node67 (EqualityPatterns.family3.label 4) = PairSemantics.raw85 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node67 PairSemantics.raw85; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical85 hH).trans (PairSemantics.sound310 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue67, PairSemantics.value0, PairSemantics.value10, PairSemantics.value26, PairSemantics.value67, PairSemantics.value310, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue68 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-25 / 288)), (2, (-25 / 432)), (3, (5 / 54)), (5, (-5 / 108)), (6, (-5 / 864)), (7, (5 / 27)), (9, (5 / 108)), (35, (5 / 27)), (52, (5 / 54)), (69, (5 / 54)), (70, (5 / 54))]

theorem singlePair68 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node68 node68Labels = Sparse.eval singlePairValue68 (familyPairVector B) := by
  have hp := single_label_three B hB node68
  have hl : node68Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node68 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node68 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node68 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node68 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node68 (EqualityPatterns.family3.label 1) = PairSemantics.raw891 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node68 PairSemantics.raw891; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical891 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node68 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node68 (EqualityPatterns.family3.label 2) = PairSemantics.raw7672 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node68 PairSemantics.raw7672; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7672 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node68 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value68 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node68 (EqualityPatterns.family3.label 3) = PairSemantics.raw189 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node68 PairSemantics.raw189; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical189 hH).trans (PairSemantics.sound68 hH)
  have hm4 : familyPairMoment B (groupedColumns node68 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value639 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node68 (EqualityPatterns.family3.label 4) = PairSemantics.raw86 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node68 PairSemantics.raw86; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical86 hH).trans (PairSemantics.sound639 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue68, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value68, PairSemantics.value639, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue69 : Sparse (Fin 909) := [(0, (17 / 432)), (1, (5 / 54)), (2, (25 / 432)), (5, (-5 / 54)), (8, (5 / 27)), (9, (5 / 108)), (71, (5 / 27))]

theorem singlePair69 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node69 node69Labels = Sparse.eval singlePairValue69 (familyPairVector B) := by
  have hp := single_label_three B hB node69
  have hl : node69Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node69 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node69 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node69 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node69 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node69 (EqualityPatterns.family3.label 1) = PairSemantics.raw893 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node69 PairSemantics.raw893; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical893 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node69 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node69 (EqualityPatterns.family3.label 2) = PairSemantics.raw7670 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node69 PairSemantics.raw7670; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7670 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node69 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value68 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node69 (EqualityPatterns.family3.label 3) = PairSemantics.raw189 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node69 PairSemantics.raw189; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical189 hH).trans (PairSemantics.sound68 hH)
  have hm4 : familyPairMoment B (groupedColumns node69 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value733 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node69 (EqualityPatterns.family3.label 4) = PairSemantics.raw87 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node69 PairSemantics.raw87; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical87 hH).trans (PairSemantics.sound733 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue69, PairSemantics.value0, PairSemantics.value26, PairSemantics.value65, PairSemantics.value68, PairSemantics.value733, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue70 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-35 / 432)), (2, (-25 / 432)), (5, (5 / 54)), (6, (-5 / 108)), (9, (5 / 108)), (58, (5 / 432))]

theorem singlePair70 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node70 node70Labels = Sparse.eval singlePairValue70 (familyPairVector B) := by
  have hp := single_label_three B hB node70
  have hl : node70Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node70 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node70 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node70 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node70 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node70 (EqualityPatterns.family3.label 1) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node70 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node70 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node70 (EqualityPatterns.family3.label 2) = PairSemantics.raw7671 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node70 PairSemantics.raw7671; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7671 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node70 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value14 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node70 (EqualityPatterns.family3.label 3) = PairSemantics.raw190 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node70 PairSemantics.raw190; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical190 hH).trans (PairSemantics.sound14 hH)
  have hm4 : familyPairMoment B (groupedColumns node70 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value143 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node70 (EqualityPatterns.family3.label 4) = PairSemantics.raw88 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node70 PairSemantics.raw88; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical88 hH).trans (PairSemantics.sound143 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue70, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value14, PairSemantics.value143, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue71 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 144)), (2, (5 / 27)), (5, (-5 / 108)), (9, (-5 / 108)), (35, (-5 / 27)), (70, (-5 / 27))]

theorem singlePair71 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node71 node71Labels = Sparse.eval singlePairValue71 (familyPairVector B) := by
  have hp := single_label_three B hB node71
  have hl : node71Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node71 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node71 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node71 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node71 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node71 (EqualityPatterns.family3.label 1) = PairSemantics.raw887 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node71 PairSemantics.raw887; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical887 hH).trans (PairSemantics.sound3 hH)
  have hm2 : familyPairMoment B (groupedColumns node71 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node71 (EqualityPatterns.family3.label 2) = PairSemantics.raw7685 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node71 PairSemantics.raw7685; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7685 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node71 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value15 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node71 (EqualityPatterns.family3.label 3) = PairSemantics.raw191 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node71 PairSemantics.raw191; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical191 hH).trans (PairSemantics.sound15 hH)
  have hm4 : familyPairMoment B (groupedColumns node71 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value195 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node71 (EqualityPatterns.family3.label 4) = PairSemantics.raw89 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node71 PairSemantics.raw89; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical89 hH).trans (PairSemantics.sound195 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue71, PairSemantics.value0, PairSemantics.value3, PairSemantics.value11, PairSemantics.value15, PairSemantics.value195, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
