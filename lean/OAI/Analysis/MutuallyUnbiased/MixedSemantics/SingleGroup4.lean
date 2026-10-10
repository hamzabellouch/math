import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleRules
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical238
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical239
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical241
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound5

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue72 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-35 / 432)), (2, (-5 / 144)), (6, (5 / 432)), (9, (-5 / 108)), (52, (-5 / 27)), (69, (-5 / 27))]

theorem singlePair72 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node72 node72Labels = Sparse.eval singlePairValue72 (familyPairVector B) := by
  have hp := single_label_three B hB node72
  have hl : node72Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node72 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node72 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node72 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node72 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node72 (EqualityPatterns.family3.label 1) = PairSemantics.raw898 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node72 PairSemantics.raw898; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical898 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node72 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node72 (EqualityPatterns.family3.label 2) = PairSemantics.raw7671 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node72 PairSemantics.raw7671; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7671 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node72 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value15 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node72 (EqualityPatterns.family3.label 3) = PairSemantics.raw191 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node72 PairSemantics.raw191; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical191 hH).trans (PairSemantics.sound15 hH)
  have hm4 : familyPairMoment B (groupedColumns node72 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value166 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node72 (EqualityPatterns.family3.label 4) = PairSemantics.raw90 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node72 PairSemantics.raw90; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical90 hH).trans (PairSemantics.sound166 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue72, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value15, PairSemantics.value166, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue73 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 144)), (2, (25 / 144)), (5, (-5 / 108)), (6, (5 / 432)), (9, (-5 / 108)), (35, (-5 / 27)), (60, (-5 / 27)), (257, (-5 / 27))]

theorem singlePair73 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node73 node73Labels = Sparse.eval singlePairValue73 (familyPairVector B) := by
  have hp := single_label_three B hB node73
  have hl : node73Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node73 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node73 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node73 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node73 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node73 (EqualityPatterns.family3.label 1) = PairSemantics.raw901 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node73 PairSemantics.raw901; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical901 hH).trans (PairSemantics.sound3 hH)
  have hm2 : familyPairMoment B (groupedColumns node73 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node73 (EqualityPatterns.family3.label 2) = PairSemantics.raw7663 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node73 PairSemantics.raw7663; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7663 hH).trans (PairSemantics.sound26 hH)
  have hm3 : familyPairMoment B (groupedColumns node73 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value15 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node73 (EqualityPatterns.family3.label 3) = PairSemantics.raw191 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node73 PairSemantics.raw191; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical191 hH).trans (PairSemantics.sound15 hH)
  have hm4 : familyPairMoment B (groupedColumns node73 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value79 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node73 (EqualityPatterns.family3.label 4) = PairSemantics.raw91 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node73 PairSemantics.raw91; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical91 hH).trans (PairSemantics.sound79 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue73, PairSemantics.value0, PairSemantics.value3, PairSemantics.value15, PairSemantics.value26, PairSemantics.value79, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue74 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-55 / 864)), (2, (-35 / 864)), (5, (-5 / 216)), (6, (-5 / 432)), (7, (5 / 54)), (9, (5 / 108)), (35, (5 / 54)), (54, (-5 / 18)), (259, (-5 / 18)), (260, (-5 / 18))]

theorem singlePair74 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node74 node74Labels = Sparse.eval singlePairValue74 (familyPairVector B) := by
  have hp := single_label_three B hB node74
  have hl : node74Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node74 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node74 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node74 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node74 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node74 (EqualityPatterns.family3.label 1) = PairSemantics.raw906 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node74 PairSemantics.raw906; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical906 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node74 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node74 (EqualityPatterns.family3.label 2) = PairSemantics.raw7637 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node74 PairSemantics.raw7637; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7637 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node74 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value68 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node74 (EqualityPatterns.family3.label 3) = PairSemantics.raw189 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node74 PairSemantics.raw189; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical189 hH).trans (PairSemantics.sound68 hH)
  have hm4 : familyPairMoment B (groupedColumns node74 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value315 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node74 (EqualityPatterns.family3.label 4) = PairSemantics.raw92 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node74 PairSemantics.raw92; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical92 hH).trans (PairSemantics.sound315 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue74, PairSemantics.value0, PairSemantics.value10, PairSemantics.value46, PairSemantics.value68, PairSemantics.value315, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue75 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-25 / 432)), (2, (-5 / 432)), (5, (-5 / 108)), (6, (5 / 432)), (9, (-5 / 108)), (259, (5 / 9))]

theorem singlePair75 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node75 node75Labels = Sparse.eval singlePairValue75 (familyPairVector B) := by
  have hp := single_label_three B hB node75
  have hl : node75Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node75 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node75 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node75 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node75 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node75 (EqualityPatterns.family3.label 1) = PairSemantics.raw909 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node75 PairSemantics.raw909; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical909 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node75 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node75 (EqualityPatterns.family3.label 2) = PairSemantics.raw7639 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node75 PairSemantics.raw7639; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7639 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node75 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value15 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node75 (EqualityPatterns.family3.label 3) = PairSemantics.raw191 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node75 PairSemantics.raw191; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical191 hH).trans (PairSemantics.sound15 hH)
  have hm4 : familyPairMoment B (groupedColumns node75 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value84 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node75 (EqualityPatterns.family3.label 4) = PairSemantics.raw93 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node75 PairSemantics.raw93; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical93 hH).trans (PairSemantics.sound84 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue75, PairSemantics.value0, PairSemantics.value10, PairSemantics.value15, PairSemantics.value46, PairSemantics.value84, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue76 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 72)), (2, (-25 / 432)), (5, (-5 / 108)), (6, (5 / 432)), (9, (-5 / 108)), (260, (5 / 9))]

theorem singlePair76 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node76 node76Labels = Sparse.eval singlePairValue76 (familyPairVector B) := by
  have hp := single_label_three B hB node76
  have hl : node76Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node76 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node76 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node76 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node76 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node76 (EqualityPatterns.family3.label 1) = PairSemantics.raw918 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node76 PairSemantics.raw918; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical918 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node76 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node76 (EqualityPatterns.family3.label 2) = PairSemantics.raw7627 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node76 PairSemantics.raw7627; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7627 hH).trans (PairSemantics.sound10 hH)
  have hm3 : familyPairMoment B (groupedColumns node76 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value15 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node76 (EqualityPatterns.family3.label 3) = PairSemantics.raw191 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node76 PairSemantics.raw191; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical191 hH).trans (PairSemantics.sound15 hH)
  have hm4 : familyPairMoment B (groupedColumns node76 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value86 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node76 (EqualityPatterns.family3.label 4) = PairSemantics.raw94 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node76 PairSemantics.raw94; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical94 hH).trans (PairSemantics.sound86 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue76, PairSemantics.value0, PairSemantics.value10, PairSemantics.value15, PairSemantics.value86, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue77 : Sparse (Fin 909) := [(0, (41 / 864)), (1, (25 / 864)), (2, (55 / 864)), (3, (-5 / 54)), (5, (5 / 216)), (6, (5 / 864)), (7, (-5 / 27)), (8, (-5 / 54)), (11, (-5 / 54)), (26, (-5 / 54)), (35, (-5 / 18)), (52, (-5 / 54)), (228, (5 / 18))]

theorem singlePair77 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node77 node77Labels = Sparse.eval singlePairValue77 (familyPairVector B) := by
  have hp := single_label_three B hB node77
  have hl : node77Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node77 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node77 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node77 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node77 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node77 (EqualityPatterns.family3.label 1) = PairSemantics.raw863 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node77 PairSemantics.raw863; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical863 hH).trans (PairSemantics.sound118 hH)
  have hm2 : familyPairMoment B (groupedColumns node77 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node77 (EqualityPatterns.family3.label 2) = PairSemantics.raw7733 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node77 PairSemantics.raw7733; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7733 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node77 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node77 (EqualityPatterns.family3.label 3) = PairSemantics.raw192 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node77 PairSemantics.raw192; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical192 hH).trans (PairSemantics.sound16 hH)
  have hm4 : familyPairMoment B (groupedColumns node77 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2381 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node77 (EqualityPatterns.family3.label 4) = PairSemantics.raw95 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node77 PairSemantics.raw95; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical95 hH).trans (PairSemantics.sound2381 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue77, PairSemantics.value0, PairSemantics.value16, PairSemantics.value65, PairSemantics.value118, PairSemantics.value2381, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue78 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (5 / 144)), (2, (-25 / 432)), (5, (-5 / 216)), (6, (-25 / 432)), (11, (5 / 54)), (35, (5 / 54))]

theorem singlePair78 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node78 node78Labels = Sparse.eval singlePairValue78 (familyPairVector B) := by
  have hp := single_label_three B hB node78
  have hl : node78Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node78 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node78 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node78 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node78 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node78 (EqualityPatterns.family3.label 1) = PairSemantics.raw864 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node78 PairSemantics.raw864; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical864 hH).trans (PairSemantics.sound24 hH)
  have hm2 : familyPairMoment B (groupedColumns node78 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node78 (EqualityPatterns.family3.label 2) = PairSemantics.raw7732 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node78 PairSemantics.raw7732; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7732 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node78 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node78 (EqualityPatterns.family3.label 3) = PairSemantics.raw193 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node78 PairSemantics.raw193; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical193 hH).trans (PairSemantics.sound8 hH)
  have hm4 : familyPairMoment B (groupedColumns node78 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value740 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node78 (EqualityPatterns.family3.label 4) = PairSemantics.raw96 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node78 PairSemantics.raw96; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical96 hH).trans (PairSemantics.sound740 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue78, PairSemantics.value0, PairSemantics.value8, PairSemantics.value24, PairSemantics.value65, PairSemantics.value740, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue79 : Sparse (Fin 909) := [(0, (49 / 864)), (1, (-35 / 216)), (2, (-55 / 432)), (3, (-5 / 27)), (5, (5 / 54)), (6, (5 / 864)), (7, (-5 / 54)), (8, (-5 / 27)), (35, (-5 / 27)), (52, (-10 / 27))]

theorem singlePair79 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node79 node79Labels = Sparse.eval singlePairValue79 (familyPairVector B) := by
  have hp := single_label_three B hB node79
  have hl : node79Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node79 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node79 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node79 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node79 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value383 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node79 (EqualityPatterns.family3.label 1) = PairSemantics.raw866 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node79 PairSemantics.raw866; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical866 hH).trans (PairSemantics.sound383 hH)
  have hm2 : familyPairMoment B (groupedColumns node79 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node79 (EqualityPatterns.family3.label 2) = PairSemantics.raw7729 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node79 PairSemantics.raw7729; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7729 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node79 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node79 (EqualityPatterns.family3.label 3) = PairSemantics.raw192 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node79 PairSemantics.raw192; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical192 hH).trans (PairSemantics.sound16 hH)
  have hm4 : familyPairMoment B (groupedColumns node79 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2379 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node79 (EqualityPatterns.family3.label 4) = PairSemantics.raw97 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node79 PairSemantics.raw97; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical97 hH).trans (PairSemantics.sound2379 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue79, PairSemantics.value0, PairSemantics.value16, PairSemantics.value65, PairSemantics.value383, PairSemantics.value2379, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue80 : Sparse (Fin 909) := [(0, (13 / 288)), (1, (5 / 144)), (2, (-5 / 108)), (5, (-5 / 108)), (6, (-5 / 96)), (52, (5 / 54))]

theorem singlePair80 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node80 node80Labels = Sparse.eval singlePairValue80 (familyPairVector B) := by
  have hp := single_label_three B hB node80
  have hl : node80Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node80 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node80 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node80 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node80 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node80 (EqualityPatterns.family3.label 1) = PairSemantics.raw867 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node80 PairSemantics.raw867; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical867 hH).trans (PairSemantics.sound118 hH)
  have hm2 : familyPairMoment B (groupedColumns node80 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node80 (EqualityPatterns.family3.label 2) = PairSemantics.raw7730 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node80 PairSemantics.raw7730; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7730 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node80 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node80 (EqualityPatterns.family3.label 3) = PairSemantics.raw193 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node80 PairSemantics.raw193; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical193 hH).trans (PairSemantics.sound8 hH)
  have hm4 : familyPairMoment B (groupedColumns node80 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value736 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node80 (EqualityPatterns.family3.label 4) = PairSemantics.raw98 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node80 PairSemantics.raw98; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical98 hH).trans (PairSemantics.sound736 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue80, PairSemantics.value0, PairSemantics.value8, PairSemantics.value65, PairSemantics.value118, PairSemantics.value736, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue81 : Sparse (Fin 909) := [(0, (13 / 288)), (1, (25 / 864)), (2, (5 / 216)), (5, (5 / 24)), (7, (5 / 54)), (8, (5 / 54)), (35, (5 / 54))]

theorem singlePair81 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node81 node81Labels = Sparse.eval singlePairValue81 (familyPairVector B) := by
  have hp := single_label_three B hB node81
  have hl : node81Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node81 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node81 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node81 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node81 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node81 (EqualityPatterns.family3.label 1) = PairSemantics.raw867 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node81 PairSemantics.raw867; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical867 hH).trans (PairSemantics.sound118 hH)
  have hm2 : familyPairMoment B (groupedColumns node81 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node81 (EqualityPatterns.family3.label 2) = PairSemantics.raw7732 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node81 PairSemantics.raw7732; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7732 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node81 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value9 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node81 (EqualityPatterns.family3.label 3) = PairSemantics.raw194 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node81 PairSemantics.raw194; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical194 hH).trans (PairSemantics.sound9 hH)
  have hm4 : familyPairMoment B (groupedColumns node81 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value738 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node81 (EqualityPatterns.family3.label 4) = PairSemantics.raw99 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node81 PairSemantics.raw99; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical99 hH).trans (PairSemantics.sound738 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue81, PairSemantics.value0, PairSemantics.value9, PairSemantics.value65, PairSemantics.value118, PairSemantics.value738, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue82 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (5 / 216)), (5, (5 / 108)), (6, (95 / 432))]

theorem singlePair82 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node82 node82Labels = Sparse.eval singlePairValue82 (familyPairVector B) := by
  have hp := single_label_three B hB node82
  have hl : node82Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node82 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node82 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node82 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node82 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node82 (EqualityPatterns.family3.label 1) = PairSemantics.raw869 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node82 PairSemantics.raw869; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical869 hH).trans (PairSemantics.sound24 hH)
  have hm2 : familyPairMoment B (groupedColumns node82 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node82 (EqualityPatterns.family3.label 2) = PairSemantics.raw7731 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node82 PairSemantics.raw7731; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7731 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node82 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value2 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node82 (EqualityPatterns.family3.label 3) = PairSemantics.raw195 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node82 PairSemantics.raw195; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical195 hH).trans (PairSemantics.sound2 hH)
  have hm4 : familyPairMoment B (groupedColumns node82 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value242 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node82 (EqualityPatterns.family3.label 4) = PairSemantics.raw100 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node82 PairSemantics.raw100; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical100 hH).trans (PairSemantics.sound242 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue82, PairSemantics.value0, PairSemantics.value2, PairSemantics.value24, PairSemantics.value65, PairSemantics.value242, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue83 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (5 / 144)), (2, (-5 / 108)), (5, (-5 / 54)), (6, (5 / 216)), (11, (5 / 54)), (26, (5 / 54)), (35, (5 / 27))]

theorem singlePair83 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node83 node83Labels = Sparse.eval singlePairValue83 (familyPairVector B) := by
  have hp := single_label_three B hB node83
  have hl : node83Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node83 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node83 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node83 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node83 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node83 (EqualityPatterns.family3.label 1) = PairSemantics.raw860 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node83 PairSemantics.raw860; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical860 hH).trans (PairSemantics.sound24 hH)
  have hm2 : familyPairMoment B (groupedColumns node83 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node83 (EqualityPatterns.family3.label 2) = PairSemantics.raw7742 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node83 PairSemantics.raw7742; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7742 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node83 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node83 (EqualityPatterns.family3.label 3) = PairSemantics.raw197 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node83 PairSemantics.raw197; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical197 hH).trans (PairSemantics.sound16 hH)
  have hm4 : familyPairMoment B (groupedColumns node83 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value744 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node83 (EqualityPatterns.family3.label 4) = PairSemantics.raw101 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node83 PairSemantics.raw101; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical101 hH).trans (PairSemantics.sound744 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue83, PairSemantics.value0, PairSemantics.value16, PairSemantics.value24, PairSemantics.value65, PairSemantics.value744, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue84 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (25 / 432)), (2, (5 / 72)), (5, (-5 / 54)), (6, (5 / 216)), (52, (5 / 54)), (228, (-5 / 18))]

theorem singlePair84 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node84 node84Labels = Sparse.eval singlePairValue84 (familyPairVector B) := by
  have hp := single_label_three B hB node84
  have hl : node84Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node84 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node84 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node84 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node84 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node84 (EqualityPatterns.family3.label 1) = PairSemantics.raw861 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node84 PairSemantics.raw861; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical861 hH).trans (PairSemantics.sound25 hH)
  have hm2 : familyPairMoment B (groupedColumns node84 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node84 (EqualityPatterns.family3.label 2) = PairSemantics.raw7740 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node84 PairSemantics.raw7740; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7740 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node84 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node84 (EqualityPatterns.family3.label 3) = PairSemantics.raw197 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node84 PairSemantics.raw197; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical197 hH).trans (PairSemantics.sound16 hH)
  have hm4 : familyPairMoment B (groupedColumns node84 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value743 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node84 (EqualityPatterns.family3.label 4) = PairSemantics.raw102 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node84 PairSemantics.raw102; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical102 hH).trans (PairSemantics.sound743 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue84, PairSemantics.value0, PairSemantics.value16, PairSemantics.value25, PairSemantics.value65, PairSemantics.value743, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue85 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (5 / 432)), (2, (-5 / 108)), (6, (-5 / 108)), (11, (-5 / 27))]

theorem singlePair85 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node85 node85Labels = Sparse.eval singlePairValue85 (familyPairVector B) := by
  have hp := single_label_three B hB node85
  have hl : node85Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node85 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node85 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node85 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node85 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node85 (EqualityPatterns.family3.label 1) = PairSemantics.raw862 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node85 PairSemantics.raw862; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical862 hH).trans (PairSemantics.sound8 hH)
  have hm2 : familyPairMoment B (groupedColumns node85 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node85 (EqualityPatterns.family3.label 2) = PairSemantics.raw7738 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node85 PairSemantics.raw7738; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7738 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node85 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node85 (EqualityPatterns.family3.label 3) = PairSemantics.raw198 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node85 PairSemantics.raw198; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical198 hH).trans (PairSemantics.sound8 hH)
  have hm4 : familyPairMoment B (groupedColumns node85 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value249 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node85 (EqualityPatterns.family3.label 4) = PairSemantics.raw103 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node85 PairSemantics.raw103; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical103 hH).trans (PairSemantics.sound249 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue85, PairSemantics.value0, PairSemantics.value8, PairSemantics.value65, PairSemantics.value249, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue86 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (5 / 432)), (2, (-5 / 108)), (5, (25 / 108)), (35, (-5 / 27))]

theorem singlePair86 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node86 node86Labels = Sparse.eval singlePairValue86 (familyPairVector B) := by
  have hp := single_label_three B hB node86
  have hl : node86Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node86 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node86 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node86 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node86 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node86 (EqualityPatterns.family3.label 1) = PairSemantics.raw869 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node86 PairSemantics.raw869; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical869 hH).trans (PairSemantics.sound24 hH)
  have hm2 : familyPairMoment B (groupedColumns node86 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node86 (EqualityPatterns.family3.label 2) = PairSemantics.raw7738 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node86 PairSemantics.raw7738; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7738 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node86 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value9 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node86 (EqualityPatterns.family3.label 3) = PairSemantics.raw199 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node86 PairSemantics.raw199; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical199 hH).trans (PairSemantics.sound9 hH)
  have hm4 : familyPairMoment B (groupedColumns node86 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value247 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node86 (EqualityPatterns.family3.label 4) = PairSemantics.raw104 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node86 PairSemantics.raw104; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical104 hH).trans (PairSemantics.sound247 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue86, PairSemantics.value0, PairSemantics.value9, PairSemantics.value24, PairSemantics.value65, PairSemantics.value247, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue87 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (25 / 288)), (2, (5 / 288)), (5, (-5 / 108)), (6, (-5 / 216)), (13, (5 / 54)), (35, (5 / 27)), (52, (5 / 27)), (60, (5 / 27)), (128, (5 / 54))]

theorem singlePair87 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node87 node87Labels = Sparse.eval singlePairValue87 (familyPairVector B) := by
  have hp := single_label_three B hB node87
  have hl : node87Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node87 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node87 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node87 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node87 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node87 (EqualityPatterns.family3.label 1) = PairSemantics.raw915 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node87 PairSemantics.raw915; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical915 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node87 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node87 (EqualityPatterns.family3.label 2) = PairSemantics.raw7656 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node87 PairSemantics.raw7656; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7656 hH).trans (PairSemantics.sound26 hH)
  have hm3 : familyPairMoment B (groupedColumns node87 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node87 (EqualityPatterns.family3.label 3) = PairSemantics.raw193 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node87 PairSemantics.raw193; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical193 hH).trans (PairSemantics.sound8 hH)
  have hm4 : familyPairMoment B (groupedColumns node87 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value324 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node87 (EqualityPatterns.family3.label 4) = PairSemantics.raw105 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node87 PairSemantics.raw105; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical105 hH).trans (PairSemantics.sound324 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue87, PairSemantics.value0, PairSemantics.value8, PairSemantics.value26, PairSemantics.value324, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
