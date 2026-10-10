import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleRules
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical238
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical239
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical240
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue88 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 72)), (2, (5 / 216)), (5, (5 / 54)), (6, (25 / 216)), (128, (-5 / 27))]

theorem singlePair88 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node88 node88Labels = Sparse.eval singlePairValue88 (familyPairVector B) := by
  have hp := single_label_three B hB node88
  have hl : node88Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node88 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node88 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node88 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node88 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node88 (EqualityPatterns.family3.label 1) = PairSemantics.raw914 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node88 PairSemantics.raw914; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical914 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node88 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node88 (EqualityPatterns.family3.label 2) = PairSemantics.raw7663 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node88 PairSemantics.raw7663; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7663 hH).trans (PairSemantics.sound26 hH)
  have hm3 : familyPairMoment B (groupedColumns node88 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value2 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node88 (EqualityPatterns.family3.label 3) = PairSemantics.raw195 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node88 PairSemantics.raw195; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical195 hH).trans (PairSemantics.sound2 hH)
  have hm4 : familyPairMoment B (groupedColumns node88 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value90 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node88 (EqualityPatterns.family3.label 4) = PairSemantics.raw106 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node88 PairSemantics.raw106; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical106 hH).trans (PairSemantics.sound90 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue88, PairSemantics.value0, PairSemantics.value2, PairSemantics.value26, PairSemantics.value90, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue89 : Sparse (Fin 909) := [(0, (31 / 864)), (1, (-5 / 216)), (2, (25 / 864)), (3, (5 / 54)), (5, (-5 / 108)), (6, (5 / 432)), (7, (5 / 54)), (11, (5 / 54)), (26, (5 / 54)), (35, (5 / 27)), (228, (-5 / 18))]

theorem singlePair89 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node89 node89Labels = Sparse.eval singlePairValue89 (familyPairVector B) := by
  have hp := single_label_three B hB node89
  have hl : node89Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node89 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node89 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node89 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node89 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node89 (EqualityPatterns.family3.label 1) = PairSemantics.raw902 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node89 PairSemantics.raw902; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical902 hH).trans (PairSemantics.sound118 hH)
  have hm2 : familyPairMoment B (groupedColumns node89 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node89 (EqualityPatterns.family3.label 2) = PairSemantics.raw7686 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node89 PairSemantics.raw7686; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7686 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node89 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node89 (EqualityPatterns.family3.label 3) = PairSemantics.raw197 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node89 PairSemantics.raw197; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical197 hH).trans (PairSemantics.sound16 hH)
  have hm4 : familyPairMoment B (groupedColumns node89 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value701 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node89 (EqualityPatterns.family3.label 4) = PairSemantics.raw107 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node89 PairSemantics.raw107; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical107 hH).trans (PairSemantics.sound701 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue89, PairSemantics.value0, PairSemantics.value11, PairSemantics.value16, PairSemantics.value118, PairSemantics.value701, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue90 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 216)), (2, (-5 / 216)), (6, (-5 / 144)), (11, (-5 / 27)), (35, (-5 / 27))]

theorem singlePair90 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node90 node90Labels = Sparse.eval singlePairValue90 (familyPairVector B) := by
  have hp := single_label_three B hB node90
  have hl : node90Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node90 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node90 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node90 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node90 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node90 (EqualityPatterns.family3.label 1) = PairSemantics.raw903 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node90 PairSemantics.raw903; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical903 hH).trans (PairSemantics.sound24 hH)
  have hm2 : familyPairMoment B (groupedColumns node90 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node90 (EqualityPatterns.family3.label 2) = PairSemantics.raw7685 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node90 PairSemantics.raw7685; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7685 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node90 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node90 (EqualityPatterns.family3.label 3) = PairSemantics.raw198 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node90 PairSemantics.raw198; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical198 hH).trans (PairSemantics.sound8 hH)
  have hm4 : familyPairMoment B (groupedColumns node90 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value221 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node90 (EqualityPatterns.family3.label 4) = PairSemantics.raw108 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node90 PairSemantics.raw108; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical108 hH).trans (PairSemantics.sound221 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue90, PairSemantics.value0, PairSemantics.value8, PairSemantics.value11, PairSemantics.value24, PairSemantics.value221, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue91 : Sparse (Fin 909) := [(0, (37 / 864)), (1, (-5 / 216)), (2, (-55 / 432)), (3, (-5 / 27)), (5, (10 / 27)), (6, (-55 / 864)), (7, (-5 / 54)), (8, (-5 / 27)), (35, (-5 / 27)), (52, (-10 / 27))]

theorem singlePair91 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node91 node91Labels = Sparse.eval singlePairValue91 (familyPairVector B) := by
  have hp := single_label_three B hB node91
  have hl : node91Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node91 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node91 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node91 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node91 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node91 (EqualityPatterns.family3.label 1) = PairSemantics.raw905 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node91 PairSemantics.raw905; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical905 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node91 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node91 (EqualityPatterns.family3.label 2) = PairSemantics.raw7680 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node91 PairSemantics.raw7680; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7680 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node91 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value69 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node91 (EqualityPatterns.family3.label 3) = PairSemantics.raw196 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node91 PairSemantics.raw196; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical196 hH).trans (PairSemantics.sound69 hH)
  have hm4 : familyPairMoment B (groupedColumns node91 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2380 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node91 (EqualityPatterns.family3.label 4) = PairSemantics.raw109 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node91 PairSemantics.raw109; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical109 hH).trans (PairSemantics.sound2380 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue91, PairSemantics.value0, PairSemantics.value26, PairSemantics.value65, PairSemantics.value69, PairSemantics.value2380, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue92 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-35 / 864)), (2, (-5 / 108)), (5, (-25 / 216)), (6, (25 / 864)), (7, (5 / 54)), (35, (5 / 54))]

theorem singlePair92 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node92 node92Labels = Sparse.eval singlePairValue92 (familyPairVector B) := by
  have hp := single_label_three B hB node92
  have hl : node92Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node92 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node92 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node92 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node92 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node92 (EqualityPatterns.family3.label 1) = PairSemantics.raw906 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node92 PairSemantics.raw906; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical906 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node92 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node92 (EqualityPatterns.family3.label 2) = PairSemantics.raw7679 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node92 PairSemantics.raw7679; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7679 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node92 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node92 (EqualityPatterns.family3.label 3) = PairSemantics.raw197 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node92 PairSemantics.raw197; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical197 hH).trans (PairSemantics.sound16 hH)
  have hm4 : familyPairMoment B (groupedColumns node92 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value739 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node92 (EqualityPatterns.family3.label 4) = PairSemantics.raw110 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node92 PairSemantics.raw110; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical110 hH).trans (PairSemantics.sound739 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue92, PairSemantics.value0, PairSemantics.value10, PairSemantics.value16, PairSemantics.value65, PairSemantics.value739, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue93 : Sparse (Fin 909) := [(0, (17 / 432)), (1, (5 / 48)), (2, (5 / 54)), (5, (-5 / 36)), (6, (5 / 216)), (8, (5 / 54)), (52, (5 / 54))]

theorem singlePair93 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node93 node93Labels = Sparse.eval singlePairValue93 (familyPairVector B) := by
  have hp := single_label_three B hB node93
  have hl : node93Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node93 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node93 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node93 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node93 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node93 (EqualityPatterns.family3.label 1) = PairSemantics.raw907 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node93 PairSemantics.raw907; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical907 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node93 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node93 (EqualityPatterns.family3.label 2) = PairSemantics.raw7677 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node93 PairSemantics.raw7677; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7677 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node93 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node93 (EqualityPatterns.family3.label 3) = PairSemantics.raw197 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node93 PairSemantics.raw197; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical197 hH).trans (PairSemantics.sound16 hH)
  have hm4 : familyPairMoment B (groupedColumns node93 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value737 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node93 (EqualityPatterns.family3.label 4) = PairSemantics.raw111 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node93 PairSemantics.raw111; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical111 hH).trans (PairSemantics.sound737 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue93, PairSemantics.value0, PairSemantics.value16, PairSemantics.value26, PairSemantics.value65, PairSemantics.value737, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue94 : Sparse (Fin 909) := [(0, (19 / 432)), (1, (-5 / 108)), (2, (-5 / 72)), (5, (5 / 108)), (6, (-25 / 432))]

theorem singlePair94 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node94 node94Labels = Sparse.eval singlePairValue94 (familyPairVector B) := by
  have hp := single_label_three B hB node94
  have hl : node94Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node94 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node94 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node94 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node94 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node94 (EqualityPatterns.family3.label 1) = PairSemantics.raw909 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node94 PairSemantics.raw909; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical909 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node94 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node94 (EqualityPatterns.family3.label 2) = PairSemantics.raw7678 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node94 PairSemantics.raw7678; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7678 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node94 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node94 (EqualityPatterns.family3.label 3) = PairSemantics.raw198 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node94 PairSemantics.raw198; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical198 hH).trans (PairSemantics.sound8 hH)
  have hm4 : familyPairMoment B (groupedColumns node94 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value243 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node94 (EqualityPatterns.family3.label 4) = PairSemantics.raw112 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node94 PairSemantics.raw112; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical112 hH).trans (PairSemantics.sound243 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue94, PairSemantics.value0, PairSemantics.value8, PairSemantics.value10, PairSemantics.value65, PairSemantics.value243, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue95 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (5 / 216)), (2, (35 / 432)), (3, (5 / 27)), (5, (-5 / 54)), (6, (5 / 288)), (7, (5 / 54)), (35, (5 / 27)), (52, (5 / 27))]

theorem singlePair95 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node95 node95Labels = Sparse.eval singlePairValue95 (familyPairVector B) := by
  have hp := single_label_three B hB node95
  have hl : node95Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node95 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node95 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node95 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node95 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node95 (EqualityPatterns.family3.label 1) = PairSemantics.raw915 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node95 PairSemantics.raw915; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical915 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node95 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node95 (EqualityPatterns.family3.label 2) = PairSemantics.raw7669 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node95 PairSemantics.raw7669; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7669 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node95 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node95 (EqualityPatterns.family3.label 3) = PairSemantics.raw197 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node95 PairSemantics.raw197; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical197 hH).trans (PairSemantics.sound16 hH)
  have hm4 : familyPairMoment B (groupedColumns node95 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value653 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node95 (EqualityPatterns.family3.label 4) = PairSemantics.raw113 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node95 PairSemantics.raw113; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical113 hH).trans (PairSemantics.sound653 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue95, PairSemantics.value0, PairSemantics.value11, PairSemantics.value16, PairSemantics.value26, PairSemantics.value653, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue96 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-5 / 216)), (2, (-5 / 108)), (5, (5 / 108)), (6, (-5 / 108)), (52, (-5 / 27))]

theorem singlePair96 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node96 node96Labels = Sparse.eval singlePairValue96 (familyPairVector B) := by
  have hp := single_label_three B hB node96
  have hl : node96Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node96 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node96 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node96 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node96 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node96 (EqualityPatterns.family3.label 1) = PairSemantics.raw914 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node96 PairSemantics.raw914; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical914 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node96 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node96 (EqualityPatterns.family3.label 2) = PairSemantics.raw7671 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node96 PairSemantics.raw7671; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7671 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node96 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node96 (EqualityPatterns.family3.label 3) = PairSemantics.raw198 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node96 PairSemantics.raw198; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical198 hH).trans (PairSemantics.sound8 hH)
  have hm4 : familyPairMoment B (groupedColumns node96 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value173 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node96 (EqualityPatterns.family3.label 4) = PairSemantics.raw114 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node96 PairSemantics.raw114; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical114 hH).trans (PairSemantics.sound173 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue96, PairSemantics.value0, PairSemantics.value8, PairSemantics.value11, PairSemantics.value26, PairSemantics.value173, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue97 : Sparse (Fin 909) := [(0, (11 / 432)), (2, (-5 / 108)), (6, (-5 / 144)), (35, (-5 / 27)), (52, (-5 / 27)), (60, (-5 / 27))]

theorem singlePair97 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node97 node97Labels = Sparse.eval singlePairValue97 (familyPairVector B) := by
  have hp := single_label_three B hB node97
  have hl : node97Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node97 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node97 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node97 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node97 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node97 (EqualityPatterns.family3.label 1) = PairSemantics.raw918 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node97 PairSemantics.raw918; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical918 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node97 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node97 (EqualityPatterns.family3.label 2) = PairSemantics.raw7663 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node97 PairSemantics.raw7663; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7663 hH).trans (PairSemantics.sound26 hH)
  have hm3 : familyPairMoment B (groupedColumns node97 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node97 (EqualityPatterns.family3.label 3) = PairSemantics.raw198 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node97 PairSemantics.raw198; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical198 hH).trans (PairSemantics.sound8 hH)
  have hm4 : familyPairMoment B (groupedColumns node97 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value87 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node97 (EqualityPatterns.family3.label 4) = PairSemantics.raw115 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node97 PairSemantics.raw115; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical115 hH).trans (PairSemantics.sound87 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue97, PairSemantics.value0, PairSemantics.value8, PairSemantics.value10, PairSemantics.value26, PairSemantics.value87, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue98 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-35 / 432)), (2, (-5 / 108)), (5, (5 / 27)), (7, (-5 / 27)), (35, (-5 / 27))]

theorem singlePair98 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node98 node98Labels = Sparse.eval singlePairValue98 (familyPairVector B) := by
  have hp := single_label_three B hB node98
  have hl : node98Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node98 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node98 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node98 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node98 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node98 (EqualityPatterns.family3.label 1) = PairSemantics.raw909 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node98 PairSemantics.raw909; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical909 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node98 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node98 (EqualityPatterns.family3.label 2) = PairSemantics.raw7685 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node98 PairSemantics.raw7685; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7685 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node98 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value9 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node98 (EqualityPatterns.family3.label 3) = PairSemantics.raw199 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node98 PairSemantics.raw199; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical199 hH).trans (PairSemantics.sound9 hH)
  have hm4 : familyPairMoment B (groupedColumns node98 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value201 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node98 (EqualityPatterns.family3.label 4) = PairSemantics.raw116 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node98 PairSemantics.raw116; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical116 hH).trans (PairSemantics.sound201 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue98, PairSemantics.value0, PairSemantics.value9, PairSemantics.value10, PairSemantics.value11, PairSemantics.value201, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue99 : Sparse (Fin 909) := [(0, (1 / 24)), (1, (5 / 216)), (5, (25 / 108)), (8, (-5 / 27))]

theorem singlePair99 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node99 node99Labels = Sparse.eval singlePairValue99 (familyPairVector B) := by
  have hp := single_label_three B hB node99
  have hl : node99Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node99 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node99 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node99 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node99 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node99 (EqualityPatterns.family3.label 1) = PairSemantics.raw914 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node99 PairSemantics.raw914; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical914 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node99 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node99 (EqualityPatterns.family3.label 2) = PairSemantics.raw7678 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node99 PairSemantics.raw7678; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7678 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node99 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value9 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node99 (EqualityPatterns.family3.label 3) = PairSemantics.raw199 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node99 PairSemantics.raw199; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical199 hH).trans (PairSemantics.sound9 hH)
  have hm4 : familyPairMoment B (groupedColumns node99 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value244 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node99 (EqualityPatterns.family3.label 4) = PairSemantics.raw117 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node99 PairSemantics.raw117; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical117 hH).trans (PairSemantics.sound244 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue99, PairSemantics.value0, PairSemantics.value9, PairSemantics.value26, PairSemantics.value65, PairSemantics.value244, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue100 : Sparse (Fin 909) := [(0, (5 / 144)), (1, (-5 / 72)), (5, (-5 / 36)), (6, (25 / 144))]

theorem singlePair100 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node100 node100Labels = Sparse.eval singlePairValue100 (familyPairVector B) := by
  have hp := single_label_three B hB node100
  have hl : node100Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node100 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node100 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node100 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node100 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node100 (EqualityPatterns.family3.label 1) = PairSemantics.raw917 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node100 PairSemantics.raw917; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical917 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node100 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node100 (EqualityPatterns.family3.label 2) = PairSemantics.raw7683 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node100 PairSemantics.raw7683; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7683 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node100 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value2 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node100 (EqualityPatterns.family3.label 3) = PairSemantics.raw200 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node100 PairSemantics.raw200; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical200 hH).trans (PairSemantics.sound2 hH)
  have hm4 : familyPairMoment B (groupedColumns node100 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value59 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node100 (EqualityPatterns.family3.label 4) = PairSemantics.raw118 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node100 PairSemantics.raw118; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical118 hH).trans (PairSemantics.sound59 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue100, PairSemantics.value0, PairSemantics.value2, PairSemantics.value10, PairSemantics.value11, PairSemantics.value59, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue101 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-5 / 108)), (3, (5 / 54)), (5, (-5 / 108)), (6, (5 / 432)), (12, (5 / 54)), (13, (5 / 18)), (35, (5 / 54)), (52, (5 / 54)), (59, (-5 / 18)), (60, (5 / 54)), (128, (5 / 54))]

theorem singlePair101 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node101 node101Labels = Sparse.eval singlePairValue101 (familyPairVector B) := by
  have hp := single_label_three B hB node101
  have hl : node101Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node101 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node101 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node101 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node101 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node101 (EqualityPatterns.family3.label 1) = PairSemantics.raw923 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node101 PairSemantics.raw923; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical923 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node101 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node101 (EqualityPatterns.family3.label 2) = PairSemantics.raw7631 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node101 PairSemantics.raw7631; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7631 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node101 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node101 (EqualityPatterns.family3.label 3) = PairSemantics.raw197 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node101 PairSemantics.raw197; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical197 hH).trans (PairSemantics.sound16 hH)
  have hm4 : familyPairMoment B (groupedColumns node101 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value317 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node101 (EqualityPatterns.family3.label 4) = PairSemantics.raw119 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node101 PairSemantics.raw119; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical119 hH).trans (PairSemantics.sound317 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue101, PairSemantics.value0, PairSemantics.value10, PairSemantics.value16, PairSemantics.value46, PairSemantics.value317, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue102 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 72)), (2, (-5 / 48)), (6, (-5 / 144)), (13, (-5 / 27)), (60, (-5 / 27)), (128, (-5 / 27))]

theorem singlePair102 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node102 node102Labels = Sparse.eval singlePairValue102 (familyPairVector B) := by
  have hp := single_label_three B hB node102
  have hl : node102Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node102 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node102 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node102 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node102 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node102 (EqualityPatterns.family3.label 1) = PairSemantics.raw925 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node102 PairSemantics.raw925; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical925 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node102 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node102 (EqualityPatterns.family3.label 2) = PairSemantics.raw7627 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node102 PairSemantics.raw7627; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7627 hH).trans (PairSemantics.sound10 hH)
  have hm3 : familyPairMoment B (groupedColumns node102 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node102 (EqualityPatterns.family3.label 3) = PairSemantics.raw198 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node102 PairSemantics.raw198; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical198 hH).trans (PairSemantics.sound8 hH)
  have hm4 : familyPairMoment B (groupedColumns node102 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value88 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node102 (EqualityPatterns.family3.label 4) = PairSemantics.raw120 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node102 PairSemantics.raw120; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical120 hH).trans (PairSemantics.sound88 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue102, PairSemantics.value0, PairSemantics.value8, PairSemantics.value10, PairSemantics.value88, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue103 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-25 / 432)), (2, (-5 / 216)), (5, (5 / 36)), (59, (5 / 9))]

theorem singlePair103 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node103 node103Labels = Sparse.eval singlePairValue103 (familyPairVector B) := by
  have hp := single_label_three B hB node103
  have hl : node103Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node103 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node103 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node103 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node103 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node103 (EqualityPatterns.family3.label 1) = PairSemantics.raw922 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node103 PairSemantics.raw922; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical922 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node103 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node103 (EqualityPatterns.family3.label 2) = PairSemantics.raw7639 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node103 PairSemantics.raw7639; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7639 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node103 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value9 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node103 (EqualityPatterns.family3.label 3) = PairSemantics.raw199 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node103 PairSemantics.raw199; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical199 hH).trans (PairSemantics.sound9 hH)
  have hm4 : familyPairMoment B (groupedColumns node103 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value85 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node103 (EqualityPatterns.family3.label 4) = PairSemantics.raw121 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node103 PairSemantics.raw121; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical121 hH).trans (PairSemantics.sound85 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue103, PairSemantics.value0, PairSemantics.value9, PairSemantics.value10, PairSemantics.value46, PairSemantics.value85, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
