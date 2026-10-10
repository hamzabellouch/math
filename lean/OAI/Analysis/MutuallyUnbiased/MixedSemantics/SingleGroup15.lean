import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleRules
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical279
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical280
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical281
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound5

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singlePairValue248 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (145 / 864)), (2, (5 / 144)), (3, (5 / 27)), (5, (5 / 216)), (6, (-5 / 864)), (12, (5 / 27)), (13, (5 / 18)), (35, (5 / 54)), (54, (-5 / 18))]

theorem singlePair248 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node248 node248Labels = Sparse.eval singlePairValue248 (familyPairVector B) := by
  have hp := single_label_three B hB node248
  have hl : node248Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node248 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node248 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node248 PairSemantics.raw7981
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node248 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node248 (EqualityPatterns.family3.label 1) = PairSemantics.raw915 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node248 PairSemantics.raw915
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical915 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node248 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node248 (EqualityPatterns.family3.label 2) = PairSemantics.raw8969 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node248 PairSemantics.raw8969
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8969 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node248 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node248 (EqualityPatterns.family3.label 3) = PairSemantics.raw867 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node248 PairSemantics.raw867
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical867 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node248 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value651 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node248 (EqualityPatterns.family3.label 4) = PairSemantics.raw453 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node248 PairSemantics.raw453
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical453 hH).trans (PairSemantics.sound651 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue248, PairSemantics.value0, PairSemantics.value4, PairSemantics.value26, PairSemantics.value118, PairSemantics.value651, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue249 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (5 / 27)), (3, (-5 / 27)), (6, (5 / 432)), (13, (-5 / 27)), (35, (-5 / 27))]

theorem singlePair249 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node249 node249Labels = Sparse.eval singlePairValue249 (familyPairVector B) := by
  have hp := single_label_three B hB node249
  have hl : node249Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node249 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node249 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node249 PairSemantics.raw7980
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node249 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node249 (EqualityPatterns.family3.label 1) = PairSemantics.raw914 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node249 PairSemantics.raw914
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical914 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node249 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node249 (EqualityPatterns.family3.label 2) = PairSemantics.raw8972 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node249 PairSemantics.raw8972
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8972 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node249 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node249 (EqualityPatterns.family3.label 3) = PairSemantics.raw869 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node249 PairSemantics.raw869
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical869 hH).trans (PairSemantics.sound24 hH)
  have hm4 : familyPairMoment B (groupedColumns node249 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value170 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node249 (EqualityPatterns.family3.label 4) = PairSemantics.raw454 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node249 PairSemantics.raw454
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical454 hH).trans (PairSemantics.sound170 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue249, PairSemantics.value0, PairSemantics.value4, PairSemantics.value24, PairSemantics.value26, PairSemantics.value170, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue250 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-25 / 432)), (2, (-5 / 54)), (6, (5 / 432)), (62, (5 / 9))]

theorem singlePair250 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node250 node250Labels = Sparse.eval singlePairValue250 (familyPairVector B) := by
  have hp := single_label_three B hB node250
  have hl : node250Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node250 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node250 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node250 PairSemantics.raw7980
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node250 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node250 (EqualityPatterns.family3.label 1) = PairSemantics.raw918 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node250 PairSemantics.raw918
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical918 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node250 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node250 (EqualityPatterns.family3.label 2) = PairSemantics.raw8966 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node250 PairSemantics.raw8966
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8966 hH).trans (PairSemantics.sound10 hH)
  have hm3 : familyPairMoment B (groupedColumns node250 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node250 (EqualityPatterns.family3.label 3) = PairSemantics.raw869 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node250 PairSemantics.raw869
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical869 hH).trans (PairSemantics.sound24 hH)
  have hm4 : familyPairMoment B (groupedColumns node250 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value98 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node250 (EqualityPatterns.family3.label 4) = PairSemantics.raw455 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node250 PairSemantics.raw455
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical455 hH).trans (PairSemantics.sound98 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue250, PairSemantics.value0, PairSemantics.value10, PairSemantics.value24, PairSemantics.value98, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue251 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (55 / 432)), (2, (-5 / 432)), (5, (-5 / 108)), (54, (5 / 9))]

theorem singlePair251 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node251 node251Labels = Sparse.eval singlePairValue251 (familyPairVector B) := by
  have hp := single_label_three B hB node251
  have hl : node251Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node251 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node251 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node251 PairSemantics.raw7980
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node251 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node251 (EqualityPatterns.family3.label 1) = PairSemantics.raw909 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node251 PairSemantics.raw909
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical909 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node251 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node251 (EqualityPatterns.family3.label 2) = PairSemantics.raw8987 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node251 PairSemantics.raw8987
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8987 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node251 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node251 (EqualityPatterns.family3.label 3) = PairSemantics.raw872 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node251 PairSemantics.raw872
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical872 hH).trans (PairSemantics.sound25 hH)
  have hm4 : familyPairMoment B (groupedColumns node251 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value198 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node251 (EqualityPatterns.family3.label 4) = PairSemantics.raw456 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node251 PairSemantics.raw456
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical456 hH).trans (PairSemantics.sound198 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue251, PairSemantics.value0, PairSemantics.value4, PairSemantics.value10, PairSemantics.value25, PairSemantics.value198, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue252 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (5 / 216)), (2, (5 / 108)), (5, (-5 / 108)), (56, (5 / 9))]

theorem singlePair252 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node252 node252Labels = Sparse.eval singlePairValue252 (familyPairVector B) := by
  have hp := single_label_three B hB node252
  have hl : node252Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node252 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node252 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node252 PairSemantics.raw7980
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node252 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node252 (EqualityPatterns.family3.label 1) = PairSemantics.raw914 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node252 PairSemantics.raw914
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical914 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node252 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node252 (EqualityPatterns.family3.label 2) = PairSemantics.raw8979 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node252 PairSemantics.raw8979
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8979 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node252 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node252 (EqualityPatterns.family3.label 3) = PairSemantics.raw872 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node252 PairSemantics.raw872
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical872 hH).trans (PairSemantics.sound25 hH)
  have hm4 : familyPairMoment B (groupedColumns node252 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value223 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node252 (EqualityPatterns.family3.label 4) = PairSemantics.raw457 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node252 PairSemantics.raw457
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical457 hH).trans (PairSemantics.sound223 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue252, PairSemantics.value0, PairSemantics.value11, PairSemantics.value25, PairSemantics.value26, PairSemantics.value223, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue253 : Sparse (Fin 909) := [(0, (1 / 27)), (1, (-5 / 48)), (2, (-25 / 288)), (3, (-5 / 6)), (5, (-5 / 72)), (6, (5 / 288)), (12, (-5 / 18)), (13, (-35 / 27)), (26, (-5 / 18)), (32, (-5 / 27)), (34, (-5 / 9)), (60, (-5 / 18)), (61, (5 / 6))]

theorem singlePair253 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node253 node253Labels = Sparse.eval singlePairValue253 (familyPairVector B) := by
  have hp := single_label_three B hB node253
  have hl : node253Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node253 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node253 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node253 PairSemantics.raw7982
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node253 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node253 (EqualityPatterns.family3.label 1) = PairSemantics.raw920 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node253 PairSemantics.raw920
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical920 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node253 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node253 (EqualityPatterns.family3.label 2) = PairSemantics.raw8952 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node253 PairSemantics.raw8952
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8952 hH).trans (PairSemantics.sound26 hH)
  have hm3 : familyPairMoment B (groupedColumns node253 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value383 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node253 (EqualityPatterns.family3.label 3) = PairSemantics.raw866 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node253 PairSemantics.raw866
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical866 hH).trans (PairSemantics.sound383 hH)
  have hm4 : familyPairMoment B (groupedColumns node253 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1411 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node253 (EqualityPatterns.family3.label 4) = PairSemantics.raw458 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node253 PairSemantics.raw458
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical458 hH).trans (PairSemantics.sound1411 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue253, PairSemantics.value0, PairSemantics.value10, PairSemantics.value26, PairSemantics.value383, PairSemantics.value1411, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue254 : Sparse (Fin 909) := [(0, (23 / 864)), (1, (5 / 216)), (2, (5 / 432)), (3, (5 / 27)), (5, (5 / 216)), (6, (-5 / 864)), (13, (5 / 27)), (26, (5 / 54)), (34, (5 / 27)), (60, (5 / 54)), (61, (-5 / 18))]

theorem singlePair254 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node254 node254Labels = Sparse.eval singlePairValue254 (familyPairVector B) := by
  have hp := single_label_three B hB node254
  have hl : node254Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node254 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node254 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node254 PairSemantics.raw7981
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node254 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node254 (EqualityPatterns.family3.label 1) = PairSemantics.raw921 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node254 PairSemantics.raw921
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical921 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node254 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node254 (EqualityPatterns.family3.label 2) = PairSemantics.raw8951 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node254 PairSemantics.raw8951
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8951 hH).trans (PairSemantics.sound26 hH)
  have hm3 : familyPairMoment B (groupedColumns node254 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value118 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node254 (EqualityPatterns.family3.label 3) = PairSemantics.raw867 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node254 PairSemantics.raw867
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical867 hH).trans (PairSemantics.sound118 hH)
  have hm4 : familyPairMoment B (groupedColumns node254 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value343 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node254 (EqualityPatterns.family3.label 4) = PairSemantics.raw459 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node254 PairSemantics.raw459
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical459 hH).trans (PairSemantics.sound343 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue254, PairSemantics.value0, PairSemantics.value10, PairSemantics.value26, PairSemantics.value118, PairSemantics.value343, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue255 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-25 / 432)), (2, (-5 / 54)), (6, (5 / 432)), (13, (-5 / 27)), (34, (-5 / 27)), (60, (-5 / 27))]

theorem singlePair255 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node255 node255Labels = Sparse.eval singlePairValue255 (familyPairVector B) := by
  have hp := single_label_three B hB node255
  have hl : node255Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node255 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node255 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node255 PairSemantics.raw7980
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node255 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node255 (EqualityPatterns.family3.label 1) = PairSemantics.raw922 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node255 PairSemantics.raw922
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical922 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node255 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node255 (EqualityPatterns.family3.label 2) = PairSemantics.raw8953 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node255 PairSemantics.raw8953
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8953 hH).trans (PairSemantics.sound10 hH)
  have hm3 : familyPairMoment B (groupedColumns node255 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node255 (EqualityPatterns.family3.label 3) = PairSemantics.raw869 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node255 PairSemantics.raw869
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical869 hH).trans (PairSemantics.sound24 hH)
  have hm4 : familyPairMoment B (groupedColumns node255 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value95 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node255 (EqualityPatterns.family3.label 4) = PairSemantics.raw460 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node255 PairSemantics.raw460
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical460 hH).trans (PairSemantics.sound95 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue255, PairSemantics.value0, PairSemantics.value10, PairSemantics.value24, PairSemantics.value95, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue256 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-5 / 108)), (2, (-5 / 108)), (5, (-5 / 108)), (61, (5 / 9))]

theorem singlePair256 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node256 node256Labels = Sparse.eval singlePairValue256 (familyPairVector B) := by
  have hp := single_label_three B hB node256
  have hl : node256Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node256 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node256 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node256 PairSemantics.raw7980
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node256 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node256 (EqualityPatterns.family3.label 1) = PairSemantics.raw922 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node256 PairSemantics.raw922
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical922 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node256 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node256 (EqualityPatterns.family3.label 2) = PairSemantics.raw8955 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node256 PairSemantics.raw8955
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8955 hH).trans (PairSemantics.sound10 hH)
  have hm3 : familyPairMoment B (groupedColumns node256 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node256 (EqualityPatterns.family3.label 3) = PairSemantics.raw872 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node256 PairSemantics.raw872
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical872 hH).trans (PairSemantics.sound25 hH)
  have hm4 : familyPairMoment B (groupedColumns node256 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value97 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node256 (EqualityPatterns.family3.label 4) = PairSemantics.raw461 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node256 PairSemantics.raw461
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical461 hH).trans (PairSemantics.sound97 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue256, PairSemantics.value0, PairSemantics.value10, PairSemantics.value25, PairSemantics.value97, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue257 : Sparse (Fin 909) := [(0, (23 / 864)), (1, (5 / 96)), (2, (-5 / 72)), (3, (-5 / 6)), (12, (-5 / 9)), (13, (-85 / 54)), (32, (-5 / 27))]

theorem singlePair257 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node257 node257Labels = Sparse.eval singlePairValue257 (familyPairVector B) := by
  have hp := single_label_three B hB node257
  have hl : node257Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node257 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node257 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node257 PairSemantics.raw7982
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node257 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node257 (EqualityPatterns.family3.label 1) = PairSemantics.raw916 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node257 PairSemantics.raw916
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical916 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node257 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node257 (EqualityPatterns.family3.label 2) = PairSemantics.raw9002 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node257 PairSemantics.raw9002
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9002 hH).trans (PairSemantics.sound232 hH)
  have hm3 : familyPairMoment B (groupedColumns node257 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node257 (EqualityPatterns.family3.label 3) = PairSemantics.raw879 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node257 PairSemantics.raw879
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical879 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node257 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1410 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node257 (EqualityPatterns.family3.label 4) = PairSemantics.raw514 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node257 PairSemantics.raw514
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical514 hH).trans (PairSemantics.sound1410 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue257, PairSemantics.value0, PairSemantics.value10, PairSemantics.value26, PairSemantics.value232, PairSemantics.value1410, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue258 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 48)), (2, (25 / 144)), (13, (5 / 9)), (32, (5 / 27))]

theorem singlePair258 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node258 node258Labels = Sparse.eval singlePairValue258 (familyPairVector B) := by
  have hp := single_label_three B hB node258
  have hl : node258Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node258 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node258 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node258 PairSemantics.raw7981
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node258 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node258 (EqualityPatterns.family3.label 1) = PairSemantics.raw915 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node258 PairSemantics.raw915
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical915 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node258 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node258 (EqualityPatterns.family3.label 2) = PairSemantics.raw9004 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node258 PairSemantics.raw9004
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9004 hH).trans (PairSemantics.sound26 hH)
  have hm3 : familyPairMoment B (groupedColumns node258 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node258 (EqualityPatterns.family3.label 3) = PairSemantics.raw881 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node258 PairSemantics.raw881
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical881 hH).trans (PairSemantics.sound3 hH)
  have hm4 : familyPairMoment B (groupedColumns node258 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value341 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node258 (EqualityPatterns.family3.label 4) = PairSemantics.raw515 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node258 PairSemantics.raw515
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical515 hH).trans (PairSemantics.sound341 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue258, PairSemantics.value0, PairSemantics.value3, PairSemantics.value26, PairSemantics.value341, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue259 : Sparse (Fin 909) := [(0, (13 / 432)), (1, (115 / 432)), (2, (5 / 54)), (3, (-10 / 27)), (12, (-5 / 54)), (13, (-10 / 27))]

theorem singlePair259 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node259 node259Labels = Sparse.eval singlePairValue259 (familyPairVector B) := by
  have hp := single_label_three B hB node259
  have hl : node259Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node259 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node259 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node259 PairSemantics.raw7982
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node259 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node259 (EqualityPatterns.family3.label 1) = PairSemantics.raw911 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node259 PairSemantics.raw911
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical911 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node259 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node259 (EqualityPatterns.family3.label 2) = PairSemantics.raw9012 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node259 PairSemantics.raw9012
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9012 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node259 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node259 (EqualityPatterns.family3.label 3) = PairSemantics.raw883 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node259 PairSemantics.raw883
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical883 hH).trans (PairSemantics.sound26 hH)
  have hm4 : familyPairMoment B (groupedColumns node259 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2791 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node259 (EqualityPatterns.family3.label 4) = PairSemantics.raw518 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node259 PairSemantics.raw518
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical518 hH).trans (PairSemantics.sound2791 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue259, PairSemantics.value0, PairSemantics.value26, PairSemantics.value65, PairSemantics.value2791, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue260 : Sparse (Fin 909) := [(0, (11 / 288)), (1, (-5 / 864)), (2, (-5 / 216)), (3, (5 / 54)), (13, (5 / 54))]

theorem singlePair260 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node260 node260Labels = Sparse.eval singlePairValue260 (familyPairVector B) := by
  have hp := single_label_three B hB node260
  have hl : node260Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node260 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node260 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node260 PairSemantics.raw7981
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node260 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node260 (EqualityPatterns.family3.label 1) = PairSemantics.raw912 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node260 PairSemantics.raw912
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical912 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node260 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node260 (EqualityPatterns.family3.label 2) = PairSemantics.raw9011 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node260 PairSemantics.raw9011
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9011 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node260 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node260 (EqualityPatterns.family3.label 3) = PairSemantics.raw884 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node260 PairSemantics.raw884
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical884 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node260 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value1139 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node260 (EqualityPatterns.family3.label 4) = PairSemantics.raw519 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node260 PairSemantics.raw519
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical519 hH).trans (PairSemantics.sound1139 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue260, PairSemantics.value0, PairSemantics.value10, PairSemantics.value26, PairSemantics.value65, PairSemantics.value1139, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue261 : Sparse (Fin 909) := [(0, (13 / 432)), (1, (-25 / 864)), (2, (5 / 864)), (3, (5 / 27)), (12, (5 / 54)), (13, (5 / 18))]

theorem singlePair261 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node261 node261Labels = Sparse.eval singlePairValue261 (familyPairVector B) := by
  have hp := single_label_three B hB node261
  have hl : node261Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node261 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node261 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node261 PairSemantics.raw7981
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node261 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node261 (EqualityPatterns.family3.label 1) = PairSemantics.raw915 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node261 PairSemantics.raw915
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical915 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node261 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node261 (EqualityPatterns.family3.label 2) = PairSemantics.raw9008 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node261 PairSemantics.raw9008
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9008 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node261 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node261 (EqualityPatterns.family3.label 3) = PairSemantics.raw884 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node261 PairSemantics.raw884
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical884 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node261 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value663 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node261 (EqualityPatterns.family3.label 4) = PairSemantics.raw520 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node261 PairSemantics.raw520
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical520 hH).trans (PairSemantics.sound663 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue261, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value26, PairSemantics.value663, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue262 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (-5 / 144)), (2, (25 / 144)), (13, (-5 / 27))]

theorem singlePair262 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node262 node262Labels = Sparse.eval singlePairValue262 (familyPairVector B) := by
  have hp := single_label_three B hB node262
  have hl : node262Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node262 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node262 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node262 PairSemantics.raw7980
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node262 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node262 (EqualityPatterns.family3.label 1) = PairSemantics.raw914 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node262 PairSemantics.raw914
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical914 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node262 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node262 (EqualityPatterns.family3.label 2) = PairSemantics.raw9013 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node262 PairSemantics.raw9013
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9013 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node262 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node262 (EqualityPatterns.family3.label 3) = PairSemantics.raw887 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node262 PairSemantics.raw887
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical887 hH).trans (PairSemantics.sound3 hH)
  have hm4 : familyPairMoment B (groupedColumns node262 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value188 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node262 (EqualityPatterns.family3.label 4) = PairSemantics.raw522 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node262 PairSemantics.raw522
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical522 hH).trans (PairSemantics.sound188 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue262, PairSemantics.value0, PairSemantics.value3, PairSemantics.value11, PairSemantics.value26, PairSemantics.value188, Sparse.eval] at hp ⊢
  linarith only [hp]

def singlePairValue263 : Sparse (Fin 909) := [(0, (11 / 432)), (1, (-35 / 432)), (2, (-5 / 108)), (3, (5 / 27)), (12, (5 / 27)), (13, (5 / 9)), (32, (5 / 54))]

theorem singlePair263 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node263 node263Labels = Sparse.eval singlePairValue263 (familyPairVector B) := by
  have hp := single_label_three B hB node263
  have hl : node263Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node263 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node263 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node263 PairSemantics.raw7981
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node263 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node263 (EqualityPatterns.family3.label 1) = PairSemantics.raw919 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node263 PairSemantics.raw919
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical919 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node263 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node263 (EqualityPatterns.family3.label 2) = PairSemantics.raw8995 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node263 PairSemantics.raw8995
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8995 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node263 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node263 (EqualityPatterns.family3.label 3) = PairSemantics.raw884 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node263 PairSemantics.raw884
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical884 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node263 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value346 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node263 (EqualityPatterns.family3.label 4) = PairSemantics.raw525 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node263 PairSemantics.raw525
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical525 hH).trans (PairSemantics.sound346 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue263, PairSemantics.value0, PairSemantics.value10, PairSemantics.value46, PairSemantics.value346, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
