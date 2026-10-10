import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical86
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical88
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical90
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical92
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical102
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical112
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical143
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical151
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical174
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical184
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical185
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical186
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical214
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical228
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical229
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical231
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical235
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical236
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical237
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical238
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical239
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical240
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical241
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical245
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical248
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical250

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2304 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2304 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC2304 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceForm2304 : Integer.Sparse Master := [(Sum.inr 1810, 2), (Sum.inr 1818, 1), (Sum.inr 1819, 1), (Sum.inr 2066, 1), (Sum.inr 3397, 1), (Sum.inr 4084, -1)]

theorem sourceEq2304 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2304 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2304 + difference 0 1) (sourceB2304 + difference 1 0) sourceC2304) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3397) := by
    have ha : (tripleCharges (sourceA2304 + difference 0 1) (sourceB2304 + difference 1 0) sourceC2304) = raw31765 := by
      apply Matrix.ext; unfold tripleCharges sourceA2304 sourceB2304 sourceC2304 difference raw31765; decide +kernel
    rw [ha]
    exact (canonical31765 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2304 + difference 1 1) (sourceB2304 + difference 1 1) sourceC2304) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2066) := by
    have ha : (tripleCharges (sourceA2304 + difference 1 1) (sourceB2304 + difference 1 1) sourceC2304) = raw31766 := by
      apply Matrix.ext; unfold tripleCharges sourceA2304 sourceB2304 sourceC2304 difference raw31766; decide +kernel
    rw [ha]
    exact (canonical31766 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2304 + difference 2 1) (sourceB2304 + difference 1 2) sourceC2304) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1810) := by
    have ha : (tripleCharges (sourceA2304 + difference 2 1) (sourceB2304 + difference 1 2) sourceC2304) = raw31767 := by
      apply Matrix.ext; unfold tripleCharges sourceA2304 sourceB2304 sourceC2304 difference raw31767; decide +kernel
    rw [ha]
    exact (canonical31767 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2304 + difference 3 1) (sourceB2304 + difference 1 3) sourceC2304) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1810) := by
    have ha : (tripleCharges (sourceA2304 + difference 3 1) (sourceB2304 + difference 1 3) sourceC2304) = raw31768 := by
      apply Matrix.ext; unfold tripleCharges sourceA2304 sourceB2304 sourceC2304 difference raw31768; decide +kernel
    rw [ha]
    exact (canonical31768 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2304 + difference 4 1) (sourceB2304 + difference 1 4) sourceC2304) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1818) := by
    have ha : (tripleCharges (sourceA2304 + difference 4 1) (sourceB2304 + difference 1 4) sourceC2304) = raw31769 := by
      apply Matrix.ext; unfold tripleCharges sourceA2304 sourceB2304 sourceC2304 difference raw31769; decide +kernel
    rw [ha]
    exact (canonical31769 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2304 + difference 5 1) (sourceB2304 + difference 1 5) sourceC2304) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1819) := by
    have ha : (tripleCharges (sourceA2304 + difference 5 1) (sourceB2304 + difference 1 5) sourceC2304) = raw31770 := by
      apply Matrix.ext; unfold tripleCharges sourceA2304 sourceB2304 sourceC2304 difference raw31770; decide +kernel
    rw [ha]
    exact (canonical31770 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2304 + sourceB2304) sourceC2304) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2304 + sourceB2304) sourceC2304) = raw19413 := by
      apply Matrix.ext; unfold doubleCharges sourceA2304 sourceB2304 sourceC2304 raw19413; decide +kernel
    rw [ha]
    exact (canonical19413 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2304 sourceB2304 sourceC2304
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2304, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2305 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2305 : Charge := ![0, 1, 0, -1, 0, 0]
def sourceC2305 : Charge := ![3, 0, 0, 1, -2, -2]
def sourceForm2305 : Integer.Sparse Master := [(Sum.inr 4082, 1), (Sum.inr 4321, 1), (Sum.inr 4325, 2), (Sum.inr 4339, 1), (Sum.inr 4432, 1), (Sum.inr 4659, 1), (Sum.inr 4662, 2), (Sum.inr 4674, 1), (Sum.inr 4711, 1), (Sum.inr 4718, 2), (Sum.inr 4755, 2), (Sum.inr 4758, 1), (Sum.inr 4782, 2), (Sum.inr 4788, 2), (Sum.inr 4790, 1), (Sum.inr 4828, 2), (Sum.inr 4846, 2), (Sum.inr 5063, 1), (Sum.inr 5125, 1), (Sum.inr 5126, 1), (Sum.inr 5141, 2)]

theorem sourceEq2305 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2305 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2305 + difference 0 1) (sourceB2305 + difference 1 0) sourceC2305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5125) := by
    have ha : (tripleCharges (sourceA2305 + difference 0 1) (sourceB2305 + difference 1 0) sourceC2305) = raw31771 := by
      apply Matrix.ext; unfold tripleCharges sourceA2305 sourceB2305 sourceC2305 difference raw31771; decide +kernel
    rw [ha]
    exact (canonical31771 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2305 + difference 0 2) (sourceB2305 + difference 2 0) sourceC2305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5126) := by
    have ha : (tripleCharges (sourceA2305 + difference 0 2) (sourceB2305 + difference 2 0) sourceC2305) = raw31772 := by
      apply Matrix.ext; unfold tripleCharges sourceA2305 sourceB2305 sourceC2305 difference raw31772; decide +kernel
    rw [ha]
    exact (canonical31772 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2305 + difference 0 3) (sourceB2305 + difference 3 0) sourceC2305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5063) := by
    have ha : (tripleCharges (sourceA2305 + difference 0 3) (sourceB2305 + difference 3 0) sourceC2305) = raw31773 := by
      apply Matrix.ext; unfold tripleCharges sourceA2305 sourceB2305 sourceC2305 difference raw31773; decide +kernel
    rw [ha]
    exact (canonical31773 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2305 + difference 0 4) (sourceB2305 + difference 4 0) sourceC2305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2305 + difference 0 4) (sourceB2305 + difference 4 0) sourceC2305) = raw31774 := by
      apply Matrix.ext; unfold tripleCharges sourceA2305 sourceB2305 sourceC2305 difference raw31774; decide +kernel
    rw [ha]
    exact (canonical31774 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2305 + difference 0 5) (sourceB2305 + difference 5 0) sourceC2305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2305 + difference 0 5) (sourceB2305 + difference 5 0) sourceC2305) = raw31775 := by
      apply Matrix.ext; unfold tripleCharges sourceA2305 sourceB2305 sourceC2305 difference raw31775; decide +kernel
    rw [ha]
    exact (canonical31775 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2305 + difference 1 0) (sourceB2305 + difference 0 1) sourceC2305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4432) := by
    have ha : (tripleCharges (sourceA2305 + difference 1 0) (sourceB2305 + difference 0 1) sourceC2305) = raw31776 := by
      apply Matrix.ext; unfold tripleCharges sourceA2305 sourceB2305 sourceC2305 difference raw31776; decide +kernel
    rw [ha]
    exact (canonical31776 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2305 + difference 1 2) (sourceB2305 + difference 2 1) sourceC2305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4790) := by
    have ha : (tripleCharges (sourceA2305 + difference 1 2) (sourceB2305 + difference 2 1) sourceC2305) = raw23580 := by
      apply Matrix.ext; unfold tripleCharges sourceA2305 sourceB2305 sourceC2305 difference raw23580; decide +kernel
    rw [ha]
    exact (canonical23580 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2305 + difference 1 3) (sourceB2305 + difference 3 1) sourceC2305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA2305 + difference 1 3) (sourceB2305 + difference 3 1) sourceC2305) = raw23581 := by
      apply Matrix.ext; unfold tripleCharges sourceA2305 sourceB2305 sourceC2305 difference raw23581; decide +kernel
    rw [ha]
    exact (canonical23581 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2305 + difference 1 4) (sourceB2305 + difference 4 1) sourceC2305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA2305 + difference 1 4) (sourceB2305 + difference 4 1) sourceC2305) = raw23582 := by
      apply Matrix.ext; unfold tripleCharges sourceA2305 sourceB2305 sourceC2305 difference raw23582; decide +kernel
    rw [ha]
    exact (canonical23582 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2305 + difference 1 5) (sourceB2305 + difference 5 1) sourceC2305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA2305 + difference 1 5) (sourceB2305 + difference 5 1) sourceC2305) = raw23583 := by
      apply Matrix.ext; unfold tripleCharges sourceA2305 sourceB2305 sourceC2305 difference raw23583; decide +kernel
    rw [ha]
    exact (canonical23583 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2305 + difference 2 0) (sourceB2305 + difference 0 2) sourceC2305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4321) := by
    have ha : (tripleCharges (sourceA2305 + difference 2 0) (sourceB2305 + difference 0 2) sourceC2305) = raw23590 := by
      apply Matrix.ext; unfold tripleCharges sourceA2305 sourceB2305 sourceC2305 difference raw23590; decide +kernel
    rw [ha]
    exact (canonical23590 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2305 + difference 2 1) (sourceB2305 + difference 1 2) sourceC2305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4659) := by
    have ha : (tripleCharges (sourceA2305 + difference 2 1) (sourceB2305 + difference 1 2) sourceC2305) = raw31777 := by
      apply Matrix.ext; unfold tripleCharges sourceA2305 sourceB2305 sourceC2305 difference raw31777; decide +kernel
    rw [ha]
    exact (canonical31777 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2305 + difference 2 3) (sourceB2305 + difference 3 2) sourceC2305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4711) := by
    have ha : (tripleCharges (sourceA2305 + difference 2 3) (sourceB2305 + difference 3 2) sourceC2305) = raw31778 := by
      apply Matrix.ext; unfold tripleCharges sourceA2305 sourceB2305 sourceC2305 difference raw31778; decide +kernel
    rw [ha]
    exact (canonical31778 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2305 + difference 2 4) (sourceB2305 + difference 4 2) sourceC2305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4782) := by
    have ha : (tripleCharges (sourceA2305 + difference 2 4) (sourceB2305 + difference 4 2) sourceC2305) = raw31779 := by
      apply Matrix.ext; unfold tripleCharges sourceA2305 sourceB2305 sourceC2305 difference raw31779; decide +kernel
    rw [ha]
    exact (canonical31779 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2305 + difference 2 5) (sourceB2305 + difference 5 2) sourceC2305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4782) := by
    have ha : (tripleCharges (sourceA2305 + difference 2 5) (sourceB2305 + difference 5 2) sourceC2305) = raw31780 := by
      apply Matrix.ext; unfold tripleCharges sourceA2305 sourceB2305 sourceC2305 difference raw31780; decide +kernel
    rw [ha]
    exact (canonical31780 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2305 + difference 3 0) (sourceB2305 + difference 0 3) sourceC2305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4339) := by
    have ha : (tripleCharges (sourceA2305 + difference 3 0) (sourceB2305 + difference 0 3) sourceC2305) = raw23595 := by
      apply Matrix.ext; unfold tripleCharges sourceA2305 sourceB2305 sourceC2305 difference raw23595; decide +kernel
    rw [ha]
    exact (canonical23595 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2305 + difference 3 1) (sourceB2305 + difference 1 3) sourceC2305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4674) := by
    have ha : (tripleCharges (sourceA2305 + difference 3 1) (sourceB2305 + difference 1 3) sourceC2305) = raw31781 := by
      apply Matrix.ext; unfold tripleCharges sourceA2305 sourceB2305 sourceC2305 difference raw31781; decide +kernel
    rw [ha]
    exact (canonical31781 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2305 + difference 3 2) (sourceB2305 + difference 2 3) sourceC2305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4758) := by
    have ha : (tripleCharges (sourceA2305 + difference 3 2) (sourceB2305 + difference 2 3) sourceC2305) = raw31782 := by
      apply Matrix.ext; unfold tripleCharges sourceA2305 sourceB2305 sourceC2305 difference raw31782; decide +kernel
    rw [ha]
    exact (canonical31782 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2305 + difference 3 4) (sourceB2305 + difference 4 3) sourceC2305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4828) := by
    have ha : (tripleCharges (sourceA2305 + difference 3 4) (sourceB2305 + difference 4 3) sourceC2305) = raw31783 := by
      apply Matrix.ext; unfold tripleCharges sourceA2305 sourceB2305 sourceC2305 difference raw31783; decide +kernel
    rw [ha]
    exact (canonical31783 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2305 + difference 3 5) (sourceB2305 + difference 5 3) sourceC2305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4828) := by
    have ha : (tripleCharges (sourceA2305 + difference 3 5) (sourceB2305 + difference 5 3) sourceC2305) = raw31784 := by
      apply Matrix.ext; unfold tripleCharges sourceA2305 sourceB2305 sourceC2305 difference raw31784; decide +kernel
    rw [ha]
    exact (canonical31784 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2305 + difference 4 0) (sourceB2305 + difference 0 4) sourceC2305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4325) := by
    have ha : (tripleCharges (sourceA2305 + difference 4 0) (sourceB2305 + difference 0 4) sourceC2305) = raw23600 := by
      apply Matrix.ext; unfold tripleCharges sourceA2305 sourceB2305 sourceC2305 difference raw23600; decide +kernel
    rw [ha]
    exact (canonical23600 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2305 + difference 4 1) (sourceB2305 + difference 1 4) sourceC2305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4662) := by
    have ha : (tripleCharges (sourceA2305 + difference 4 1) (sourceB2305 + difference 1 4) sourceC2305) = raw31785 := by
      apply Matrix.ext; unfold tripleCharges sourceA2305 sourceB2305 sourceC2305 difference raw31785; decide +kernel
    rw [ha]
    exact (canonical31785 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2305 + difference 4 2) (sourceB2305 + difference 2 4) sourceC2305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4755) := by
    have ha : (tripleCharges (sourceA2305 + difference 4 2) (sourceB2305 + difference 2 4) sourceC2305) = raw31786 := by
      apply Matrix.ext; unfold tripleCharges sourceA2305 sourceB2305 sourceC2305 difference raw31786; decide +kernel
    rw [ha]
    exact (canonical31786 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2305 + difference 4 3) (sourceB2305 + difference 3 4) sourceC2305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4718) := by
    have ha : (tripleCharges (sourceA2305 + difference 4 3) (sourceB2305 + difference 3 4) sourceC2305) = raw31787 := by
      apply Matrix.ext; unfold tripleCharges sourceA2305 sourceB2305 sourceC2305 difference raw31787; decide +kernel
    rw [ha]
    exact (canonical31787 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2305 + difference 4 5) (sourceB2305 + difference 5 4) sourceC2305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4788) := by
    have ha : (tripleCharges (sourceA2305 + difference 4 5) (sourceB2305 + difference 5 4) sourceC2305) = raw31788 := by
      apply Matrix.ext; unfold tripleCharges sourceA2305 sourceB2305 sourceC2305 difference raw31788; decide +kernel
    rw [ha]
    exact (canonical31788 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2305 + difference 5 0) (sourceB2305 + difference 0 5) sourceC2305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4325) := by
    have ha : (tripleCharges (sourceA2305 + difference 5 0) (sourceB2305 + difference 0 5) sourceC2305) = raw23605 := by
      apply Matrix.ext; unfold tripleCharges sourceA2305 sourceB2305 sourceC2305 difference raw23605; decide +kernel
    rw [ha]
    exact (canonical23605 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2305 + difference 5 1) (sourceB2305 + difference 1 5) sourceC2305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4662) := by
    have ha : (tripleCharges (sourceA2305 + difference 5 1) (sourceB2305 + difference 1 5) sourceC2305) = raw31789 := by
      apply Matrix.ext; unfold tripleCharges sourceA2305 sourceB2305 sourceC2305 difference raw31789; decide +kernel
    rw [ha]
    exact (canonical31789 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2305 + difference 5 2) (sourceB2305 + difference 2 5) sourceC2305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4755) := by
    have ha : (tripleCharges (sourceA2305 + difference 5 2) (sourceB2305 + difference 2 5) sourceC2305) = raw31790 := by
      apply Matrix.ext; unfold tripleCharges sourceA2305 sourceB2305 sourceC2305 difference raw31790; decide +kernel
    rw [ha]
    exact (canonical31790 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2305 + difference 5 3) (sourceB2305 + difference 3 5) sourceC2305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4718) := by
    have ha : (tripleCharges (sourceA2305 + difference 5 3) (sourceB2305 + difference 3 5) sourceC2305) = raw31791 := by
      apply Matrix.ext; unfold tripleCharges sourceA2305 sourceB2305 sourceC2305 difference raw31791; decide +kernel
    rw [ha]
    exact (canonical31791 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2305 + difference 5 4) (sourceB2305 + difference 4 5) sourceC2305) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4788) := by
    have ha : (tripleCharges (sourceA2305 + difference 5 4) (sourceB2305 + difference 4 5) sourceC2305) = raw31792 := by
      apply Matrix.ext; unfold tripleCharges sourceA2305 sourceB2305 sourceC2305 difference raw31792; decide +kernel
    rw [ha]
    exact (canonical31792 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2305 sourceB2305 sourceC2305
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2305, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2306 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2306 : Charge := ![0, 0, 2, 0, 0, -2]
def sourceC2306 : Charge := ![3, 1, -2, 0, -2, 0]
def sourceForm2306 : Integer.Sparse Master := [(Sum.inr 891, 1), (Sum.inr 1781, 1), (Sum.inr 1870, 1), (Sum.inr 1928, 1), (Sum.inr 1945, 1), (Sum.inr 1949, 1), (Sum.inr 4082, -1)]

theorem sourceEq2306 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2306 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2306 + difference 2 0) (sourceB2306 + difference 0 2) sourceC2306) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 891) := by
    have ha : (tripleCharges (sourceA2306 + difference 2 0) (sourceB2306 + difference 0 2) sourceC2306) = raw31793 := by
      apply Matrix.ext; unfold tripleCharges sourceA2306 sourceB2306 sourceC2306 difference raw31793; decide +kernel
    rw [ha]
    exact (canonical31793 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2306 + difference 2 1) (sourceB2306 + difference 1 2) sourceC2306) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1781) := by
    have ha : (tripleCharges (sourceA2306 + difference 2 1) (sourceB2306 + difference 1 2) sourceC2306) = raw31794 := by
      apply Matrix.ext; unfold tripleCharges sourceA2306 sourceB2306 sourceC2306 difference raw31794; decide +kernel
    rw [ha]
    exact (canonical31794 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2306 + difference 2 2) (sourceB2306 + difference 2 2) sourceC2306) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1928) := by
    have ha : (tripleCharges (sourceA2306 + difference 2 2) (sourceB2306 + difference 2 2) sourceC2306) = raw31795 := by
      apply Matrix.ext; unfold tripleCharges sourceA2306 sourceB2306 sourceC2306 difference raw31795; decide +kernel
    rw [ha]
    exact (canonical31795 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2306 + difference 2 3) (sourceB2306 + difference 3 2) sourceC2306) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1870) := by
    have ha : (tripleCharges (sourceA2306 + difference 2 3) (sourceB2306 + difference 3 2) sourceC2306) = raw31796 := by
      apply Matrix.ext; unfold tripleCharges sourceA2306 sourceB2306 sourceC2306 difference raw31796; decide +kernel
    rw [ha]
    exact (canonical31796 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2306 + difference 2 4) (sourceB2306 + difference 4 2) sourceC2306) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1949) := by
    have ha : (tripleCharges (sourceA2306 + difference 2 4) (sourceB2306 + difference 4 2) sourceC2306) = raw31797 := by
      apply Matrix.ext; unfold tripleCharges sourceA2306 sourceB2306 sourceC2306 difference raw31797; decide +kernel
    rw [ha]
    exact (canonical31797 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2306 + difference 2 5) (sourceB2306 + difference 5 2) sourceC2306) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1945) := by
    have ha : (tripleCharges (sourceA2306 + difference 2 5) (sourceB2306 + difference 5 2) sourceC2306) = raw31798 := by
      apply Matrix.ext; unfold tripleCharges sourceA2306 sourceB2306 sourceC2306 difference raw31798; decide +kernel
    rw [ha]
    exact (canonical31798 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2306 + sourceB2306) sourceC2306) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2306 + sourceB2306) sourceC2306) = raw31799 := by
      apply Matrix.ext; unfold doubleCharges sourceA2306 sourceB2306 sourceC2306 raw31799; decide +kernel
    rw [ha]
    exact (canonical31799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2306 sourceB2306 sourceC2306
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2306, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2307 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2307 : Charge := ![0, 0, 2, 0, -1, -1]
def sourceC2307 : Charge := ![3, 1, -2, 0, -1, -1]
def sourceForm2307 : Integer.Sparse Master := [(Sum.inr 892, 1), (Sum.inr 1782, 1), (Sum.inr 1871, 1), (Sum.inr 1929, 1), (Sum.inr 1947, 2), (Sum.inr 4080, -1)]

theorem sourceEq2307 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2307 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2307 + difference 2 0) (sourceB2307 + difference 0 2) sourceC2307) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 892) := by
    have ha : (tripleCharges (sourceA2307 + difference 2 0) (sourceB2307 + difference 0 2) sourceC2307) = raw31800 := by
      apply Matrix.ext; unfold tripleCharges sourceA2307 sourceB2307 sourceC2307 difference raw31800; decide +kernel
    rw [ha]
    exact (canonical31800 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2307 + difference 2 1) (sourceB2307 + difference 1 2) sourceC2307) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1782) := by
    have ha : (tripleCharges (sourceA2307 + difference 2 1) (sourceB2307 + difference 1 2) sourceC2307) = raw31801 := by
      apply Matrix.ext; unfold tripleCharges sourceA2307 sourceB2307 sourceC2307 difference raw31801; decide +kernel
    rw [ha]
    exact (canonical31801 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2307 + difference 2 2) (sourceB2307 + difference 2 2) sourceC2307) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1929) := by
    have ha : (tripleCharges (sourceA2307 + difference 2 2) (sourceB2307 + difference 2 2) sourceC2307) = raw31802 := by
      apply Matrix.ext; unfold tripleCharges sourceA2307 sourceB2307 sourceC2307 difference raw31802; decide +kernel
    rw [ha]
    exact (canonical31802 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2307 + difference 2 3) (sourceB2307 + difference 3 2) sourceC2307) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1871) := by
    have ha : (tripleCharges (sourceA2307 + difference 2 3) (sourceB2307 + difference 3 2) sourceC2307) = raw31803 := by
      apply Matrix.ext; unfold tripleCharges sourceA2307 sourceB2307 sourceC2307 difference raw31803; decide +kernel
    rw [ha]
    exact (canonical31803 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2307 + difference 2 4) (sourceB2307 + difference 4 2) sourceC2307) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1947) := by
    have ha : (tripleCharges (sourceA2307 + difference 2 4) (sourceB2307 + difference 4 2) sourceC2307) = raw31804 := by
      apply Matrix.ext; unfold tripleCharges sourceA2307 sourceB2307 sourceC2307 difference raw31804; decide +kernel
    rw [ha]
    exact (canonical31804 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2307 + difference 2 5) (sourceB2307 + difference 5 2) sourceC2307) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1947) := by
    have ha : (tripleCharges (sourceA2307 + difference 2 5) (sourceB2307 + difference 5 2) sourceC2307) = raw31805 := by
      apply Matrix.ext; unfold tripleCharges sourceA2307 sourceB2307 sourceC2307 difference raw31805; decide +kernel
    rw [ha]
    exact (canonical31805 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2307 + sourceB2307) sourceC2307) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2307 + sourceB2307) sourceC2307) = raw31806 := by
      apply Matrix.ext; unfold doubleCharges sourceA2307 sourceB2307 sourceC2307 raw31806; decide +kernel
    rw [ha]
    exact (canonical31806 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2307 sourceB2307 sourceC2307
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2307, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2308 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2308 : Charge := ![0, 0, 1, 0, 0, -1]
def sourceC2308 : Charge := ![3, 1, -1, 0, -2, -1]
def sourceForm2308 : Integer.Sparse Master := [(Sum.inr 4080, 1), (Sum.inr 4288, 1), (Sum.inr 4295, 1), (Sum.inr 4296, 1), (Sum.inr 4311, 1), (Sum.inr 4404, 1), (Sum.inr 4632, 1), (Sum.inr 4637, 1), (Sum.inr 4638, 1), (Sum.inr 4652, 1), (Sum.inr 4706, 1), (Sum.inr 4707, 1), (Sum.inr 4715, 1), (Sum.inr 4722, 1), (Sum.inr 4726, 1), (Sum.inr 4727, 1), (Sum.inr 4736, 1), (Sum.inr 4737, 1), (Sum.inr 4741, 1), (Sum.inr 4742, 1), (Sum.inr 4752, 1), (Sum.inr 4782, 1), (Sum.inr 4828, 1), (Sum.inr 4834, 1), (Sum.inr 4835, 1), (Sum.inr 5015, 1), (Sum.inr 5056, 1), (Sum.inr 5095, 1), (Sum.inr 5101, 1), (Sum.inr 5102, 1)]

theorem sourceEq2308 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2308 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2308 + difference 0 1) (sourceB2308 + difference 1 0) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5015) := by
    have ha : (tripleCharges (sourceA2308 + difference 0 1) (sourceB2308 + difference 1 0) sourceC2308) = raw31807 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31807; decide +kernel
    rw [ha]
    exact (canonical31807 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2308 + difference 0 2) (sourceB2308 + difference 2 0) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5095) := by
    have ha : (tripleCharges (sourceA2308 + difference 0 2) (sourceB2308 + difference 2 0) sourceC2308) = raw31808 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31808; decide +kernel
    rw [ha]
    exact (canonical31808 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2308 + difference 0 3) (sourceB2308 + difference 3 0) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5056) := by
    have ha : (tripleCharges (sourceA2308 + difference 0 3) (sourceB2308 + difference 3 0) sourceC2308) = raw31809 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31809; decide +kernel
    rw [ha]
    exact (canonical31809 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2308 + difference 0 4) (sourceB2308 + difference 4 0) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA2308 + difference 0 4) (sourceB2308 + difference 4 0) sourceC2308) = raw31810 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31810; decide +kernel
    rw [ha]
    exact (canonical31810 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2308 + difference 0 5) (sourceB2308 + difference 5 0) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA2308 + difference 0 5) (sourceB2308 + difference 5 0) sourceC2308) = raw31811 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31811; decide +kernel
    rw [ha]
    exact (canonical31811 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2308 + difference 1 0) (sourceB2308 + difference 0 1) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4404) := by
    have ha : (tripleCharges (sourceA2308 + difference 1 0) (sourceB2308 + difference 0 1) sourceC2308) = raw31812 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31812; decide +kernel
    rw [ha]
    exact (canonical31812 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2308 + difference 1 2) (sourceB2308 + difference 2 1) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4828) := by
    have ha : (tripleCharges (sourceA2308 + difference 1 2) (sourceB2308 + difference 2 1) sourceC2308) = raw31813 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31813; decide +kernel
    rw [ha]
    exact (canonical31813 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2308 + difference 1 3) (sourceB2308 + difference 3 1) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4782) := by
    have ha : (tripleCharges (sourceA2308 + difference 1 3) (sourceB2308 + difference 3 1) sourceC2308) = raw31814 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31814; decide +kernel
    rw [ha]
    exact (canonical31814 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2308 + difference 1 4) (sourceB2308 + difference 4 1) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA2308 + difference 1 4) (sourceB2308 + difference 4 1) sourceC2308) = raw31815 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31815; decide +kernel
    rw [ha]
    exact (canonical31815 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2308 + difference 1 5) (sourceB2308 + difference 5 1) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2308 + difference 1 5) (sourceB2308 + difference 5 1) sourceC2308) = raw31816 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31816; decide +kernel
    rw [ha]
    exact (canonical31816 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2308 + difference 2 0) (sourceB2308 + difference 0 2) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4311) := by
    have ha : (tripleCharges (sourceA2308 + difference 2 0) (sourceB2308 + difference 0 2) sourceC2308) = raw31817 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31817; decide +kernel
    rw [ha]
    exact (canonical31817 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2308 + difference 2 1) (sourceB2308 + difference 1 2) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4652) := by
    have ha : (tripleCharges (sourceA2308 + difference 2 1) (sourceB2308 + difference 1 2) sourceC2308) = raw31818 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31818; decide +kernel
    rw [ha]
    exact (canonical31818 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2308 + difference 2 3) (sourceB2308 + difference 3 2) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4715) := by
    have ha : (tripleCharges (sourceA2308 + difference 2 3) (sourceB2308 + difference 3 2) sourceC2308) = raw31819 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31819; decide +kernel
    rw [ha]
    exact (canonical31819 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2308 + difference 2 4) (sourceB2308 + difference 4 2) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4752) := by
    have ha : (tripleCharges (sourceA2308 + difference 2 4) (sourceB2308 + difference 4 2) sourceC2308) = raw31820 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31820; decide +kernel
    rw [ha]
    exact (canonical31820 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2308 + difference 2 5) (sourceB2308 + difference 5 2) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2308 + difference 2 5) (sourceB2308 + difference 5 2) sourceC2308) = raw31821 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31821; decide +kernel
    rw [ha]
    exact (canonical31821 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2308 + difference 3 0) (sourceB2308 + difference 0 3) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4288) := by
    have ha : (tripleCharges (sourceA2308 + difference 3 0) (sourceB2308 + difference 0 3) sourceC2308) = raw31822 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31822; decide +kernel
    rw [ha]
    exact (canonical31822 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2308 + difference 3 1) (sourceB2308 + difference 1 3) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4632) := by
    have ha : (tripleCharges (sourceA2308 + difference 3 1) (sourceB2308 + difference 1 3) sourceC2308) = raw31823 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31823; decide +kernel
    rw [ha]
    exact (canonical31823 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2308 + difference 3 2) (sourceB2308 + difference 2 3) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4722) := by
    have ha : (tripleCharges (sourceA2308 + difference 3 2) (sourceB2308 + difference 2 3) sourceC2308) = raw31824 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31824; decide +kernel
    rw [ha]
    exact (canonical31824 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2308 + difference 3 4) (sourceB2308 + difference 4 3) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4737) := by
    have ha : (tripleCharges (sourceA2308 + difference 3 4) (sourceB2308 + difference 4 3) sourceC2308) = raw31825 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31825; decide +kernel
    rw [ha]
    exact (canonical31825 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2308 + difference 3 5) (sourceB2308 + difference 5 3) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4736) := by
    have ha : (tripleCharges (sourceA2308 + difference 3 5) (sourceB2308 + difference 5 3) sourceC2308) = raw31826 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31826; decide +kernel
    rw [ha]
    exact (canonical31826 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2308 + difference 4 0) (sourceB2308 + difference 0 4) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4295) := by
    have ha : (tripleCharges (sourceA2308 + difference 4 0) (sourceB2308 + difference 0 4) sourceC2308) = raw31827 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31827; decide +kernel
    rw [ha]
    exact (canonical31827 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2308 + difference 4 1) (sourceB2308 + difference 1 4) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4637) := by
    have ha : (tripleCharges (sourceA2308 + difference 4 1) (sourceB2308 + difference 1 4) sourceC2308) = raw31828 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31828; decide +kernel
    rw [ha]
    exact (canonical31828 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2308 + difference 4 2) (sourceB2308 + difference 2 4) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4726) := by
    have ha : (tripleCharges (sourceA2308 + difference 4 2) (sourceB2308 + difference 2 4) sourceC2308) = raw31829 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31829; decide +kernel
    rw [ha]
    exact (canonical31829 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2308 + difference 4 3) (sourceB2308 + difference 3 4) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4706) := by
    have ha : (tripleCharges (sourceA2308 + difference 4 3) (sourceB2308 + difference 3 4) sourceC2308) = raw31830 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31830; decide +kernel
    rw [ha]
    exact (canonical31830 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2308 + difference 4 5) (sourceB2308 + difference 5 4) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4741) := by
    have ha : (tripleCharges (sourceA2308 + difference 4 5) (sourceB2308 + difference 5 4) sourceC2308) = raw31831 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31831; decide +kernel
    rw [ha]
    exact (canonical31831 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2308 + difference 5 0) (sourceB2308 + difference 0 5) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4296) := by
    have ha : (tripleCharges (sourceA2308 + difference 5 0) (sourceB2308 + difference 0 5) sourceC2308) = raw31832 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31832; decide +kernel
    rw [ha]
    exact (canonical31832 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2308 + difference 5 1) (sourceB2308 + difference 1 5) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4638) := by
    have ha : (tripleCharges (sourceA2308 + difference 5 1) (sourceB2308 + difference 1 5) sourceC2308) = raw31833 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31833; decide +kernel
    rw [ha]
    exact (canonical31833 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2308 + difference 5 2) (sourceB2308 + difference 2 5) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4727) := by
    have ha : (tripleCharges (sourceA2308 + difference 5 2) (sourceB2308 + difference 2 5) sourceC2308) = raw31834 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31834; decide +kernel
    rw [ha]
    exact (canonical31834 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2308 + difference 5 3) (sourceB2308 + difference 3 5) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4707) := by
    have ha : (tripleCharges (sourceA2308 + difference 5 3) (sourceB2308 + difference 3 5) sourceC2308) = raw31835 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31835; decide +kernel
    rw [ha]
    exact (canonical31835 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2308 + difference 5 4) (sourceB2308 + difference 4 5) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4742) := by
    have ha : (tripleCharges (sourceA2308 + difference 5 4) (sourceB2308 + difference 4 5) sourceC2308) = raw31836 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31836; decide +kernel
    rw [ha]
    exact (canonical31836 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2308 sourceB2308 sourceC2308
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2308, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2309 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2309 : Charge := ![0, 0, 1, 0, 0, -1]
def sourceC2309 : Charge := ![3, 1, -1, 0, -2, -1]
def sourceForm2309 : Integer.Sparse Master := [(Sum.inr 1554, 1), (Sum.inr 1569, 1), (Sum.inr 1570, 1), (Sum.inr 1572, 1), (Sum.inr 1618, 1), (Sum.inr 1837, 1), (Sum.inr 1850, 1), (Sum.inr 1851, 1), (Sum.inr 1853, 1), (Sum.inr 1888, 1), (Sum.inr 1889, 1), (Sum.inr 1890, 1), (Sum.inr 1906, 1), (Sum.inr 1908, 1), (Sum.inr 1909, 1), (Sum.inr 1938, 1), (Sum.inr 1939, 1), (Sum.inr 1944, 1), (Sum.inr 1946, 1), (Sum.inr 1947, 1), (Sum.inr 1997, 1), (Sum.inr 2048, 1), (Sum.inr 2053, 1), (Sum.inr 2054, 1), (Sum.inr 2400, 1), (Sum.inr 2459, 1), (Sum.inr 2505, 1), (Sum.inr 2511, 1), (Sum.inr 2512, 1), (Sum.inr 4080, 1)]

theorem sourceEq2309 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2309 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2309 + difference 0 1) (sourceB2309 + difference 1 0) sourceC2309) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2400) := by
    have ha : (tripleCharges (sourceA2309 + difference 0 1) (sourceB2309 + difference 1 0) sourceC2309) = raw31837 := by
      apply Matrix.ext; unfold tripleCharges sourceA2309 sourceB2309 sourceC2309 difference raw31837; decide +kernel
    rw [ha]
    exact (canonical31837 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2309 + difference 0 2) (sourceB2309 + difference 2 0) sourceC2309) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2505) := by
    have ha : (tripleCharges (sourceA2309 + difference 0 2) (sourceB2309 + difference 2 0) sourceC2309) = raw31838 := by
      apply Matrix.ext; unfold tripleCharges sourceA2309 sourceB2309 sourceC2309 difference raw31838; decide +kernel
    rw [ha]
    exact (canonical31838 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2309 + difference 0 3) (sourceB2309 + difference 3 0) sourceC2309) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2459) := by
    have ha : (tripleCharges (sourceA2309 + difference 0 3) (sourceB2309 + difference 3 0) sourceC2309) = raw31839 := by
      apply Matrix.ext; unfold tripleCharges sourceA2309 sourceB2309 sourceC2309 difference raw31839; decide +kernel
    rw [ha]
    exact (canonical31839 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2309 + difference 0 4) (sourceB2309 + difference 4 0) sourceC2309) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA2309 + difference 0 4) (sourceB2309 + difference 4 0) sourceC2309) = raw31840 := by
      apply Matrix.ext; unfold tripleCharges sourceA2309 sourceB2309 sourceC2309 difference raw31840; decide +kernel
    rw [ha]
    exact (canonical31840 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2309 + difference 0 5) (sourceB2309 + difference 5 0) sourceC2309) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2511) := by
    have ha : (tripleCharges (sourceA2309 + difference 0 5) (sourceB2309 + difference 5 0) sourceC2309) = raw31841 := by
      apply Matrix.ext; unfold tripleCharges sourceA2309 sourceB2309 sourceC2309 difference raw31841; decide +kernel
    rw [ha]
    exact (canonical31841 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2309 + difference 1 0) (sourceB2309 + difference 0 1) sourceC2309) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1618) := by
    have ha : (tripleCharges (sourceA2309 + difference 1 0) (sourceB2309 + difference 0 1) sourceC2309) = raw31842 := by
      apply Matrix.ext; unfold tripleCharges sourceA2309 sourceB2309 sourceC2309 difference raw31842; decide +kernel
    rw [ha]
    exact (canonical31842 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2309 + difference 1 2) (sourceB2309 + difference 2 1) sourceC2309) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2048) := by
    have ha : (tripleCharges (sourceA2309 + difference 1 2) (sourceB2309 + difference 2 1) sourceC2309) = raw31843 := by
      apply Matrix.ext; unfold tripleCharges sourceA2309 sourceB2309 sourceC2309 difference raw31843; decide +kernel
    rw [ha]
    exact (canonical31843 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2309 + difference 1 3) (sourceB2309 + difference 3 1) sourceC2309) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1997) := by
    have ha : (tripleCharges (sourceA2309 + difference 1 3) (sourceB2309 + difference 3 1) sourceC2309) = raw31844 := by
      apply Matrix.ext; unfold tripleCharges sourceA2309 sourceB2309 sourceC2309 difference raw31844; decide +kernel
    rw [ha]
    exact (canonical31844 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2309 + difference 1 4) (sourceB2309 + difference 4 1) sourceC2309) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2054) := by
    have ha : (tripleCharges (sourceA2309 + difference 1 4) (sourceB2309 + difference 4 1) sourceC2309) = raw31845 := by
      apply Matrix.ext; unfold tripleCharges sourceA2309 sourceB2309 sourceC2309 difference raw31845; decide +kernel
    rw [ha]
    exact (canonical31845 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2309 + difference 1 5) (sourceB2309 + difference 5 1) sourceC2309) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2053) := by
    have ha : (tripleCharges (sourceA2309 + difference 1 5) (sourceB2309 + difference 5 1) sourceC2309) = raw31846 := by
      apply Matrix.ext; unfold tripleCharges sourceA2309 sourceB2309 sourceC2309 difference raw31846; decide +kernel
    rw [ha]
    exact (canonical31846 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2309 + difference 2 0) (sourceB2309 + difference 0 2) sourceC2309) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1572) := by
    have ha : (tripleCharges (sourceA2309 + difference 2 0) (sourceB2309 + difference 0 2) sourceC2309) = raw31847 := by
      apply Matrix.ext; unfold tripleCharges sourceA2309 sourceB2309 sourceC2309 difference raw31847; decide +kernel
    rw [ha]
    exact (canonical31847 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2309 + difference 2 1) (sourceB2309 + difference 1 2) sourceC2309) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1853) := by
    have ha : (tripleCharges (sourceA2309 + difference 2 1) (sourceB2309 + difference 1 2) sourceC2309) = raw31848 := by
      apply Matrix.ext; unfold tripleCharges sourceA2309 sourceB2309 sourceC2309 difference raw31848; decide +kernel
    rw [ha]
    exact (canonical31848 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2309 + difference 2 3) (sourceB2309 + difference 3 2) sourceC2309) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1890) := by
    have ha : (tripleCharges (sourceA2309 + difference 2 3) (sourceB2309 + difference 3 2) sourceC2309) = raw31849 := by
      apply Matrix.ext; unfold tripleCharges sourceA2309 sourceB2309 sourceC2309 difference raw31849; decide +kernel
    rw [ha]
    exact (canonical31849 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2309 + difference 2 4) (sourceB2309 + difference 4 2) sourceC2309) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1947) := by
    have ha : (tripleCharges (sourceA2309 + difference 2 4) (sourceB2309 + difference 4 2) sourceC2309) = raw31850 := by
      apply Matrix.ext; unfold tripleCharges sourceA2309 sourceB2309 sourceC2309 difference raw31850; decide +kernel
    rw [ha]
    exact (canonical31850 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2309 + difference 2 5) (sourceB2309 + difference 5 2) sourceC2309) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2309 + difference 2 5) (sourceB2309 + difference 5 2) sourceC2309) = raw31851 := by
      apply Matrix.ext; unfold tripleCharges sourceA2309 sourceB2309 sourceC2309 difference raw31851; decide +kernel
    rw [ha]
    exact (canonical31851 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2309 + difference 3 0) (sourceB2309 + difference 0 3) sourceC2309) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1554) := by
    have ha : (tripleCharges (sourceA2309 + difference 3 0) (sourceB2309 + difference 0 3) sourceC2309) = raw31852 := by
      apply Matrix.ext; unfold tripleCharges sourceA2309 sourceB2309 sourceC2309 difference raw31852; decide +kernel
    rw [ha]
    exact (canonical31852 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2309 + difference 3 1) (sourceB2309 + difference 1 3) sourceC2309) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1837) := by
    have ha : (tripleCharges (sourceA2309 + difference 3 1) (sourceB2309 + difference 1 3) sourceC2309) = raw31853 := by
      apply Matrix.ext; unfold tripleCharges sourceA2309 sourceB2309 sourceC2309 difference raw31853; decide +kernel
    rw [ha]
    exact (canonical31853 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2309 + difference 3 2) (sourceB2309 + difference 2 3) sourceC2309) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1906) := by
    have ha : (tripleCharges (sourceA2309 + difference 3 2) (sourceB2309 + difference 2 3) sourceC2309) = raw31854 := by
      apply Matrix.ext; unfold tripleCharges sourceA2309 sourceB2309 sourceC2309 difference raw31854; decide +kernel
    rw [ha]
    exact (canonical31854 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2309 + difference 3 4) (sourceB2309 + difference 4 3) sourceC2309) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1909) := by
    have ha : (tripleCharges (sourceA2309 + difference 3 4) (sourceB2309 + difference 4 3) sourceC2309) = raw31855 := by
      apply Matrix.ext; unfold tripleCharges sourceA2309 sourceB2309 sourceC2309 difference raw31855; decide +kernel
    rw [ha]
    exact (canonical31855 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2309 + difference 3 5) (sourceB2309 + difference 5 3) sourceC2309) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1908) := by
    have ha : (tripleCharges (sourceA2309 + difference 3 5) (sourceB2309 + difference 5 3) sourceC2309) = raw31856 := by
      apply Matrix.ext; unfold tripleCharges sourceA2309 sourceB2309 sourceC2309 difference raw31856; decide +kernel
    rw [ha]
    exact (canonical31856 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2309 + difference 4 0) (sourceB2309 + difference 0 4) sourceC2309) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1569) := by
    have ha : (tripleCharges (sourceA2309 + difference 4 0) (sourceB2309 + difference 0 4) sourceC2309) = raw31857 := by
      apply Matrix.ext; unfold tripleCharges sourceA2309 sourceB2309 sourceC2309 difference raw31857; decide +kernel
    rw [ha]
    exact (canonical31857 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2309 + difference 4 1) (sourceB2309 + difference 1 4) sourceC2309) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1850) := by
    have ha : (tripleCharges (sourceA2309 + difference 4 1) (sourceB2309 + difference 1 4) sourceC2309) = raw31858 := by
      apply Matrix.ext; unfold tripleCharges sourceA2309 sourceB2309 sourceC2309 difference raw31858; decide +kernel
    rw [ha]
    exact (canonical31858 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2309 + difference 4 2) (sourceB2309 + difference 2 4) sourceC2309) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1938) := by
    have ha : (tripleCharges (sourceA2309 + difference 4 2) (sourceB2309 + difference 2 4) sourceC2309) = raw31859 := by
      apply Matrix.ext; unfold tripleCharges sourceA2309 sourceB2309 sourceC2309 difference raw31859; decide +kernel
    rw [ha]
    exact (canonical31859 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2309 + difference 4 3) (sourceB2309 + difference 3 4) sourceC2309) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1888) := by
    have ha : (tripleCharges (sourceA2309 + difference 4 3) (sourceB2309 + difference 3 4) sourceC2309) = raw31860 := by
      apply Matrix.ext; unfold tripleCharges sourceA2309 sourceB2309 sourceC2309 difference raw31860; decide +kernel
    rw [ha]
    exact (canonical31860 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2309 + difference 4 5) (sourceB2309 + difference 5 4) sourceC2309) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1944) := by
    have ha : (tripleCharges (sourceA2309 + difference 4 5) (sourceB2309 + difference 5 4) sourceC2309) = raw31861 := by
      apply Matrix.ext; unfold tripleCharges sourceA2309 sourceB2309 sourceC2309 difference raw31861; decide +kernel
    rw [ha]
    exact (canonical31861 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2309 + difference 5 0) (sourceB2309 + difference 0 5) sourceC2309) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1570) := by
    have ha : (tripleCharges (sourceA2309 + difference 5 0) (sourceB2309 + difference 0 5) sourceC2309) = raw31862 := by
      apply Matrix.ext; unfold tripleCharges sourceA2309 sourceB2309 sourceC2309 difference raw31862; decide +kernel
    rw [ha]
    exact (canonical31862 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2309 + difference 5 1) (sourceB2309 + difference 1 5) sourceC2309) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1851) := by
    have ha : (tripleCharges (sourceA2309 + difference 5 1) (sourceB2309 + difference 1 5) sourceC2309) = raw31863 := by
      apply Matrix.ext; unfold tripleCharges sourceA2309 sourceB2309 sourceC2309 difference raw31863; decide +kernel
    rw [ha]
    exact (canonical31863 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2309 + difference 5 2) (sourceB2309 + difference 2 5) sourceC2309) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1939) := by
    have ha : (tripleCharges (sourceA2309 + difference 5 2) (sourceB2309 + difference 2 5) sourceC2309) = raw31864 := by
      apply Matrix.ext; unfold tripleCharges sourceA2309 sourceB2309 sourceC2309 difference raw31864; decide +kernel
    rw [ha]
    exact (canonical31864 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2309 + difference 5 3) (sourceB2309 + difference 3 5) sourceC2309) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1889) := by
    have ha : (tripleCharges (sourceA2309 + difference 5 3) (sourceB2309 + difference 3 5) sourceC2309) = raw31865 := by
      apply Matrix.ext; unfold tripleCharges sourceA2309 sourceB2309 sourceC2309 difference raw31865; decide +kernel
    rw [ha]
    exact (canonical31865 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2309 + difference 5 4) (sourceB2309 + difference 4 5) sourceC2309) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1946) := by
    have ha : (tripleCharges (sourceA2309 + difference 5 4) (sourceB2309 + difference 4 5) sourceC2309) = raw31866 := by
      apply Matrix.ext; unfold tripleCharges sourceA2309 sourceB2309 sourceC2309 difference raw31866; decide +kernel
    rw [ha]
    exact (canonical31866 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2309 sourceB2309 sourceC2309
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2309, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2310 : Charge := ![0, 0, 1, 0, 0, -1]
def sourceB2310 : Charge := ![3, 1, -1, 0, -2, -1]
def sourceC2310 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2310 : Integer.Sparse Master := [(Sum.inr 4082, 1), (Sum.inr 4298, 1), (Sum.inr 4303, 1), (Sum.inr 4305, 1), (Sum.inr 4313, 1), (Sum.inr 4419, 1), (Sum.inr 4640, 1), (Sum.inr 4644, 1), (Sum.inr 4646, 1), (Sum.inr 4653, 1), (Sum.inr 4709, 1), (Sum.inr 4711, 1), (Sum.inr 4716, 1), (Sum.inr 4731, 1), (Sum.inr 4732, 1), (Sum.inr 4744, 1), (Sum.inr 4745, 2), (Sum.inr 4749, 1), (Sum.inr 4750, 1), (Sum.inr 4753, 1), (Sum.inr 4782, 1), (Sum.inr 4810, 1), (Sum.inr 4811, 1), (Sum.inr 4846, 1), (Sum.inr 5003, 1), (Sum.inr 5050, 1), (Sum.inr 5080, 1), (Sum.inr 5081, 1), (Sum.inr 5111, 1)]

theorem sourceEq2310 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2310 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2310 + difference 0 1) (sourceB2310 + difference 1 0) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5003) := by
    have ha : (tripleCharges (sourceA2310 + difference 0 1) (sourceB2310 + difference 1 0) sourceC2310) = raw30381 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw30381; decide +kernel
    rw [ha]
    exact (canonical30381 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2310 + difference 0 2) (sourceB2310 + difference 2 0) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5111) := by
    have ha : (tripleCharges (sourceA2310 + difference 0 2) (sourceB2310 + difference 2 0) sourceC2310) = raw29691 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw29691; decide +kernel
    rw [ha]
    exact (canonical29691 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2310 + difference 0 3) (sourceB2310 + difference 3 0) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5050) := by
    have ha : (tripleCharges (sourceA2310 + difference 0 3) (sourceB2310 + difference 3 0) sourceC2310) = raw30174 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw30174; decide +kernel
    rw [ha]
    exact (canonical30174 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2310 + difference 0 4) (sourceB2310 + difference 4 0) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA2310 + difference 0 4) (sourceB2310 + difference 4 0) sourceC2310) = raw29683 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw29683; decide +kernel
    rw [ha]
    exact (canonical29683 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2310 + difference 0 5) (sourceB2310 + difference 5 0) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA2310 + difference 0 5) (sourceB2310 + difference 5 0) sourceC2310) = raw30547 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw30547; decide +kernel
    rw [ha]
    exact (canonical30547 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2310 + difference 1 0) (sourceB2310 + difference 0 1) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4419) := by
    have ha : (tripleCharges (sourceA2310 + difference 1 0) (sourceB2310 + difference 0 1) sourceC2310) = raw31434 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw31434; decide +kernel
    rw [ha]
    exact (canonical31434 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2310 + difference 1 2) (sourceB2310 + difference 2 1) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA2310 + difference 1 2) (sourceB2310 + difference 2 1) sourceC2310) = raw29690 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw29690; decide +kernel
    rw [ha]
    exact (canonical29690 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2310 + difference 1 3) (sourceB2310 + difference 3 1) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4782) := by
    have ha : (tripleCharges (sourceA2310 + difference 1 3) (sourceB2310 + difference 3 1) sourceC2310) = raw30173 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw30173; decide +kernel
    rw [ha]
    exact (canonical30173 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2310 + difference 1 4) (sourceB2310 + difference 4 1) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA2310 + difference 1 4) (sourceB2310 + difference 4 1) sourceC2310) = raw29682 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw29682; decide +kernel
    rw [ha]
    exact (canonical29682 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2310 + difference 1 5) (sourceB2310 + difference 5 1) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2310 + difference 1 5) (sourceB2310 + difference 5 1) sourceC2310) = raw30363 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw30363; decide +kernel
    rw [ha]
    exact (canonical30363 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2310 + difference 2 0) (sourceB2310 + difference 0 2) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4313) := by
    have ha : (tripleCharges (sourceA2310 + difference 2 0) (sourceB2310 + difference 0 2) sourceC2310) = raw31867 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw31867; decide +kernel
    rw [ha]
    exact (canonical31867 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2310 + difference 2 1) (sourceB2310 + difference 1 2) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4653) := by
    have ha : (tripleCharges (sourceA2310 + difference 2 1) (sourceB2310 + difference 1 2) sourceC2310) = raw31868 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw31868; decide +kernel
    rw [ha]
    exact (canonical31868 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2310 + difference 2 3) (sourceB2310 + difference 3 2) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4716) := by
    have ha : (tripleCharges (sourceA2310 + difference 2 3) (sourceB2310 + difference 3 2) sourceC2310) = raw31869 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw31869; decide +kernel
    rw [ha]
    exact (canonical31869 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2310 + difference 2 4) (sourceB2310 + difference 4 2) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4750) := by
    have ha : (tripleCharges (sourceA2310 + difference 2 4) (sourceB2310 + difference 4 2) sourceC2310) = raw30541 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw30541; decide +kernel
    rw [ha]
    exact (canonical30541 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2310 + difference 2 5) (sourceB2310 + difference 5 2) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4749) := by
    have ha : (tripleCharges (sourceA2310 + difference 2 5) (sourceB2310 + difference 5 2) sourceC2310) = raw30365 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw30365; decide +kernel
    rw [ha]
    exact (canonical30365 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2310 + difference 3 0) (sourceB2310 + difference 0 3) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4298) := by
    have ha : (tripleCharges (sourceA2310 + difference 3 0) (sourceB2310 + difference 0 3) sourceC2310) = raw31870 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw31870; decide +kernel
    rw [ha]
    exact (canonical31870 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2310 + difference 3 1) (sourceB2310 + difference 1 3) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4640) := by
    have ha : (tripleCharges (sourceA2310 + difference 3 1) (sourceB2310 + difference 1 3) sourceC2310) = raw31871 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw31871; decide +kernel
    rw [ha]
    exact (canonical31871 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2310 + difference 3 2) (sourceB2310 + difference 2 3) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4745) := by
    have ha : (tripleCharges (sourceA2310 + difference 3 2) (sourceB2310 + difference 2 3) sourceC2310) = raw31872 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw31872; decide +kernel
    rw [ha]
    exact (canonical31872 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2310 + difference 3 4) (sourceB2310 + difference 4 3) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4732) := by
    have ha : (tripleCharges (sourceA2310 + difference 3 4) (sourceB2310 + difference 4 3) sourceC2310) = raw30545 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw30545; decide +kernel
    rw [ha]
    exact (canonical30545 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2310 + difference 3 5) (sourceB2310 + difference 5 3) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4731) := by
    have ha : (tripleCharges (sourceA2310 + difference 3 5) (sourceB2310 + difference 5 3) sourceC2310) = raw30370 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw30370; decide +kernel
    rw [ha]
    exact (canonical30370 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2310 + difference 4 0) (sourceB2310 + difference 0 4) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4303) := by
    have ha : (tripleCharges (sourceA2310 + difference 4 0) (sourceB2310 + difference 0 4) sourceC2310) = raw31873 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw31873; decide +kernel
    rw [ha]
    exact (canonical31873 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2310 + difference 4 1) (sourceB2310 + difference 1 4) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4644) := by
    have ha : (tripleCharges (sourceA2310 + difference 4 1) (sourceB2310 + difference 1 4) sourceC2310) = raw31874 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw31874; decide +kernel
    rw [ha]
    exact (canonical31874 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2310 + difference 4 2) (sourceB2310 + difference 2 4) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4753) := by
    have ha : (tripleCharges (sourceA2310 + difference 4 2) (sourceB2310 + difference 2 4) sourceC2310) = raw30699 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw30699; decide +kernel
    rw [ha]
    exact (canonical30699 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2310 + difference 4 3) (sourceB2310 + difference 3 4) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4709) := by
    have ha : (tripleCharges (sourceA2310 + difference 4 3) (sourceB2310 + difference 3 4) sourceC2310) = raw31875 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw31875; decide +kernel
    rw [ha]
    exact (canonical31875 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2310 + difference 4 5) (sourceB2310 + difference 5 4) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4744) := by
    have ha : (tripleCharges (sourceA2310 + difference 4 5) (sourceB2310 + difference 5 4) sourceC2310) = raw30375 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw30375; decide +kernel
    rw [ha]
    exact (canonical30375 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2310 + difference 5 0) (sourceB2310 + difference 0 5) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4305) := by
    have ha : (tripleCharges (sourceA2310 + difference 5 0) (sourceB2310 + difference 0 5) sourceC2310) = raw31876 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw31876; decide +kernel
    rw [ha]
    exact (canonical31876 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2310 + difference 5 1) (sourceB2310 + difference 1 5) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4646) := by
    have ha : (tripleCharges (sourceA2310 + difference 5 1) (sourceB2310 + difference 1 5) sourceC2310) = raw30922 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw30922; decide +kernel
    rw [ha]
    exact (canonical30922 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2310 + difference 5 2) (sourceB2310 + difference 2 5) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA2310 + difference 5 2) (sourceB2310 + difference 2 5) sourceC2310) = raw30836 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw30836; decide +kernel
    rw [ha]
    exact (canonical30836 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2310 + difference 5 3) (sourceB2310 + difference 3 5) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4711) := by
    have ha : (tripleCharges (sourceA2310 + difference 5 3) (sourceB2310 + difference 3 5) sourceC2310) = raw30833 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw30833; decide +kernel
    rw [ha]
    exact (canonical30833 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2310 + difference 5 4) (sourceB2310 + difference 4 5) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4745) := by
    have ha : (tripleCharges (sourceA2310 + difference 5 4) (sourceB2310 + difference 4 5) sourceC2310) = raw30548 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw30548; decide +kernel
    rw [ha]
    exact (canonical30548 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2310 sourceB2310 sourceC2310
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2310, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2311 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2311 : Charge := ![3, 1, 0, 0, -2, -2]
def sourceC2311 : Charge := ![0, 0, 0, 0, 0, 0]
def sourceForm2311 : Integer.Sparse Master := [(Sum.inr 4065, 2), (Sum.inr 4067, 2), (Sum.inr 4071, 1), (Sum.inr 4074, 4), (Sum.inr 4075, 2), (Sum.inr 4076, 2), (Sum.inr 4078, 2), (Sum.inr 4080, 4), (Sum.inr 4081, 2), (Sum.inr 4082, 2), (Sum.inr 4084, 2), (Sum.inr 4088, 2), (Sum.inr 4089, 1), (Sum.inr 4092, 2)]

theorem sourceEq2311 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2311 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2311 + difference 0 1) (sourceB2311 + difference 1 0) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4089) := by
    have ha : (tripleCharges (sourceA2311 + difference 0 1) (sourceB2311 + difference 1 0) sourceC2311) = raw18339 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw18339; decide +kernel
    rw [ha]
    exact (canonical18339 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2311 + difference 0 2) (sourceB2311 + difference 2 0) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2311 + difference 0 2) (sourceB2311 + difference 2 0) sourceC2311) = raw18340 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw18340; decide +kernel
    rw [ha]
    exact (canonical18340 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2311 + difference 0 3) (sourceB2311 + difference 3 0) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2311 + difference 0 3) (sourceB2311 + difference 3 0) sourceC2311) = raw18341 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw18341; decide +kernel
    rw [ha]
    exact (canonical18341 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2311 + difference 0 4) (sourceB2311 + difference 4 0) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2311 + difference 0 4) (sourceB2311 + difference 4 0) sourceC2311) = raw2930 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw2930; decide +kernel
    rw [ha]
    exact (canonical2930 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2311 + difference 0 5) (sourceB2311 + difference 5 0) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2311 + difference 0 5) (sourceB2311 + difference 5 0) sourceC2311) = raw3336 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw3336; decide +kernel
    rw [ha]
    exact (canonical3336 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2311 + difference 1 0) (sourceB2311 + difference 0 1) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (tripleCharges (sourceA2311 + difference 1 0) (sourceB2311 + difference 0 1) sourceC2311) = raw11540 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw11540; decide +kernel
    rw [ha]
    exact (canonical11540 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2311 + difference 1 2) (sourceB2311 + difference 2 1) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA2311 + difference 1 2) (sourceB2311 + difference 2 1) sourceC2311) = raw11542 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw11542; decide +kernel
    rw [ha]
    exact (canonical11542 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2311 + difference 1 3) (sourceB2311 + difference 3 1) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA2311 + difference 1 3) (sourceB2311 + difference 3 1) sourceC2311) = raw11543 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw11543; decide +kernel
    rw [ha]
    exact (canonical11543 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2311 + difference 1 4) (sourceB2311 + difference 4 1) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA2311 + difference 1 4) (sourceB2311 + difference 4 1) sourceC2311) = raw2929 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw2929; decide +kernel
    rw [ha]
    exact (canonical2929 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2311 + difference 1 5) (sourceB2311 + difference 5 1) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA2311 + difference 1 5) (sourceB2311 + difference 5 1) sourceC2311) = raw3335 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw3335; decide +kernel
    rw [ha]
    exact (canonical3335 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2311 + difference 2 0) (sourceB2311 + difference 0 2) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4065) := by
    have ha : (tripleCharges (sourceA2311 + difference 2 0) (sourceB2311 + difference 0 2) sourceC2311) = raw23782 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw23782; decide +kernel
    rw [ha]
    exact (canonical23782 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2311 + difference 2 1) (sourceB2311 + difference 1 2) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (tripleCharges (sourceA2311 + difference 2 1) (sourceB2311 + difference 1 2) sourceC2311) = raw31877 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw31877; decide +kernel
    rw [ha]
    exact (canonical31877 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2311 + difference 2 3) (sourceB2311 + difference 3 2) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4078) := by
    have ha : (tripleCharges (sourceA2311 + difference 2 3) (sourceB2311 + difference 3 2) sourceC2311) = raw31878 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw31878; decide +kernel
    rw [ha]
    exact (canonical31878 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2311 + difference 2 4) (sourceB2311 + difference 4 2) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2311 + difference 2 4) (sourceB2311 + difference 4 2) sourceC2311) = raw11535 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw11535; decide +kernel
    rw [ha]
    exact (canonical11535 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2311 + difference 2 5) (sourceB2311 + difference 5 2) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2311 + difference 2 5) (sourceB2311 + difference 5 2) sourceC2311) = raw31879 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw31879; decide +kernel
    rw [ha]
    exact (canonical31879 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2311 + difference 3 0) (sourceB2311 + difference 0 3) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4065) := by
    have ha : (tripleCharges (sourceA2311 + difference 3 0) (sourceB2311 + difference 0 3) sourceC2311) = raw23786 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw23786; decide +kernel
    rw [ha]
    exact (canonical23786 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2311 + difference 3 1) (sourceB2311 + difference 1 3) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4075) := by
    have ha : (tripleCharges (sourceA2311 + difference 3 1) (sourceB2311 + difference 1 3) sourceC2311) = raw31880 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw31880; decide +kernel
    rw [ha]
    exact (canonical31880 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2311 + difference 3 2) (sourceB2311 + difference 2 3) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4078) := by
    have ha : (tripleCharges (sourceA2311 + difference 3 2) (sourceB2311 + difference 2 3) sourceC2311) = raw31881 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw31881; decide +kernel
    rw [ha]
    exact (canonical31881 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2311 + difference 3 4) (sourceB2311 + difference 4 3) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2311 + difference 3 4) (sourceB2311 + difference 4 3) sourceC2311) = raw11538 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw11538; decide +kernel
    rw [ha]
    exact (canonical11538 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2311 + difference 3 5) (sourceB2311 + difference 5 3) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2311 + difference 3 5) (sourceB2311 + difference 5 3) sourceC2311) = raw14374 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw14374; decide +kernel
    rw [ha]
    exact (canonical14374 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2311 + difference 4 0) (sourceB2311 + difference 0 4) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (tripleCharges (sourceA2311 + difference 4 0) (sourceB2311 + difference 0 4) sourceC2311) = raw23789 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw23789; decide +kernel
    rw [ha]
    exact (canonical23789 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2311 + difference 4 1) (sourceB2311 + difference 1 4) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4076) := by
    have ha : (tripleCharges (sourceA2311 + difference 4 1) (sourceB2311 + difference 1 4) sourceC2311) = raw31882 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw31882; decide +kernel
    rw [ha]
    exact (canonical31882 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2311 + difference 4 2) (sourceB2311 + difference 2 4) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (tripleCharges (sourceA2311 + difference 4 2) (sourceB2311 + difference 2 4) sourceC2311) = raw31883 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw31883; decide +kernel
    rw [ha]
    exact (canonical31883 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2311 + difference 4 3) (sourceB2311 + difference 3 4) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (tripleCharges (sourceA2311 + difference 4 3) (sourceB2311 + difference 3 4) sourceC2311) = raw31884 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw31884; decide +kernel
    rw [ha]
    exact (canonical31884 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2311 + difference 4 5) (sourceB2311 + difference 5 4) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA2311 + difference 4 5) (sourceB2311 + difference 5 4) sourceC2311) = raw31885 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw31885; decide +kernel
    rw [ha]
    exact (canonical31885 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2311 + difference 5 0) (sourceB2311 + difference 0 5) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (tripleCharges (sourceA2311 + difference 5 0) (sourceB2311 + difference 0 5) sourceC2311) = raw22311 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw22311; decide +kernel
    rw [ha]
    exact (canonical22311 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2311 + difference 5 1) (sourceB2311 + difference 1 5) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4076) := by
    have ha : (tripleCharges (sourceA2311 + difference 5 1) (sourceB2311 + difference 1 5) sourceC2311) = raw29299 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw29299; decide +kernel
    rw [ha]
    exact (canonical29299 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2311 + difference 5 2) (sourceB2311 + difference 2 5) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (tripleCharges (sourceA2311 + difference 5 2) (sourceB2311 + difference 2 5) sourceC2311) = raw29300 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw29300; decide +kernel
    rw [ha]
    exact (canonical29300 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2311 + difference 5 3) (sourceB2311 + difference 3 5) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (tripleCharges (sourceA2311 + difference 5 3) (sourceB2311 + difference 3 5) sourceC2311) = raw29301 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw29301; decide +kernel
    rw [ha]
    exact (canonical29301 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2311 + difference 5 4) (sourceB2311 + difference 4 5) sourceC2311) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA2311 + difference 5 4) (sourceB2311 + difference 4 5) sourceC2311) = raw5210 := by
      apply Matrix.ext; unfold tripleCharges sourceA2311 sourceB2311 sourceC2311 difference raw5210; decide +kernel
    rw [ha]
    exact (canonical5210 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2311 sourceB2311 sourceC2311
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2311, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2312 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2312 : Charge := ![0, 1, 1, -1, 1, -2]
def sourceC2312 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceForm2312 : Integer.Sparse Master := [(Sum.inr 923, 1), (Sum.inr 1806, 1), (Sum.inr 2021, 1), (Sum.inr 2034, 1), (Sum.inr 2051, 1), (Sum.inr 2058, 1), (Sum.inr 4084, -1)]

theorem sourceEq2312 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2312 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2312 + difference 2 0) (sourceB2312 + difference 0 2) sourceC2312) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 923) := by
    have ha : (tripleCharges (sourceA2312 + difference 2 0) (sourceB2312 + difference 0 2) sourceC2312) = raw23805 := by
      apply Matrix.ext; unfold tripleCharges sourceA2312 sourceB2312 sourceC2312 difference raw23805; decide +kernel
    rw [ha]
    exact (canonical23805 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2312 + difference 2 1) (sourceB2312 + difference 1 2) sourceC2312) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1806) := by
    have ha : (tripleCharges (sourceA2312 + difference 2 1) (sourceB2312 + difference 1 2) sourceC2312) = raw31886 := by
      apply Matrix.ext; unfold tripleCharges sourceA2312 sourceB2312 sourceC2312 difference raw31886; decide +kernel
    rw [ha]
    exact (canonical31886 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2312 + difference 2 2) (sourceB2312 + difference 2 2) sourceC2312) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2021) := by
    have ha : (tripleCharges (sourceA2312 + difference 2 2) (sourceB2312 + difference 2 2) sourceC2312) = raw31378 := by
      apply Matrix.ext; unfold tripleCharges sourceA2312 sourceB2312 sourceC2312 difference raw31378; decide +kernel
    rw [ha]
    exact (canonical31378 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2312 + difference 2 3) (sourceB2312 + difference 3 2) sourceC2312) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2058) := by
    have ha : (tripleCharges (sourceA2312 + difference 2 3) (sourceB2312 + difference 3 2) sourceC2312) = raw31374 := by
      apply Matrix.ext; unfold tripleCharges sourceA2312 sourceB2312 sourceC2312 difference raw31374; decide +kernel
    rw [ha]
    exact (canonical31374 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2312 + difference 2 4) (sourceB2312 + difference 4 2) sourceC2312) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2034) := by
    have ha : (tripleCharges (sourceA2312 + difference 2 4) (sourceB2312 + difference 4 2) sourceC2312) = raw31887 := by
      apply Matrix.ext; unfold tripleCharges sourceA2312 sourceB2312 sourceC2312 difference raw31887; decide +kernel
    rw [ha]
    exact (canonical31887 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2312 + difference 2 5) (sourceB2312 + difference 5 2) sourceC2312) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2051) := by
    have ha : (tripleCharges (sourceA2312 + difference 2 5) (sourceB2312 + difference 5 2) sourceC2312) = raw31888 := by
      apply Matrix.ext; unfold tripleCharges sourceA2312 sourceB2312 sourceC2312 difference raw31888; decide +kernel
    rw [ha]
    exact (canonical31888 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2312 + sourceB2312) sourceC2312) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2312 + sourceB2312) sourceC2312) = raw23810 := by
      apply Matrix.ext; unfold doubleCharges sourceA2312 sourceB2312 sourceC2312 raw23810; decide +kernel
    rw [ha]
    exact (canonical23810 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2312 sourceB2312 sourceC2312
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2312, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2313 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2313 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceC2313 : Charge := ![0, 1, 1, -1, 1, -2]
def sourceForm2313 : Integer.Sparse Master := [(Sum.inr 2440, 1), (Sum.inr 3062, 1), (Sum.inr 3189, 1), (Sum.inr 3202, 2), (Sum.inr 3789, 1), (Sum.inr 4091, -1)]

theorem sourceEq2313 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2313 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2313 + difference 0 2) (sourceB2313 + difference 2 0) sourceC2313) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3789) := by
    have ha : (tripleCharges (sourceA2313 + difference 0 2) (sourceB2313 + difference 2 0) sourceC2313) = raw31889 := by
      apply Matrix.ext; unfold tripleCharges sourceA2313 sourceB2313 sourceC2313 difference raw31889; decide +kernel
    rw [ha]
    exact (canonical31889 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2313 + difference 1 2) (sourceB2313 + difference 2 1) sourceC2313) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3202) := by
    have ha : (tripleCharges (sourceA2313 + difference 1 2) (sourceB2313 + difference 2 1) sourceC2313) = raw31890 := by
      apply Matrix.ext; unfold tripleCharges sourceA2313 sourceB2313 sourceC2313 difference raw31890; decide +kernel
    rw [ha]
    exact (canonical31890 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2313 + difference 2 2) (sourceB2313 + difference 2 2) sourceC2313) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3202) := by
    have ha : (tripleCharges (sourceA2313 + difference 2 2) (sourceB2313 + difference 2 2) sourceC2313) = raw31891 := by
      apply Matrix.ext; unfold tripleCharges sourceA2313 sourceB2313 sourceC2313 difference raw31891; decide +kernel
    rw [ha]
    exact (canonical31891 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2313 + difference 3 2) (sourceB2313 + difference 2 3) sourceC2313) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3189) := by
    have ha : (tripleCharges (sourceA2313 + difference 3 2) (sourceB2313 + difference 2 3) sourceC2313) = raw31892 := by
      apply Matrix.ext; unfold tripleCharges sourceA2313 sourceB2313 sourceC2313 difference raw31892; decide +kernel
    rw [ha]
    exact (canonical31892 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2313 + difference 4 2) (sourceB2313 + difference 2 4) sourceC2313) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3062) := by
    have ha : (tripleCharges (sourceA2313 + difference 4 2) (sourceB2313 + difference 2 4) sourceC2313) = raw31893 := by
      apply Matrix.ext; unfold tripleCharges sourceA2313 sourceB2313 sourceC2313 difference raw31893; decide +kernel
    rw [ha]
    exact (canonical31893 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2313 + difference 5 2) (sourceB2313 + difference 2 5) sourceC2313) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2440) := by
    have ha : (tripleCharges (sourceA2313 + difference 5 2) (sourceB2313 + difference 2 5) sourceC2313) = raw31894 := by
      apply Matrix.ext; unfold tripleCharges sourceA2313 sourceB2313 sourceC2313 difference raw31894; decide +kernel
    rw [ha]
    exact (canonical31894 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2313 + sourceB2313) sourceC2313) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2313 + sourceB2313) sourceC2313) = raw31895 := by
      apply Matrix.ext; unfold doubleCharges sourceA2313 sourceB2313 sourceC2313 raw31895; decide +kernel
    rw [ha]
    exact (canonical31895 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2313 sourceB2313 sourceC2313
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2313, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2314 : Charge := ![0, 1, 1, -1, 1, -2]
def sourceB2314 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceC2314 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceForm2314 : Integer.Sparse Master := [(Sum.inr 2195, 1), (Sum.inr 2500, 1), (Sum.inr 3463, 1), (Sum.inr 3560, 1), (Sum.inr 3605, 1), (Sum.inr 3606, 1), (Sum.inr 4080, -1)]

theorem sourceEq2314 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2314 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2314 + difference 0 0) (sourceB2314 + difference 0 0) sourceC2314) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA2314 + difference 0 0) (sourceB2314 + difference 0 0) sourceC2314) = raw31896 := by
      apply Matrix.ext; unfold tripleCharges sourceA2314 sourceB2314 sourceC2314 difference raw31896; decide +kernel
    rw [ha]
    exact (canonical31896 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2314 + difference 0 1) (sourceB2314 + difference 1 0) sourceC2314) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3463) := by
    have ha : (tripleCharges (sourceA2314 + difference 0 1) (sourceB2314 + difference 1 0) sourceC2314) = raw31897 := by
      apply Matrix.ext; unfold tripleCharges sourceA2314 sourceB2314 sourceC2314 difference raw31897; decide +kernel
    rw [ha]
    exact (canonical31897 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2314 + difference 0 2) (sourceB2314 + difference 2 0) sourceC2314) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3606) := by
    have ha : (tripleCharges (sourceA2314 + difference 0 2) (sourceB2314 + difference 2 0) sourceC2314) = raw31898 := by
      apply Matrix.ext; unfold tripleCharges sourceA2314 sourceB2314 sourceC2314 difference raw31898; decide +kernel
    rw [ha]
    exact (canonical31898 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2314 + difference 0 3) (sourceB2314 + difference 3 0) sourceC2314) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3560) := by
    have ha : (tripleCharges (sourceA2314 + difference 0 3) (sourceB2314 + difference 3 0) sourceC2314) = raw31899 := by
      apply Matrix.ext; unfold tripleCharges sourceA2314 sourceB2314 sourceC2314 difference raw31899; decide +kernel
    rw [ha]
    exact (canonical31899 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2314 + difference 0 4) (sourceB2314 + difference 4 0) sourceC2314) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3605) := by
    have ha : (tripleCharges (sourceA2314 + difference 0 4) (sourceB2314 + difference 4 0) sourceC2314) = raw31900 := by
      apply Matrix.ext; unfold tripleCharges sourceA2314 sourceB2314 sourceC2314 difference raw31900; decide +kernel
    rw [ha]
    exact (canonical31900 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2314 + difference 0 5) (sourceB2314 + difference 5 0) sourceC2314) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2500) := by
    have ha : (tripleCharges (sourceA2314 + difference 0 5) (sourceB2314 + difference 5 0) sourceC2314) = raw31901 := by
      apply Matrix.ext; unfold tripleCharges sourceA2314 sourceB2314 sourceC2314 difference raw31901; decide +kernel
    rw [ha]
    exact (canonical31901 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2314 + sourceB2314) sourceC2314) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2314 + sourceB2314) sourceC2314) = raw31902 := by
      apply Matrix.ext; unfold doubleCharges sourceA2314 sourceB2314 sourceC2314 raw31902; decide +kernel
    rw [ha]
    exact (canonical31902 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2314 sourceB2314 sourceC2314
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2314, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2315 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2315 : Charge := ![0, 1, 2, -1, -1, -1]
def sourceC2315 : Charge := ![3, 0, -2, 0, 0, -1]
def sourceForm2315 : Integer.Sparse Master := [(Sum.inr 920, 1), (Sum.inr 1803, 1), (Sum.inr 2033, 1), (Sum.inr 2051, 1), (Sum.inr 2054, 2), (Sum.inr 4084, -1)]

theorem sourceEq2315 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2315 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2315 + difference 2 0) (sourceB2315 + difference 0 2) sourceC2315) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 920) := by
    have ha : (tripleCharges (sourceA2315 + difference 2 0) (sourceB2315 + difference 0 2) sourceC2315) = raw23833 := by
      apply Matrix.ext; unfold tripleCharges sourceA2315 sourceB2315 sourceC2315 difference raw23833; decide +kernel
    rw [ha]
    exact (canonical23833 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2315 + difference 2 1) (sourceB2315 + difference 1 2) sourceC2315) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1803) := by
    have ha : (tripleCharges (sourceA2315 + difference 2 1) (sourceB2315 + difference 1 2) sourceC2315) = raw31903 := by
      apply Matrix.ext; unfold tripleCharges sourceA2315 sourceB2315 sourceC2315 difference raw31903; decide +kernel
    rw [ha]
    exact (canonical31903 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2315 + difference 2 2) (sourceB2315 + difference 2 2) sourceC2315) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2033) := by
    have ha : (tripleCharges (sourceA2315 + difference 2 2) (sourceB2315 + difference 2 2) sourceC2315) = raw31904 := by
      apply Matrix.ext; unfold tripleCharges sourceA2315 sourceB2315 sourceC2315 difference raw31904; decide +kernel
    rw [ha]
    exact (canonical31904 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2315 + difference 2 3) (sourceB2315 + difference 3 2) sourceC2315) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2054) := by
    have ha : (tripleCharges (sourceA2315 + difference 2 3) (sourceB2315 + difference 3 2) sourceC2315) = raw31905 := by
      apply Matrix.ext; unfold tripleCharges sourceA2315 sourceB2315 sourceC2315 difference raw31905; decide +kernel
    rw [ha]
    exact (canonical31905 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2315 + difference 2 4) (sourceB2315 + difference 4 2) sourceC2315) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2054) := by
    have ha : (tripleCharges (sourceA2315 + difference 2 4) (sourceB2315 + difference 4 2) sourceC2315) = raw31906 := by
      apply Matrix.ext; unfold tripleCharges sourceA2315 sourceB2315 sourceC2315 difference raw31906; decide +kernel
    rw [ha]
    exact (canonical31906 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2315 + difference 2 5) (sourceB2315 + difference 5 2) sourceC2315) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2051) := by
    have ha : (tripleCharges (sourceA2315 + difference 2 5) (sourceB2315 + difference 5 2) sourceC2315) = raw31907 := by
      apply Matrix.ext; unfold tripleCharges sourceA2315 sourceB2315 sourceC2315 difference raw31907; decide +kernel
    rw [ha]
    exact (canonical31907 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2315 + sourceB2315) sourceC2315) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2315 + sourceB2315) sourceC2315) = raw23838 := by
      apply Matrix.ext; unfold doubleCharges sourceA2315 sourceB2315 sourceC2315 raw23838; decide +kernel
    rw [ha]
    exact (canonical23838 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2315 sourceB2315 sourceC2315
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2315, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2316 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2316 : Charge := ![3, 0, -2, 0, 0, -1]
def sourceC2316 : Charge := ![0, 1, 2, -1, -1, -1]
def sourceForm2316 : Integer.Sparse Master := [(Sum.inr 2895, 1), (Sum.inr 3164, 2), (Sum.inr 3172, 1), (Sum.inr 3197, 1), (Sum.inr 3964, 1), (Sum.inr 4091, -1)]

theorem sourceEq2316 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2316 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2316 + difference 0 2) (sourceB2316 + difference 2 0) sourceC2316) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3964) := by
    have ha : (tripleCharges (sourceA2316 + difference 0 2) (sourceB2316 + difference 2 0) sourceC2316) = raw31908 := by
      apply Matrix.ext; unfold tripleCharges sourceA2316 sourceB2316 sourceC2316 difference raw31908; decide +kernel
    rw [ha]
    exact (canonical31908 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2316 + difference 1 2) (sourceB2316 + difference 2 1) sourceC2316) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3172) := by
    have ha : (tripleCharges (sourceA2316 + difference 1 2) (sourceB2316 + difference 2 1) sourceC2316) = raw31909 := by
      apply Matrix.ext; unfold tripleCharges sourceA2316 sourceB2316 sourceC2316 difference raw31909; decide +kernel
    rw [ha]
    exact (canonical31909 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2316 + difference 2 2) (sourceB2316 + difference 2 2) sourceC2316) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3197) := by
    have ha : (tripleCharges (sourceA2316 + difference 2 2) (sourceB2316 + difference 2 2) sourceC2316) = raw31910 := by
      apply Matrix.ext; unfold tripleCharges sourceA2316 sourceB2316 sourceC2316 difference raw31910; decide +kernel
    rw [ha]
    exact (canonical31910 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2316 + difference 3 2) (sourceB2316 + difference 2 3) sourceC2316) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3164) := by
    have ha : (tripleCharges (sourceA2316 + difference 3 2) (sourceB2316 + difference 2 3) sourceC2316) = raw31911 := by
      apply Matrix.ext; unfold tripleCharges sourceA2316 sourceB2316 sourceC2316 difference raw31911; decide +kernel
    rw [ha]
    exact (canonical31911 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2316 + difference 4 2) (sourceB2316 + difference 2 4) sourceC2316) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3164) := by
    have ha : (tripleCharges (sourceA2316 + difference 4 2) (sourceB2316 + difference 2 4) sourceC2316) = raw31912 := by
      apply Matrix.ext; unfold tripleCharges sourceA2316 sourceB2316 sourceC2316 difference raw31912; decide +kernel
    rw [ha]
    exact (canonical31912 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2316 + difference 5 2) (sourceB2316 + difference 2 5) sourceC2316) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2895) := by
    have ha : (tripleCharges (sourceA2316 + difference 5 2) (sourceB2316 + difference 2 5) sourceC2316) = raw31913 := by
      apply Matrix.ext; unfold tripleCharges sourceA2316 sourceB2316 sourceC2316 difference raw31913; decide +kernel
    rw [ha]
    exact (canonical31913 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2316 + sourceB2316) sourceC2316) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2316 + sourceB2316) sourceC2316) = raw31914 := by
      apply Matrix.ext; unfold doubleCharges sourceA2316 sourceB2316 sourceC2316 raw31914; decide +kernel
    rw [ha]
    exact (canonical31914 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2316 sourceB2316 sourceC2316
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2316, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2317 : Charge := ![0, 1, 2, -1, -1, -1]
def sourceB2317 : Charge := ![3, 0, -2, 0, 0, -1]
def sourceC2317 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceForm2317 : Integer.Sparse Master := [(Sum.inr 2192, 1), (Sum.inr 3461, 1), (Sum.inr 3559, 2), (Sum.inr 3600, 1), (Sum.inr 3601, 1), (Sum.inr 4080, -1)]

theorem sourceEq2317 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2317 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2317 + difference 0 0) (sourceB2317 + difference 0 0) sourceC2317) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2192) := by
    have ha : (tripleCharges (sourceA2317 + difference 0 0) (sourceB2317 + difference 0 0) sourceC2317) = raw31915 := by
      apply Matrix.ext; unfold tripleCharges sourceA2317 sourceB2317 sourceC2317 difference raw31915; decide +kernel
    rw [ha]
    exact (canonical31915 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2317 + difference 0 1) (sourceB2317 + difference 1 0) sourceC2317) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3461) := by
    have ha : (tripleCharges (sourceA2317 + difference 0 1) (sourceB2317 + difference 1 0) sourceC2317) = raw31916 := by
      apply Matrix.ext; unfold tripleCharges sourceA2317 sourceB2317 sourceC2317 difference raw31916; decide +kernel
    rw [ha]
    exact (canonical31916 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2317 + difference 0 2) (sourceB2317 + difference 2 0) sourceC2317) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3601) := by
    have ha : (tripleCharges (sourceA2317 + difference 0 2) (sourceB2317 + difference 2 0) sourceC2317) = raw31917 := by
      apply Matrix.ext; unfold tripleCharges sourceA2317 sourceB2317 sourceC2317 difference raw31917; decide +kernel
    rw [ha]
    exact (canonical31917 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2317 + difference 0 3) (sourceB2317 + difference 3 0) sourceC2317) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3559) := by
    have ha : (tripleCharges (sourceA2317 + difference 0 3) (sourceB2317 + difference 3 0) sourceC2317) = raw31918 := by
      apply Matrix.ext; unfold tripleCharges sourceA2317 sourceB2317 sourceC2317 difference raw31918; decide +kernel
    rw [ha]
    exact (canonical31918 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2317 + difference 0 4) (sourceB2317 + difference 4 0) sourceC2317) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3559) := by
    have ha : (tripleCharges (sourceA2317 + difference 0 4) (sourceB2317 + difference 4 0) sourceC2317) = raw31919 := by
      apply Matrix.ext; unfold tripleCharges sourceA2317 sourceB2317 sourceC2317 difference raw31919; decide +kernel
    rw [ha]
    exact (canonical31919 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2317 + difference 0 5) (sourceB2317 + difference 5 0) sourceC2317) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3600) := by
    have ha : (tripleCharges (sourceA2317 + difference 0 5) (sourceB2317 + difference 5 0) sourceC2317) = raw31920 := by
      apply Matrix.ext; unfold tripleCharges sourceA2317 sourceB2317 sourceC2317 difference raw31920; decide +kernel
    rw [ha]
    exact (canonical31920 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2317 + sourceB2317) sourceC2317) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2317 + sourceB2317) sourceC2317) = raw31902 := by
      apply Matrix.ext; unfold doubleCharges sourceA2317 sourceB2317 sourceC2317 raw31902; decide +kernel
    rw [ha]
    exact (canonical31902 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2317 sourceB2317 sourceC2317
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2317, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2318 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2318 : Charge := ![3, 0, -2, 0, -1, 0]
def sourceC2318 : Charge := ![0, 1, 2, -1, 0, -2]
def sourceForm2318 : Integer.Sparse Master := [(Sum.inr 2430, 1), (Sum.inr 3162, 1), (Sum.inr 3163, 1), (Sum.inr 3170, 1), (Sum.inr 3196, 1), (Sum.inr 3782, 1), (Sum.inr 4092, -1)]

theorem sourceEq2318 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2318 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2318 + difference 0 2) (sourceB2318 + difference 2 0) sourceC2318) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3782) := by
    have ha : (tripleCharges (sourceA2318 + difference 0 2) (sourceB2318 + difference 2 0) sourceC2318) = raw31921 := by
      apply Matrix.ext; unfold tripleCharges sourceA2318 sourceB2318 sourceC2318 difference raw31921; decide +kernel
    rw [ha]
    exact (canonical31921 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2318 + difference 1 2) (sourceB2318 + difference 2 1) sourceC2318) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3170) := by
    have ha : (tripleCharges (sourceA2318 + difference 1 2) (sourceB2318 + difference 2 1) sourceC2318) = raw31922 := by
      apply Matrix.ext; unfold tripleCharges sourceA2318 sourceB2318 sourceC2318 difference raw31922; decide +kernel
    rw [ha]
    exact (canonical31922 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2318 + difference 2 2) (sourceB2318 + difference 2 2) sourceC2318) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3196) := by
    have ha : (tripleCharges (sourceA2318 + difference 2 2) (sourceB2318 + difference 2 2) sourceC2318) = raw31923 := by
      apply Matrix.ext; unfold tripleCharges sourceA2318 sourceB2318 sourceC2318 difference raw31923; decide +kernel
    rw [ha]
    exact (canonical31923 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2318 + difference 3 2) (sourceB2318 + difference 2 3) sourceC2318) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3162) := by
    have ha : (tripleCharges (sourceA2318 + difference 3 2) (sourceB2318 + difference 2 3) sourceC2318) = raw31924 := by
      apply Matrix.ext; unfold tripleCharges sourceA2318 sourceB2318 sourceC2318 difference raw31924; decide +kernel
    rw [ha]
    exact (canonical31924 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2318 + difference 4 2) (sourceB2318 + difference 2 4) sourceC2318) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3163) := by
    have ha : (tripleCharges (sourceA2318 + difference 4 2) (sourceB2318 + difference 2 4) sourceC2318) = raw31925 := by
      apply Matrix.ext; unfold tripleCharges sourceA2318 sourceB2318 sourceC2318 difference raw31925; decide +kernel
    rw [ha]
    exact (canonical31925 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2318 + difference 5 2) (sourceB2318 + difference 2 5) sourceC2318) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2430) := by
    have ha : (tripleCharges (sourceA2318 + difference 5 2) (sourceB2318 + difference 2 5) sourceC2318) = raw31926 := by
      apply Matrix.ext; unfold tripleCharges sourceA2318 sourceB2318 sourceC2318 difference raw31926; decide +kernel
    rw [ha]
    exact (canonical31926 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2318 + sourceB2318) sourceC2318) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2318 + sourceB2318) sourceC2318) = raw31927 := by
      apply Matrix.ext; unfold doubleCharges sourceA2318 sourceB2318 sourceC2318 raw31927; decide +kernel
    rw [ha]
    exact (canonical31927 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2318 sourceB2318 sourceC2318
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2318, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2319 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2319 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceC2319 : Charge := ![0, 2, 0, -1, 1, -2]
def sourceForm2319 : Integer.Sparse Master := [(Sum.inr 2443, 1), (Sum.inr 3033, 1), (Sum.inr 3136, 1), (Sum.inr 3138, 1), (Sum.inr 3180, 1), (Sum.inr 3732, 1), (Sum.inr 4092, -1)]

theorem sourceEq2319 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2319 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2319 + difference 0 1) (sourceB2319 + difference 1 0) sourceC2319) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3732) := by
    have ha : (tripleCharges (sourceA2319 + difference 0 1) (sourceB2319 + difference 1 0) sourceC2319) = raw31928 := by
      apply Matrix.ext; unfold tripleCharges sourceA2319 sourceB2319 sourceC2319 difference raw31928; decide +kernel
    rw [ha]
    exact (canonical31928 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2319 + difference 1 1) (sourceB2319 + difference 1 1) sourceC2319) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3180) := by
    have ha : (tripleCharges (sourceA2319 + difference 1 1) (sourceB2319 + difference 1 1) sourceC2319) = raw31929 := by
      apply Matrix.ext; unfold tripleCharges sourceA2319 sourceB2319 sourceC2319 difference raw31929; decide +kernel
    rw [ha]
    exact (canonical31929 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2319 + difference 2 1) (sourceB2319 + difference 1 2) sourceC2319) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3136) := by
    have ha : (tripleCharges (sourceA2319 + difference 2 1) (sourceB2319 + difference 1 2) sourceC2319) = raw31930 := by
      apply Matrix.ext; unfold tripleCharges sourceA2319 sourceB2319 sourceC2319 difference raw31930; decide +kernel
    rw [ha]
    exact (canonical31930 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2319 + difference 3 1) (sourceB2319 + difference 1 3) sourceC2319) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3138) := by
    have ha : (tripleCharges (sourceA2319 + difference 3 1) (sourceB2319 + difference 1 3) sourceC2319) = raw31931 := by
      apply Matrix.ext; unfold tripleCharges sourceA2319 sourceB2319 sourceC2319 difference raw31931; decide +kernel
    rw [ha]
    exact (canonical31931 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2319 + difference 4 1) (sourceB2319 + difference 1 4) sourceC2319) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3033) := by
    have ha : (tripleCharges (sourceA2319 + difference 4 1) (sourceB2319 + difference 1 4) sourceC2319) = raw31932 := by
      apply Matrix.ext; unfold tripleCharges sourceA2319 sourceB2319 sourceC2319 difference raw31932; decide +kernel
    rw [ha]
    exact (canonical31932 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2319 + difference 5 1) (sourceB2319 + difference 1 5) sourceC2319) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2443) := by
    have ha : (tripleCharges (sourceA2319 + difference 5 1) (sourceB2319 + difference 1 5) sourceC2319) = raw31933 := by
      apply Matrix.ext; unfold tripleCharges sourceA2319 sourceB2319 sourceC2319 difference raw31933; decide +kernel
    rw [ha]
    exact (canonical31933 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2319 + sourceB2319) sourceC2319) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2319 + sourceB2319) sourceC2319) = raw31934 := by
      apply Matrix.ext; unfold doubleCharges sourceA2319 sourceB2319 sourceC2319 raw31934; decide +kernel
    rw [ha]
    exact (canonical31934 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2319 sourceB2319 sourceC2319
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2319, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2320 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2320 : Charge := ![0, 2, 1, -1, -1, -1]
def sourceC2320 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceForm2320 : Integer.Sparse Master := [(Sum.inr 942, 1), (Sum.inr 1822, 1), (Sum.inr 2088, 1), (Sum.inr 2105, 1), (Sum.inr 2107, 2), (Sum.inr 4083, -1)]

theorem sourceEq2320 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2320 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2320 + difference 2 0) (sourceB2320 + difference 0 2) sourceC2320) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 942) := by
    have ha : (tripleCharges (sourceA2320 + difference 2 0) (sourceB2320 + difference 0 2) sourceC2320) = raw31935 := by
      apply Matrix.ext; unfold tripleCharges sourceA2320 sourceB2320 sourceC2320 difference raw31935; decide +kernel
    rw [ha]
    exact (canonical31935 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2320 + difference 2 1) (sourceB2320 + difference 1 2) sourceC2320) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1822) := by
    have ha : (tripleCharges (sourceA2320 + difference 2 1) (sourceB2320 + difference 1 2) sourceC2320) = raw31936 := by
      apply Matrix.ext; unfold tripleCharges sourceA2320 sourceB2320 sourceC2320 difference raw31936; decide +kernel
    rw [ha]
    exact (canonical31936 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2320 + difference 2 2) (sourceB2320 + difference 2 2) sourceC2320) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2088) := by
    have ha : (tripleCharges (sourceA2320 + difference 2 2) (sourceB2320 + difference 2 2) sourceC2320) = raw11309 := by
      apply Matrix.ext; unfold tripleCharges sourceA2320 sourceB2320 sourceC2320 difference raw11309; decide +kernel
    rw [ha]
    exact (canonical11309 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2320 + difference 2 3) (sourceB2320 + difference 3 2) sourceC2320) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA2320 + difference 2 3) (sourceB2320 + difference 3 2) sourceC2320) = raw11308 := by
      apply Matrix.ext; unfold tripleCharges sourceA2320 sourceB2320 sourceC2320 difference raw11308; decide +kernel
    rw [ha]
    exact (canonical11308 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2320 + difference 2 4) (sourceB2320 + difference 4 2) sourceC2320) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA2320 + difference 2 4) (sourceB2320 + difference 4 2) sourceC2320) = raw31937 := by
      apply Matrix.ext; unfold tripleCharges sourceA2320 sourceB2320 sourceC2320 difference raw31937; decide +kernel
    rw [ha]
    exact (canonical31937 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2320 + difference 2 5) (sourceB2320 + difference 5 2) sourceC2320) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2105) := by
    have ha : (tripleCharges (sourceA2320 + difference 2 5) (sourceB2320 + difference 5 2) sourceC2320) = raw31938 := by
      apply Matrix.ext; unfold tripleCharges sourceA2320 sourceB2320 sourceC2320 difference raw31938; decide +kernel
    rw [ha]
    exact (canonical31938 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2320 + sourceB2320) sourceC2320) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA2320 + sourceB2320) sourceC2320) = raw11298 := by
      apply Matrix.ext; unfold doubleCharges sourceA2320 sourceB2320 sourceC2320 raw11298; decide +kernel
    rw [ha]
    exact (canonical11298 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2320 sourceB2320 sourceC2320
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2320, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2321 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2321 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceC2321 : Charge := ![0, 2, 1, -1, -1, -1]
def sourceForm2321 : Integer.Sparse Master := [(Sum.inr 2890, 1), (Sum.inr 3135, 2), (Sum.inr 3137, 1), (Sum.inr 3172, 1), (Sum.inr 3721, 1), (Sum.inr 4091, -1)]

theorem sourceEq2321 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2321 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2321 + difference 0 1) (sourceB2321 + difference 1 0) sourceC2321) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3721) := by
    have ha : (tripleCharges (sourceA2321 + difference 0 1) (sourceB2321 + difference 1 0) sourceC2321) = raw31939 := by
      apply Matrix.ext; unfold tripleCharges sourceA2321 sourceB2321 sourceC2321 difference raw31939; decide +kernel
    rw [ha]
    exact (canonical31939 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2321 + difference 1 1) (sourceB2321 + difference 1 1) sourceC2321) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3172) := by
    have ha : (tripleCharges (sourceA2321 + difference 1 1) (sourceB2321 + difference 1 1) sourceC2321) = raw31940 := by
      apply Matrix.ext; unfold tripleCharges sourceA2321 sourceB2321 sourceC2321 difference raw31940; decide +kernel
    rw [ha]
    exact (canonical31940 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2321 + difference 2 1) (sourceB2321 + difference 1 2) sourceC2321) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3137) := by
    have ha : (tripleCharges (sourceA2321 + difference 2 1) (sourceB2321 + difference 1 2) sourceC2321) = raw31941 := by
      apply Matrix.ext; unfold tripleCharges sourceA2321 sourceB2321 sourceC2321 difference raw31941; decide +kernel
    rw [ha]
    exact (canonical31941 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2321 + difference 3 1) (sourceB2321 + difference 1 3) sourceC2321) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3135) := by
    have ha : (tripleCharges (sourceA2321 + difference 3 1) (sourceB2321 + difference 1 3) sourceC2321) = raw31942 := by
      apply Matrix.ext; unfold tripleCharges sourceA2321 sourceB2321 sourceC2321 difference raw31942; decide +kernel
    rw [ha]
    exact (canonical31942 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2321 + difference 4 1) (sourceB2321 + difference 1 4) sourceC2321) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3135) := by
    have ha : (tripleCharges (sourceA2321 + difference 4 1) (sourceB2321 + difference 1 4) sourceC2321) = raw31943 := by
      apply Matrix.ext; unfold tripleCharges sourceA2321 sourceB2321 sourceC2321 difference raw31943; decide +kernel
    rw [ha]
    exact (canonical31943 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2321 + difference 5 1) (sourceB2321 + difference 1 5) sourceC2321) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2890) := by
    have ha : (tripleCharges (sourceA2321 + difference 5 1) (sourceB2321 + difference 1 5) sourceC2321) = raw31944 := by
      apply Matrix.ext; unfold tripleCharges sourceA2321 sourceB2321 sourceC2321 difference raw31944; decide +kernel
    rw [ha]
    exact (canonical31944 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2321 + sourceB2321) sourceC2321) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2321 + sourceB2321) sourceC2321) = raw31945 := by
      apply Matrix.ext; unfold doubleCharges sourceA2321 sourceB2321 sourceC2321 raw31945; decide +kernel
    rw [ha]
    exact (canonical31945 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2321 sourceB2321 sourceC2321
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2321, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2322 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2322 : Charge := ![0, 2, 1, -1, 0, -2]
def sourceC2322 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceForm2322 : Integer.Sparse Master := [(Sum.inr 944, 1), (Sum.inr 1824, 1), (Sum.inr 2089, 2), (Sum.inr 2105, 1), (Sum.inr 2110, 1), (Sum.inr 4083, -1)]

theorem sourceEq2322 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2322 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2322 + difference 2 0) (sourceB2322 + difference 0 2) sourceC2322) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 944) := by
    have ha : (tripleCharges (sourceA2322 + difference 2 0) (sourceB2322 + difference 0 2) sourceC2322) = raw31946 := by
      apply Matrix.ext; unfold tripleCharges sourceA2322 sourceB2322 sourceC2322 difference raw31946; decide +kernel
    rw [ha]
    exact (canonical31946 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2322 + difference 2 1) (sourceB2322 + difference 1 2) sourceC2322) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1824) := by
    have ha : (tripleCharges (sourceA2322 + difference 2 1) (sourceB2322 + difference 1 2) sourceC2322) = raw31947 := by
      apply Matrix.ext; unfold tripleCharges sourceA2322 sourceB2322 sourceC2322 difference raw31947; decide +kernel
    rw [ha]
    exact (canonical31947 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2322 + difference 2 2) (sourceB2322 + difference 2 2) sourceC2322) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2089) := by
    have ha : (tripleCharges (sourceA2322 + difference 2 2) (sourceB2322 + difference 2 2) sourceC2322) = raw11093 := by
      apply Matrix.ext; unfold tripleCharges sourceA2322 sourceB2322 sourceC2322 difference raw11093; decide +kernel
    rw [ha]
    exact (canonical11093 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2322 + difference 2 3) (sourceB2322 + difference 3 2) sourceC2322) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2110) := by
    have ha : (tripleCharges (sourceA2322 + difference 2 3) (sourceB2322 + difference 3 2) sourceC2322) = raw11092 := by
      apply Matrix.ext; unfold tripleCharges sourceA2322 sourceB2322 sourceC2322 difference raw11092; decide +kernel
    rw [ha]
    exact (canonical11092 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2322 + difference 2 4) (sourceB2322 + difference 4 2) sourceC2322) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2089) := by
    have ha : (tripleCharges (sourceA2322 + difference 2 4) (sourceB2322 + difference 4 2) sourceC2322) = raw31948 := by
      apply Matrix.ext; unfold tripleCharges sourceA2322 sourceB2322 sourceC2322 difference raw31948; decide +kernel
    rw [ha]
    exact (canonical31948 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2322 + difference 2 5) (sourceB2322 + difference 5 2) sourceC2322) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2105) := by
    have ha : (tripleCharges (sourceA2322 + difference 2 5) (sourceB2322 + difference 5 2) sourceC2322) = raw31949 := by
      apply Matrix.ext; unfold tripleCharges sourceA2322 sourceB2322 sourceC2322 difference raw31949; decide +kernel
    rw [ha]
    exact (canonical31949 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2322 + sourceB2322) sourceC2322) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA2322 + sourceB2322) sourceC2322) = raw11086 := by
      apply Matrix.ext; unfold doubleCharges sourceA2322 sourceB2322 sourceC2322 raw11086; decide +kernel
    rw [ha]
    exact (canonical11086 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2322 sourceB2322 sourceC2322
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2322, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2323 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2323 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceC2323 : Charge := ![0, 2, 1, -1, 0, -2]
def sourceForm2323 : Integer.Sparse Master := [(Sum.inr 2423, 1), (Sum.inr 3133, 1), (Sum.inr 3134, 1), (Sum.inr 3136, 1), (Sum.inr 3170, 1), (Sum.inr 3719, 1), (Sum.inr 4092, -1)]

theorem sourceEq2323 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2323 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2323 + difference 0 1) (sourceB2323 + difference 1 0) sourceC2323) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3719) := by
    have ha : (tripleCharges (sourceA2323 + difference 0 1) (sourceB2323 + difference 1 0) sourceC2323) = raw31950 := by
      apply Matrix.ext; unfold tripleCharges sourceA2323 sourceB2323 sourceC2323 difference raw31950; decide +kernel
    rw [ha]
    exact (canonical31950 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2323 + difference 1 1) (sourceB2323 + difference 1 1) sourceC2323) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3170) := by
    have ha : (tripleCharges (sourceA2323 + difference 1 1) (sourceB2323 + difference 1 1) sourceC2323) = raw31951 := by
      apply Matrix.ext; unfold tripleCharges sourceA2323 sourceB2323 sourceC2323 difference raw31951; decide +kernel
    rw [ha]
    exact (canonical31951 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2323 + difference 2 1) (sourceB2323 + difference 1 2) sourceC2323) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3136) := by
    have ha : (tripleCharges (sourceA2323 + difference 2 1) (sourceB2323 + difference 1 2) sourceC2323) = raw31952 := by
      apply Matrix.ext; unfold tripleCharges sourceA2323 sourceB2323 sourceC2323 difference raw31952; decide +kernel
    rw [ha]
    exact (canonical31952 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2323 + difference 3 1) (sourceB2323 + difference 1 3) sourceC2323) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3133) := by
    have ha : (tripleCharges (sourceA2323 + difference 3 1) (sourceB2323 + difference 1 3) sourceC2323) = raw31953 := by
      apply Matrix.ext; unfold tripleCharges sourceA2323 sourceB2323 sourceC2323 difference raw31953; decide +kernel
    rw [ha]
    exact (canonical31953 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2323 + difference 4 1) (sourceB2323 + difference 1 4) sourceC2323) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3134) := by
    have ha : (tripleCharges (sourceA2323 + difference 4 1) (sourceB2323 + difference 1 4) sourceC2323) = raw31954 := by
      apply Matrix.ext; unfold tripleCharges sourceA2323 sourceB2323 sourceC2323 difference raw31954; decide +kernel
    rw [ha]
    exact (canonical31954 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2323 + difference 5 1) (sourceB2323 + difference 1 5) sourceC2323) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2423) := by
    have ha : (tripleCharges (sourceA2323 + difference 5 1) (sourceB2323 + difference 1 5) sourceC2323) = raw31955 := by
      apply Matrix.ext; unfold tripleCharges sourceA2323 sourceB2323 sourceC2323 difference raw31955; decide +kernel
    rw [ha]
    exact (canonical31955 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2323 + sourceB2323) sourceC2323) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2323 + sourceB2323) sourceC2323) = raw31956 := by
      apply Matrix.ext; unfold doubleCharges sourceA2323 sourceB2323 sourceC2323 raw31956; decide +kernel
    rw [ha]
    exact (canonical31956 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2323 sourceB2323 sourceC2323
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2323, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2324 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2324 : Charge := ![3, -1, -2, 0, 0, 0]
def sourceC2324 : Charge := ![0, 2, 2, -1, -1, -2]
def sourceForm2324 : Integer.Sparse Master := [(Sum.inr 3165, 1), (Sum.inr 3713, 1), (Sum.inr 3759, 1), (Sum.inr 3762, 2), (Sum.inr 3778, 1), (Sum.inr 4088, -1)]

theorem sourceEq2324 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2324 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2324 + difference 0 0) (sourceB2324 + difference 0 0) sourceC2324) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3165) := by
    have ha : (tripleCharges (sourceA2324 + difference 0 0) (sourceB2324 + difference 0 0) sourceC2324) = raw31957 := by
      apply Matrix.ext; unfold tripleCharges sourceA2324 sourceB2324 sourceC2324 difference raw31957; decide +kernel
    rw [ha]
    exact (canonical31957 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2324 + difference 0 1) (sourceB2324 + difference 1 0) sourceC2324) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3713) := by
    have ha : (tripleCharges (sourceA2324 + difference 0 1) (sourceB2324 + difference 1 0) sourceC2324) = raw31958 := by
      apply Matrix.ext; unfold tripleCharges sourceA2324 sourceB2324 sourceC2324 difference raw31958; decide +kernel
    rw [ha]
    exact (canonical31958 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2324 + difference 0 2) (sourceB2324 + difference 2 0) sourceC2324) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3778) := by
    have ha : (tripleCharges (sourceA2324 + difference 0 2) (sourceB2324 + difference 2 0) sourceC2324) = raw31959 := by
      apply Matrix.ext; unfold tripleCharges sourceA2324 sourceB2324 sourceC2324 difference raw31959; decide +kernel
    rw [ha]
    exact (canonical31959 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2324 + difference 0 3) (sourceB2324 + difference 3 0) sourceC2324) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3762) := by
    have ha : (tripleCharges (sourceA2324 + difference 0 3) (sourceB2324 + difference 3 0) sourceC2324) = raw31960 := by
      apply Matrix.ext; unfold tripleCharges sourceA2324 sourceB2324 sourceC2324 difference raw31960; decide +kernel
    rw [ha]
    exact (canonical31960 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2324 + difference 0 4) (sourceB2324 + difference 4 0) sourceC2324) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3762) := by
    have ha : (tripleCharges (sourceA2324 + difference 0 4) (sourceB2324 + difference 4 0) sourceC2324) = raw31961 := by
      apply Matrix.ext; unfold tripleCharges sourceA2324 sourceB2324 sourceC2324 difference raw31961; decide +kernel
    rw [ha]
    exact (canonical31961 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2324 + difference 0 5) (sourceB2324 + difference 5 0) sourceC2324) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3759) := by
    have ha : (tripleCharges (sourceA2324 + difference 0 5) (sourceB2324 + difference 5 0) sourceC2324) = raw31962 := by
      apply Matrix.ext; unfold tripleCharges sourceA2324 sourceB2324 sourceC2324 difference raw31962; decide +kernel
    rw [ha]
    exact (canonical31962 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2324 + sourceB2324) sourceC2324) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2324 + sourceB2324) sourceC2324) = raw31963 := by
      apply Matrix.ext; unfold doubleCharges sourceA2324 sourceB2324 sourceC2324 raw31963; decide +kernel
    rw [ha]
    exact (canonical31963 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2324 sourceB2324 sourceC2324
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2324, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2325 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2325 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC2325 : Charge := ![0, 3, 0, -1, -1, -1]
def sourceForm2325 : Integer.Sparse Master := [(Sum.inr 2899, 1), (Sum.inr 3128, 1), (Sum.inr 3132, 2), (Sum.inr 3158, 1), (Sum.inr 3394, 1), (Sum.inr 4083, -1)]

theorem sourceEq2325 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2325 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2325 + difference 0 1) (sourceB2325 + difference 1 0) sourceC2325) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3394) := by
    have ha : (tripleCharges (sourceA2325 + difference 0 1) (sourceB2325 + difference 1 0) sourceC2325) = raw31964 := by
      apply Matrix.ext; unfold tripleCharges sourceA2325 sourceB2325 sourceC2325 difference raw31964; decide +kernel
    rw [ha]
    exact (canonical31964 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2325 + difference 1 1) (sourceB2325 + difference 1 1) sourceC2325) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3158) := by
    have ha : (tripleCharges (sourceA2325 + difference 1 1) (sourceB2325 + difference 1 1) sourceC2325) = raw31965 := by
      apply Matrix.ext; unfold tripleCharges sourceA2325 sourceB2325 sourceC2325 difference raw31965; decide +kernel
    rw [ha]
    exact (canonical31965 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2325 + difference 2 1) (sourceB2325 + difference 1 2) sourceC2325) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3128) := by
    have ha : (tripleCharges (sourceA2325 + difference 2 1) (sourceB2325 + difference 1 2) sourceC2325) = raw31966 := by
      apply Matrix.ext; unfold tripleCharges sourceA2325 sourceB2325 sourceC2325 difference raw31966; decide +kernel
    rw [ha]
    exact (canonical31966 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2325 + difference 3 1) (sourceB2325 + difference 1 3) sourceC2325) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3132) := by
    have ha : (tripleCharges (sourceA2325 + difference 3 1) (sourceB2325 + difference 1 3) sourceC2325) = raw31967 := by
      apply Matrix.ext; unfold tripleCharges sourceA2325 sourceB2325 sourceC2325 difference raw31967; decide +kernel
    rw [ha]
    exact (canonical31967 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2325 + difference 4 1) (sourceB2325 + difference 1 4) sourceC2325) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3132) := by
    have ha : (tripleCharges (sourceA2325 + difference 4 1) (sourceB2325 + difference 1 4) sourceC2325) = raw31968 := by
      apply Matrix.ext; unfold tripleCharges sourceA2325 sourceB2325 sourceC2325 difference raw31968; decide +kernel
    rw [ha]
    exact (canonical31968 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2325 + difference 5 1) (sourceB2325 + difference 1 5) sourceC2325) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2899) := by
    have ha : (tripleCharges (sourceA2325 + difference 5 1) (sourceB2325 + difference 1 5) sourceC2325) = raw31969 := by
      apply Matrix.ext; unfold tripleCharges sourceA2325 sourceB2325 sourceC2325 difference raw31969; decide +kernel
    rw [ha]
    exact (canonical31969 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2325 + sourceB2325) sourceC2325) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA2325 + sourceB2325) sourceC2325) = raw31970 := by
      apply Matrix.ext; unfold doubleCharges sourceA2325 sourceB2325 sourceC2325 raw31970; decide +kernel
    rw [ha]
    exact (canonical31970 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2325 sourceB2325 sourceC2325
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2325, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2326 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2326 : Charge := ![3, -2, 0, 0, -1, 0]
def sourceC2326 : Charge := ![0, 3, 0, -1, 0, -2]
def sourceForm2326 : Integer.Sparse Master := [(Sum.inr 2435, 1), (Sum.inr 3127, 1), (Sum.inr 3129, 1), (Sum.inr 3131, 1), (Sum.inr 3156, 1), (Sum.inr 3391, 1), (Sum.inr 4084, -1)]

theorem sourceEq2326 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2326 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2326 + difference 0 1) (sourceB2326 + difference 1 0) sourceC2326) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3391) := by
    have ha : (tripleCharges (sourceA2326 + difference 0 1) (sourceB2326 + difference 1 0) sourceC2326) = raw31971 := by
      apply Matrix.ext; unfold tripleCharges sourceA2326 sourceB2326 sourceC2326 difference raw31971; decide +kernel
    rw [ha]
    exact (canonical31971 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2326 + difference 1 1) (sourceB2326 + difference 1 1) sourceC2326) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3156) := by
    have ha : (tripleCharges (sourceA2326 + difference 1 1) (sourceB2326 + difference 1 1) sourceC2326) = raw31972 := by
      apply Matrix.ext; unfold tripleCharges sourceA2326 sourceB2326 sourceC2326 difference raw31972; decide +kernel
    rw [ha]
    exact (canonical31972 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2326 + difference 2 1) (sourceB2326 + difference 1 2) sourceC2326) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3127) := by
    have ha : (tripleCharges (sourceA2326 + difference 2 1) (sourceB2326 + difference 1 2) sourceC2326) = raw31973 := by
      apply Matrix.ext; unfold tripleCharges sourceA2326 sourceB2326 sourceC2326 difference raw31973; decide +kernel
    rw [ha]
    exact (canonical31973 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2326 + difference 3 1) (sourceB2326 + difference 1 3) sourceC2326) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3129) := by
    have ha : (tripleCharges (sourceA2326 + difference 3 1) (sourceB2326 + difference 1 3) sourceC2326) = raw31974 := by
      apply Matrix.ext; unfold tripleCharges sourceA2326 sourceB2326 sourceC2326 difference raw31974; decide +kernel
    rw [ha]
    exact (canonical31974 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2326 + difference 4 1) (sourceB2326 + difference 1 4) sourceC2326) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3131) := by
    have ha : (tripleCharges (sourceA2326 + difference 4 1) (sourceB2326 + difference 1 4) sourceC2326) = raw31975 := by
      apply Matrix.ext; unfold tripleCharges sourceA2326 sourceB2326 sourceC2326 difference raw31975; decide +kernel
    rw [ha]
    exact (canonical31975 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2326 + difference 5 1) (sourceB2326 + difference 1 5) sourceC2326) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2435) := by
    have ha : (tripleCharges (sourceA2326 + difference 5 1) (sourceB2326 + difference 1 5) sourceC2326) = raw31976 := by
      apply Matrix.ext; unfold tripleCharges sourceA2326 sourceB2326 sourceC2326 difference raw31976; decide +kernel
    rw [ha]
    exact (canonical31976 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2326 + sourceB2326) sourceC2326) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2326 + sourceB2326) sourceC2326) = raw31977 := by
      apply Matrix.ext; unfold doubleCharges sourceA2326 sourceB2326 sourceC2326 raw31977; decide +kernel
    rw [ha]
    exact (canonical31977 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2326 sourceB2326 sourceC2326
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2326, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2327 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2327 : Charge := ![1, 0, 1, -1, 1, -2]
def sourceC2327 : Charge := ![2, 1, -1, 0, -2, 0]
def sourceForm2327 : Integer.Sparse Master := [(Sum.inr 1130, 1), (Sum.inr 2333, 1), (Sum.inr 2481, 1), (Sum.inr 2494, 1), (Sum.inr 2508, 1), (Sum.inr 2515, 1), (Sum.inr 4092, -1)]

theorem sourceEq2327 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2327 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2327 + difference 2 0) (sourceB2327 + difference 0 2) sourceC2327) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1130) := by
    have ha : (tripleCharges (sourceA2327 + difference 2 0) (sourceB2327 + difference 0 2) sourceC2327) = raw31978 := by
      apply Matrix.ext; unfold tripleCharges sourceA2327 sourceB2327 sourceC2327 difference raw31978; decide +kernel
    rw [ha]
    exact (canonical31978 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2327 + difference 2 1) (sourceB2327 + difference 1 2) sourceC2327) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2333) := by
    have ha : (tripleCharges (sourceA2327 + difference 2 1) (sourceB2327 + difference 1 2) sourceC2327) = raw31979 := by
      apply Matrix.ext; unfold tripleCharges sourceA2327 sourceB2327 sourceC2327 difference raw31979; decide +kernel
    rw [ha]
    exact (canonical31979 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2327 + difference 2 2) (sourceB2327 + difference 2 2) sourceC2327) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2481) := by
    have ha : (tripleCharges (sourceA2327 + difference 2 2) (sourceB2327 + difference 2 2) sourceC2327) = raw31980 := by
      apply Matrix.ext; unfold tripleCharges sourceA2327 sourceB2327 sourceC2327 difference raw31980; decide +kernel
    rw [ha]
    exact (canonical31980 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2327 + difference 2 3) (sourceB2327 + difference 3 2) sourceC2327) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA2327 + difference 2 3) (sourceB2327 + difference 3 2) sourceC2327) = raw31981 := by
      apply Matrix.ext; unfold tripleCharges sourceA2327 sourceB2327 sourceC2327 difference raw31981; decide +kernel
    rw [ha]
    exact (canonical31981 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2327 + difference 2 4) (sourceB2327 + difference 4 2) sourceC2327) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2494) := by
    have ha : (tripleCharges (sourceA2327 + difference 2 4) (sourceB2327 + difference 4 2) sourceC2327) = raw31982 := by
      apply Matrix.ext; unfold tripleCharges sourceA2327 sourceB2327 sourceC2327 difference raw31982; decide +kernel
    rw [ha]
    exact (canonical31982 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2327 + difference 2 5) (sourceB2327 + difference 5 2) sourceC2327) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2508) := by
    have ha : (tripleCharges (sourceA2327 + difference 2 5) (sourceB2327 + difference 5 2) sourceC2327) = raw31983 := by
      apply Matrix.ext; unfold tripleCharges sourceA2327 sourceB2327 sourceC2327 difference raw31983; decide +kernel
    rw [ha]
    exact (canonical31983 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2327 + sourceB2327) sourceC2327) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2327 + sourceB2327) sourceC2327) = raw30305 := by
      apply Matrix.ext; unfold doubleCharges sourceA2327 sourceB2327 sourceC2327 raw30305; decide +kernel
    rw [ha]
    exact (canonical30305 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2327 sourceB2327 sourceC2327
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2327, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2328 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2328 : Charge := ![2, 1, -1, 0, -2, 0]
def sourceC2328 : Charge := ![1, 0, 1, -1, 1, -2]
def sourceForm2328 : Integer.Sparse Master := [(Sum.inr 2437, 1), (Sum.inr 2900, 1), (Sum.inr 2902, 1), (Sum.inr 2954, 1), (Sum.inr 2984, 1), (Sum.inr 3787, 1), (Sum.inr 4091, -1)]

theorem sourceEq2328 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2328 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2328 + difference 0 2) (sourceB2328 + difference 2 0) sourceC2328) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3787) := by
    have ha : (tripleCharges (sourceA2328 + difference 0 2) (sourceB2328 + difference 2 0) sourceC2328) = raw31984 := by
      apply Matrix.ext; unfold tripleCharges sourceA2328 sourceB2328 sourceC2328 difference raw31984; decide +kernel
    rw [ha]
    exact (canonical31984 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2328 + difference 1 2) (sourceB2328 + difference 2 1) sourceC2328) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA2328 + difference 1 2) (sourceB2328 + difference 2 1) sourceC2328) = raw23811 := by
      apply Matrix.ext; unfold tripleCharges sourceA2328 sourceB2328 sourceC2328 difference raw23811; decide +kernel
    rw [ha]
    exact (canonical23811 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2328 + difference 2 2) (sourceB2328 + difference 2 2) sourceC2328) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2984) := by
    have ha : (tripleCharges (sourceA2328 + difference 2 2) (sourceB2328 + difference 2 2) sourceC2328) = raw31985 := by
      apply Matrix.ext; unfold tripleCharges sourceA2328 sourceB2328 sourceC2328 difference raw31985; decide +kernel
    rw [ha]
    exact (canonical31985 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2328 + difference 3 2) (sourceB2328 + difference 2 3) sourceC2328) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2900) := by
    have ha : (tripleCharges (sourceA2328 + difference 3 2) (sourceB2328 + difference 2 3) sourceC2328) = raw31986 := by
      apply Matrix.ext; unfold tripleCharges sourceA2328 sourceB2328 sourceC2328 difference raw31986; decide +kernel
    rw [ha]
    exact (canonical31986 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2328 + difference 4 2) (sourceB2328 + difference 2 4) sourceC2328) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2902) := by
    have ha : (tripleCharges (sourceA2328 + difference 4 2) (sourceB2328 + difference 2 4) sourceC2328) = raw31987 := by
      apply Matrix.ext; unfold tripleCharges sourceA2328 sourceB2328 sourceC2328 difference raw31987; decide +kernel
    rw [ha]
    exact (canonical31987 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2328 + difference 5 2) (sourceB2328 + difference 2 5) sourceC2328) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2437) := by
    have ha : (tripleCharges (sourceA2328 + difference 5 2) (sourceB2328 + difference 2 5) sourceC2328) = raw31988 := by
      apply Matrix.ext; unfold tripleCharges sourceA2328 sourceB2328 sourceC2328 difference raw31988; decide +kernel
    rw [ha]
    exact (canonical31988 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2328 + sourceB2328) sourceC2328) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2328 + sourceB2328) sourceC2328) = raw23817 := by
      apply Matrix.ext; unfold doubleCharges sourceA2328 sourceB2328 sourceC2328 raw23817; decide +kernel
    rw [ha]
    exact (canonical23817 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2328 sourceB2328 sourceC2328
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2328, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2329 : Charge := ![1, 0, 1, -1, 1, -2]
def sourceB2329 : Charge := ![2, 1, -1, 0, -2, 0]
def sourceC2329 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceForm2329 : Integer.Sparse Master := [(Sum.inr 2476, 1), (Sum.inr 3463, 1), (Sum.inr 3499, 1), (Sum.inr 3501, 1), (Sum.inr 3514, 1), (Sum.inr 3564, 1), (Sum.inr 4080, -1)]

theorem sourceEq2329 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2329 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2329 + difference 0 0) (sourceB2329 + difference 0 0) sourceC2329) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3463) := by
    have ha : (tripleCharges (sourceA2329 + difference 0 0) (sourceB2329 + difference 0 0) sourceC2329) = raw31897 := by
      apply Matrix.ext; unfold tripleCharges sourceA2329 sourceB2329 sourceC2329 difference raw31897; decide +kernel
    rw [ha]
    exact (canonical31897 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2329 + difference 0 1) (sourceB2329 + difference 1 0) sourceC2329) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3501) := by
    have ha : (tripleCharges (sourceA2329 + difference 0 1) (sourceB2329 + difference 1 0) sourceC2329) = raw31989 := by
      apply Matrix.ext; unfold tripleCharges sourceA2329 sourceB2329 sourceC2329 difference raw31989; decide +kernel
    rw [ha]
    exact (canonical31989 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2329 + difference 0 2) (sourceB2329 + difference 2 0) sourceC2329) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3564) := by
    have ha : (tripleCharges (sourceA2329 + difference 0 2) (sourceB2329 + difference 2 0) sourceC2329) = raw31990 := by
      apply Matrix.ext; unfold tripleCharges sourceA2329 sourceB2329 sourceC2329 difference raw31990; decide +kernel
    rw [ha]
    exact (canonical31990 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2329 + difference 0 3) (sourceB2329 + difference 3 0) sourceC2329) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3499) := by
    have ha : (tripleCharges (sourceA2329 + difference 0 3) (sourceB2329 + difference 3 0) sourceC2329) = raw31991 := by
      apply Matrix.ext; unfold tripleCharges sourceA2329 sourceB2329 sourceC2329 difference raw31991; decide +kernel
    rw [ha]
    exact (canonical31991 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2329 + difference 0 4) (sourceB2329 + difference 4 0) sourceC2329) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3514) := by
    have ha : (tripleCharges (sourceA2329 + difference 0 4) (sourceB2329 + difference 4 0) sourceC2329) = raw31992 := by
      apply Matrix.ext; unfold tripleCharges sourceA2329 sourceB2329 sourceC2329 difference raw31992; decide +kernel
    rw [ha]
    exact (canonical31992 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2329 + difference 0 5) (sourceB2329 + difference 5 0) sourceC2329) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2476) := by
    have ha : (tripleCharges (sourceA2329 + difference 0 5) (sourceB2329 + difference 5 0) sourceC2329) = raw31993 := by
      apply Matrix.ext; unfold tripleCharges sourceA2329 sourceB2329 sourceC2329 difference raw31993; decide +kernel
    rw [ha]
    exact (canonical31993 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2329 + sourceB2329) sourceC2329) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2329 + sourceB2329) sourceC2329) = raw31902 := by
      apply Matrix.ext; unfold doubleCharges sourceA2329 sourceB2329 sourceC2329 raw31902; decide +kernel
    rw [ha]
    exact (canonical31902 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2329 sourceB2329 sourceC2329
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2329, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2330 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2330 : Charge := ![1, 0, 2, -1, -1, -1]
def sourceC2330 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceForm2330 : Integer.Sparse Master := [(Sum.inr 1127, 1), (Sum.inr 2331, 1), (Sum.inr 2493, 1), (Sum.inr 2508, 1), (Sum.inr 2512, 2), (Sum.inr 4092, -1)]

theorem sourceEq2330 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2330 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2330 + difference 2 0) (sourceB2330 + difference 0 2) sourceC2330) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1127) := by
    have ha : (tripleCharges (sourceA2330 + difference 2 0) (sourceB2330 + difference 0 2) sourceC2330) = raw31994 := by
      apply Matrix.ext; unfold tripleCharges sourceA2330 sourceB2330 sourceC2330 difference raw31994; decide +kernel
    rw [ha]
    exact (canonical31994 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2330 + difference 2 1) (sourceB2330 + difference 1 2) sourceC2330) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2331) := by
    have ha : (tripleCharges (sourceA2330 + difference 2 1) (sourceB2330 + difference 1 2) sourceC2330) = raw31995 := by
      apply Matrix.ext; unfold tripleCharges sourceA2330 sourceB2330 sourceC2330 difference raw31995; decide +kernel
    rw [ha]
    exact (canonical31995 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2330 + difference 2 2) (sourceB2330 + difference 2 2) sourceC2330) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2493) := by
    have ha : (tripleCharges (sourceA2330 + difference 2 2) (sourceB2330 + difference 2 2) sourceC2330) = raw11881 := by
      apply Matrix.ext; unfold tripleCharges sourceA2330 sourceB2330 sourceC2330 difference raw11881; decide +kernel
    rw [ha]
    exact (canonical11881 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2330 + difference 2 3) (sourceB2330 + difference 3 2) sourceC2330) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA2330 + difference 2 3) (sourceB2330 + difference 3 2) sourceC2330) = raw31996 := by
      apply Matrix.ext; unfold tripleCharges sourceA2330 sourceB2330 sourceC2330 difference raw31996; decide +kernel
    rw [ha]
    exact (canonical31996 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2330 + difference 2 4) (sourceB2330 + difference 4 2) sourceC2330) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA2330 + difference 2 4) (sourceB2330 + difference 4 2) sourceC2330) = raw31997 := by
      apply Matrix.ext; unfold tripleCharges sourceA2330 sourceB2330 sourceC2330 difference raw31997; decide +kernel
    rw [ha]
    exact (canonical31997 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2330 + difference 2 5) (sourceB2330 + difference 5 2) sourceC2330) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2508) := by
    have ha : (tripleCharges (sourceA2330 + difference 2 5) (sourceB2330 + difference 5 2) sourceC2330) = raw11878 := by
      apply Matrix.ext; unfold tripleCharges sourceA2330 sourceB2330 sourceC2330 difference raw11878; decide +kernel
    rw [ha]
    exact (canonical11878 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2330 + sourceB2330) sourceC2330) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2330 + sourceB2330) sourceC2330) = raw11868 := by
      apply Matrix.ext; unfold doubleCharges sourceA2330 sourceB2330 sourceC2330 raw11868; decide +kernel
    rw [ha]
    exact (canonical11868 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2330 sourceB2330 sourceC2330
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2330, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2331 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2331 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC2331 : Charge := ![1, 0, 2, -1, -1, -1]
def sourceForm2331 : Integer.Sparse Master := [(Sum.inr 2847, 1), (Sum.inr 2849, 2), (Sum.inr 2884, 1), (Sum.inr 2976, 1), (Sum.inr 3945, 1), (Sum.inr 4091, -1)]

theorem sourceEq2331 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2331 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2331 + difference 0 2) (sourceB2331 + difference 2 0) sourceC2331) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3945) := by
    have ha : (tripleCharges (sourceA2331 + difference 0 2) (sourceB2331 + difference 2 0) sourceC2331) = raw31998 := by
      apply Matrix.ext; unfold tripleCharges sourceA2331 sourceB2331 sourceC2331 difference raw31998; decide +kernel
    rw [ha]
    exact (canonical31998 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2331 + difference 1 2) (sourceB2331 + difference 2 1) sourceC2331) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2884) := by
    have ha : (tripleCharges (sourceA2331 + difference 1 2) (sourceB2331 + difference 2 1) sourceC2331) = raw23839 := by
      apply Matrix.ext; unfold tripleCharges sourceA2331 sourceB2331 sourceC2331 difference raw23839; decide +kernel
    rw [ha]
    exact (canonical23839 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2331 + difference 2 2) (sourceB2331 + difference 2 2) sourceC2331) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2976) := by
    have ha : (tripleCharges (sourceA2331 + difference 2 2) (sourceB2331 + difference 2 2) sourceC2331) = raw13068 := by
      apply Matrix.ext; unfold tripleCharges sourceA2331 sourceB2331 sourceC2331 difference raw13068; decide +kernel
    rw [ha]
    exact (canonical13068 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2331 + difference 3 2) (sourceB2331 + difference 2 3) sourceC2331) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2849) := by
    have ha : (tripleCharges (sourceA2331 + difference 3 2) (sourceB2331 + difference 2 3) sourceC2331) = raw31999 := by
      apply Matrix.ext; unfold tripleCharges sourceA2331 sourceB2331 sourceC2331 difference raw31999; decide +kernel
    rw [ha]
    exact (canonical31999 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2331 + difference 4 2) (sourceB2331 + difference 2 4) sourceC2331) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2849) := by
    have ha : (tripleCharges (sourceA2331 + difference 4 2) (sourceB2331 + difference 2 4) sourceC2331) = raw32000 := by
      apply Matrix.ext; unfold tripleCharges sourceA2331 sourceB2331 sourceC2331 difference raw32000; decide +kernel
    rw [ha]
    exact (canonical32000 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2331 + difference 5 2) (sourceB2331 + difference 2 5) sourceC2331) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2847) := by
    have ha : (tripleCharges (sourceA2331 + difference 5 2) (sourceB2331 + difference 2 5) sourceC2331) = raw32001 := by
      apply Matrix.ext; unfold tripleCharges sourceA2331 sourceB2331 sourceC2331 difference raw32001; decide +kernel
    rw [ha]
    exact (canonical32001 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2331 + sourceB2331) sourceC2331) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2331 + sourceB2331) sourceC2331) = raw13064 := by
      apply Matrix.ext; unfold doubleCharges sourceA2331 sourceB2331 sourceC2331 raw13064; decide +kernel
    rw [ha]
    exact (canonical13064 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2331 sourceB2331 sourceC2331
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2331, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2332 : Charge := ![1, 0, 2, -1, -1, -1]
def sourceB2332 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC2332 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceForm2332 : Integer.Sparse Master := [(Sum.inr 3370, 1), (Sum.inr 3371, 2), (Sum.inr 3384, 1), (Sum.inr 3461, 1), (Sum.inr 3521, 1), (Sum.inr 4080, -1)]

theorem sourceEq2332 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2332 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2332 + difference 0 0) (sourceB2332 + difference 0 0) sourceC2332) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3461) := by
    have ha : (tripleCharges (sourceA2332 + difference 0 0) (sourceB2332 + difference 0 0) sourceC2332) = raw31916 := by
      apply Matrix.ext; unfold tripleCharges sourceA2332 sourceB2332 sourceC2332 difference raw31916; decide +kernel
    rw [ha]
    exact (canonical31916 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2332 + difference 0 1) (sourceB2332 + difference 1 0) sourceC2332) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3384) := by
    have ha : (tripleCharges (sourceA2332 + difference 0 1) (sourceB2332 + difference 1 0) sourceC2332) = raw32002 := by
      apply Matrix.ext; unfold tripleCharges sourceA2332 sourceB2332 sourceC2332 difference raw32002; decide +kernel
    rw [ha]
    exact (canonical32002 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2332 + difference 0 2) (sourceB2332 + difference 2 0) sourceC2332) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3521) := by
    have ha : (tripleCharges (sourceA2332 + difference 0 2) (sourceB2332 + difference 2 0) sourceC2332) = raw32003 := by
      apply Matrix.ext; unfold tripleCharges sourceA2332 sourceB2332 sourceC2332 difference raw32003; decide +kernel
    rw [ha]
    exact (canonical32003 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2332 + difference 0 3) (sourceB2332 + difference 3 0) sourceC2332) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3371) := by
    have ha : (tripleCharges (sourceA2332 + difference 0 3) (sourceB2332 + difference 3 0) sourceC2332) = raw32004 := by
      apply Matrix.ext; unfold tripleCharges sourceA2332 sourceB2332 sourceC2332 difference raw32004; decide +kernel
    rw [ha]
    exact (canonical32004 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2332 + difference 0 4) (sourceB2332 + difference 4 0) sourceC2332) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3371) := by
    have ha : (tripleCharges (sourceA2332 + difference 0 4) (sourceB2332 + difference 4 0) sourceC2332) = raw32005 := by
      apply Matrix.ext; unfold tripleCharges sourceA2332 sourceB2332 sourceC2332 difference raw32005; decide +kernel
    rw [ha]
    exact (canonical32005 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2332 + difference 0 5) (sourceB2332 + difference 5 0) sourceC2332) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3370) := by
    have ha : (tripleCharges (sourceA2332 + difference 0 5) (sourceB2332 + difference 5 0) sourceC2332) = raw32006 := by
      apply Matrix.ext; unfold tripleCharges sourceA2332 sourceB2332 sourceC2332 difference raw32006; decide +kernel
    rw [ha]
    exact (canonical32006 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2332 + sourceB2332) sourceC2332) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2332 + sourceB2332) sourceC2332) = raw31902 := by
      apply Matrix.ext; unfold doubleCharges sourceA2332 sourceB2332 sourceC2332 raw31902; decide +kernel
    rw [ha]
    exact (canonical31902 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2332 sourceB2332 sourceC2332
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2332, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2333 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2333 : Charge := ![2, 1, -2, 0, -1, 0]
def sourceC2333 : Charge := ![1, 0, 2, -1, 0, -2]
def sourceForm2333 : Integer.Sparse Master := [(Sum.inr 2426, 1), (Sum.inr 2846, 1), (Sum.inr 2848, 1), (Sum.inr 2881, 1), (Sum.inr 2974, 1), (Sum.inr 3781, 1), (Sum.inr 4092, -1)]

theorem sourceEq2333 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2333 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2333 + difference 0 2) (sourceB2333 + difference 2 0) sourceC2333) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3781) := by
    have ha : (tripleCharges (sourceA2333 + difference 0 2) (sourceB2333 + difference 2 0) sourceC2333) = raw32007 := by
      apply Matrix.ext; unfold tripleCharges sourceA2333 sourceB2333 sourceC2333 difference raw32007; decide +kernel
    rw [ha]
    exact (canonical32007 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2333 + difference 1 2) (sourceB2333 + difference 2 1) sourceC2333) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2881) := by
    have ha : (tripleCharges (sourceA2333 + difference 1 2) (sourceB2333 + difference 2 1) sourceC2333) = raw23860 := by
      apply Matrix.ext; unfold tripleCharges sourceA2333 sourceB2333 sourceC2333 difference raw23860; decide +kernel
    rw [ha]
    exact (canonical23860 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2333 + difference 2 2) (sourceB2333 + difference 2 2) sourceC2333) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2974) := by
    have ha : (tripleCharges (sourceA2333 + difference 2 2) (sourceB2333 + difference 2 2) sourceC2333) = raw32008 := by
      apply Matrix.ext; unfold tripleCharges sourceA2333 sourceB2333 sourceC2333 difference raw32008; decide +kernel
    rw [ha]
    exact (canonical32008 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2333 + difference 3 2) (sourceB2333 + difference 2 3) sourceC2333) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2846) := by
    have ha : (tripleCharges (sourceA2333 + difference 3 2) (sourceB2333 + difference 2 3) sourceC2333) = raw32009 := by
      apply Matrix.ext; unfold tripleCharges sourceA2333 sourceB2333 sourceC2333 difference raw32009; decide +kernel
    rw [ha]
    exact (canonical32009 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2333 + difference 4 2) (sourceB2333 + difference 2 4) sourceC2333) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2848) := by
    have ha : (tripleCharges (sourceA2333 + difference 4 2) (sourceB2333 + difference 2 4) sourceC2333) = raw32010 := by
      apply Matrix.ext; unfold tripleCharges sourceA2333 sourceB2333 sourceC2333 difference raw32010; decide +kernel
    rw [ha]
    exact (canonical32010 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2333 + difference 5 2) (sourceB2333 + difference 2 5) sourceC2333) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2426) := by
    have ha : (tripleCharges (sourceA2333 + difference 5 2) (sourceB2333 + difference 2 5) sourceC2333) = raw32011 := by
      apply Matrix.ext; unfold tripleCharges sourceA2333 sourceB2333 sourceC2333 difference raw32011; decide +kernel
    rw [ha]
    exact (canonical32011 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2333 + sourceB2333) sourceC2333) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2333 + sourceB2333) sourceC2333) = raw23866 := by
      apply Matrix.ext; unfold doubleCharges sourceA2333 sourceB2333 sourceC2333 raw23866; decide +kernel
    rw [ha]
    exact (canonical23866 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2333 sourceB2333 sourceC2333
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2333, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2334 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2334 : Charge := ![1, 1, -1, -1, -1, 1]
def sourceC2334 : Charge := ![2, 0, 1, 0, 0, -3]
def sourceForm2334 : Integer.Sparse Master := [(Sum.inr 1960, 1), (Sum.inr 2427, 2), (Sum.inr 2509, 1), (Sum.inr 2552, 1), (Sum.inr 3493, 1), (Sum.inr 4084, -1)]

theorem sourceEq2334 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2334 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2334 + difference 0 2) (sourceB2334 + difference 2 0) sourceC2334) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3493) := by
    have ha : (tripleCharges (sourceA2334 + difference 0 2) (sourceB2334 + difference 2 0) sourceC2334) = raw32012 := by
      apply Matrix.ext; unfold tripleCharges sourceA2334 sourceB2334 sourceC2334 difference raw32012; decide +kernel
    rw [ha]
    exact (canonical32012 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2334 + difference 1 2) (sourceB2334 + difference 2 1) sourceC2334) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2509) := by
    have ha : (tripleCharges (sourceA2334 + difference 1 2) (sourceB2334 + difference 2 1) sourceC2334) = raw32013 := by
      apply Matrix.ext; unfold tripleCharges sourceA2334 sourceB2334 sourceC2334 difference raw32013; decide +kernel
    rw [ha]
    exact (canonical32013 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2334 + difference 2 2) (sourceB2334 + difference 2 2) sourceC2334) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2552) := by
    have ha : (tripleCharges (sourceA2334 + difference 2 2) (sourceB2334 + difference 2 2) sourceC2334) = raw32014 := by
      apply Matrix.ext; unfold tripleCharges sourceA2334 sourceB2334 sourceC2334 difference raw32014; decide +kernel
    rw [ha]
    exact (canonical32014 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2334 + difference 3 2) (sourceB2334 + difference 2 3) sourceC2334) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2427) := by
    have ha : (tripleCharges (sourceA2334 + difference 3 2) (sourceB2334 + difference 2 3) sourceC2334) = raw32015 := by
      apply Matrix.ext; unfold tripleCharges sourceA2334 sourceB2334 sourceC2334 difference raw32015; decide +kernel
    rw [ha]
    exact (canonical32015 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2334 + difference 4 2) (sourceB2334 + difference 2 4) sourceC2334) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2427) := by
    have ha : (tripleCharges (sourceA2334 + difference 4 2) (sourceB2334 + difference 2 4) sourceC2334) = raw29434 := by
      apply Matrix.ext; unfold tripleCharges sourceA2334 sourceB2334 sourceC2334 difference raw29434; decide +kernel
    rw [ha]
    exact (canonical29434 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2334 + difference 5 2) (sourceB2334 + difference 2 5) sourceC2334) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1960) := by
    have ha : (tripleCharges (sourceA2334 + difference 5 2) (sourceB2334 + difference 2 5) sourceC2334) = raw32016 := by
      apply Matrix.ext; unfold tripleCharges sourceA2334 sourceB2334 sourceC2334 difference raw32016; decide +kernel
    rw [ha]
    exact (canonical32016 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2334 + sourceB2334) sourceC2334) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2334 + sourceB2334) sourceC2334) = raw29437 := by
      apply Matrix.ext; unfold doubleCharges sourceA2334 sourceB2334 sourceC2334 raw29437; decide +kernel
    rw [ha]
    exact (canonical29437 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2334 sourceB2334 sourceC2334
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2334, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2335 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2335 : Charge := ![1, 1, -1, -1, 1, -1]
def sourceC2335 : Charge := ![2, 0, 1, 0, -2, -1]
def sourceForm2335 : Integer.Sparse Master := [(Sum.inr 2426, 1), (Sum.inr 2428, 1), (Sum.inr 2433, 1), (Sum.inr 2512, 1), (Sum.inr 2554, 1), (Sum.inr 3781, 1), (Sum.inr 4092, -1)]

theorem sourceEq2335 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2335 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2335 + difference 0 2) (sourceB2335 + difference 2 0) sourceC2335) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3781) := by
    have ha : (tripleCharges (sourceA2335 + difference 0 2) (sourceB2335 + difference 2 0) sourceC2335) = raw32017 := by
      apply Matrix.ext; unfold tripleCharges sourceA2335 sourceB2335 sourceC2335 difference raw32017; decide +kernel
    rw [ha]
    exact (canonical32017 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2335 + difference 1 2) (sourceB2335 + difference 2 1) sourceC2335) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA2335 + difference 1 2) (sourceB2335 + difference 2 1) sourceC2335) = raw32018 := by
      apply Matrix.ext; unfold tripleCharges sourceA2335 sourceB2335 sourceC2335 difference raw32018; decide +kernel
    rw [ha]
    exact (canonical32018 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2335 + difference 2 2) (sourceB2335 + difference 2 2) sourceC2335) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2554) := by
    have ha : (tripleCharges (sourceA2335 + difference 2 2) (sourceB2335 + difference 2 2) sourceC2335) = raw32019 := by
      apply Matrix.ext; unfold tripleCharges sourceA2335 sourceB2335 sourceC2335 difference raw32019; decide +kernel
    rw [ha]
    exact (canonical32019 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2335 + difference 3 2) (sourceB2335 + difference 2 3) sourceC2335) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2433) := by
    have ha : (tripleCharges (sourceA2335 + difference 3 2) (sourceB2335 + difference 2 3) sourceC2335) = raw32020 := by
      apply Matrix.ext; unfold tripleCharges sourceA2335 sourceB2335 sourceC2335 difference raw32020; decide +kernel
    rw [ha]
    exact (canonical32020 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2335 + difference 4 2) (sourceB2335 + difference 2 4) sourceC2335) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2428) := by
    have ha : (tripleCharges (sourceA2335 + difference 4 2) (sourceB2335 + difference 2 4) sourceC2335) = raw32021 := by
      apply Matrix.ext; unfold tripleCharges sourceA2335 sourceB2335 sourceC2335 difference raw32021; decide +kernel
    rw [ha]
    exact (canonical32021 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2335 + difference 5 2) (sourceB2335 + difference 2 5) sourceC2335) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2426) := by
    have ha : (tripleCharges (sourceA2335 + difference 5 2) (sourceB2335 + difference 2 5) sourceC2335) = raw27463 := by
      apply Matrix.ext; unfold tripleCharges sourceA2335 sourceB2335 sourceC2335 difference raw27463; decide +kernel
    rw [ha]
    exact (canonical27463 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2335 + sourceB2335) sourceC2335) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2335 + sourceB2335) sourceC2335) = raw27466 := by
      apply Matrix.ext; unfold doubleCharges sourceA2335 sourceB2335 sourceC2335 raw27466; decide +kernel
    rw [ha]
    exact (canonical27466 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2335 sourceB2335 sourceC2335
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2335, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
